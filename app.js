'use strict';

/*
 * こえそろえ - Dialogue Voice Leveler
 * All audio samples stay inside the user's browser.
 * Measurement: gated voice-active RMS (NOT LUFS / EBU R128).
 * Processing: a constant linear gain, limited by the sample-peak ceiling.
 */

(() => {
  const $ = (selector) => document.querySelector(selector);
  const dom = {
    fileInput: $('#fileInput'), dropzone: $('#dropzone'), fileList: $('#fileList'),
    fileCount: $('#fileCount'), toolbarCount: $('#toolbarCount'), clearAll: $('#clearAll'),
    fileFooter: $('#fileFooter'), footerInfo: $('#footerInfo'), addMore: $('#addMore'),
    exportAll: $('#exportAll'), formatWav: $('input[value="wav"]'),
    sampleRate: $('#sampleRate'), bitrate: $('#bitrate'), bitrateRow: $('#bitrateRow'),
    target: $('#target'), ceiling: $('#ceiling'), boost: $('#boost'), suffix: $('#suffix'),
    targetValue: $('#targetValue'), ceilingValue: $('#ceilingValue'), boostValue: $('#boostValue'),
    progressBox: $('#progressBox'), progressMessage: $('#progressMessage'),
    progressNumber: $('#progressNumber'), progressBar: $('#progressBar'), toastRegion: $('#toastRegion')
  };

  const state = {
    files: [], nextId: 1, analyzing: false, exporting: false,
    audioContext: null, playing: null, playbackToken: 0,
    targetDb: -20, ceilingDb: -1, maxBoostDb: 18, format: 'wav',
    outputRate: 44100, kbps: 192, suffix: '_leveled'
  };
  const MAX_FILE_SIZE = 250 * 1024 * 1024;
  const yieldUI = () => new Promise(resolve => setTimeout(resolve, 0));
  const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
  const dbToAmp = x => Math.pow(10, x / 20);
  const ampToDb = x => x > 1e-12 ? 20 * Math.log10(x) : -Infinity;
  const formatDb = (x, digits = 1) => Number.isFinite(x) ? `${x.toFixed(digits)} dB` : '—';
  const formatChange = x => `${x >= 0 ? '+' : ''}${x.toFixed(1)} dB`;
  const formatDuration = s => {
    const min = Math.floor(s / 60);
    const sec = Math.floor(s % 60).toString().padStart(2, '0');
    return `${min}:${sec}`;
  };
  const formatBytes = bytes => bytes < 1024 * 1024
    ? `${(bytes / 1024).toFixed(0)} KB` : `${(bytes / (1024 * 1024)).toFixed(1)} MB`;
  const escapeHtml = value => String(value).replace(/[&<>"']/g, c =>
    ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);

  function toast(message, type = 'info') {
    const element = document.createElement('div');
    element.className = `toast ${type}`;
    element.textContent = message;
    dom.toastRegion.append(element);
    setTimeout(() => { element.remove(); }, 4500);
  }

  function audioContext() {
    if (!state.audioContext || state.audioContext.state === 'closed') {
      const AudioContextClass = window.AudioContext || window.webkitAudioContext;
      if (!AudioContextClass) throw new Error('このブラウザはWeb Audio APIに対応していません。');
      try { state.audioContext = new AudioContextClass({ sampleRate: 44100 }); }
      catch { state.audioContext = new AudioContextClass(); }
    }
    return state.audioContext;
  }

  async function decode(file) {
    const arrayBuffer = await file.arrayBuffer();
    const audio = await audioContext().decodeAudioData(arrayBuffer);
    if (!audio.length || !audio.numberOfChannels) throw new Error('音声データが空です。');
    if (audio.numberOfChannels > 2) throw new Error('3チャンネル以上の音声は未対応です。モノラルまたはステレオを使用してください。');
    return audio;
  }

  /** Analyze the audio as 20 ms blocks, excluding blocks much quieter than speech. */
  function analyzeBuffer(buffer) {
    const channels = Array.from({ length: buffer.numberOfChannels }, (_, i) => buffer.getChannelData(i));
    const channelCount = channels.length;
    const frameSize = Math.max(128, Math.round(buffer.sampleRate * 0.020));
    const numFrames = Math.ceil(buffer.length / frameSize);
    const energies = new Float64Array(numFrames);
    const lengths = new Uint32Array(numFrames);
    let peak = 0;
    let loudestFrame = 0;

    for (let f = 0; f < numFrames; f++) {
      const start = f * frameSize;
      const end = Math.min(start + frameSize, buffer.length);
      let energy = 0;
      for (let ch = 0; ch < channelCount; ch++) {
        const samples = channels[ch];
        for (let i = start; i < end; i++) {
          const v = samples[i];
          energy += v * v;
          const a = Math.abs(v);
          if (a > peak) peak = a;
        }
      }
      const count = (end - start);
      const meanSquare = energy / (count * channelCount);
      energies[f] = meanSquare;
      lengths[f] = count;
      if (meanSquare > loudestFrame) loudestFrame = meanSquare;
    }

    const silence = peak < 1e-6;
    const loudestDb = ampToDb(Math.sqrt(loudestFrame));
    // At least 30 dB under the loudest 20ms segment, not below -55 dBFS.
    const gateDb = Math.max(-55, loudestDb - 30);
    const gateEnergy = Math.pow(10, gateDb / 10);
    let activeEnergy = 0;
    let activeLength = 0;
    if (!silence) {
      for (let f = 0; f < numFrames; f++) {
        if (energies[f] >= gateEnergy) {
          activeEnergy += energies[f] * lengths[f];
          activeLength += lengths[f];
        }
      }
    }
    // Whisper-quiet or heavily filtered files: fall back to the whole-file RMS.
    if (!silence && !activeLength) {
      for (let f = 0; f < numFrames; f++) {
        activeEnergy += energies[f] * lengths[f];
        activeLength += lengths[f];
      }
    }
    const rms = activeLength ? Math.sqrt(activeEnergy / activeLength) : 0;

    const waveBins = 108;
    const waveform = new Float32Array(waveBins);
    // A maximum of ~1500 sample points per bin is enough for a small preview.
    for (let b = 0; b < waveBins; b++) {
      const start = Math.floor(b * buffer.length / waveBins);
      const end = Math.max(start + 1, Math.floor((b + 1) * buffer.length / waveBins));
      const step = Math.max(1, Math.floor((end - start) / 1500));
      let top = 0;
      for (let ch = 0; ch < channelCount; ch++) {
        for (let i = start; i < end; i += step) {
          const a = Math.abs(channels[ch][i]);
          if (a > top) top = a;
        }
      }
      waveform[b] = top;
    }
    return {
      length: buffer.duration, channels: channelCount,
      sampleRate: buffer.sampleRate, peak, peakDb: ampToDb(peak),
      activeRms: rms, activeDb: ampToDb(rms),
      activeRatio: activeLength / buffer.length, silence, waveform
    };
  }

  function gainInfo(stats) {
    if (!stats || stats.silence || !Number.isFinite(stats.activeDb)) {
      return { gain: 1, gainDb: 0, outputDb: -Infinity, outputPeakDb: -Infinity, reason: '' };
    }
    const desiredGain = dbToAmp(state.targetDb - stats.activeDb);
    const maxGain = dbToAmp(state.maxBoostDb);
    const ceilingGain = stats.peak > 0 ? dbToAmp(state.ceilingDb) / stats.peak : Infinity;
    const gain = Math.min(desiredGain, maxGain, ceilingGain);
    const reason = gain >= desiredGain * (1 - 1e-8) ? '' :
      (ceilingGain <= maxGain && ceilingGain < desiredGain ? 'ピーク上限を優先したため、目標音量には届きません。' :
        '最大増幅量を優先したため、目標音量には届きません。');
    return {
      gain, gainDb: ampToDb(gain), reason,
      outputDb: stats.activeDb + ampToDb(gain),
      outputPeakDb: stats.peakDb + ampToDb(gain)
    };
  }

  function waveSvg(stats, gain) {
    const base = Math.max(stats.peak, stats.peak * gain, 0.02);
    let raw = '', adjusted = '';
    const wave = stats.waveform;
    const width = 480;
    for (let i = 0; i < wave.length; i++) {
      const x = (i + .5) * width / wave.length;
      const h1 = Math.max(.5, wave[i] / base * 21);
      const h2 = Math.max(.5, wave[i] * gain / base * 21);
      raw += `M${(x - .85).toFixed(1)},${(23 - h1).toFixed(1)}V${(23 + h1).toFixed(1)} `;
      adjusted += `M${(x + .85).toFixed(1)},${(23 - h2).toFixed(1)}V${(23 + h2).toFixed(1)} `;
    }
    return `<svg viewBox="0 0 480 46" preserveAspectRatio="none" role="img" aria-label="元音量と調整後の波形の比較"><path class="baseline" d="M0 23H480"/><path class="raw" d="${raw}"/><path class="adjusted" d="${adjusted}"/></svg>`;
  }

  function createRow(item) {
    const ext = item.file.name.toLowerCase().endsWith('.mp3') ? 'MP3' : 'WAV';
    const name = escapeHtml(item.file.name);
    if (item.status !== 'ready') {
      const isError = item.status === 'error';
      return `<article class="file-row" data-id="${item.id}">
        <div class="row-main"><div class="file-badge">${ext}</div><div class="file-details">
        <div class="file-title" title="${name}">${name}</div><div class="file-subtitle"><span>${formatBytes(item.file.size)}</span></div></div>
        <button class="file-remove" type="button" data-action="remove" data-id="${item.id}" aria-label="${name} を削除">×</button></div>
        ${isError ? `<div class="error-note">⚠ ${escapeHtml(item.error || '解析に失敗しました。')}</div>` :
        '<div class="pending-note"><span class="spinner"></span> 音声を解析しています…</div>'}</article>`;
    }
    const stats = item.stats;
    const gain = gainInfo(stats);
    const playingRaw = state.playing && state.playing.id === item.id && state.playing.mode === 'raw';
    const playingNew = state.playing && state.playing.id === item.id && state.playing.mode === 'new';
    const note = gain.reason ? `<div class="limit-note">ℹ ${gain.reason}</div>` : '';
    return `<article class="file-row" data-id="${item.id}">
      <div class="row-main"><div class="file-badge">${ext}</div><div class="file-details">
        <div class="file-title" title="${name}">${name}</div>
        <div class="file-subtitle"><span>${formatDuration(stats.length)}</span><span>${stats.channels === 1 ? 'モノラル' : 'ステレオ'}</span><span>${formatBytes(item.file.size)}</span></div>
        </div><button class="file-remove" type="button" data-action="remove" data-id="${item.id}" aria-label="${name} を削除" ${state.exporting ? 'disabled' : ''}>×</button></div>
      <div class="file-visual"><div class="waveform">${waveSvg(stats, gain.gain)}</div><div class="volume-change">${stats.silence ? '無音' : formatChange(gain.gainDb)}</div></div>
      <div class="row-bottom"><div class="metrics"><span class="metric">元 <strong>${formatDb(stats.activeDb)}</strong></span><span class="metric">→ 後 <strong><em>${formatDb(gain.outputDb)}</em></strong></span><span class="metric">Peak <strong>${formatDb(gain.outputPeakDb)}</strong></span></div>
      <div class="row-actions"><button type="button" class="mini-button ${playingRaw ? 'active' : ''}" data-action="play-raw" data-id="${item.id}" aria-label="${name} 元の音声を再生" ${state.exporting ? 'disabled' : ''}>${playingRaw ? '■ 停止' : '▶ 元'}</button>
      <button type="button" class="mini-button ${playingNew ? 'active' : ''}" data-action="play-new" data-id="${item.id}" aria-label="${name} 調整後の音声を再生" ${state.exporting ? 'disabled' : ''}>${playingNew ? '■ 停止' : '▶ 調整後'}</button>
      <button type="button" class="mini-button save" data-action="save" data-id="${item.id}" ${state.exporting ? 'disabled' : ''}>↓ 保存</button></div></div>${note}</article>`;
  }

  function render() {
    const ready = state.files.filter(f => f.status === 'ready');
    const loading = state.files.some(f => f.status === 'pending' || f.status === 'analyzing');
    dom.fileCount.textContent = state.files.length;
    dom.clearAll.disabled = state.exporting || !state.files.length;
    dom.exportAll.disabled = state.exporting || loading || ready.length === 0;
    dom.toolbarCount.textContent = state.files.length
      ? `${ready.length} 件の音声を解析済み${loading ? ' · 解析中…' : ''}` : 'まだファイルがありません';
    dom.fileList.innerHTML = state.files.length
      ? state.files.map(createRow).join('')
      : '<div class="empty-state"><div class="empty-doodle" aria-hidden="true">♪ <span>〜</span> ♬</div><strong>まだ声が並んでいません。</strong><p>まずは台詞音声を読み込んでください。<br>ファイルごとの音量差を自動でチェックします。</p></div>';
    dom.fileFooter.hidden = state.files.length === 0;
    const total = ready.reduce((acc, f) => acc + f.stats.length, 0);
    dom.footerInfo.textContent = `${ready.length} ファイル · 合計 ${formatDuration(total)}`;
  }

  function fileSupported(file) {
    return /\.(mp3|wav)$/i.test(file.name);
  }

  async function addFiles(list) {
    if (state.exporting) return;
    const incoming = Array.from(list || []);
    let skipped = 0;
    for (const file of incoming) {
      if (!fileSupported(file) || !file.size || file.size > MAX_FILE_SIZE) { skipped++; continue; }
      state.files.push({ id: state.nextId++, file, status: 'pending', stats: null });
    }
    dom.fileInput.value = '';
    if (skipped) toast(`${skipped} 件は読み込めませんでした。WAV・MP3（1ファイル250MB以内）を選んでください。`, 'error');
    render();
    await analyzeQueue();
  }

  async function analyzeQueue() {
    if (state.analyzing) return;
    state.analyzing = true;
    try {
      while (true) {
        const item = state.files.find(f => f.status === 'pending');
        if (!item) break;
        item.status = 'analyzing';
        render();
        await yieldUI();
        try {
          const buffer = await decode(item.file);
          item.stats = analyzeBuffer(buffer);
          item.status = 'ready';
        } catch (error) {
          console.error(`音声の解析に失敗: ${item.file.name}`, error);
          item.status = 'error';
          item.error = error instanceof Error ? error.message : '読み込めない形式です。';
        }
        render();
        await yieldUI();
      }
    } finally { state.analyzing = false; render(); }
  }

  function stopPlayback() {
    state.playbackToken++;
    if (state.playing) {
      try { state.playing.source.stop(); } catch { /* already stopped */ }
      try { state.playing.source.disconnect(); } catch { /* disconnected */ }
      state.playing = null;
    }
    render();
  }

  async function play(item, mode) {
    if (state.exporting || item.status !== 'ready') return;
    if (state.playing?.id === item.id && state.playing?.mode === mode) {
      stopPlayback();
      return;
    }
    stopPlayback();
    const token = state.playbackToken;
    try {
      const context = audioContext();
      await context.resume();
      const buffer = await decode(item.file);
      if (token !== state.playbackToken || !state.files.includes(item)) return;
      const source = context.createBufferSource();
      const volume = context.createGain();
      source.buffer = buffer;
      volume.gain.value = mode === 'new' ? gainInfo(item.stats).gain : 1;
      source.connect(volume);
      volume.connect(context.destination);
      source.onended = () => {
        if (state.playing?.source === source) { state.playing = null; render(); }
        source.disconnect(); volume.disconnect();
      };
      state.playing = { source, id: item.id, mode };
      source.start();
      render();
    } catch (error) {
      toast(`再生できませんでした：${error.message || '形式を確認してください。'}`, 'error');
    }
  }

  function setBusy(busy) {
    state.exporting = busy;
    [dom.fileInput, dom.addMore, dom.target, dom.ceiling, dom.boost, dom.suffix,
      dom.sampleRate, dom.bitrate, ...document.querySelectorAll('input[name="format"]')]
      .forEach(el => { el.disabled = busy; });
    dom.dropzone.setAttribute('aria-disabled', String(busy));
    dom.progressBox.hidden = !busy;
    if (!busy) dom.progressBar.style.width = '0%';
    render();
  }

  function setProgress(fraction, message) {
    const pct = clamp(Math.round(fraction * 100), 0, 100);
    dom.progressNumber.textContent = `${pct}%`;
    dom.progressBar.style.width = `${pct}%`;
    dom.progressMessage.textContent = message;
  }

  async function resampleIfNeeded(buffer, sampleRate) {
    if (buffer.sampleRate === sampleRate) return buffer;
    const samples = Math.ceil(buffer.duration * sampleRate);
    const OfflineContext = window.OfflineAudioContext || window.webkitOfflineAudioContext;
    if (!OfflineContext) throw new Error('このブラウザではサンプルレートの変更ができません。');
    const offline = new OfflineContext(buffer.numberOfChannels, samples, sampleRate);
    const source = offline.createBufferSource();
    source.buffer = buffer;
    source.connect(offline.destination);
    source.start();
    return offline.startRendering();
  }

  function peakOfBuffer(buffer) {
    let peak = 0;
    for (let ch = 0; ch < buffer.numberOfChannels; ch++) {
      const data = buffer.getChannelData(ch);
      for (let i = 0; i < data.length; i++) {
        const a = Math.abs(data[i]);
        if (a > peak) peak = a;
      }
    }
    return peak;
  }

  function actualGain(item, buffer) {
    const desired = gainInfo(item.stats).gain;
    const actualPeak = peakOfBuffer(buffer);
    const headroom = actualPeak ? dbToAmp(state.ceilingDb) / actualPeak : Infinity;
    return Math.min(desired, headroom);
  }

  async function encodeWav(buffer, gain, progress) {
    const numChannels = buffer.numberOfChannels;
    const sampleRate = buffer.sampleRate;
    const length = buffer.length;
    const byteLength = 44 + length * numChannels * 2;
    if (byteLength > 0xFFFFFFFF) throw new Error('WAVの最大サイズ（4GB）を超えています。');
    const output = new ArrayBuffer(byteLength);
    const view = new DataView(output);
    const bytes = new Uint8Array(output);
    const writeString = (position, value) => {
      for (let i = 0; i < value.length; i++) bytes[position + i] = value.charCodeAt(i);
    };
    writeString(0, 'RIFF'); view.setUint32(4, byteLength - 8, true);
    writeString(8, 'WAVE'); writeString(12, 'fmt ');
    view.setUint32(16, 16, true); // PCM fmt chunk
    view.setUint16(20, 1, true); // PCM format
    view.setUint16(22, numChannels, true);
    view.setUint32(24, sampleRate, true);
    view.setUint32(28, sampleRate * numChannels * 2, true);
    view.setUint16(32, numChannels * 2, true);
    view.setUint16(34, 16, true);
    writeString(36, 'data'); view.setUint32(40, byteLength - 44, true);
    const data = Array.from({ length: numChannels }, (_, ch) => buffer.getChannelData(ch));
    let position = 44;
    for (let start = 0; start < length; start += 65536) {
      const end = Math.min(start + 65536, length);
      for (let i = start; i < end; i++) {
        for (let ch = 0; ch < numChannels; ch++) {
          const sample = clamp(data[ch][i] * gain, -1, 1);
          view.setInt16(position, sample < 0 ? Math.round(sample * 32768) : Math.round(sample * 32767), true);
          position += 2;
        }
      }
      progress(end / length);
      await yieldUI();
    }
    return new Blob([output], { type: 'audio/wav' });
  }

  function ensureMp3Encoder() {
    if (window.lamejs && typeof window.lamejs.Mp3Encoder === 'function') return Promise.resolve();
    if (ensureMp3Encoder.promise) return ensureMp3Encoder.promise;
    ensureMp3Encoder.promise = new Promise((resolve, reject) => {
      // Fallback if the primary CDN (loaded by index.html) was blocked.
      const script = document.createElement('script');
      script.src = 'https://cdn.jsdelivr.net/npm/lamejs@1.2.1/lame.all.js';
      script.onload = () => window.lamejs?.Mp3Encoder ? resolve() : reject(new Error('MP3ライブラリを読み込めませんでした。'));
      script.onerror = () => reject(new Error('MP3出力にはインターネット接続が必要です。WAV出力はオフラインでも利用できます。'));
      document.head.appendChild(script);
    }).catch(error => { ensureMp3Encoder.promise = null; throw error; });
    return ensureMp3Encoder.promise;
  }

  async function encodeMp3(buffer, gain, bitrate, progress) {
    await ensureMp3Encoder();
    const channels = buffer.numberOfChannels;
    const encoder = new window.lamejs.Mp3Encoder(channels, buffer.sampleRate, bitrate);
    const samples = Array.from({ length: channels }, (_, ch) => buffer.getChannelData(ch));
    const chunkSamples = 1152 * 10;
    const chunks = [];
    for (let start = 0; start < buffer.length; start += chunkSamples) {
      const end = Math.min(start + chunkSamples, buffer.length);
      const n = end - start;
      const input = samples.map(channel => {
        const pcm = new Int16Array(n);
        for (let i = 0; i < n; i++) {
          const value = clamp(channel[start + i] * gain, -1, 1);
          pcm[i] = value < 0 ? Math.round(value * 32768) : Math.round(value * 32767);
        }
        return pcm;
      });
      const encoded = channels === 1
        ? encoder.encodeBuffer(input[0]) : encoder.encodeBuffer(input[0], input[1]);
      if (encoded.length) chunks.push(new Uint8Array(encoded));
      progress(end / buffer.length);
      // Make long encodes cancellable by navigation and keep the UI responsive.
      await yieldUI();
    }
    const last = encoder.flush();
    if (last.length) chunks.push(new Uint8Array(last));
    return new Blob(chunks, { type: 'audio/mpeg' });
  }

  async function encodeItem(item, progress) {
    let buffer = await decode(item.file);
    progress(0.04);
    buffer = await resampleIfNeeded(buffer, state.outputRate);
    progress(0.10);
    const gain = actualGain(item, buffer);
    const update = ratio => progress(.10 + .90 * ratio);
    return state.format === 'mp3'
      ? encodeMp3(buffer, gain, state.kbps, update)
      : encodeWav(buffer, gain, update);
  }

  function exportName(item, used) {
    const original = item.file.name.replace(/\.[^.]+$/, '');
    const base = `${original}${state.suffix}`.replace(/[\\/:*?"<>|\u0000-\u001f]/g, '_').trim() || 'voice';
    const ext = state.format;
    let name = `${base}.${ext}`;
    let serial = 2;
    while (used.has(name.toLocaleLowerCase())) {
      name = `${base}_${serial}.${ext}`;
      serial++;
    }
    used.add(name.toLocaleLowerCase());
    return name;
  }

  function downloadBlob(blob, filename) {
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = filename;
    link.style.display = 'none';
    document.body.append(link);
    link.click();
    link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 60000);
  }

  async function exportItems(items, zipMode) {
    if (state.exporting || !items.length) return;
    stopPlayback();
    setBusy(true);
    setProgress(0, '準備しています…');
    try {
      if (state.format === 'mp3') await ensureMp3Encoder();
      if (zipMode && typeof window.JSZip !== 'function') throw new Error('ZIPライブラリが見つかりません。ページを再読み込みしてください。');
      const zip = zipMode ? new window.JSZip() : null;
      const used = new Set();
      let individualName = '';
      let individualBlob = null;
      for (let i = 0; i < items.length; i++) {
        if (!state.files.includes(items[i])) continue;
        const item = items[i];
        const name = exportName(item, used);
        setProgress(i / items.length, `${i + 1}/${items.length} ${item.file.name} を変換中`);
        await yieldUI();
        const blob = await encodeItem(item, f => {
          setProgress((i + f * .94) / items.length, `${i + 1}/${items.length} ${item.file.name} を変換中`);
        });
        if (zip) zip.file(name, blob, { compression: 'STORE' });
        else { individualBlob = blob; individualName = name; }
        await yieldUI();
      }
      if (zip) {
        setProgress(.96, 'ZIPファイルを作成しています…');
        const blob = await zip.generateAsync({ type: 'blob', compression: 'STORE' }, metadata => {
          setProgress(.96 + .04 * metadata.percent / 100, 'ZIPファイルを作成しています…');
        });
        const time = new Date();
        const stamp = [time.getFullYear(), String(time.getMonth() + 1).padStart(2, '0'), String(time.getDate()).padStart(2, '0')].join('');
        downloadBlob(blob, `こえそろえ_${stamp}.zip`);
      } else if (individualBlob) {
        downloadBlob(individualBlob, individualName);
      }
      setProgress(1, '書き出し完了！');
      toast(`${items.length} 件の書き出しが完了しました。`, 'success');
    } catch (error) {
      console.error('書き出しエラー', error);
      toast(`書き出しに失敗しました：${error?.message || '不明なエラー'}`, 'error');
    } finally { setBusy(false); }
  }

  function updateSettings() {
    state.targetDb = Number(dom.target.value);
    state.ceilingDb = Number(dom.ceiling.value);
    state.maxBoostDb = Number(dom.boost.value);
    state.outputRate = Number(dom.sampleRate.value);
    state.kbps = Number(dom.bitrate.value);
    state.format = document.querySelector('input[name="format"]:checked').value;
    state.suffix = dom.suffix.value;
    dom.targetValue.textContent = state.targetDb;
    dom.ceilingValue.textContent = `${state.ceilingDb.toFixed(1)} dBFS`;
    dom.boostValue.textContent = `+${state.maxBoostDb} dB`;
    dom.bitrateRow.hidden = state.format !== 'mp3';
    render();
  }

  dom.dropzone.addEventListener('click', () => { if (!state.exporting) dom.fileInput.click(); });
  dom.dropzone.addEventListener('keydown', e => {
    if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); if (!state.exporting) dom.fileInput.click(); }
  });
  dom.fileInput.addEventListener('change', e => { void addFiles(e.target.files); });
  dom.addMore.addEventListener('click', () => { if (!state.exporting) dom.fileInput.click(); });
  ['dragenter', 'dragover'].forEach(eventName => dom.dropzone.addEventListener(eventName, e => {
    e.preventDefault(); if (!state.exporting) dom.dropzone.classList.add('dragover');
  }));
  ['dragleave', 'dragend'].forEach(eventName => dom.dropzone.addEventListener(eventName, e => {
    e.preventDefault(); dom.dropzone.classList.remove('dragover');
  }));
  dom.dropzone.addEventListener('drop', e => {
    e.preventDefault(); dom.dropzone.classList.remove('dragover');
    if (!state.exporting) void addFiles(e.dataTransfer.files);
  });
  // Avoid the browser opening a dropped WAV/MP3 when a file misses the dropzone.
  document.addEventListener('dragover', e => e.preventDefault());
  document.addEventListener('drop', e => e.preventDefault());

  [dom.target, dom.ceiling, dom.boost, dom.sampleRate, dom.bitrate, dom.suffix,
    ...document.querySelectorAll('input[name="format"]')]
    .forEach(el => { el.addEventListener('input', updateSettings); el.addEventListener('change', updateSettings); });

  dom.fileList.addEventListener('click', async event => {
    const button = event.target.closest('button[data-action]');
    if (!button || state.exporting) return;
    const id = Number(button.dataset.id);
    const item = state.files.find(f => f.id === id);
    if (!item) return;
    switch (button.dataset.action) {
      case 'remove':
        if (state.playing?.id === item.id) stopPlayback();
        state.files = state.files.filter(f => f.id !== id);
        render();
        break;
      case 'play-raw': await play(item, 'raw'); break;
      case 'play-new': await play(item, 'new'); break;
      case 'save': await exportItems([item], false); break;
    }
  });

  dom.clearAll.addEventListener('click', () => {
    if (state.exporting) return;
    stopPlayback();
    state.files = [];
    render();
  });
  dom.exportAll.addEventListener('click', async () => {
    const items = state.files.filter(f => f.status === 'ready');
    await exportItems(items, true);
  });

  updateSettings();
})();
