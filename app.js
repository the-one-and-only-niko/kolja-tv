// KÖLJA TV-14, the big screen. The phone is the brain and the remote: it sends the whole state over
// a WebSocket, this page plays what it's told (straight from the source, or through the phone's relay)
// and reports back whether a picture came up.
(function () {
  'use strict';
  const $ = id => document.getElementById(id);
  const video = $('v'), canvas = $('static'), ctx = canvas.getContext('2d');
  const params = new URLSearchParams(location.search);
  const frag = new URLSearchParams(location.hash.slice(1));
  // two ways to the phone: this page served by the phone itself on the Wi-Fi (http), or the public page
  // (https) that reaches it through internet relays when the Wi-Fi way is blocked
  const NET = location.protocol === 'https:' || params.has('net');
  let code = (params.get('k') || localStorage.getItem('rtv-code') || '').toUpperCase();
  let link = null, lanUrl = null, lanTried = false;
  let ws = null, st = null, unlocked = false, lastTune = -1, lastOsd = -1, hls = null, trying = null;
  let attemptSeq = 0, picture = false, failed = false, osdTimer = 0, powered = true, retryWs = 0;
  let pt = (navigator.language || '').toLowerCase().startsWith('pt');
  const T = (en, p) => (pt ? p : en);

  function words() {
    $('pairText').textContent = T('Type the 6-letter code shown on your phone', 'Digite o código de 6 letras que aparece no celular');
    $('pairGo').textContent = T('CONNECT', 'CONECTAR');
    $('powerText').textContent = T('CLICK TO TURN ON THE TV', 'CLIQUE PARA LIGAR A TV');
    $('powerSub').textContent = T('Your phone is the remote. Keys work here too: ↑↓ channel, ←→ volume, M menu, F full screen.',
      'O celular é o controle. O teclado também funciona: ↑↓ canal, ←→ volume, M menu, F tela cheia.');
    $('help').textContent = T('F full screen \u2003 C picture \u2003 M menu', 'F tela cheia \u2003 C imagem \u2003 M menu');
    mode();
  }
  let via = null; // 'lan' | 'net' once the phone answers
  function mode() {
    const el = $('mode');
    if (!el) return;
    el.textContent = via === 'lan' ? T('● WI-FI', '● WI-FI') : via === 'net' ? T('● INTERNET', '● INTERNET') : '';
    el.title = via === 'net' ? T('Talking to the phone through internet relays (the Wi-Fi way is blocked here).', 'Falando com o celular pela internet (o caminho pelo Wi-Fi está bloqueado aqui).') : '';
  }
  words();

  // ---------- static: noise drawn here, nothing crosses the network ----------
  const img = ctx.createImageData(canvas.width, canvas.height);
  let roll = 0;
  function noise() {
    const d = img.data, w = canvas.width;
    roll = (roll + 3) % canvas.height;
    for (let i = 0, p = 0; i < d.length; i += 4, p++) {
      const y = (p / w) | 0, band = Math.abs(y - roll) < 10 ? 40 : 0;
      const v = Math.min(255, (Math.random() * 215 + band) | 0);
      d[i] = d[i + 1] = d[i + 2] = v; d[i + 3] = 255;
    }
    ctx.putImageData(img, 0, 0);
  }
  function frame() {
    if (canvas.classList.contains('on')) noise();
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);

  let audio = null, hiss = null;
  function sound() {
    if (audio || !unlocked) return;
    try {
      audio = new (window.AudioContext || window.webkitAudioContext)();
      const len = audio.sampleRate * 2, buf = audio.createBuffer(1, len, audio.sampleRate), ch = buf.getChannelData(0);
      for (let i = 0; i < len; i++) ch[i] = Math.random() * 2 - 1;
      const src = audio.createBufferSource(); src.buffer = buf; src.loop = true;
      const lp = audio.createBiquadFilter(); lp.type = 'lowpass'; lp.frequency.value = 5200;
      hiss = audio.createGain(); hiss.gain.value = 0;
      src.connect(lp); lp.connect(hiss); hiss.connect(audio.destination); src.start();
    } catch (e) { audio = null; }
  }
  function levels() {
    const on = st && st.power;
    const vol = st ? st.vol : 0.6, mute = !st || st.mute;
    video.volume = Math.max(0, Math.min(1, vol));
    video.muted = mute || !unlocked;
    if (hiss) hiss.gain.setTargetAtTime(on && !mute && canvas.classList.contains('on') ? vol * 0.22 : 0, audio.currentTime, 0.05);
  }
  function setStatic(on) { canvas.classList.toggle('on', on); levels(); }

  // ---------- playback ----------
  function stopVideo() {
    if (trying) { clearTimeout(trying.timer); trying = null; }
    if (hls) { try { hls.destroy(); } catch (e) {} hls = null; }
    video.removeAttribute('src');
    try { video.load(); } catch (e) {}
  }

  function tune(ch, id) {
    stopVideo();
    picture = false; failed = false;
    document.body.classList.remove('roll', 'flip');
    void document.body.offsetWidth;
    document.body.classList.add('flip');
    setStatic(true);
    msg('');
    if (!ch) return;
    if (NET && (ch.forceRelay || /^http:/.test(ch.url))) { // only the phone on the same Wi-Fi can fetch this one for us
      failed = true; msg(T('THIS CHANNEL ONLY PLAYS ON THE SAME WI-FI', 'ESTE CANAL SÓ PASSA NO MESMO WI-FI'));
      send({ t: 'st', tune: id, ok: false, err: 'needs-lan' });
      return;
    }
    const order = NET ? ['direct'] : ch.forceRelay ? ['relay'] : ['direct', 'relay'];
    let i = 0;
    const next = (why) => {
      if (id !== lastTune) return;
      if (i >= order.length) { failed = true; msg(T('NO SIGNAL', 'SEM SINAL')); send({ t: 'st', tune: id, ok: false, err: why || 'no picture' }); return; }
      const via = order[i++], src = via === 'direct' ? ch.url : ch.relay;
      attempt(src, id, via, next);
    };
    next();
  }

  function attempt(src, id, via, next) {
    stopVideo();
    let done = false;
    const my = ++attemptSeq;
    const finish = (ok, why) => {
      if (done || id !== lastTune || my !== attemptSeq) return;
      done = true;
      if (trying) { clearTimeout(trying.timer); trying = null; }
      if (ok) {
        picture = true;
        setStatic(false);
        document.body.classList.remove('flip'); void document.body.offsetWidth; document.body.classList.add('roll');
        const audioOnly = !video.videoWidth;
        if (audioOnly) msg(T('AUDIO ONLY', 'SÓ ÁUDIO'));
        send({ t: 'st', tune: id, ok: true, via, w: video.videoWidth, h: video.videoHeight, audio: audioOnly });
      } else next(why);
    };
    trying = { timer: setTimeout(() => finish(false, 'timeout'), 14000) };
    const onPlaying = () => { video.removeEventListener('playing', onPlaying); finish(true); };
    video.addEventListener('playing', onPlaying);
    if (window.Hls && Hls.isSupported()) {
      hls = new Hls({ enableWorker: true, capLevelToPlayerSize: true, maxBufferLength: 20, backBufferLength: 10,
                      manifestLoadingMaxRetry: 1, levelLoadingMaxRetry: 2, fragLoadingMaxRetry: 3, startLevel: -1 });
      let recovered = false;
      hls.on(Hls.Events.ERROR, (e, d) => {
        if (!d.fatal || my !== attemptSeq) return;
        if (picture && d.type === Hls.ErrorTypes.NETWORK_ERROR) { hls.startLoad(); return; } // a hiccup mid-show
        if (d.type === Hls.ErrorTypes.MEDIA_ERROR && !recovered) { recovered = true; hls.recoverMediaError(); return; }
        if (picture) { lost(); return; }
        finish(false, d.details || d.type);
      });
      hls.loadSource(src);
      hls.attachMedia(video);
      hls.on(Hls.Events.MANIFEST_PARSED, () => video.play().catch(() => {}));
    } else if (video.canPlayType('application/vnd.apple.mpegurl')) { // Safari plays HLS itself
      video.src = src;
      video.onerror = () => (picture ? lost() : finish(false, 'media error'));
      video.play().catch(() => {});
    } else finish(false, 'no HLS player');
  }

  function lost() { // the channel dropped after it had been playing: show static, tell the phone
    picture = false; setStatic(true); msg(T('NO SIGNAL', 'SEM SINAL'));
    send({ t: 'st', tune: lastTune, ok: false, err: 'dropped', dropped: true });
  }

  // ---------- OSD and menu ----------
  function msg(s) { $('msg').textContent = s; $('msg').classList.toggle('hide', !s); }
  function osd(show) {
    const ch = st && st.ch;
    $('num').textContent = st && st.digits ? st.digits : ch ? String(ch.n).padStart(2, '0') : '';
    $('name').textContent = ch ? ch.name : '';
    $('where').textContent = ch ? [ch.flag, ch.cc, ch.band].filter(Boolean).join(' ') : '';
    if (show) {
      $('num').classList.remove('hide'); $('bar').classList.remove('hide');
      clearTimeout(osdTimer);
      osdTimer = setTimeout(() => { if (!(st && st.digits)) { $('num').classList.add('hide'); $('bar').classList.add('hide'); } }, 4000);
    }
  }
  function menu(m) {
    const el = $('menu');
    el.classList.toggle('on', !!m);
    if (!m) return;
    $('num').classList.add('hide'); $('bar').classList.add('hide');
    el.innerHTML = '';
    const h = document.createElement('h2'); h.textContent = m.title; el.appendChild(h);
    m.items.forEach((s, i) => {
      const d = document.createElement('div');
      d.textContent = s;
      if (i + m.first === m.cursor) d.className = 'sel';
      el.appendChild(d);
    });
  }

  // ---------- state from the phone ----------
  function apply(s) {
    const before = st;
    st = s;
    if (typeof s.lang === 'string') { pt = s.lang === 'pt'; words(); }
    document.body.classList.remove('crt0', 'crt1', 'crt2');
    document.body.classList.add('crt' + (s.crt | 0));
    $('lamp').classList.toggle('on', !!s.power);
    if (!s.power) {
      if (powered) {
        powered = false;
        stopVideo(); setStatic(false); msg('');
        $('screen').classList.add('off'); $('dot').classList.remove('fade'); void $('dot').offsetWidth; $('dot').classList.add('fade');
        $('num').classList.add('hide'); $('bar').classList.add('hide');
      }
      menu(null);
      lastTune = -1;
      return;
    }
    if (!powered) { powered = true; const sc = $('screen'); sc.classList.remove('off'); sc.classList.remove('warm'); void sc.offsetWidth; sc.classList.add('warm'); setTimeout(() => sc.classList.remove('warm'), 1600); }
    if (s.tune !== lastTune) {
      lastTune = s.tune;
      tune(s.ch, s.tune);
      osd(true);
    } else if (s.osd !== lastOsd || (before && before.digits !== s.digits)) osd(true);
    else osd(false);
    lastOsd = s.osd;
    if (s.lanOnly && !picture) msg(T('THIS CHANNEL ONLY PLAYS ON THE SAME WI-FI', 'ESTE CANAL SÓ PASSA NO MESMO WI-FI'));
    else if (s.noSignal && !picture) msg(T('NO SIGNAL', 'SEM SINAL'));
    else if (!s.ch && s.status) msg(s.status);
    menu(s.menu);
    levels();
  }

  function send(o) {
    if (link) { link.send(o); return; }
    if (ws && ws.readyState === 1) ws.send(JSON.stringify(o));
  }

  function connect() {
    if (NET) { netConnect(); return; }
    if (!code) { showPair(); return; }
    fetch('check?k=' + encodeURIComponent(code)).then(r => {
      if (r.status === 403) { localStorage.removeItem('rtv-code'); showPair(T('That code is not right. Try again:', 'Código errado. Tente de novo:')); return; }
      return r.text().then(t => {
      const tok = /^ok ([A-Z0-9]{6})$/.exec(t.trim()); // the short code on the remote rotates; keep the lasting one
      if (tok) code = tok[1];
      localStorage.setItem('rtv-code', code);
      $('pair').style.display = 'none';
      if (!unlocked) $('power').style.display = 'flex';
      open();
      });
    }).catch(() => later());
  }
  function open() {
    ws = new WebSocket((location.protocol === 'https:' ? 'wss://' : 'ws://') + location.host + '/ws?k=' + encodeURIComponent(code));
    ws.onopen = () => { retryWs = 0; $('net').textContent = ''; via = 'lan'; mode(); };
    ws.onmessage = e => { try { const s = JSON.parse(e.data); if (s.t === 'tv') apply(s); } catch (x) {} };
    ws.onclose = () => { ws = null; later(); };
  }
  function later() {
    via = null; mode();
    $('net').textContent = T('Looking for the phone…', 'Procurando o celular…');
    if (retryWs >= 3) { // the Wi-Fi keeps the two apart: point at the way that goes through the internet
      $('net').innerHTML = '';
      $('net').append(T('Can\'t reach the phone on this Wi-Fi. Open ', 'Não acho o celular neste Wi-Fi. Abra '));
      const a = document.createElement('a');
      a.href = 'https://the-one-and-only-niko.github.io/kolja-tv/'; a.textContent = 'the-one-and-only-niko.github.io/kolja-tv';
      $('net').append(a, T(' (works over the internet).', ' (funciona pela internet).'));
    }
    setTimeout(connect, Math.min(8000, 1000 * ++retryWs));
  }

  // ---------- internet mode (the public page) ----------
  function netConnect() {
    if (!window.RtvNet || !window.crypto || !crypto.subtle) { $('net').textContent = T('This browser can\'t do internet mode.', 'Este navegador não faz o modo internet.'); return; }
    const fc = (frag.get('c') || '').toUpperCase(), fp = frag.get('p'), fl = frag.get('l'), fk = frag.get('k');
    if (location.hash) history.replaceState(null, '', location.pathname + location.search); // the code stays out of history and bookmarks
    if (fl && fk) lanUrl = 'http://' + fl + '/?k=' + encodeURIComponent(fk);
    link = RtvNet.start({
      onMessage(o) {
        if (o.t === 'tv') {
          if (o.lan && !lanUrl) lanUrl = o.lan;
          if (via !== 'net') { via = 'net'; mode(); }
          $('net').textContent = '';
          $('pair').style.display = 'none';
          if (!unlocked) $('power').style.display = 'flex';
          apply(o);
          tryLan();
        } else if (o.t === 'bye') { via = null; mode(); $('net').textContent = T('The phone stopped casting.', 'O celular parou de transmitir.'); }
      },
      onStatus(k, n) {
        if (k === 'relays') { if (!n) $('net').textContent = T('No internet relay answers. Check the internet.', 'Nenhum servidor da internet responde. Confira a internet.'); }
        else if (k === 'pairing') { $('net').textContent = T('Connecting through the internet…', 'Conectando pela internet…'); }
        else if (k === 'paired') { $('net').textContent = ''; }
        else if (k === 'badcode') showPair(T('No phone answered that code. Check it on the phone (it changes every 5 minutes):', 'Nenhum celular respondeu a esse código. Confira no celular (ele muda a cada 5 minutos):'));
        else if (k === 'quiet') { via = null; mode(); $('net').textContent = T('Looking for the phone… (is Retrotv still casting?)', 'Procurando o celular… (o Retrotv ainda está transmitindo?)'); }
      },
    });
    let pub = null;
    try { if (fp) pub = RtvNet.hex(RtvNet.b64url(fp)); } catch (e) {}
    if (fc) link.pair(fc, pub);
    else if (!link.paired()) showPair();
    else { $('net').textContent = T('Looking for the phone…', 'Procurando o celular…'); setTimeout(() => { if (!via) showPair(T('The phone didn\'t answer. If it shows a code, type it here:', 'O celular não respondeu. Se ele mostra um código, digite aqui:')); }, 12000); }
    tryLan();
  }

  // The Wi-Fi way is better (the phone can fetch the channels a browser can't), so if this computer can
  // reach the phone directly, hop to the page the phone serves. Chrome and Brave ask the user first
  // ("access devices on your local network"); refused, blocked or unreachable, we stay on the internet way.
  function tryLan() {
    if (lanTried || !lanUrl) return;
    lanTried = true;
    const u = new URL(lanUrl);
    const space = /^(127\.|localhost$|\[::1\]$)/.test(u.hostname) ? 'loopback' : 'local'; // Local Network Access: say where we're going
    fetch(u.origin + '/check?k=' + encodeURIComponent(u.searchParams.get('k') || ''), { targetAddressSpace: space, cache: 'no-store' })
      .then(r => r.ok ? r.text() : Promise.reject(r.status)) // no time limit: the browser may be asking the user first
      .then(t => { if (/^ok /.test(t)) { if (link) link.bye(); location.href = lanUrl; } })
      .catch(() => {});
  }
  function showPair(text) {
    $('pair').style.display = 'flex';
    if (text) $('pairText').textContent = text;
    $('code').focus();
  }
  $('pairGo').onclick = () => {
    const c = $('code').value.trim().toUpperCase();
    if (NET) { if (c.length === 6) { $('pair').style.display = 'none'; link.pair(c); } return; }
    code = c; connect();
  };
  $('code').addEventListener('keydown', e => { if (e.key === 'Enter') $('pairGo').click(); e.stopPropagation(); });
  $('power').onclick = () => {
    unlocked = true; $('power').style.display = 'none'; sound(); levels();
    if (audio && audio.state === 'suspended') audio.resume();
    video.play().catch(() => {});
  };

  // ---------- this computer's keyboard works as a second remote ----------
  function full() {
    if (document.fullscreenElement) document.exitFullscreen().catch(() => {});
    else document.documentElement.requestFullscreen().catch(() => {});
  }
  document.addEventListener('fullscreenchange', () => document.body.classList.toggle('full', !!document.fullscreenElement));
  $('glass').addEventListener('dblclick', full);
  document.addEventListener('keydown', e => {
    if ($('pair').style.display === 'flex') return;
    const m = st && st.menu;
    const k = {
      ArrowUp: m ? 'up' : 'chup', ArrowDown: m ? 'down' : 'chdn', PageUp: 'chup', PageDown: 'chdn',
      ArrowLeft: m ? 'left' : 'voldn', ArrowRight: m ? 'right' : 'volup', Enter: 'ok', Escape: 'back', Backspace: 'back',
      m: 'menu', M: 'menu', c: 'crt', C: 'crt', b: 'band', B: 'band', x: 'mute', X: 'mute', '-': 'dash', '+': 'volup', '=': 'volup', '*': 'fav'
    }[e.key] || (/^[0-9]$/.test(e.key) ? 'd' + e.key : null);
    if (e.key === 'f' || e.key === 'F') { full(); e.preventDefault(); return; }
    if (!k) return;
    if (!unlocked) $('power').click();
    send({ t: 'key', k });
    e.preventDefault();
  });

  connect();
})();
