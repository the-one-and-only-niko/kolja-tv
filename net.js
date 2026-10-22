// Relay mode: the page and the phone talk through public Nostr relays when they can't reach each
// other on the Wi-Fi. Every message is sealed (AES-GCM, key from ECDH of the two keys plus the pairing
// code), so a relay only ever sees noise addressed to a random key. Nothing here is secret: the keys
// are made in this browser and kept in its localStorage.
(function () {
  'use strict';
  const RELAYS = ['wss://nos.lol', 'wss://relay.primal.net', 'wss://nostr.mom', 'wss://relay.snort.social', 'wss://relay.nostr.net'];
  const KIND_MSG = 23377, KIND_OFFER = 23378;
  const enc = new TextEncoder(), dec = new TextDecoder();

  // ---------- secp256k1 + BIP-340, small and plain (BigInt) ----------
  const P = 2n ** 256n - 2n ** 32n - 977n;
  const N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
  const GX = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n;
  const GY = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8n;
  const mod = (a, m = P) => { const r = a % m; return r >= 0n ? r : r + m; };
  function pow(b, e, m = P) { let r = 1n; b = mod(b, m); while (e > 0n) { if (e & 1n) r = r * b % m; b = b * b % m; e >>= 1n; } return r; }
  const inv = a => pow(a, P - 2n);
  // Jacobian points [X, Y, Z]; Z = 0 is infinity
  function dbl(p) {
    const [X, Y, Z] = p;
    if (Z === 0n || Y === 0n) return [0n, 1n, 0n];
    const YY = Y * Y % P, S = 4n * X * YY % P, M = 3n * X * X % P;
    const X3 = mod(M * M - 2n * S), Y3 = mod(M * (S - X3) - 8n * YY * YY), Z3 = 2n * Y * Z % P;
    return [X3, Y3, Z3];
  }
  function add(p, q) {
    if (p[2] === 0n) return q;
    if (q[2] === 0n) return p;
    const Z1Z1 = p[2] * p[2] % P, Z2Z2 = q[2] * q[2] % P;
    const U1 = p[0] * Z2Z2 % P, U2 = q[0] * Z1Z1 % P;
    const S1 = p[1] * q[2] % P * Z2Z2 % P, S2 = q[1] * p[2] % P * Z1Z1 % P;
    if (U1 === U2) return S1 === S2 ? dbl(p) : [0n, 1n, 0n];
    const H = mod(U2 - U1), R = mod(S2 - S1), HH = H * H % P, HHH = H * HH % P, V = U1 * HH % P;
    const X3 = mod(R * R - HHH - 2n * V), Y3 = mod(R * (V - X3) - S1 * HHH), Z3 = H * p[2] % P * q[2] % P;
    return [X3, Y3, Z3];
  }
  function mul(pt, k) {
    let r = [0n, 1n, 0n], a = [pt[0], pt[1], 1n];
    while (k > 0n) { if (k & 1n) r = add(r, a); a = dbl(a); k >>= 1n; }
    return r;
  }
  function affine(p) { if (p[2] === 0n) return null; const zi = inv(p[2]), z2 = zi * zi % P; return [p[0] * z2 % P, p[1] * z2 % P * zi % P]; }
  const mulG = k => affine(mul([GX, GY], k));
  function liftX(x) {
    if (x >= P) return null;
    const c = mod(x * x * x + 7n), y = pow(c, (P + 1n) / 4n);
    if (y * y % P !== c) return null;
    return [x, y & 1n ? P - y : y];
  }
  const hex = b => Array.from(b, x => x.toString(16).padStart(2, '0')).join('');
  const unhex = s => Uint8Array.from(s.match(/../g) || [], h => parseInt(h, 16));
  const num = b => BigInt('0x' + (hex(b) || '0'));
  const bytes32 = n => unhex(n.toString(16).padStart(64, '0'));
  const cat = (...a) => { const o = new Uint8Array(a.reduce((s, x) => s + x.length, 0)); let i = 0; for (const x of a) { o.set(x, i); i += x.length; } return o; };
  const sha = async b => new Uint8Array(await crypto.subtle.digest('SHA-256', b));
  async function tagged(tag, ...m) { const t = await sha(enc.encode(tag)); return sha(cat(t, t, ...m)); }
  const rand = n => crypto.getRandomValues(new Uint8Array(n));

  function newSecret() { for (;;) { const s = rand(32), d = num(s); if (d > 0n && d < N) return s; } }
  const pubOf = sec => bytes32(mulG(num(sec))[0]);

  async function sign(sec, msg) {
    const d0 = num(sec), Pp = mulG(d0), d = Pp[1] & 1n ? N - d0 : d0, px = bytes32(Pp[0]);
    const aux = await tagged('BIP0340/aux', rand(32));
    const db = bytes32(d), t = db.map((v, i) => v ^ aux[i]);
    const k0 = mod(num(await tagged('BIP0340/nonce', t, px, msg)), N);
    if (k0 === 0n) throw new Error('bad nonce');
    const R = mulG(k0), k = R[1] & 1n ? N - k0 : k0, rx = bytes32(R[0]);
    const e = mod(num(await tagged('BIP0340/challenge', rx, px, msg)), N);
    return cat(rx, bytes32(mod(k + e * d, N)));
  }

  /** x of (my even-y secret) · lift_x(their key): the same number on both sides (matches Secp.ecdh). */
  function ecdh(sec, theirPubHex) {
    const them = liftX(num(unhex(theirPubHex)));
    if (!them) return null;
    const d0 = num(sec), mine = mulG(d0), d = mine[1] & 1n ? N - d0 : d0;
    const s = affine(mul(them, d));
    return s && bytes32(s[0]);
  }

  // ---------- sealing ----------
  const b64 = b => btoa(String.fromCharCode(...b));
  const unb64 = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
  const b64url = s => unb64(s.replace(/-/g, '+').replace(/_/g, '/') + '==='.slice((s.length + 3) % 4));
  async function keyFor(sec, theirPub, code) {
    const shared = ecdh(sec, theirPub);
    if (!shared) throw new Error('bad key');
    const ikm = await crypto.subtle.importKey('raw', shared, 'HKDF', false, ['deriveBits']);
    return new Uint8Array(await crypto.subtle.deriveBits({ name: 'HKDF', hash: 'SHA-256',
      salt: enc.encode('retrotv-pair:' + code), info: enc.encode('retrotv cast 1') }, ikm, 256));
  }
  async function seal(raw, senderPub, obj) {
    const k = await crypto.subtle.importKey('raw', raw, 'AES-GCM', false, ['encrypt']);
    const iv = rand(12);
    const ct = new Uint8Array(await crypto.subtle.encrypt({ name: 'AES-GCM', iv, additionalData: enc.encode(senderPub) }, k, enc.encode(JSON.stringify(obj))));
    return b64(cat(iv, ct));
  }
  async function open(raw, senderPub, content) {
    try {
      const all = unb64(content), k = await crypto.subtle.importKey('raw', raw, 'AES-GCM', false, ['decrypt']);
      const pt = await crypto.subtle.decrypt({ name: 'AES-GCM', iv: all.slice(0, 12), additionalData: enc.encode(senderPub) }, k, all.slice(12));
      return JSON.parse(dec.decode(pt));
    } catch (e) { return null; }
  }
  const codeTag = async code => hex(await sha(enc.encode('retrotv-code:' + code))).slice(0, 2);

  async function event(sec, kind, tags, content) {
    const pubkey = hex(pubOf(sec)), created_at = Math.floor(Date.now() / 1000);
    const id = await sha(enc.encode(JSON.stringify([0, pubkey, created_at, kind, tags, content])));
    return { id: hex(id), pubkey, created_at, kind, tags, content, sig: hex(await sign(sec, id)) };
  }

  // ---------- relays ----------
  function Pool(onEvent, onChange) {
    const socks = {}, subs = {}, seen = new Set(), seenQ = [];
    let stopped = false;
    function connect(url, wait) {
      if (stopped) return;
      let ws;
      try { ws = new WebSocket(url); } catch (e) { setTimeout(() => connect(url, wait * 2), wait); return; }
      socks[url] = ws;
      ws.onopen = () => { wait = 1000; for (const id in subs) ws.send(JSON.stringify(['REQ', id, ...subs[id]])); onChange(); };
      ws.onmessage = m => {
        let a; try { a = JSON.parse(m.data); } catch (e) { return; }
        if (a[0] !== 'EVENT' || !a[2] || seen.has(a[2].id)) return;
        seen.add(a[2].id); seenQ.push(a[2].id);
        if (seenQ.length > 600) seen.delete(seenQ.shift());
        onEvent(a[2], a[1]);
      };
      ws.onclose = () => { if (socks[url] === ws) delete socks[url]; onChange(); setTimeout(() => connect(url, Math.min(30000, wait * 2)), wait); };
    }
    RELAYS.forEach(u => connect(u, 1000));
    return {
      sub(id, ...filters) { subs[id] = filters; for (const u in socks) if (socks[u].readyState === 1) socks[u].send(JSON.stringify(['REQ', id, ...filters])); },
      unsub(id) { delete subs[id]; for (const u in socks) if (socks[u].readyState === 1) socks[u].send(JSON.stringify(['CLOSE', id])); },
      pub(ev) { let n = 0; for (const u in socks) if (socks[u].readyState === 1) { socks[u].send(JSON.stringify(['EVENT', ev])); n++; } return n; },
      open() { let n = 0; for (const u in socks) if (socks[u].readyState === 1) n++; return n; },
      stop() { stopped = true; for (const u in socks) try { socks[u].close(); } catch (e) {} },
    };
  }

  // ---------- the link to one phone ----------
  // h: { onMessage(obj), onStatus(kind, info) } with kind: 'pairing' | 'paired' | 'live' | 'quiet' | 'badcode' | 'relays'
  function start(h) {
    const store = {
      get() { try { return JSON.parse(localStorage.getItem('rtv-net') || 'null'); } catch (e) { return null; } },
      set(v) { localStorage.setItem('rtv-net', JSON.stringify(v)); },
    };
    let me = store.get();
    if (!me || !me.sec) { me = { sec: hex(newSecret()) }; store.set(me); }
    const sec = unhex(me.sec), myPub = hex(pubOf(sec));
    let phone = me.phone || null, key = me.key ? unb64(me.key) : null, lastTs = me.lastTs || 0, sendTs = 0;
    let heard = 0, pairing = null;
    let hiAt = 0;
    const pool = Pool(onEvent, () => {
      h.onStatus('relays', pool.open());
      if (phone && !heard && Date.now() - hiAt > 1500) { hiAt = Date.now(); send({ t: 'hi' }); } // say hello as soon as a relay is up
    });

    function save() { me.phone = phone; me.key = key && b64(key); me.lastTs = lastTs; store.set(me); }

    async function onEvent(ev) {
      if (ev.kind === KIND_OFFER && pairing) { offer(ev.pubkey); return; }
      if (ev.kind !== KIND_MSG) return;
      const cands = [];
      if (pairing && pairing.keys[ev.pubkey]) cands.push(await pairing.keys[ev.pubkey].catch(() => null));
      if (phone === ev.pubkey && key) cands.push(key);
      for (const k of cands) {
        if (!k) continue;
        const o = await open(k, ev.pubkey, ev.content);
        if (!o || !o.m) continue;
        if (pairing && k !== key) { // only the phone that took our code can seal with this key: paired
          phone = ev.pubkey; key = k; lastTs = 0; pairing = null; pool.unsub('offer'); h.onStatus('paired');
        }
        if (phone !== ev.pubkey || !(o.ts > lastTs)) return;
        lastTs = o.ts; save();
        if (!heard || Date.now() - heard > 30000) h.onStatus('live');
        heard = Date.now();
        h.onMessage(o.m);
        return;
      }
    }

    async function send(m, to, k) {
      to = to || phone; k = k || key;
      if (!to || !k) return false;
      sendTs = Math.max(sendTs + 1, Date.now());
      const tags = m.t === 'pair' ? [['p', to], ['t', 'pair']] : [['p', to]];
      const ev = await event(sec, KIND_MSG, tags, await seal(k, myPub, { ts: sendTs, m }));
      return pool.pub(ev) > 0;
    }

    function offer(pub) { // a phone showing our code: try to pair with it
      if (!pairing || pairing.keys[pub]) return;
      pairing.keys[pub] = keyFor(sec, pub, pairing.code);
      pairing.keys[pub].then(k => send({ t: 'pair', ua: navigator.userAgent.slice(0, 80) }, pub, k)).catch(() => {});
    }

    async function pair(code, pubHint) {
      code = code.toUpperCase();
      pairing = { code, keys: {}, at: Date.now() };
      h.onStatus('pairing');
      // ask "who has this code?" by a 1-byte tag of it; phones with a matching code answer with their key
      pool.sub('offer', { kinds: [KIND_OFFER], '#p': [myPub], since: Math.floor(Date.now() / 1000) - 20 });
      const tag = await codeTag(code), my = pairing;
      const seek = () => event(sec, KIND_OFFER, [['x', tag]], '').then(ev => pool.pub(ev));
      if (pubHint) offer(pubHint); else seek();
      const again = setInterval(() => { // relays can drop the first try; ask again until the phone answers
        if (pairing !== my) { clearInterval(again); return; }
        if (Date.now() - my.at > 40000) { clearInterval(again); pairing = null; pool.unsub('offer'); h.onStatus('badcode'); return; }
        if (!Object.keys(my.keys).length) seek();
        for (const pub in my.keys) my.keys[pub].then(k => send({ t: 'pair', again: true }, pub, k)).catch(() => {});
      }, 4000);
    }

    pool.sub('in', { kinds: [KIND_MSG], '#p': [myPub], since: Math.floor(Date.now() / 1000) - 10 });
    setInterval(() => {
      if (phone) send({ t: 'ping' });
      if (heard && Date.now() - heard > 30000) { heard = 0; h.onStatus('quiet'); }
    }, 10000);

    return {
      paired: () => !!phone,
      pair, send,
      forget() { phone = null; key = null; lastTs = 0; save(); },
      relays: () => pool.open(),
      bye() { if (phone) send({ t: 'bye' }); },
    };
  }

  window.RtvNet = { start, b64url, hex, _test: { sign, pubOf, ecdh, keyFor, seal, open, event, unhex, codeTag } };
})();
