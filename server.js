// Presence — shared canvas server.
// Serves presence.html and keeps the authoritative shared state over WebSockets:
// who is where, who is pressing, how people group, and every painted trace.
// No dependencies: run with `node server.js`.
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT      = process.env.PORT || 3000;
const MAX_USERS = 5;          // active participants; extra connections only watch
const NEAR      = 4;            // ±cells horizontally and vertically to count as "nearby"
const SETTLE    = 8000 + 20000; // HOLD + FADE in presence.html: after this a trace is pure residue

// ---- HTTP: serve the page ---------------------------------------------------
const server = http.createServer((req, res) => {
  if (req.url === '/' || req.url.startsWith('/?')) {
    res.writeHead(200, { 'content-type': 'text/html; charset=utf-8' });
    fs.createReadStream(path.join(__dirname, 'presence.html')).pipe(res);
  } else {
    res.writeHead(404); res.end();
  }
});

// ---- State ----------------------------------------------------------------
let nextId = 1;
const users = new Map();   // ws -> { id, c, r, down, erase }   (c === null: not on the canvas)
const entPrev = new Map(); // entity id -> { c, r, painting } from the previous update
// Painted traces: key -> [ {settled, stamps[]} per colour: 0 pink, 1 orange, 2 blue, 3 yellow, 4 purple ]
const cells = new Map();
const KEY = (c, r) => r * 100000 + c;

// ---- Grouping ---------------------------------------------------------------
const near = (a, b) => Math.abs(a.c - b.c) <= NEAR && Math.abs(a.r - b.r) <= NEAR;

// First MAX_USERS connections (by join order) are the active participants.
const activeUsers = () => [...users.values()].sort((a, b) => a.id - b.id).slice(0, MAX_USERS);

// A set of people is a group only if EVERY pair is near (no chains).
const isGroup = set => set.every((a, i) => set.slice(i + 1).every(b => near(a, b)));

// Ranking between candidate groups: bigger first, then tighter (largest pairwise
// distance, then sum of pairwise distances), then join order. Fully deterministic.
function score(set) {
  let spread = 0, sum = 0;
  for (let i = 0; i < set.length; i++) for (let j = i + 1; j < set.length; j++) {
    const dc = Math.abs(set[i].c - set[j].c), dr = Math.abs(set[i].r - set[j].r);
    spread = Math.max(spread, dc, dr); sum += dc + dr;
  }
  return [-set.length, spread, sum, ...set.map(u => u.id)];
}
const better = (a, b) => { for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] < b[i]; return false; };

// Partition people into groups: repeatedly take the best valid group among those left.
// With at most 5 people this simply tries every subset.
function partition(ps) {
  const out = [];
  let left = ps.slice();
  while (left.length) {
    let best = null, bestScore = null;
    for (let mask = 1; mask < (1 << left.length); mask++) {
      const set = left.filter((_, i) => mask & (1 << i));
      if (!isGroup(set)) continue;
      const sc = score(set);
      if (!best || better(sc, bestScore)) { best = set; bestScore = sc; }
    }
    out.push(best);
    left = left.filter(u => !best.includes(u));
  }
  return out;
}

// Erasers only group with erasers; everyone else only with non-erasers.
function groups() {
  const ps = activeUsers().filter(u => u.c !== null);
  return [
    ...partition(ps.filter(u => !u.erase)).map(m => ({ members: m, erase: false })),
    ...partition(ps.filter(u => u.erase)).map(m => ({ members: m, erase: true })),
  ];
}

// A group becomes one entity: size = member count, centred on the members' mean position.
function entity({ members, erase }) {
  const s = members.length;
  const mc = members.reduce((t, u) => t + u.c, 0) / s;
  const mr = members.reduce((t, u) => t + u.r, 0) / s;
  return {
    id: (erase ? 'x' : '') + members.map(u => u.id).join('-'),
    s,
    erase,
    c: Math.max(0, Math.round(mc + 0.5 - s / 2)),   // top-left cell of the s×s footprint
    r: Math.max(0, Math.round(mr + 0.5 - s / 2)),
    painting: !erase && members.every(u => u.down), // collective intention: everyone presses
  };
}

// ---- Painting ---------------------------------------------------------------
function deposit(c, r, ci, out) {
  const key = KEY(c, r);
  if (!cells.has(key)) cells.set(key, [0, 1, 2, 3, 4].map(() => ({ settled: 0, stamps: [] })));
  cells.get(key)[ci].stamps.push(Date.now());
  out.push(c, r, ci);
}

const inFoot = (x, y, fc, fr, s) => x >= fc && x < fc + s && y >= fr && y < fr + s;

// Deposit the cells of footprint (c, r) that weren't already covered by footprint (pc, pr).
function depositFoot(c, r, s, out, pc = null, pr = null) {
  for (let y = r; y < r + s; y++) for (let x = c; x < c + s; x++)
    if (pc === null || !inFoot(x, y, pc, pr, s)) deposit(x, y, s - 1, out);
}

// ---- Erasing ----------------------------------------------------------------
// Removes the stored cell entirely: every colour, every deposit, all residue.
function eraseFoot(c, r, s, out) {
  for (let y = r; y < r + s; y++) for (let x = c; x < c + s; x++)
    if (cells.delete(KEY(x, y))) out.push(x, y);
}

// ---- Update loop ------------------------------------------------------------
function update() {
  const ents = groups().map(entity);
  const deposits = [], erased = [];
  for (const e of ents) {
    const p = entPrev.get(e.id);
    if (e.erase) {
      // erase the whole footprint at every step between the previous and new position
      if (p) {
        const dc = e.c - p.c, dr = e.r - p.r, steps = Math.max(Math.abs(dc), Math.abs(dr));
        for (let i = 1; i <= steps; i++)
          eraseFoot(Math.round(p.c + dc * i / steps), Math.round(p.r + dr * i / steps), e.s, erased);
      }
      eraseFoot(e.c, e.r, e.s, erased);
    } else if (e.painting) {
      if (p && p.painting) {
        // walk from the previous footprint position to the new one so strokes have no gaps
        const dc = e.c - p.c, dr = e.r - p.r, steps = Math.max(Math.abs(dc), Math.abs(dr));
        let x = p.c, y = p.r;
        for (let i = 1; i <= steps; i++) {
          const nx = Math.round(p.c + dc * i / steps), ny = Math.round(p.r + dr * i / steps);
          if (nx === x && ny === y) continue;
          depositFoot(nx, ny, e.s, deposits, x, y);
          x = nx; y = ny;
        }
      } else {
        depositFoot(e.c, e.r, e.s, deposits);   // just started painting (or a click)
      }
    }
  }
  entPrev.clear();
  for (const e of ents) entPrev.set(e.id, { c: e.c, r: e.r, painting: e.painting });

  broadcast({ t: 's', e: ents.map(e => [e.id, e.c, e.r, e.s, e.painting ? 1 : 0, e.erase ? 1 : 0]) });
  if (erased.length) broadcast({ t: 'x', d: erased });
  if (deposits.length) broadcast({ t: 'p', d: deposits });
}

function broadcast(msg) {
  const data = JSON.stringify(msg);
  for (const ws of users.keys()) if (ws.readyState === 1) ws.send(data);
}

// Everything painted so far, as ages, so a newly joined client sees the same canvas.
function snapshot() {
  const now = Date.now(), out = [];
  for (const [key, layers] of cells) {
    const r = Math.floor(key / 100000), c = key - r * 100000;
    layers.forEach((l, ci) => {
      l.stamps = l.stamps.filter(t => (now - t < SETTLE) || (l.settled++, false));
      if (l.settled || l.stamps.length) out.push([c, r, ci, l.settled, l.stamps.map(t => now - t)]);
    });
  }
  return { t: 'init', cells: out };
}

// ---- Minimal WebSocket (text messages only) ---------------------------------
// Just enough of RFC 6455 for this prototype; swap for the `ws` package if it grows.
function accept(req, socket, onConnection) {
  const key = req.headers['sec-websocket-key'];
  if (!key) return socket.destroy();
  const hash = crypto.createHash('sha1').update(key + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
  socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n' +
               `Sec-WebSocket-Accept: ${hash}\r\n\r\n`);
  socket.setNoDelay(true);

  const ws = { readyState: 1, onmessage: () => {}, onclose: () => {} };
  const frame = (op, payload) => {
    const n = payload.length;
    const head = n < 126 ? Buffer.from([0x80 | op, n])
      : n < 65536 ? Buffer.from([0x80 | op, 126, n >> 8, n & 255])
      : Buffer.concat([Buffer.from([0x80 | op, 127]), (b => (b.writeBigUInt64BE(BigInt(n)), b))(Buffer.alloc(8))]);
    if (!socket.destroyed) socket.write(Buffer.concat([head, payload]));
  };
  ws.send = str => { if (ws.readyState === 1) frame(1, Buffer.from(str)); };
  const close = () => { if (ws.readyState !== 1) return; ws.readyState = 3; socket.destroy(); ws.onclose(); };

  let buf = Buffer.alloc(0), parts = [];
  socket.on('data', chunk => {
    buf = Buffer.concat([buf, chunk]);
    while (buf.length >= 2) {
      const fin = buf[0] & 0x80, op = buf[0] & 0x0f, masked = buf[1] & 0x80;
      let len = buf[1] & 0x7f, off = 2;
      if (len === 126) { if (buf.length < 4) return; len = buf.readUInt16BE(2); off = 4; }
      else if (len === 127) { if (buf.length < 10) return; len = Number(buf.readBigUInt64BE(2)); off = 10; }
      const maskOff = off; if (masked) off += 4;
      if (buf.length < off + len) return;
      const data = Buffer.from(buf.subarray(off, off + len));
      if (masked) for (let i = 0; i < len; i++) data[i] ^= buf[maskOff + (i & 3)];
      buf = buf.subarray(off + len);
      if (op === 8) return close();
      if (op === 9) { frame(10, data); continue; }
      if (op === 10) { ws.alive = true; continue; }
      if (op === 1 || op === 0) {
        parts.push(data);
        if (fin) { const msg = Buffer.concat(parts).toString(); parts = []; ws.onmessage(msg); }
      }
    }
  });
  ws.alive = true;
  ws.ping = () => { if (ws.readyState === 1) frame(9, Buffer.alloc(0)); };
  ws.close = close;
  socket.on('close', close);
  socket.on('error', close);
  onConnection(ws);
}

// ---- Connections ------------------------------------------------------------
server.on('upgrade', (req, socket) => accept(req, socket, onConnection));
function onConnection(ws) {
  const user = { id: nextId++, c: null, r: null, down: false, erase: false };
  users.set(ws, user);
  ws.send(JSON.stringify(snapshot()));
  update();

  ws.onmessage = raw => {
    let m; try { m = JSON.parse(raw); } catch { return; }
    if (m.t === 'm' || m.t === 'd') { user.c = Math.max(0, m.c | 0); user.r = Math.max(0, m.r | 0); }
    if (m.t === 'd') user.down = true;
    if (m.t === 'u') user.down = false;
    if (m.t === 'l') { user.c = user.r = null; user.down = false; }
    if (m.t === 'e') user.erase = !!m.v;   // erase mode on/off (Shift, Delete, Backspace)
    update();
  };
  ws.onclose = () => { users.delete(ws); update(); };
}

// Heartbeat: hosting proxies drop silent connections, and a vanished participant
// (closed laptop, lost network) should free their slot. Browsers answer pings automatically.
setInterval(() => {
  for (const ws of users.keys()) {
    if (!ws.alive) { ws.close(); continue; }
    ws.alive = false;
    ws.ping();
  }
}, 25000);

// 0.0.0.0 so the server is reachable inside a hosting container (Render sets PORT).
server.listen(PORT, '0.0.0.0', () => console.log(`Presence running on port ${PORT} (locally: http://localhost:${PORT})`));
