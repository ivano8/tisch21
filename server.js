// Tisch 21 — Blackjack fuer bis zu 6 Spieler gegen den Dealer.
// Ein Node-Server ohne Abhaengigkeiten: der Server entscheidet alles,
// die Browser bekommen den Tisch per Server-Sent Events und schicken Aktionen per POST.
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT || 3000;
const START = 1000, MAX_SEATS = 6, MAX_HANDS = 4;
const TURN_MS = 30000, OFFLINE_TURN_MS = 4000, NEXT_ROUND_MS = 8000;
const INDEX = fs.readFileSync(path.join(__dirname, 'public', 'index.html'));

/* ---------- cards ---------- */
const RANKS = ['A','2','3','4','5','6','7','8','9','10','J','Q','K'];
const rankOf = c => c.slice(0, -1);
const val = r => r === 'A' ? 11 : ['10','J','Q','K'].includes(r) ? 10 : +r;
function total(cards) {
  let t = 0, a = 0;
  for (const c of cards) { const r = rankOf(c); t += val(r); if (r === 'A') a++; }
  while (t > 21 && a) { t -= 10; a--; }
  return t;
}
const isBJ = cards => cards.length === 2 && total(cards) === 21;
function newShoe() {
  const d = [];
  for (let k = 0; k < 6; k++) for (const s of 'SHDC') for (const r of RANKS) d.push(r + s);
  for (let i = d.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [d[i], d[j]] = [d[j], d[i]]; }
  return d;
}
function draw(r) { if (r.deck.length < 60) r.deck = newShoe(); return r.deck.pop(); }

/* ---------- rooms ---------- */
const rooms = new Map();
function getRoom(code) {
  let r = rooms.get(code);
  if (!r) {
    r = { code, players: {}, bank: {}, phase: 'betting', dealer: [], hidden: false, deck: newShoe(),
          turn: null, turnEnds: 0, nextAt: 0, round: 0, clients: new Set(), timer: null, touched: Date.now() };
    rooms.set(code, r);
  }
  r.touched = Date.now();
  return r;
}
const seated = r => Object.values(r.players).sort((a, b) => a.seat - b.seat);
const isOnline = (r, id) => [...r.clients].some(c => c.id === id);
const newHand = bet => ({ cards: [], bet, status: 'playing', doubled: false, result: null, pay: 0 });

/* ---------- rules ---------- */
function deal(r) {
  const ps = seated(r).filter(p => p.ready && p.bet > 0 && p.bet <= p.chips);
  if (!ps.length) return false;
  r.round++; r.dealer = []; r.hidden = true;
  for (const p of seated(r)) { p.hands = []; p.active = 0; p.inRound = false; p.delta = 0; }
  for (const p of ps) { p.chips -= p.bet; p.inRound = true; p.hands = [newHand(p.bet)]; }
  for (let k = 0; k < 2; k++) { for (const p of ps) p.hands[0].cards.push(draw(r)); r.dealer.push(draw(r)); }
  for (const p of ps) if (isBJ(p.hands[0].cards)) p.hands[0].status = 'blackjack';
  r.phase = 'playing';
  if (isBJ(r.dealer)) finish(r); else advance(r);
  return true;
}
function advance(r) {
  for (const p of seated(r)) {
    if (!p.inRound) continue;
    const i = p.hands.findIndex(h => h.status === 'playing');
    if (i >= 0) { r.turn = p.id; p.active = i; return; }
  }
  r.turn = null; r.hidden = false;
  if (seated(r).some(p => p.inRound && p.hands.some(h => h.status === 'stand')))
    while (total(r.dealer) < 17) r.dealer.push(draw(r));
  finish(r);
}
function finish(r) {
  r.hidden = false; r.turn = null; r.phase = 'done';
  const d = total(r.dealer), dBJ = isBJ(r.dealer);
  for (const p of seated(r)) {
    if (!p.inRound) continue;
    let pay = 0, staked = 0;
    for (const h of p.hands) {
      const t = total(h.cards), pBJ = h.status === 'blackjack';
      let hp = 0, res;
      if (h.status === 'bust') res = 'bust';
      else if (pBJ && dBJ) { hp = h.bet; res = 'push'; }
      else if (pBJ) { hp = h.bet + Math.floor(h.bet * 1.5); res = 'blackjack'; }
      else if (dBJ) res = 'lose';
      else if (d > 21 || t > d) { hp = h.bet * 2; res = 'win'; }
      else if (t === d) { hp = h.bet; res = 'push'; }
      else res = 'lose';
      h.pay = hp; h.result = res; pay += hp; staked += h.bet;
    }
    p.chips += pay; p.delta = pay - staked;
  }
}
function newRound(r) {
  r.phase = 'betting'; r.dealer = []; r.hidden = false; r.turn = null;
  for (const p of seated(r)) {
    if (!isOnline(r, p.id)) { r.bank[p.id] = p.chips; delete r.players[p.id]; continue; }
    p.hands = []; p.active = 0; p.ready = false; p.inRound = false; p.delta = 0;
    if (p.bet > p.chips) p.bet = 0;
  }
}
const canSplit = (p, h) => h && h.status === 'playing' && h.cards.length === 2 && p.hands.length < MAX_HANDS
  && p.chips >= h.bet && val(rankOf(h.cards[0])) === val(rankOf(h.cards[1]));
const canDouble = (p, h) => h && h.status === 'playing' && h.cards.length === 2 && p.chips >= h.bet;
function allReady(r) { const ps = seated(r); return ps.length > 0 && ps.every(p => p.ready); }

/* ---------- actions ---------- */
function act(r, id, a) {
  const p = r.players[id];
  const mine = () => (r.phase === 'playing' && r.turn === id && p) ? p.hands[p.active] : null;
  switch (a.type) {
    case 'join': {
      if (p) { p.left = false; return true; }
      if (seated(r).length >= MAX_SEATS) return 'Alle 6 Plätze sind belegt';
      const name = String(a.name || '').trim().slice(0, 18) || 'Gast';
      r.players[id] = { id, name, chips: r.bank[id] ?? START, seat: Date.now(), bet: 0, ready: false,
                        hands: [], active: 0, inRound: false, delta: 0 };
      delete r.bank[id];
      return true;
    }
    case 'bet': {
      const amt = Math.floor(+a.amount);
      if (!p || r.phase !== 'betting' || !(amt > 0) || amt > p.chips) return false;
      p.bet = amt; p.ready = true;
      if (allReady(r)) deal(r);
      return true;
    }
    case 'unready': if (!p || r.phase !== 'betting') return false; p.ready = false; return true;
    case 'deal': if (r.phase !== 'betting' || !p || !p.ready) return false; return deal(r);
    case 'hit': {
      const h = mine(); if (!h) return false;
      h.cards.push(draw(r)); const t = total(h.cards);
      if (t > 21) h.status = 'bust'; else if (t === 21) h.status = 'stand';
      if (h.status !== 'playing') advance(r);
      return true;
    }
    case 'stand': { const h = mine(); if (!h) return false; h.status = 'stand'; advance(r); return true; }
    case 'double': {
      const h = mine(); if (!canDouble(p, h)) return false;
      p.chips -= h.bet; h.bet *= 2; h.doubled = true; h.cards.push(draw(r));
      h.status = total(h.cards) > 21 ? 'bust' : 'stand'; advance(r); return true;
    }
    case 'split': {
      const h = mine(); if (!canSplit(p, h)) return false;
      p.chips -= h.bet;
      const nh = newHand(h.bet); nh.cards.push(h.cards.pop());
      p.hands.splice(p.active + 1, 0, nh);
      h.cards.push(draw(r)); nh.cards.push(draw(r));
      const aces = rankOf(h.cards[0]) === 'A';
      for (const x of [h, nh]) if (aces || total(x.cards) === 21) x.status = 'stand';
      if (h.status !== 'playing') advance(r);
      return true;
    }
    case 'rebuy': if (!p || p.chips >= 5 || p.inRound) return false; p.chips = START; return true;
    case 'leave': {
      if (!p) return false;
      if (r.phase === 'playing' && p.inRound) {
        p.hands.forEach(h => { if (h.status === 'playing') h.status = 'stand'; });
        if (r.turn === id) advance(r);
        p.left = true; // removed at the next round
      } else { r.bank[id] = p.chips; delete r.players[id]; }
      if (r.phase === 'betting' && allReady(r)) deal(r);
      return true;
    }
  }
  return false;
}

/* ---------- timing ---------- */
function schedule(r) {
  // only restart the clock when the situation really changed, not when someone reconnects
  const tp = r.turn && r.players[r.turn];
  const key = [r.phase, r.round, r.turn, tp && tp.active, tp && tp.hands[tp.active] && tp.hands[tp.active].cards.length,
               tp && (isOnline(r, r.turn) && !tp.left)].join('|');
  if (key === r.schedKey) return;
  r.schedKey = key;
  clearTimeout(r.timer); r.turnEnds = 0; r.nextAt = 0;
  if (r.phase === 'playing' && r.turn) {
    const ms = isOnline(r, r.turn) && !r.players[r.turn].left ? TURN_MS : OFFLINE_TURN_MS;
    r.turnEnds = Date.now() + ms;
    const turnAtStart = r.turn, roundAtStart = r.round;
    r.timer = setTimeout(() => {
      if (r.turn !== turnAtStart || r.round !== roundAtStart) return;
      r.players[r.turn].hands.forEach(h => { if (h.status === 'playing') h.status = 'stand'; });
      advance(r); update(r);
    }, ms);
  } else if (r.phase === 'done') {
    r.nextAt = Date.now() + NEXT_ROUND_MS;
    r.timer = setTimeout(() => {
      for (const p of seated(r)) if (p.left) { r.bank[p.id] = p.chips; delete r.players[p.id]; }
      newRound(r); update(r);
    }, NEXT_ROUND_MS);
  }
}
function view(r) {
  return {
    code: r.code, phase: r.phase, round: r.round, turn: r.turn,
    turnLeft: r.turnEnds ? Math.max(0, r.turnEnds - Date.now()) : 0,
    dealer: r.hidden ? [r.dealer[0], '??'] : r.dealer,
    shoe: r.deck.length,
    players: seated(r).filter(p => !p.left || p.inRound).map(p => ({
      id: p.id, name: p.name, chips: p.chips, bet: p.bet, ready: p.ready, inRound: p.inRound,
      active: p.active, delta: p.delta, online: isOnline(r, p.id),
      canSplit: r.turn === p.id && canSplit(p, p.hands[p.active]),
      canDouble: r.turn === p.id && canDouble(p, p.hands[p.active]),
      hands: p.hands.map(h => ({ cards: h.cards, bet: h.bet, status: h.status, doubled: h.doubled, result: h.result, pay: h.pay })),
    })),
  };
}
function update(r) {
  schedule(r);
  const msg = `data: ${JSON.stringify(view(r))}\n\n`;
  for (const c of r.clients) c.res.write(msg);
}

/* ---------- http ---------- */
const validCode = c => typeof c === 'string' && /^[a-z0-9]{3,12}$/.test(c);
const validId = id => typeof id === 'string' && /^[A-Za-z0-9-]{8,64}$/.test(id);

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://x');
  if (req.method === 'GET' && url.pathname === '/events') {
    const code = url.searchParams.get('t'), id = url.searchParams.get('id');
    if (!validCode(code) || !validId(id)) { res.writeHead(400); return res.end(); }
    const r = getRoom(code);
    res.writeHead(200, { 'Content-Type': 'text/event-stream', 'Cache-Control': 'no-cache', 'Connection': 'keep-alive', 'X-Accel-Buffering': 'no' });
    const client = { id, res };
    r.clients.add(client);
    update(r);
    req.on('close', () => { r.clients.delete(client); update(r); });
    return;
  }
  if (req.method === 'POST' && url.pathname === '/action') {
    let body = '';
    req.on('data', d => { body += d; if (body.length > 2000) req.destroy(); });
    req.on('end', () => {
      let a; try { a = JSON.parse(body); } catch { res.writeHead(400); return res.end(); }
      if (!validCode(a.t) || !validId(a.id)) { res.writeHead(400); return res.end(); }
      const r = getRoom(a.t);
      const out = act(r, a.id, a);
      if (out) update(r);
      res.writeHead(200, { 'Content-Type': 'application/json' });
      res.end(JSON.stringify(typeof out === 'string' ? { error: out } : { ok: !!out }));
    });
    return;
  }
  if (req.method === 'GET' && url.pathname === '/health') { res.writeHead(200); return res.end('ok'); }
  if (req.method === 'GET') {
    res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' });
    return res.end(INDEX);
  }
  res.writeHead(404); res.end();
});

// keep streams open through proxies, drop tables nobody used for 2 hours
setInterval(() => {
  for (const r of rooms.values()) {
    for (const c of r.clients) c.res.write(': ping\n\n');
    if (!r.clients.size && Date.now() - r.touched > 2 * 3600e3) { clearTimeout(r.timer); rooms.delete(r.code); }
  }
}, 20000);

server.listen(PORT, () => console.log(`Tisch 21 läuft auf http://localhost:${PORT}`));
