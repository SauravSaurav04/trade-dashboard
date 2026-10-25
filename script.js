/* ==========================================================================
   Trading Journal Analytics
   --------------------------------------------------------------------------
   Pipeline:
     1. LOAD      a trades CSV chosen by the user (file picker, drag & drop, or ?file= over http)
     2. PARSE     broker executions into round-turn trades           (parseTradesCsv; parseJournal reads a journal .md)
                  trade numbers (t.id) come from the CSV "Trade No" column (required, unique); the legacy export is numbered 1..n by trading day, then close time
     2b. FILTER   narrow the trade list from the filter bar          (applyFilters)
     3. ANALYSE   compute every statistic from the trade list        (analyze)
     4. INSIGHT   rule-based psychology insights + recommendations   (buildInsights)
     5. RENDER    KPI cards, Chart.js charts, calendar and tables    (render*)

   The CSV is the single source of truth: every number on the page is recomputed
   from its executions (a journal .md is still accepted and is reconciled against
   its own "Headline Numbers" table).
   ========================================================================== */

'use strict';

/* ==========================================================================
   0. CONFIGURATION & SMALL HELPERS
   ========================================================================== */

// Trading day runs 06:00 -> 05:59 and is decided by the opening time.
const DAY_START_HOUR = 6;
// Hold at or under this many minutes counts as a scalp.
const SCALP_MAX_MIN = 6;
// Same-symbol entry within this many minutes of a losing close counts as a re-entry.
const REENTRY_WINDOW_MIN = 15;

// Same limit the journal recommends ("Cap daily trades at 6").
const OVERTRADE_THRESHOLD = 6;
// A trade held at least this long is tagged "Long hold".
const LONG_HOLD_MIN = 60;

// Chart colours; the solid ones are overwritten from the CSS variables in readThemeColors() so styles.css stays the source.
const C = {
  green: '#26a69a', red: '#ef5350', blue: '#2962ff', amber: '#f5a623',
  grey: '#787b86', grid: 'rgba(120,123,134,0.15)', text: '#9aa4b2',
  greenFill: 'rgba(38,166,154,0.18)', redFill: 'rgba(239,83,80,0.18)',
  panel: '#1a1e2b', bg: '#0b0e14', border: '#2a2e39',
};
const THEME_VARS = { green: '--green', red: '--red', blue: '--blue', amber: '--amber', grey: '--muted', panel: '--panel', bg: '--bg', border: '--border' };
const WEEKDAYS = ['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun'];
const MONTHS = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];

const pad2 = n => String(n).padStart(2, '0');
const sum = arr => arr.reduce((s, x) => s + x, 0);
// Spreading a huge array into Math.min/max can overflow the call stack.
const minOf = (arr, init = Infinity) => arr.reduce((m, x) => (x < m ? x : m), init);
const maxOf = (arr, init = -Infinity) => arr.reduce((m, x) => (x > m ? x : m), init);

/** Escape text before inserting it into innerHTML. */
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
/** Minimal inline-markdown renderer (bold + code) applied after escaping. */
const mdInline = s => esc(s).replace(/\*\*(.+?)\*\*/g, '<strong>$1</strong>').replace(/`(.+?)`/g, '<code>$1</code>');
const stripMd = s => String(s).replace(/\*\*|`/g, '').trim();

const money = (v, signed = false) => {
  if (!isFinite(v)) return '—';
  const abs = Math.abs(v).toLocaleString('en-US', { minimumFractionDigits: 2, maximumFractionDigits: 2 });
  return `${v < 0 ? '-' : (signed && v > 0 ? '+' : '')}$${abs}`;
};
const pct = (v, d = 1) => (isFinite(v) ? (v * 100).toFixed(d) + '%' : '—');
const ratio = v => (v === Infinity ? '∞' : isFinite(v) ? v.toFixed(2) : '—');
const signClass = v => (v > 0 ? 'pos' : v < 0 ? 'neg' : '');
const plural = (n, word, many = word + 's') => `${n} ${n === 1 ? word : many}`;

/* ==========================================================================
   1. PARSING  -  markdown  ->  structured journal object
   ========================================================================== */

/**
 * Convert a money-like cell into a number.
 *   "+$108.79" -> 108.79   "-$15.71" -> -15.71   "**-$85.12**" -> -85.12   "$0.00" -> 0
 * Bold markers and thousands separators are stripped first. Returns NaN if no number is found.
 */
function parseMoney(raw) {
  if (raw == null) return NaN;
  const s = String(raw).replace(/\*/g, '').replace(/,/g, '');
  const m = s.match(/([+\-−–])?\s*\$?\s*(\d+(?:\.\d+)?)/);
  if (!m) return NaN;
  const v = parseFloat(m[2]);
  return m[1] && m[1] !== '+' ? -v : v;
}

/** "02 Oct 2026" -> Date at UTC midnight (UTC avoids local time-zone day shifts). */
function parseDateText(text) {
  const m = String(text).match(/(\d{1,2})\s+([A-Za-z]{3})[a-z]*\s+(\d{4})/);
  if (!m) return null;
  const mi = MONTHS.findIndex(x => x.toLowerCase() === m[2].toLowerCase());
  return mi < 0 ? null : new Date(Date.UTC(+m[3], mi, +m[1]));
}

const dateKey = d => d.toISOString().slice(0, 10);                       // 2026-10-02
const dayLabel = d => `${pad2(d.getUTCDate())} ${MONTHS[d.getUTCMonth()]}`; // 02 Oct
const weekdayIndex = d => (d.getUTCDay() + 6) % 7;                       // Mon=0 ... Sun=6
const weekStart = d => new Date(d.getTime() - weekdayIndex(d) * 86400000); // Monday of that week

/** Split a markdown table row "| a | b |" into trimmed cells. */
const splitRow = line => line.trim().replace(/^\|/, '').replace(/\|$/, '').split('|').map(c => c.trim());
/** Detects the "|---|:---:|" separator row. */
const isSeparator = cells => cells.every(c => /^:?-{2,}:?$/.test(c));

/**
 * Extract behavioural facts from the free-text Notes cell. Examples of notes handled:
 *   "Scalp (4.5 min hold)"
 *   "Re-entry 7.6 min after Trade #3 loss; size up 0.5 → 0.8"
 *   "Largest win; held 175.3 min"        "Longest hold (176.9 min)"
 *   "Trading-day rollover (opened 08 Oct 00:33, closed 01:41; ...)"
 * Note the care taken with "re-entry 10.4 min after ..." - that is a gap, NOT a holding time.
 */
function parseNotes(notes) {
  const n = notes || '';
  let holdMin = null;
  const holdPatterns = [
    /held\s+(\d+(?:\.\d+)?)\s*min/i,          // "Held 83.0 min"
    /\((\d+(?:\.\d+)?)\s*min hold\)/i,        // "(4.5 min hold)"
    /hold\s*\((\d+(?:\.\d+)?)\s*min\)/i,      // "Longest hold (176.9 min)"
  ];
  for (const re of holdPatterns) {
    const m = n.match(re);
    if (m) { holdMin = parseFloat(m[1]); break; }
  }
  const gap = n.match(/re-entry\s+(\d+(?:\.\d+)?)\s*min/i);
  return {
    holdMin,
    reentryGapMin: gap ? parseFloat(gap[1]) : null,
    tags: {
      scalp: /scalp/i.test(n),
      reentry: /re-entry/i.test(n),
      sizeUp: /size up/i.test(n),
      rollover: /rollover/i.test(n),
      longHold: holdMin != null && holdMin >= LONG_HOLD_MIN,
    },
  };
}

/**
 * Primary "setup" label for the by-setup breakdown. The journal has no explicit strategy
 * column, so a setup is inferred from the notes. One label per trade, ordered by priority
 * (the behavioural problem wins over the descriptive label).
 */
function classifySetup(tags) {
  if (tags.reentry) return 'Re-entry after loss';
  if (tags.scalp) return 'Scalp (≤6 min)';
  if (tags.rollover) return 'Overnight rollover';
  if (tags.longHold) return `Long hold (${LONG_HOLD_MIN}+ min)`;
  return 'Standard entry';
}

/**
 * Parse the whole markdown document.
 *
 * The document is walked line by line while tracking state:
 *   - `section`      number from headings like "## 3. Trade-by-Trade Detail"
 *   - `currentDate`  from day headings like "#### Friday, 02 Oct 2026" (inside section 3)
 *   - table state    first '|' row after a non-table line is the header; later rows are data
 * What is extracted:
 *   section 1  headline key/value table  (used to reconcile computed numbers)
 *   section 3  one row per trade         (the data every statistic is built from)
 *   section 8  hour-of-day table         (trade times are not in section 3)
 *   section 11 numbered findings, section 12 recommendation bullets (shown verbatim)
 */
function parseJournal(md) {
  const out = { title: '', period: '', headline: {}, trades: [], hours: [], findings: [], recommendations: [] };
  let section = 0;
  let currentDate = null;
  let header = null;
  let inTable = false;
  let seq = 0;

  for (const rawLine of md.split(/\r?\n/)) {
    const line = rawLine.trim();

    // ---- headings ----
    if (/^#\s+/.test(line) && !out.title) out.title = line.replace(/^#\s+/, '');
    const sec = line.match(/^##\s+(\d+)\./);
    if (sec) { section = +sec[1]; inTable = false; header = null; continue; }

    const period = line.match(/^\*\*Period covered:\*\*\s*(.+)$/i);
    if (period) out.period = period[1];

    const day = line.match(/^#{3,4}\s+[A-Za-z]+,\s*(\d{1,2}\s+[A-Za-z]{3}\s+\d{4})/);
    if (day && section === 3) { currentDate = parseDateText(day[1]); inTable = false; header = null; continue; }

    // ---- tables ----
    if (line.startsWith('|')) {
      const cells = splitRow(line);
      if (isSeparator(cells)) continue;
      if (!inTable) { header = cells.map(c => stripMd(c).toLowerCase()); inTable = true; continue; }

      if (section === 1 && cells.length >= 2) {
        out.headline[stripMd(cells[0])] = cells[1];
      } else if (section === 3 && currentDate) {
        // Map columns by header name so column order / extra columns never break parsing.
        const col = name => header.findIndex(h => h.startsWith(name));
        const idx = { id: col('trade id'), sym: col('symbol'), side: col('side'), qty: col('qty'), pnl: col('net p&l'), bal: Math.max(col('balance'), col('equity')), notes: col('notes') };
        const pnl = parseMoney(cells[idx.pnl]);
        if (!isFinite(pnl) || idx.sym < 0) continue;
        const notes = idx.notes >= 0 ? stripMd(cells[idx.notes] || '') : '';
        const info = parseNotes(notes);
        out.trades.push({
          seq: ++seq,
          id: parseInt(cells[idx.id], 10) || seq,
          symbol: stripMd(cells[idx.sym]),
          side: stripMd(cells[idx.side] || ''),
          qty: parseFloat(cells[idx.qty]) || 0,
          pnl,
          balance: idx.bal >= 0 ? parseMoney(cells[idx.bal]) : NaN,
          notes: notes === '-' ? '' : notes,
          date: currentDate,
          dateKey: dateKey(currentDate),
          weekday: weekdayIndex(currentDate),
          holdMin: info.holdMin,
          reentryGapMin: info.reentryGapMin,
          tags: info.tags,
          setup: classifySetup(info.tags),
        });
      } else if (section === 8 && /^\d{1,2}:\d{2}$/.test(cells[0])) {
        out.hours.push({ hour: parseInt(cells[0], 10), trades: parseInt(cells[1], 10) || 0, pnl: parseMoney(cells[2]) });
      }
      continue;
    }
    inTable = false;
    header = null;

    // ---- lists ----
    if (section === 11) {
      const m = line.match(/^\d+\.\s+(.*)$/);
      if (m) out.findings.push(splitTitle(m[1]));
    } else if (section === 12) {
      const m = line.match(/^[-*]\s+(.*)$/);
      if (m) out.recommendations.push(splitTitle(m[1]));
    }
  }
  return out;
}

/** "**Title:** body text" -> { title, body } */
function splitTitle(text) {
  const m = text.match(/^\*\*(.+?)\*\*:?\s*(.*)$/);
  return m ? { title: m[1].replace(/:$/, ''), body: m[2] } : { title: '', body: text };
}

/** Split one CSV line, honouring "quoted, fields". */
function splitCsvLine(line) {
  const out = [];
  let cur = '', quoted = false;
  for (let i = 0; i < line.length; i++) {
    const ch = line[i];
    if (ch === '"') {
      if (quoted && line[i + 1] === '"') { cur += '"'; i++; } else quoted = !quoted;
    } else if (ch === ',' && !quoted) { out.push(cur); cur = ''; } else cur += ch;
  }
  out.push(cur);
  return out.map(c => c.trim());
}

/** "10/09/2026, 11:00:02" (MM/DD/YYYY) or "2026-10-09 11:00:02" -> epoch ms; read as UTC so the wall-clock time is kept. */
function parseTradeTime(text) {
  const s = String(text);
  let m = s.match(/(\d{1,2})\/(\d{1,2})\/(\d{4}),?\s+(\d{1,2}):(\d{2})(?::(\d{2}))?/);
  if (m) return Date.UTC(+m[3], +m[1] - 1, +m[2], +m[4], +m[5], +m[6] || 0);
  m = s.match(/(\d{4})-(\d{2})-(\d{2})[T\s]+(\d{1,2}):(\d{2})(?::(\d{2}))?/);
  return m ? Date.UTC(+m[1], +m[2] - 1, +m[3], +m[4], +m[5], +m[6] || 0) : NaN;
}

const cents = v => Math.round(v * 100) / 100;
const isoDay = ms => new Date(ms).toISOString().slice(0, 10);
const stampLabel = ms => { const d = new Date(ms); return `${dayLabel(d)} ${pad2(d.getUTCHours())}:${pad2(d.getUTCMinutes())}`; };

/**
 * Pair executions into positions per symbol, oldest first: a leg opposite to the open lots closes one
 * (preferring the oldest lot of the same qty), anything else opens a new lot. Unmatched lots stay single-leg.
 */
function pairLegsFifo(legs) {
  const chrono = [...legs].sort((a, b) => a.time - b.time || b.n - a.n);
  const queues = new Map();
  const lots = [];
  chrono.forEach(leg => {
    const queue = queues.get(leg.symbol) || [];
    queues.set(leg.symbol, queue);
    if (queue.length && queue[0][0].side.toLowerCase() !== leg.side.toLowerCase()) {
      const i = Math.max(0, queue.findIndex(lot => lot[0].qty === leg.qty));
      queue.splice(i, 1)[0].push(leg);
    } else {
      const lot = [leg];
      queue.push(lot);
      lots.push(lot);
    }
  });
  return lots;
}

/**
 * Latest trade in `byClose` (one symbol, sorted by close time) that closed at or before `t` opened, excluding `t`.
 * Among equal close times the earliest in trade order wins, matching the original linear scan.
 */
function previousClosed(byClose, t) {
  let lo = 0, hi = byClose.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (byClose[mid].closeMs <= t.openMs) lo = mid + 1; else hi = mid;
  }
  let end = lo - 1;
  while (end >= 0) {
    const closeMs = byClose[end].closeMs;
    let start = end;
    while (start > 0 && byClose[start - 1].closeMs === closeMs) start--;
    for (let i = start; i <= end; i++) if (byClose[i] !== t) return byClose[i];
    end = start - 1;
  }
  return null;
}

/**
 * Parse a broker export (one row per execution) into the same journal object parseJournal returns.
 *   - rows sharing a Position ID are the legs of one round-turn trade (paired by symbol and time if the IDs are unusable)
 *   - Net P&L is all-in: Profit + Swap + Commission over every leg
 *   - side/qty come from the opening leg; the trading day comes from the opening time (06:00 cut-off)
 *   - trades are numbered and ordered by the required, unique "Trade No" column (the legacy export is numbered 1..n
 *     by trading day, then close time)
 *   - notes/tags (scalp, re-entry, size up, rollover, long hold) are derived from the timestamps
 * A position with no closing leg is still open and is left out.
 */
function parseTradesCsv(text) {
  const cleanUrl = v => {
    const s = String(v == null ? '' : v).trim();
    try { return /^https?:$/.test(new URL(s).protocol) ? s : ''; } catch (err) { return ''; }
  };
  // Outcome: 1 = meets the strategy (take again), 0 = does not; anything else is unknown.
  const parseOutcome = v => { const o = String(v == null ? '' : v).trim(); return o === '1' ? 1 : o === '0' ? 0 : null; };
  // Score: integer 1-5, anything else is unknown.
  const parseScore = v => { const s = String(v == null ? '' : v).trim(); if (!/^\d+$/.test(s)) return null; const n = parseInt(s, 10); return n >= 1 && n <= 5 ? n : null; };
  // Trade No: positive whole number, an optional leading "#" is ignored; anything else is unknown.
  const parseTradeNo = v => { const s = String(v == null ? '' : v).replace(/^\s*#\s*/, '').trim(); if (!/^\d+$/.test(s)) return null; const n = parseInt(s, 10); return n > 0 && Number.isSafeInteger(n) ? n : null; };
  const lines = text.split(/\r?\n/).filter(l => l.trim());
  const head = splitCsvLine((lines.shift() || '').replace(/^\uFEFF/, '')).map(h => h.trim().toLowerCase());
  const col = name => head.indexOf(name);
  // New format: one row per closed trade (Open Date, Close Date, Entry/Exit Price, Fee, Swap Fees, Net P&L).
  const isTradeFormat = head.includes('open date') && head.includes('close date') && head.includes('net p&l');
  const idx = isTradeFormat
    ? { tradeNo: Math.max(...['trade no', 'trade #', 'trade id', 'tradeno'].map(col)), sym: col('symbol'), side: col('side'), qty: col('qty'), open: col('open date'), close: col('close date'), entry: col('entry price'), exit: col('exit price'), fee: col('fee'), swap: col('swap fees'), net: col('net p&l'), entryVideo: col('entry chart video link'), exitVideo: col('exit chart video link'), outcome: col('outcome'), setup: col('entry setup score'), risk: col('risk management score'), stopLoss: col('stop loss discipline score'), exit2: col('exit management score'), emotion: col('emotion control score') }
    : { sym: col('symbol'), side: col('side'), qty: col('qty'), profit: col('profit'), swap: col('swap'), time: col('date/time'), comm: col('commission'), pos: col('position id') };
  const required = isTradeFormat ? [idx.sym, idx.side, idx.qty, idx.open, idx.close, idx.net] : [idx.sym, idx.side, idx.qty, idx.profit, idx.time, idx.pos];
  if (required.some(i => i < 0)) {
    throw new Error('CSV needs the columns Symbol, Side, Qty, Open Date, Close Date and Net P&L (or the legacy Symbol, Side, Qty, Profit, Date/Time and Position ID).');
  }
  if (isTradeFormat && idx.tradeNo < 0) throw new Error('CSV needs a "Trade No" column holding a unique whole number for every trade.');
  const num = (cells, i) => (i >= 0 ? parseFloat(String(cells[i]).replace(/,/g, '')) || 0 : 0);

  // 1. Group executions (legs) into positions.
  const allLegs = [];
  const directTrades = []; // new format: already round-turn trades
  lines.forEach((line, n) => {
    const c = splitCsvLine(line);
    if (isTradeFormat) {
      const openMs = parseTradeTime(c[idx.open]), closeMs = parseTradeTime(c[idx.close]);
      if (isFinite(openMs) && isFinite(closeMs)) {
        const sc = k => parseScore(idx[k] >= 0 ? c[idx[k]] : '');
        const scores = { setup: sc('setup'), risk: sc('risk'), stopLoss: sc('stopLoss'), exit: sc('exit2'), emotion: sc('emotion') };
        const vals = Object.values(scores);
        directTrades.push({
          tradeNo: parseTradeNo(c[idx.tradeNo]), row: n + 1,
          scores, score: vals.every(v => v !== null) ? sum(vals) : null,
          symbol: c[idx.sym], side: c[idx.side], qty: num(c, idx.qty), openMs, closeMs,
          entryPrice: num(c, idx.entry), exitPrice: num(c, idx.exit),
          commission: -Math.abs(num(c, idx.fee)), // Fee is a positive cost; stored negative like the legacy Commission
          swap: num(c, idx.swap), pnl: cents(num(c, idx.net)), // Net P&L already includes fee and swap
          entryVideo: cleanUrl(idx.entryVideo >= 0 ? c[idx.entryVideo] : ''), exitVideo: cleanUrl(idx.exitVideo >= 0 ? c[idx.exitVideo] : ''),
          outcome: parseOutcome(idx.outcome >= 0 ? c[idx.outcome] : ''),
        });
      }
      return;
    }
    const leg = { n, pos: c[idx.pos], symbol: c[idx.sym], side: c[idx.side], qty: num(c, idx.qty), profit: num(c, idx.profit), swap: num(c, idx.swap), commission: num(c, idx.comm), time: parseTradeTime(c[idx.time]) };
    if (isFinite(leg.time)) allLegs.push(leg);
  });
  let positions;
  if (isTradeFormat) {
    positions = [];
  } else if (allLegs.some(l => /^\d+(\.\d+)?e[+-]?\d+$/i.test(l.pos))) { // Excel turns long IDs into "5.20E+14"
    positions = pairLegsFifo(allLegs);
  } else {
    const byPos = new Map();
    allLegs.forEach(l => { if (!byPos.has(l.pos)) byPos.set(l.pos, []); byPos.get(l.pos).push(l); });
    positions = [...byPos.values()];
  }

  // 2. One round-turn trade per position.
  let openPositions = 0;
  const trades = [];
  positions.forEach(legs => {
    // Oldest first; the export is newest-first, so on equal timestamps the later row is the earlier execution.
    legs.sort((a, b) => a.time - b.time || b.n - a.n);
    const opener = legs[0];
    const sameSide = l => l.side.toLowerCase() === opener.side.toLowerCase();
    const closers = legs.filter(l => !sameSide(l));
    if (!closers.length) { openPositions++; return; }
    const openMs = opener.time, closeMs = closers[closers.length - 1].time;
    const tradingDay = new Date(openMs - DAY_START_HOUR * 3600000);
    const date = new Date(Date.UTC(tradingDay.getUTCFullYear(), tradingDay.getUTCMonth(), tradingDay.getUTCDate()));
    trades.push({
      symbol: opener.symbol, side: opener.side,
      qty: sum(legs.filter(sameSide).map(l => l.qty)),
      pnl: cents(sum(legs.map(l => l.profit + l.swap + l.commission))),
      commission: sum(legs.map(l => l.commission)), swap: sum(legs.map(l => l.swap)),
      openMs, closeMs, date, dateKey: dateKey(date), weekday: weekdayIndex(date),
    });
  });

  directTrades.forEach(t => {
    const tradingDay = new Date(t.openMs - DAY_START_HOUR * 3600000);
    const date = new Date(Date.UTC(tradingDay.getUTCFullYear(), tradingDay.getUTCMonth(), tradingDay.getUTCDate()));
    trades.push({ ...t, date, dateKey: dateKey(date), weekday: weekdayIndex(date) });
  });

  // 3. Number and order the trades; balance is the running all-in total.
  //    Trade format: "Trade No" is required, a unique positive whole number per trade, and is the trade's id and order.
  if (isTradeFormat) {
    const rowsOf = list => `row${list.length === 1 ? '' : 's'} ${list.slice(0, 5).join(', ')}${list.length > 5 ? ', …' : ''}`;
    const invalid = trades.filter(t => !t.tradeNo).map(t => t.row);
    if (invalid.length) throw new Error(`Trade No must be a positive whole number on every trade (check ${rowsOf(invalid)}).`);
    const seen = new Set(), dupes = [];
    trades.forEach(t => { if (seen.has(t.tradeNo)) dupes.push(t.tradeNo); seen.add(t.tradeNo); });
    if (dupes.length) throw new Error(`Trade No must be unique; duplicated: ${[...new Set(dupes)].slice(0, 5).map(n => '#' + n).join(', ')}.`);
    trades.forEach(t => { t.id = t.tradeNo; });
    trades.sort((a, b) => a.id - b.id);
    trades.forEach((t, i) => { t.seq = i + 1; });
  } else {
    trades.sort((a, b) => a.dateKey.localeCompare(b.dateKey) || a.closeMs - b.closeMs);
    trades.forEach((t, i) => { t.seq = t.id = i + 1; });
  }
  let balance = 0;
  trades.forEach(t => { balance = cents(balance + t.pnl); t.balance = balance; });

  // 4. Behaviour tags and notes from the timestamps.
  const closedBySymbol = new Map();
  trades.forEach(t => { if (!closedBySymbol.has(t.symbol)) closedBySymbol.set(t.symbol, []); closedBySymbol.get(t.symbol).push(t); });
  closedBySymbol.forEach(list => list.sort((a, b) => a.closeMs - b.closeMs)); // stable: ties keep trade order
  trades.forEach(t => {
    t.holdMin = (t.closeMs - t.openMs) / 60000;
    // Latest same-symbol trade that had already closed when this one opened.
    const prev = previousClosed(closedBySymbol.get(t.symbol), t);
    const gap = prev ? (t.openMs - prev.closeMs) / 60000 : null;
    const reentry = !!prev && prev.pnl < 0 && gap <= REENTRY_WINDOW_MIN;
    t.reentryGapMin = reentry ? gap : null;
    t.tags = {
      scalp: t.holdMin <= SCALP_MAX_MIN,
      reentry,
      sizeUp: reentry && t.qty > prev.qty,
      rollover: isoDay(t.openMs) !== t.dateKey || isoDay(t.closeMs) !== isoDay(t.openMs),
      longHold: t.holdMin >= LONG_HOLD_MIN,
    };
    const notes = [];
    if (t.tags.scalp) notes.push(`Scalp (${t.holdMin.toFixed(1)} min hold)`);
    if (reentry) notes.push(`Re-entry ${gap.toFixed(1)} min after Trade #${prev.id} loss`);
    if (t.tags.sizeUp) notes.push(`size up ${prev.qty} → ${t.qty}`);
    if (t.tags.rollover) notes.push(`Rollover (opened ${stampLabel(t.openMs)}, closed ${stampLabel(t.closeMs)})`);
    if (t.tags.longHold) notes.push(`Held ${t.holdMin.toFixed(1)} min`);
    t.notes = notes.join('; ');
    t.setup = classifySetup(t.tags);
  });

  const fullDay = d => `${dayLabel(d)} ${d.getUTCFullYear()}`;
  return {
    title: 'Trade History',
    period: trades.length ? `${fullDay(trades.reduce((m, t) => (t.dateKey < m.dateKey ? t : m)).date)} – ${fullDay(trades.reduce((m, t) => (t.dateKey > m.dateKey ? t : m)).date)}` : '',
    headline: {
      'Total commission paid': money(cents(sum(trades.map(t => t.commission)))),
      'Total swap paid': money(cents(sum(trades.map(t => t.swap)))),
    },
    trades,
    hours: hoursOf(trades),
    findings: [], recommendations: [], openPositions,
  };
}

/* ==========================================================================
   2. ANALYTICS  -  trades  ->  statistics
   ========================================================================== */

/** Core metrics for any subset of trades; reused for overall, per-day, per-symbol, per-setup... */
function summarize(trades) {
  const wins = trades.filter(t => t.pnl > 0);
  const losses = trades.filter(t => t.pnl < 0);
  const grossWin = sum(wins.map(t => t.pnl));
  const grossLoss = Math.abs(sum(losses.map(t => t.pnl)));
  const net = sum(trades.map(t => t.pnl));
  return {
    trades, n: trades.length, wins: wins.length, losses: losses.length,
    net, grossWin, grossLoss,
    winRate: trades.length ? wins.length / trades.length : NaN,
    avg: trades.length ? net / trades.length : NaN,
    avgWin: wins.length ? grossWin / wins.length : 0,
    avgLoss: losses.length ? grossLoss / losses.length : 0,
    profitFactor: grossLoss > 0 ? grossWin / grossLoss : (grossWin > 0 ? Infinity : NaN),
  };
}

/** Group trades by a key function, preserving first-seen order; each group is summarised. */
function groupBy(trades, keyFn) {
  const map = new Map();
  trades.forEach(t => {
    const k = keyFn(t);
    if (!map.has(k)) map.set(k, []);
    map.get(k).push(t);
  });
  return [...map.entries()].map(([key, list]) => ({ key, ...summarize(list) }));
}

/** Close hour on the UTC wall clock, matching how broker times are parsed. */
const closeHour = t => new Date(t.closeMs).getUTCHours();

/** Hour-of-day table (by close hour) for trades that carry timestamps. */
function hoursOf(trades) {
  return groupBy(trades, closeHour).map(g => ({ hour: g.key, trades: g.n, pnl: g.net }));
}

/**
 * Win/loss streaks. A breakeven trade (pnl = 0) ends the current streak.
 * Also derives P(win | previous trade was a win/loss) to expose tilt behaviour.
 */
function analyzeStreaks(trades) {
  const streaks = [];
  let cur = null;
  trades.forEach(t => {
    const type = t.pnl > 0 ? 'W' : t.pnl < 0 ? 'L' : 'B';
    if (type === 'B') { cur = null; return; }
    if (cur && cur.type === type) {
      cur.length++; cur.pnl += t.pnl; cur.endId = t.id;
    } else {
      cur = { type, length: 1, pnl: t.pnl, startId: t.id, endId: t.id };
      streaks.push(cur);
    }
  });
  const wins = streaks.filter(s => s.type === 'W');
  const losses = streaks.filter(s => s.type === 'L');
  const longest = list => list.reduce((best, s) => (!best || s.length > best.length ? s : best), null);

  let afterWin = { n: 0, wins: 0 }, afterLoss = { n: 0, wins: 0 };
  for (let i = 1; i < trades.length; i++) {
    const bucket = trades[i - 1].pnl > 0 ? afterWin : trades[i - 1].pnl < 0 ? afterLoss : null;
    if (!bucket) continue;
    bucket.n++;
    if (trades[i].pnl > 0) bucket.wins++;
  }
  const last = streaks[streaks.length - 1] || null;
  return {
    streaks,
    maxWin: longest(wins), maxLoss: longest(losses),
    avgWinLen: wins.length ? sum(wins.map(s => s.length)) / wins.length : 0,
    avgLossLen: losses.length ? sum(losses.map(s => s.length)) / losses.length : 0,
    current: last,
    pWinAfterWin: afterWin.n ? afterWin.wins / afterWin.n : NaN, nAfterWin: afterWin.n,
    pWinAfterLoss: afterLoss.n ? afterLoss.wins / afterLoss.n : NaN, nAfterLoss: afterLoss.n,
  };
}

/**
 * Master analysis. Equity curve starts at $0 and adds each trade's all-in P&L in order.
 * Drawdown = equity - running peak (peak includes the starting $0).
 */
function analyze(journal) {
  const trades = journal.trades;
  const overall = summarize(trades);

  // --- equity curve & drawdown ---
  const equity = [{ label: 'Start', value: 0, trade: null }];
  const peaks = [0];
  const drawdown = [0];
  let eq = 0, peak = 0, peakIdx = 0;
  let maxDD = { value: 0, peakValue: 0, troughValue: 0, fromId: null, toId: null };
  trades.forEach((t, i) => {
    eq += t.pnl;
    if (eq > peak) { peak = eq; peakIdx = i + 1; }
    const dd = eq - peak;
    equity.push({ label: `#${t.id}`, value: eq, trade: t });
    peaks.push(peak);
    drawdown.push(dd);
    if (dd < maxDD.value) {
      maxDD = { value: dd, peakValue: peak, troughValue: eq, fromId: peakIdx === 0 ? null : trades[peakIdx - 1].id, toId: t.id };
    }
  });

  // --- time buckets ---
  const days = groupBy(trades, t => t.dateKey).sort((a, b) => a.key.localeCompare(b.key));
  days.forEach(d => { d.date = d.trades[0].date; d.label = dayLabel(d.date); });
  // Ending account equity for each trading day = running total of daily net P&L.
  let runningEquity = 0;
  days.forEach(d => { runningEquity += d.net; d.equity = runningEquity; });

  const weeks = groupBy(trades, t => dateKey(weekStart(t.date))).sort((a, b) => a.key.localeCompare(b.key));
  weeks.forEach(w => {
    const start = weekStart(w.trades[0].date);
    const end = new Date(start.getTime() + 6 * 86400000);
    w.label = `${dayLabel(start)}–${dayLabel(end)}`;
  });

  const months = groupBy(trades, t => t.dateKey.slice(0, 7)).sort((a, b) => a.key.localeCompare(b.key));
  months.forEach(m => { const d = m.trades[0].date; m.label = `${MONTHS[d.getUTCMonth()]} ${d.getUTCFullYear()}`; });

  // --- weekday performance (Mon..Fri always shown; weekend only if traded) ---
  const byWeekdayMap = new Map(groupBy(trades, t => t.weekday).map(g => [g.key, g]));
  const lastWd = maxOf(trades.map(t => t.weekday), 4);
  const weekdays = [];
  for (let i = 0; i <= lastWd; i++) {
    weekdays.push({ label: WEEKDAYS[i], ...(byWeekdayMap.get(i) || summarize([])) });
  }

  // --- other breakdowns ---
  const bySymbol = groupBy(trades, t => t.symbol).sort((a, b) => b.net - a.net);
  const bySetup = groupBy(trades, t => t.setup).sort((a, b) => b.net - a.net);
  const bySide = groupBy(trades, t => t.side).sort((a, b) => b.net - a.net);

  // --- behaviour tags (multi-label) ---
  const tagDefs = [
    ['reentry', 'Re-entry after loss'], ['sizeUp', 'Size increase'], ['scalp', 'Scalp'],
    ['rollover', 'Overnight rollover'], ['longHold', `Long hold (${LONG_HOLD_MIN}+ min)`],
  ];
  const byTag = tagDefs.map(([k, label]) => ({ key: label, ...summarize(trades.filter(t => t.tags[k])) }));

  // --- risk / reward ---
  const payoff = overall.avgLoss > 0 ? overall.avgWin / overall.avgLoss : Infinity;
  const breakEvenWR = isFinite(payoff) ? 1 / (1 + payoff) : 0;
  const winRate = overall.winRate;
  const kelly = isFinite(payoff) && payoff > 0 ? winRate - (1 - winRate) / payoff : NaN;
  const rUnit = overall.avgLoss > 0 ? overall.avgLoss : (Math.abs(overall.avg) || 1);
  const rValues = trades.map(t => t.pnl / rUnit);

  // R histogram with 1R-wide bins.
  const rMin = Math.floor(minOf(rValues)), rMax = Math.floor(maxOf(rValues));
  const rBins = [];
  for (let lo = rMin; lo <= rMax; lo++) rBins.push({ lo, hi: lo + 1, count: 0 });
  rValues.forEach(r => { rBins[Math.floor(r) - rMin].count++; });

  const sorted = [...trades].sort((a, b) => b.pnl - a.pnl);
  const top2 = sum(sorted.slice(0, 2).map(t => t.pnl));
  const top4 = sum(sorted.slice(0, 4).map(t => t.pnl));

  // --- calendar: one entry per month that has trading days, built from `days` (day P&L is reused, not recomputed) ---
  const dayMap = new Map(days.map(d => [d.key, d]));
  const calMonths = [...new Set(days.map(d => d.key.slice(0, 7)))].map(key => {
    const year = +key.slice(0, 4), mi = +key.slice(5, 7) - 1;
    const monthStart = new Date(Date.UTC(year, mi, 1)), monthEnd = new Date(Date.UTC(year, mi + 1, 0));
    const monthDays = days.filter(d => d.key.startsWith(key));
    const calWeeks = [];
    for (let ws = weekStart(monthStart); ws <= monthEnd; ws = new Date(ws.getTime() + 7 * 86400000)) {
      const cells = Array.from({ length: 7 }, (_, i) => {
        const date = new Date(ws.getTime() + i * 86400000);
        const inMonth = date.getUTCMonth() === mi;
        return { date, inMonth, day: inMonth ? dayMap.get(dateKey(date)) || null : null };
      });
      // Week totals cover only the days that fall inside this month, so the weeks add up to the month total.
      const wd = cells.map(c => c.day).filter(Boolean);
      calWeeks.push({ cells, net: cents(sum(wd.map(d => d.net))), n: sum(wd.map(d => d.n)), tradingDays: wd.length });
    }
    const n = sum(monthDays.map(d => d.n)), wins = sum(monthDays.map(d => d.wins));
    return {
      key,
      label: monthStart.toLocaleString('en-US', { month: 'long', year: 'numeric', timeZone: 'UTC' }),
      weeks: calWeeks,
      net: cents(sum(monthDays.map(d => d.net))), n, wins, winRate: n ? wins / n : NaN, tradingDays: monthDays.length,
    };
  });
  const calendar = {
    months: calMonths,
    first: days[0].key, last: days[days.length - 1].key,
    hasWeekend: trades.some(t => t.weekday >= 5),
  };

  return {
    overall, trades, equity, peaks, drawdown, maxDD,
    days, weeks, months, weekdays, bySymbol, bySetup, bySide, byTag,
    streaks: analyzeStreaks(trades),
    payoff, breakEvenWR, kelly, rUnit, rValues, rBins,
    expectancyR: overall.avg / rUnit,
    best: sorted.slice(0, 5), worst: sorted.slice(-5).reverse(),
    netExTop2: overall.net - top2, netExTop4: overall.net - top4,
    recovery: maxDD.value < 0 ? overall.net / Math.abs(maxDD.value) : Infinity,
    calendar, hours: journal.hours,
    avgTradesPerDay: overall.n / days.length,
  };
}

/** Compare computed numbers with the journal's own headline table and report mismatches. */
function reconcile(journal, a) {
  const find = starts => {
    const k = Object.keys(journal.headline).find(key => key.toLowerCase().startsWith(starts));
    return k ? journal.headline[k] : null;
  };
  const checks = [];
  const tt = find('total trades');
  if (tt != null) checks.push({ name: 'Trade count', ok: parseInt(tt, 10) === a.overall.n, detail: `${tt} reported / ${a.overall.n} parsed` });
  const net = find('net p&l');
  if (net != null) checks.push({ name: 'Net P&L', ok: Math.abs(parseMoney(net) - a.overall.net) < 0.02, detail: `${money(parseMoney(net))} reported / ${money(a.overall.net)} computed` });
  const wl = find('wins');
  const m = wl && wl.match(/(\d+)\s*\/\s*(\d+)/);
  if (m) checks.push({ name: 'Wins / losses', ok: +m[1] === a.overall.wins && +m[2] === a.overall.losses, detail: `${m[1]}/${m[2]} reported / ${a.overall.wins}/${a.overall.losses} computed` });
  const last = a.trades[a.trades.length - 1];
  if (last && isFinite(last.balance)) checks.push({ name: 'Final balance', ok: Math.abs(last.balance - a.overall.net) < 0.02, detail: `${money(last.balance)} balance column / ${money(a.overall.net)} computed` });
  return {
    checks,
    ok: checks.length > 0 && checks.every(c => c.ok),
    costs: { commission: find('total commission'), swap: find('total swap') },
  };
}

/* ==========================================================================
   3. INSIGHTS  -  rule-based psychology read-out and recommendations
   Each rule inspects the statistics and, when it fires, emits an insight card
   (what happened) and optionally a recommendation (what to do about it).
   ========================================================================== */

function buildInsights(a) {
  const insights = [];
  const recs = [];
  const o = a.overall;
  const s = a.streaks;
  const insight = (level, title, text) => insights.push({ level, title, text });
  const rec = (priority, title, action, evidence) => recs.push({ priority, title, action, evidence });

  // Rule 1 - outlier dependence: is the profit just one or two lucky trades?
  if (o.net > 0 && a.netExTop2 <= 0) {
    insight('bad', 'Profit depends on outliers', `Without the two best trades the account is ${money(a.netExTop2)} instead of ${money(o.net)}. The edge is not yet proven.`);
    rec('High', 'Measure yourself ex-outliers', 'Track expectancy excluding the top 1–2 winners and treat it as the true baseline until typical trades are profitable.', `Net ex-top-2: ${money(a.netExTop2)}; ex-top-4: ${money(a.netExTop4)}.`);
  } else if (o.net > 0) {
    insight('good', 'Profit is broadly distributed', `Net remains ${money(a.netExTop2, true)} after removing the two best trades.`);
  }

  // Rule 2 - payoff vs. win rate (does the maths of the strategy work?)
  if (o.n && isFinite(a.payoff)) {
    if (o.winRate < a.breakEvenWR) {
      insight('bad', 'Win rate below break-even', `Payoff ${ratio(a.payoff)}:1 needs a ${pct(a.breakEvenWR)} win rate; actual is ${pct(o.winRate)}.`);
      rec('High', 'Raise payoff or selectivity', 'Either widen winners / tighten losers, or trade fewer, higher-quality setups.', `Required ${pct(a.breakEvenWR)}, actual ${pct(o.winRate)}.`);
    } else if (o.winRate < 0.5) {
      insight('good', 'Low win rate offset by payoff', `A ${pct(o.winRate)} win rate is profitable because wins average ${ratio(a.payoff)}x the average loss (break-even ${pct(a.breakEvenWR)}).`);
      rec('Medium', 'Protect the payoff ratio', 'Your edge is asymmetric. Do not cut winners early to "feel right" - write down and follow exit rules.', `Avg win ${money(o.avgWin)} vs avg loss ${money(-o.avgLoss)}.`);
    }
  }

  // Rule 3 - behaviour after a loss (tilt)
  if (s.nAfterLoss >= 5 && s.nAfterWin >= 3 && s.pWinAfterLoss < s.pWinAfterWin - 0.1) {
    insight('warn', 'Performance dips after a loss', `Win rate is ${pct(s.pWinAfterLoss, 0)} after a loss (n=${s.nAfterLoss}) vs ${pct(s.pWinAfterWin, 0)} after a win (n=${s.nAfterWin}) - a sign of emotional carry-over.`);
  } else if (s.nAfterLoss >= 5) {
    insight('info', 'Post-loss behaviour', `Win rate after a loss is ${pct(s.pWinAfterLoss, 0)} (n=${s.nAfterLoss}) vs ${pct(s.pWinAfterWin, 0)} after a win (n=${s.nAfterWin}).`);
  }

  // Rule 4 - trading on after 3 consecutive losses (no circuit breaker)
  // Losses taken as the 4th, 5th, ... trade of a losing streak are the ones a stop-rule would have avoided.
  let run = 0;
  const beyondThree = a.trades.filter(t => {
    run = t.pnl < 0 ? run + 1 : 0;
    return t.pnl < 0 && run > 3;
  });
  if (beyondThree.length) {
    const lost = sum(beyondThree.map(t => t.pnl));
    insight('bad', 'No circuit breaker after 3 losses', `${plural(beyondThree.length, 'loss', 'losses')} were taken after three straight losses, costing ${money(lost)}. Longest losing streak: ${s.maxLoss.length} trades (${money(s.maxLoss.pnl)}).`);
    rec('High', 'Hard stop after 3 consecutive losses', 'End the session after three losses in a row and never add size to recover.', `Trades #${beyondThree.map(t => t.id).join(', #')} extended losing streaks for ${money(lost)}.`);
  }

  // Rule 5 - quick re-entries after a loss (revenge trading)
  const re = a.byTag.find(t => t.key === 'Re-entry after loss');
  if (re && re.n >= 2) {
    insight(re.net < 0 ? 'bad' : 'warn', 'Quick re-entries after losses', `${plural(re.n, 'same-symbol re-entry')} right after a loss: ${re.wins} won, ${re.losses} lost, net ${money(re.net)}.`);
    if (re.net < 0) rec('High', 'Add a cooldown after each loss', 'Wait at least 15 minutes (or for the next distinct setup) before re-entering the same symbol.', `${re.losses} of ${re.n} quick re-entries lost; net ${money(re.net)}.`);
  }

  // Rule 6 - position-size inconsistency (size creep / tilt sizing)
  const sizing = a.bySymbol.map(g => {
    const qtys = g.trades.map(t => t.qty).filter(q => q > 0);
    const min = minOf(qtys), max = maxOf(qtys);
    return { symbol: g.key, min, max, big: summarize(g.trades.filter(t => t.qty === max)), ratio: max / min };
  }).filter(x => x.ratio >= 2);
  if (sizing.length) {
    const bigNet = sum(sizing.map(x => x.big.net));
    insight(bigNet < 0 ? 'warn' : 'info', 'Inconsistent position sizing', `Lot size varied 2x or more on ${sizing.map(x => `${x.symbol} (${x.min}→${x.max})`).join(', ')}. Largest-size trades on those symbols netted ${money(bigNet)}.`);
    if (bigNet < 0) rec('Medium', 'Fix one lot size per instrument', 'Set a fixed lot per symbol and block size increases after a loss.', `Largest-lot trades on ${sizing.map(x => x.symbol).join(', ')}: ${money(bigNet)}.`);
  }
  const su = a.byTag.find(t => t.key === 'Size increase');
  if (su && su.n && su.net < 0) {
    insight('warn', 'Sizing up after losses', `${plural(su.n, 'trade')} were explicitly sized up and netted ${money(su.net)}.`);
  }

  // Rule 7 - scalps
  const sc = a.byTag.find(t => t.key === 'Scalp');
  if (sc && sc.n >= 2 && sc.net < 0) {
    insight('warn', 'Scalps are a drag', `${plural(sc.n, 'scalp')} netted ${money(sc.net)} (${sc.wins} won).`);
    rec('Medium', 'Skip very short scalps', 'Avoid entries you expect to hold under ~5 minutes; they cost spread and attention and are not paying.', `${sc.n} scalps: ${money(sc.net)}.`);
  }

  // Rule 8 - overtrading
  const busy = a.days.filter(d => d.n > OVERTRADE_THRESHOLD);
  if (busy.length) {
    const b = summarize(busy.flatMap(d => d.trades));
    const calm = summarize(a.days.filter(d => d.n <= OVERTRADE_THRESHOLD).flatMap(d => d.trades));
    insight(b.net < 0 ? 'bad' : 'warn', 'Overtrading days', `${plural(busy.length, 'day')} had more than ${OVERTRADE_THRESHOLD} trades: ${b.n} trades, ${money(b.net)}, ${pct(b.winRate, 0)} win rate. Other days: ${money(calm.avg)} per trade.`);
    if (b.net < 0) rec('High', `Cap daily trades at ${OVERTRADE_THRESHOLD}`, 'Set a hard daily trade limit and stop when it is reached.', `High-activity days (${busy.map(d => d.label).join(', ')}) lost ${money(b.net)}.`);
  }

  // Rule 9 - time of day (uses journal Section 8, post-midnight window 00:00-05:59)
  if (a.hours.length) {
    const late = a.hours.filter(h => h.hour < 6);
    const lateN = sum(late.map(h => h.trades)), lateNet = sum(late.map(h => h.pnl));
    if (lateN && lateNet < 0) {
      insight('bad', 'Late-night trading leak', `${plural(lateN, 'trade')} closed between 00:00 and 05:59 for ${money(lateNet)}. Fatigue and thin liquidity hurt execution.`);
      rec('High', 'No new entries after your cut-off', 'Set a session end (e.g. 23:00) and avoid opening positions that will carry past midnight.', `Post-midnight closes: ${money(lateNet)} over ${lateN} trades.`);
    }
    const bestHr = [...a.hours].sort((x, y) => y.pnl - x.pnl)[0];
    if (bestHr && bestHr.pnl > 0) insight('info', 'Best hour', `${pad2(bestHr.hour)}:00 produced ${money(bestHr.pnl, true)} over ${plural(bestHr.trades, 'trade')}.`);
  }

  // Rule 10 - weekday & symbol drags
  const badDays = a.weekdays.filter(d => d.n >= 3 && d.net < 0).sort((x, y) => x.net - y.net);
  if (badDays.length) {
    const d = badDays[0];
    insight('warn', `${d.label} is the weakest weekday`, `${plural(d.n, 'trade')} for ${money(d.net)} at a ${pct(d.winRate, 0)} win rate.`);
    rec('Medium', `Trade smaller on ${d.label}`, 'Halve size or reduce the number of trades on your weakest weekday until it turns positive.', `${d.label}: ${money(d.net)} over ${d.n} trades.`);
  }
  const badSyms = a.bySymbol.filter(g => g.n >= 3 && g.net < 0 && g.winRate <= 0.25);
  if (badSyms.length) {
    const tot = sum(badSyms.map(g => g.net)), cnt = sum(badSyms.map(g => g.n)), w = sum(badSyms.map(g => g.wins));
    insight('bad', 'Instrument drag', `${badSyms.map(g => g.key).join(' + ')}: ${plural(cnt, 'trade')}, ${plural(w, 'win')}, net ${money(tot)}.`);
    rec('High', `Pause ${badSyms.map(g => g.key).join(' & ')}`, 'Trade them on demo or minimum size until the win rate recovers; focus capital on your best instrument.', `Combined ${money(tot)} over ${cnt} trades.`);
  }
  const bestSym = a.bySymbol.find(g => g.n >= 5 && g.net > 0);
  if (bestSym) insight('good', `${bestSym.key} is your best instrument`, `${money(bestSym.net, true)} over ${plural(bestSym.n, 'trade')} (${pct(bestSym.winRate, 0)} win rate).`);

  // Rule 11 - side bias
  const badSide = a.bySide.find(g => g.n >= 8 && g.net < 0);
  if (badSide) {
    insight('warn', `${badSide.key} side underperforms`, `${badSide.key} trades netted ${money(badSide.net)} at a ${pct(badSide.winRate, 0)} win rate over ${badSide.n} trades.`);
    rec('Medium', `Review ${badSide.key.toLowerCase()} setups`, `Require extra confirmation for ${badSide.key.toLowerCase()} entries until they show positive expectancy.`, `${badSide.key}: ${money(badSide.net)} over ${badSide.n} trades.`);
  }

  // Rule 12 - patience (hold time)
  const lh = a.byTag.find(t => t.key.startsWith('Long hold'));
  if (lh && lh.n >= 3 && lh.net > 0) {
    insight('good', 'Patience pays', `${plural(lh.n, 'trade')} held ${LONG_HOLD_MIN}+ minutes netted ${money(lh.net, true)} (${pct(lh.winRate, 0)} win rate).`);
    rec('Low', 'Keep letting winners run', 'Document the entry and exit rules behind your long holds so they can be repeated deliberately.', `Long holds: ${money(lh.net)} over ${lh.n} trades.`);
  }

  // Rule 13 - drawdown vs profit
  if (o.net > 0 && a.maxDD.value < 0 && Math.abs(a.maxDD.value) > 0.5 * o.net) {
    insight('warn', 'Drawdown is large relative to profit', `Max drawdown ${money(a.maxDD.value)} equals ${pct(Math.abs(a.maxDD.value) / o.net, 0)} of net profit (recovery factor ${ratio(a.recovery)}).`);
  }

  const order = { High: 0, Medium: 1, Low: 2 };
  recs.sort((x, y) => order[x.priority] - order[y.priority]);
  return { insights, recs };
}

/* ==========================================================================
   4. RENDERING - DOM helpers
   ========================================================================== */

const $ = id => document.getElementById(id);

function renderKPIs(a) {
  const o = a.overall, s = a.streaks;
  const bestTrade = a.best[0] && a.best[0].pnl > 0 ? a.best[0] : null;
  const worstTrade = a.worst[0] && a.worst[0].pnl < 0 ? a.worst[0] : null;
  const tradeRef = t => (t ? `#${t.id} ${t.symbol} · ${dayLabel(t.date)}` : 'No trades');
  const cards = [
    { label: 'Activity', value: `${o.n} trades`, cls: 'neutral', sub: `${plural(a.days.length, 'trading day')} · ${a.avgTradesPerDay.toFixed(1)} per day` },
    { label: 'Net P&L', value: money(o.net, true), cls: signClass(o.net), sub: `${money(o.grossWin)} won / ${money(-o.grossLoss)} lost` },
    { label: 'Win Rate', value: pct(o.winRate), cls: o.winRate >= a.breakEvenWR ? 'pos' : 'neg', sub: `${o.wins}W / ${o.losses}L of ${o.n} trades` },
    { label: 'Risk : Reward', value: `1 : ${ratio(a.payoff)}`, cls: 'neutral', sub: `Break-even win rate ${pct(a.breakEvenWR)}` },
    { label: 'Profit Factor', value: ratio(o.profitFactor), cls: o.profitFactor >= 1 ? 'pos' : 'neg', sub: 'Gross profit ÷ gross loss' },
    { label: 'Expectancy', value: money(o.avg, true), cls: signClass(o.avg), sub: `per trade · ${a.expectancyR >= 0 ? '+' : ''}${a.expectancyR.toFixed(2)}R` },
    { label: 'Max Drawdown', value: money(a.maxDD.value), cls: a.maxDD.value < 0 ? 'neg' : '', sub: `Recovery factor ${ratio(a.recovery)}` },
    { label: 'Streaks', value: `W${s.maxWin ? s.maxWin.length : 0} / L${s.maxLoss ? s.maxLoss.length : 0}`, cls: 'neutral', sub: 'Longest win / loss streak' },
    { label: 'Best Profit', value: bestTrade ? money(bestTrade.pnl, true) : '—', cls: bestTrade ? 'pos' : '', sub: tradeRef(bestTrade) },
    { label: 'Worst Loss', value: worstTrade ? money(worstTrade.pnl) : '—', cls: worstTrade ? 'neg' : '', sub: tradeRef(worstTrade) },
    { label: 'Average Profit', value: o.wins ? money(o.avgWin, true) : '—', cls: o.wins ? 'pos' : '', sub: `per winning trade · ${o.wins} wins` },
    { label: 'Average Loss', value: o.losses ? money(-o.avgLoss) : '—', cls: o.losses ? 'neg' : '', sub: `per losing trade · ${o.losses} losses` },
  ];
  $('kpiGrid').innerHTML = cards.map(c => `
    <div class="kpi ${c.cls}">
      <div class="kpi-label">${esc(c.label)}</div>
      <div class="kpi-value ${c.cls === 'neutral' ? '' : c.cls}">${esc(c.value)}</div>
      <div class="kpi-sub">${esc(c.sub)}</div>
    </div>`).join('');
}

/** Overall discipline: average total score of fully scored trades as a share of 25 (same figure as the Trade Log footer). */
function disciplineSummary(trades) {
  const scored = trades.filter(hasScore);
  if (!scored.length) return null;
  const avg = sum(scored.map(t => t.score)) / scored.length;
  const factors = SCORE_LABELS.map(([k, label]) => {
    const v = trades.map(t => (t.scores || {})[k]).filter(Number.isFinite);
    return { label, avg: v.length ? sum(v) / v.length : null };
  });
  return { avg, ratio: avg / SCORE_MAX_TOTAL, scored: scored.length, total: trades.length, factors };
}

const disciplineTier = ratio => (ratio >= 0.8 ? 'Excellent' : ratio >= 0.6 ? 'Good' : 'Needs work');

/* --------------------------------------------------------------------------
   Shared picker controls of the three score cards (Daily Discipline, Discipline, Outcome):
   a dropdown plus a strip of small coloured squares, one per item (a trading day or a trade).
   Items are { key, text, level, tip }, oldest first; level is a colour class (green / amber / red / empty).
   -------------------------------------------------------------------------- */
const PICK_STRIP_MAX = 30;
const cardPick = { discipline: 'all', outcome: 'all', daily: 'all' }; // 'all' or the key of the item picked in each card
const dayTitle = date => `${WEEKDAYS[weekdayIndex(date)]} ${dayLabel(date)} ${date.getUTCFullYear()}`;
const tradeTitle = t => `#${t.id} ${t.symbol} ${t.side}`;

/** The picked item of a card, or null for "all" (a stale pick, e.g. after a filter change, falls back to "all"). */
function pickedItem(name, items) {
  const found = items.find(x => x.key === cardPick[name]) || null;
  if (!found) cardPick[name] = 'all';
  return found;
}

function pickerHtml({ id, noun, aria, all, items, sel }) {
  const opts = [`<option value="all"${sel ? '' : ' selected'}>${esc(all)} (${items.length})</option>`]
    .concat([...items].reverse().map(x => `<option value="${esc(x.key)}"${sel && sel.key === x.key ? ' selected' : ''}>${esc(x.text)}</option>`)).join('');
  return `<label class="dd-pick kpi-sub">${esc(noun)} <select id="${id}" aria-label="${esc(aria)}">${opts}</select></label>`;
}

function stripHtml({ noun, aria, items, sel }) {
  const shown = items.slice(-PICK_STRIP_MAX);
  const squares = shown.map(x => {
    const on = !!sel && sel.key === x.key;
    return `<button type="button" class="dd-day ${x.level}${on ? ' on' : ''}" data-pick="${esc(x.key)}" aria-pressed="${on}" title="${esc(x.tip)}" aria-label="${esc(x.tip)}"></button>`;
  }).join('');
  return `<div class="dd-history"><span class="kpi-label">Last ${esc(plural(shown.length, noun))}</span><div class="dd-strip" role="group" aria-label="${esc(aria)}">${squares}</div></div>`;
}

/** Re-render a card when its dropdown changes or a square is clicked (clicking the picked square clears the pick). */
function wireCardPick(cardId, selectId, name, render) {
  const el = $(cardId);
  const pick = (value, focusSel) => {
    cardPick[name] = value;
    if (currentAnalytics) render(currentAnalytics);
    const f = el.querySelector(focusSel);
    if (f) f.focus();
  };
  el.addEventListener('change', e => { if (e.target.id === selectId) pick(e.target.value, `#${selectId}`); });
  el.addEventListener('click', e => {
    const b = e.target.closest('button[data-pick]');
    if (!b) return;
    const key = b.dataset.pick;
    pick(cardPick[name] === key ? 'all' : key, `button[data-pick="${CSS.escape(key)}"]`);
  });
}

/** Per-trade view of the Discipline Score: same shape as disciplineSummary, built from one trade's own ratings. */
function tradeDisciplineView(t) {
  const sc = t.scores || {};
  const avg = hasScore(t) ? t.score : null;
  return {
    avg, ratio: avg === null ? null : avg / SCORE_MAX_TOTAL,
    factors: SCORE_LABELS.map(([k, label]) => ({ label, avg: Number.isFinite(sc[k]) ? sc[k] : null })),
  };
}

function disciplineItems(trades) {
  return trades.map(t => {
    const v = tradeDisciplineView(t);
    return {
      key: String(t.id), trade: t,
      text: `#${t.id} ${t.symbol} · ${v.avg === null ? 'not scored' : `${v.avg}/25`}`,
      level: v.avg === null ? 'empty' : scoreLevel(v.avg) || 'green',
      tip: `${tradeTitle(t)} · ${dayTitle(t.date)}: ${v.avg === null ? 'not fully scored' : `${v.avg} / ${SCORE_MAX_TOTAL} (${pct(v.ratio)})`}`,
    };
  });
}

function renderDiscipline(a) {
  const el = $('disciplineCard');
  const d = disciplineSummary(a.trades);
  el.hidden = !d;
  if (!d) { el.innerHTML = ''; return; }
  const items = disciplineItems(a.trades);
  const sel = pickedItem('discipline', items);
  const v = sel ? tradeDisciplineView(sel.trade) : d;
  const unscored = v.avg === null;
  const level = unscored ? 'empty' : scoreLevel(v.avg) || 'green';
  const text = unscored ? DASH : pct(v.ratio);
  const tier = unscored ? 'Not scored' : disciplineTier(v.ratio);
  const rated = v.factors.filter(f => f.avg !== null);
  const weakest = rated.length > 1 && Math.min(...rated.map(f => f.avg)) < Math.max(...rated.map(f => f.avg)) ? rated.reduce((m, f) => (f.avg < m.avg ? f : m)) : null;
  const bars = v.factors.map(f => {
    const w = f.avg === null ? 0 : (f.avg / 5) * 100;
    const lvl = f.avg !== null && f.avg < 3 ? 'red' : 'green';
    return `<li class="disc-factor" role="listitem"><span class="disc-name">${esc(f.label.replace(/ Score$/, ''))}</span>`
      + `<span class="disc-bar" role="img" aria-label="${esc(f.label)}: ${f.avg === null ? 'no data' : `${f.avg.toFixed(1)} out of 5`}"><span class="disc-fill ${lvl}" style="width:${w.toFixed(1)}%"></span></span>`
      + `<span class="disc-num">${f.avg === null ? DASH : f.avg.toFixed(1)}<small>/5</small></span></li>`;
  }).join('');
  const perfect = a.trades.filter(t => hasScore(t) && t.score === SCORE_MAX_TOTAL).length; // every rating is 5/5
  const sub = `${perfect} out of ${d.scored} ${d.scored === 1 ? 'trade' : 'trades'} followed all rules`;
  const lines = sel
    ? `<div class="kpi-sub">${esc(tradeTitle(sel.trade))} · ${esc(dayTitle(sel.trade.date))}</div><div class="kpi-sub">${unscored ? `${rated.length} of 5 ratings filled in` : 'Trade score'}</div>`
    : `<div class="kpi-sub">${esc(sub)}</div>`;
  el.innerHTML = `
    <div class="disc-main">
      <div class="disc-ring ${level}" role="img" aria-label="Discipline Score ${text}, ${tier}">
        <svg viewBox="0 0 120 120" aria-hidden="true" focusable="false">
          <circle class="disc-track" cx="60" cy="60" r="52" pathLength="100"></circle>
          <circle class="disc-arc" cx="60" cy="60" r="52" pathLength="100" stroke-dasharray="${unscored ? '0' : Math.min(100, v.ratio * 100).toFixed(2)} 100"></circle>
        </svg>
        <div class="disc-center"><strong>${esc(text)}</strong><span>${unscored ? 'not scored' : `${v.avg.toFixed(1)} / ${SCORE_MAX_TOTAL}`}</span></div>
      </div>
      <div class="disc-info">
        <div class="kpi-label">Discipline Score</div>
        <span class="disc-badge ${level}">${esc(tier)}</span>
        ${lines}
        ${weakest ? `<div class="kpi-sub">Weakest area: <strong>${esc(weakest.label.replace(/ Score$/, ''))}</strong> (${weakest.avg.toFixed(1)}/5)</div>` : ''}
        ${pickerHtml({ id: 'discPick', noun: 'Trade', aria: 'Show Discipline Score for', all: 'All trades', items, sel })}
      </div>
    </div>
    <div class="dd-right">
      <ul class="disc-factors" role="list" aria-label="Discipline score by component">${bars}</ul>
      ${stripHtml({ noun: 'trade', aria: 'Discipline scores by trade', items, sel })}
    </div>`;
}

/** Trade selection quality: Outcome 1 = valid trade (should be taken), 0 = invalid. Unrated trades are left out of the share. */
function outcomeSummary(trades) {
  const valid = trades.filter(t => t.outcome === 1).length;
  const invalid = trades.filter(t => t.outcome === 0).length;
  const rated = valid + invalid;
  if (!rated) return null;
  return { valid, invalid, rated, total: trades.length, accuracy: valid / rated };
}

/** Per-trade view of the Outcome card: same shape as outcomeSummary, for one trade (accuracy is NaN when unrated). */
function tradeOutcomeView(t) {
  const valid = t.outcome === 1 ? 1 : 0, invalid = t.outcome === 0 ? 1 : 0, rated = valid + invalid;
  return { valid, invalid, rated, total: 1, accuracy: rated ? valid : NaN };
}

function outcomeItems(trades) {
  return trades.map(t => {
    const word = t.outcome === 1 ? 'Valid' : t.outcome === 0 ? 'Invalid' : 'Not rated';
    return {
      key: String(t.id), trade: t, text: `#${t.id} ${t.symbol} · ${word}`,
      level: t.outcome === 1 ? 'green' : t.outcome === 0 ? 'red' : 'empty',
      tip: `${tradeTitle(t)} · ${dayTitle(t.date)}: ${word}`,
    };
  });
}

function renderOutcomeCard(a) {
  const el = $('outcomeCard');
  const total = outcomeSummary(a.trades);
  el.hidden = !total;
  if (!total) { el.innerHTML = ''; return; }
  const items = outcomeItems(a.trades);
  const sel = pickedItem('outcome', items);
  const d = sel ? tradeOutcomeView(sel.trade) : total;
  const unrated = !d.rated;
  const acc = unrated ? 0 : d.accuracy;
  const level = unrated ? 'empty' : d.accuracy >= 0.6 ? 'green' : 'red';
  const text = unrated ? DASH : pct(d.accuracy);
  const tier = sel ? (unrated ? 'Not rated' : d.valid ? 'Valid trade' : 'Invalid trade') : disciplineTier(d.accuracy);
  const sub = `${total.valid} out of ${total.rated} ${total.rated === 1 ? 'trade was' : 'trades were'} valid`;
  const share = n => pct(n / d.rated);
  const tile = (cls, icon, label, n, note) => `
      <div class="oc-tile ${cls}">
        <div class="oc-tile-head">${icon}<span class="kpi-label">${label}</span></div>
        <div class="oc-count">${n}<small>${share(n)}</small></div>
        <div class="kpi-sub">${note}</div>
      </div>`;
  const lines = sel
    ? `<div class="kpi-sub">${esc(tradeTitle(sel.trade))} · ${esc(dayTitle(sel.trade.date))}</div>`
    : `<div class="kpi-sub">${esc(sub)}</div>`;
  el.innerHTML = `
    <div class="disc-main">
      <div class="disc-ring oc-ring" role="img" aria-label="Trade selection accuracy ${text}: ${d.valid} valid and ${d.invalid} invalid trades">
        <svg viewBox="0 0 120 120" aria-hidden="true" focusable="false">
          <circle class="oc-invalid-arc" cx="60" cy="60" r="52" pathLength="100" style="stroke:${d.invalid ? 'var(--red)' : 'var(--border)'}"></circle>
          <circle class="oc-valid-arc" cx="60" cy="60" r="52" pathLength="100" stroke-dasharray="${(acc * 100).toFixed(2)} 100"></circle>
        </svg>
        <div class="disc-center"><strong>${esc(text)}</strong><span>${unrated ? 'not rated' : `${d.valid} / ${d.rated}`}</span></div>
      </div>
      <div class="disc-info">
        <div class="kpi-label">Outcome · Trade Selection</div>
        <span class="disc-badge ${level}">${esc(tier)}</span>
        ${lines}
        <div class="kpi-sub">Measures trade selection, not profit</div>
        ${pickerHtml({ id: 'ocPick', noun: 'Trade', aria: 'Show Outcome for', all: 'All trades', items, sel })}
      </div>
    </div>
    <div class="oc-right">
      <div class="oc-tiles">
        ${tile('valid', OUTCOME_YES, 'Valid trades', d.valid, 'Outcome 1 · should be taken')}
        ${tile('invalid', OUTCOME_NO, 'Invalid trades', d.invalid, 'Outcome 0 · should be avoided')}
      </div>
      <div class="oc-split" role="img" aria-label="${d.valid} valid and ${d.invalid} invalid of ${d.rated} rated trades">
        <span class="oc-seg valid" style="width:${(acc * 100).toFixed(2)}%"></span><span class="oc-seg invalid" style="width:${unrated ? 0 : ((1 - acc) * 100).toFixed(2)}%"></span>
      </div>
      ${stripHtml({ noun: 'trade', aria: 'Outcomes by trade', items, sel })}
    </div>`;
}

/* --------------------------------------------------------------------------
   Daily Discipline Score - judges each trading day against day-level rules.
   Separate from the per-trade Discipline Score and Outcome above: it only reads trades grouped by day.
   Every rule is worth one point; the day's score is earned points / number of rules.
   -------------------------------------------------------------------------- */

/** Thresholds, hardcoded for now. Rules read them from here so they can later come from user settings. */
const DAILY_DISCIPLINE_CONFIG = Object.freeze({ maxTradesPerDay: 5, maxDailyRisk: 50, maxConsecutiveLosses: 3 });

/** Daily risk = the day's net loss (net P&L below zero, else 0), matching the Calendar and Trade Log. Swap this to change the definition. */
const dailyRiskOf = trades => Math.max(0, -cents(sum(trades.map(t => t.pnl))));

/**
 * Daily loss limit: once N losses in a row (by close time; a win or breakeven resets the run) have closed,
 * any trade opened afterwards breaks the rule. Returns { reached, after } where `after` counts those trades.
 */
function tradesAfterLossLimit(trades, maxLosses) {
  const byClose = [...trades].sort((a, b) => a.closeMs - b.closeMs || a.id - b.id);
  let run = [];
  for (const t of byClose) {
    run = t.pnl < 0 ? [...run, t] : [];
    if (run.length >= maxLosses) {
      const streak = new Set(run);
      return { reached: true, after: trades.filter(x => !streak.has(x) && x.openMs >= t.closeMs).length };
    }
  }
  return { reached: false, after: 0 };
}

const DAILY_RULES = [
  {
    key: 'maxTrades', label: 'Max trades per day',
    limit: cfg => `max ${plural(cfg.maxTradesPerDay, 'trade')}`,
    evaluate: (trades, cfg) => ({ pass: trades.length <= cfg.maxTradesPerDay, detail: `${plural(trades.length, 'trade')} taken` }),
  },
  {
    key: 'maxRisk', label: 'Max daily risk',
    limit: cfg => `max ${money(cfg.maxDailyRisk)}`,
    evaluate: (trades, cfg) => {
      const net = cents(sum(trades.map(t => t.pnl)));
      return {
        pass: dailyRiskOf(trades) <= cfg.maxDailyRisk,
        detail: `${money(Math.abs(net))} ${net < 0 ? 'loss' : 'profit'}`,
        limit: `Max daily risk: $${+cfg.maxDailyRisk}`, // overrides the short limit text in the single-day view
      };
    },
  },
  {
    key: 'lossLimit', label: 'Daily loss limit',
    limit: cfg => `stop after ${plural(cfg.maxConsecutiveLosses, 'straight loss', 'straight losses')}`,
    evaluate: (trades, cfg) => {
      const r = tradesAfterLossLimit(trades, cfg.maxConsecutiveLosses);
      const n = cfg.maxConsecutiveLosses;
      if (!r.reached) return { pass: true, detail: `${n} straight losses not reached` };
      return r.after ? { pass: false, detail: `${plural(r.after, 'trade')} after ${n} straight losses` } : { pass: true, detail: `Stopped after ${n} straight losses` };
    },
  },
];

const dailyTier = ratio => (ratio >= 0.8 ? { label: 'Excellent', level: 'green' } : ratio >= 0.6 ? { label: 'Good', level: 'amber' } : { label: 'Needs Improvement', level: 'red' });
const dailyPct = ratio => `${+(ratio * 100).toFixed(2)}%`; // 66.67%, 100%, 0%

/** Score one trading day (a group from analyze().days). */
function scoreTradingDay(day, cfg = DAILY_DISCIPLINE_CONFIG) {
  const rules = DAILY_RULES.map(r => ({ key: r.key, label: r.label, limit: r.limit(cfg), ...r.evaluate(day.trades, cfg) }));
  const earned = rules.filter(r => r.pass).length;
  const ratio = earned / rules.length;
  return { key: day.key, date: day.date, n: day.trades.length, rules, earned, total: rules.length, ratio, tier: dailyTier(ratio) };
}

/** Score every trading day and roll the results up: total points, plus how often each rule was kept. */
function dailyDisciplineSummary(days, cfg = DAILY_DISCIPLINE_CONFIG) {
  if (!days.length) return null;
  const scored = days.map(d => scoreTradingDay(d, cfg));
  const earned = sum(scored.map(d => d.earned)), total = sum(scored.map(d => d.total));
  const rules = DAILY_RULES.map((r, i) => {
    const passed = scored.filter(d => d.rules[i].pass).length;
    return { key: r.key, label: r.label, limit: r.limit(cfg), passed, failed: scored.length - passed, rate: passed / scored.length };
  });
  return { days: scored, earned, total, ratio: earned / total, tier: dailyTier(earned / total), rules };
}

const dayTierText = x => `${dayTitle(x.date)}: ${dailyPct(x.ratio)} (${x.earned}/${x.total} points)`;

function renderDailyDiscipline(a) {
  const el = $('dailyDisciplineCard');
  const d = dailyDisciplineSummary(a.days);
  el.hidden = !d;
  if (!d) { el.innerHTML = ''; return; }
  const items = d.days.map(x => ({ key: x.key, day: x, text: `${dayTitle(x.date)} · ${dailyPct(x.ratio)}`, level: x.tier.level, tip: dayTierText(x) }));
  const sel = pickedItem('daily', items);
  const day = sel ? sel.day : null;
  const view = day || d;
  const { level, label } = view.tier;
  const text = dailyPct(view.ratio);
  const pts = `${view.earned} / ${view.total}`;
  const heading = day ? `${dayTitle(day.date)} · ${plural(day.n, 'trade')}` : `Average of ${plural(d.days.length, 'trading day')}`;

  const rows = (day ? day.rules : d.rules).map(r => {
    if (day) {
      return `<li class="dd-rule ${r.pass ? 'pass' : 'fail'}"><span class="dd-status ${r.pass ? 'green' : 'red'}">${r.pass ? '✓ Pass' : '✗ Fail'}</span>`
        + `<span class="dd-rule-text"><strong>${esc(r.label)}</strong><small>${esc(r.detail)} • ${esc(r.limit)}</small></span>`
        + `<span class="dd-pts">${r.pass ? 1 : 0}<small>/1</small></span></li>`;
    }
    const lvl = dailyTier(r.rate).level;
    return `<li class="dd-rule ${lvl === 'red' ? 'fail' : 'pass'}"><span class="dd-status ${lvl}">${esc(dailyPct(r.rate))}</span>`
      + `<span class="dd-rule-text"><strong>${esc(r.label)}</strong><small>Passed ${r.passed} · failed ${plural(r.failed, 'day')} · ${esc(r.limit)}</small>`
      + `<span class="disc-bar" role="img" aria-label="${esc(r.label)}: passed ${r.passed} of ${r.passed + r.failed} days"><span class="disc-fill ${lvl}" style="width:${(r.rate * 100).toFixed(1)}%"></span></span></span>`
      + `<span class="dd-pts">${r.passed}<small>/${r.passed + r.failed}</small></span></li>`;
  }).join('');

  el.innerHTML = `
    <div class="disc-main">
      <div class="disc-ring ${level}" role="img" aria-label="Daily Discipline Score ${text}, ${label}: ${pts} points">
        <svg viewBox="0 0 120 120" aria-hidden="true" focusable="false">
          <circle class="disc-track" cx="60" cy="60" r="52" pathLength="100"></circle>
          <circle class="disc-arc" cx="60" cy="60" r="52" pathLength="100" stroke-dasharray="${Math.min(100, view.ratio * 100).toFixed(2)} 100"></circle>
        </svg>
        <div class="disc-center"><strong>${esc(text)}</strong><span>${pts} pts</span></div>
      </div>
      <div class="disc-info">
        <div class="kpi-label">Daily Discipline Score</div>
        <span class="disc-badge ${level}">${esc(label)}</span>
        <div class="kpi-sub">${esc(heading)}</div>
        <div class="kpi-sub">${view.earned} of ${view.total} points earned</div>
        ${day ? '' : `<div class="kpi-sub">${d.days.filter(x => x.earned === x.total).length} of ${plural(d.days.length, 'trading day')} followed all rules</div>`}
        ${pickerHtml({ id: 'ddDay', noun: 'Day', aria: 'Show Daily Discipline Score for', all: 'All days', items, sel })}
      </div>
    </div>
    <div class="dd-right">
      <ul class="dd-rules" role="list" aria-label="Daily discipline rules">${rows}</ul>
      ${stripHtml({ noun: 'trading day', aria: 'Daily scores by trading day', items, sel })}
    </div>`;
}

function statRows(rows) {
  return rows.map(([k, v, cls]) => `<div><span>${esc(k)}</span><span class="${cls || ''}">${esc(v)}</span></div>`).join('');
}

function renderRiskStats(a, recon) {
  const o = a.overall;
  const rows = [
    ['Average win', money(o.avgWin), 'pos'],
    ['Average loss', money(-o.avgLoss), 'neg'],
    ['Payoff ratio (avg win ÷ avg loss)', ratio(a.payoff)],
    ['Break-even win rate', pct(a.breakEvenWR)],
    ['Actual win rate', pct(o.winRate), o.winRate >= a.breakEvenWR ? 'pos' : 'neg'],
    ['Expectancy (R-multiple)', `${a.expectancyR >= 0 ? '+' : ''}${a.expectancyR.toFixed(2)}R`, signClass(a.expectancyR)],
    ['Kelly fraction', isFinite(a.kelly) ? pct(a.kelly) : '—', signClass(a.kelly)],
  ];
  if (recon.costs.commission) rows.push(['Commission paid', recon.costs.commission.replace(/\*/g, '')]);
  if (recon.costs.swap) rows.push(['Swap paid', recon.costs.swap.replace(/\*/g, '')]);
  // Only a journal .md carries its own headline numbers to check against; a CSV is the source itself.
  if (!filterCtx.hasTimes && recon.checks.length) {
    const bad = recon.checks.filter(c => !c.ok);
    rows.push(['Matches journal headline', bad.length ? bad.map(c => c.name).join(', ') + ' differ' : `Yes (${plural(recon.checks.length, 'check')})`, bad.length ? 'neg' : 'pos']);
  }
  $('rrStats').innerHTML = statRows(rows);
}

function renderStreakStats(a) {
  const s = a.streaks;
  const fmt = st => (st ? `${st.length} trades (#${st.startId}–#${st.endId}, ${money(st.pnl, true)})` : '—');
  const winsCount = s.streaks.filter(x => x.type === 'W').length;
  const lossCount = s.streaks.filter(x => x.type === 'L').length;
  $('streakStats').innerHTML = statRows([
    ['Longest win streak', fmt(s.maxWin), 'pos'],
    ['Longest loss streak', fmt(s.maxLoss), 'neg'],
    ['Win streaks / loss streaks', `${winsCount} / ${lossCount}`],
    ['Average win streak', `${s.avgWinLen.toFixed(1)} trades`],
    ['Average loss streak', `${s.avgLossLen.toFixed(1)} trades`],
    ['Current streak', s.current ? `${s.current.length}${s.current.type}` : '—', s.current && s.current.type === 'W' ? 'pos' : 'neg'],
    ['P(win) after a win', `${pct(s.pWinAfterWin, 0)} (n=${s.nAfterWin})`],
    ['P(win) after a loss', `${pct(s.pWinAfterLoss, 0)} (n=${s.nAfterLoss})`],
  ]);
  // One coloured chip per trade, so streaks are visible at a glance.
  $('streakStrip').innerHTML = a.trades.map(t => {
    const c = t.pnl > 0 ? 'w' : t.pnl < 0 ? 'l' : 'b';
    return `<span class="chip ${c}" title="#${t.id} ${esc(t.symbol)} ${esc(t.side)} ${money(t.pnl, true)}">${t.id}</span>`;
  }).join('');
}

/**
 * Daily summary tokens, e.g. { trades: "9T", wl: "1W/8L", pl: "$24.70P/-$133.71L", net: "-$109.01", equity: "-$109.01E" }.
 * Always 2 decimals; the loss figure is a positive magnitude behind the fixed "-$" prefix, as in the template.
 */
function dayMetricParts(d) {
  return {
    trades: `${d.n}T`,
    wl: `${d.wins}W/${d.losses}L`,
    pl: `${money(d.grossWin)}P/-${money(d.grossLoss)}L`,
    net: money(d.net),
    equity: `${money(d.equity)}E`,
  };
}

/** One-line form used for tooltips: "9T, 1W/8L, $24.70P/-$133.71L, -$109.01, -$109.01E" */
function formatDayMetrics(d) {
  return Object.values(dayMetricParts(d)).join(', ');
}

/**
 * Monthly P&L calendar built from CSS grid (no canvas needed): Mon-Sun day columns plus a Week summary column.
 * Cell shade: green/red by net P&L, stronger for larger |net P&L| within the displayed month.
 * Every trading day prints the full daily metrics (trades, W/L, gross P/L, net, equity); the same string stays
 * available as the tooltip, and clicking a day opens its trades below the grid.
 */
function renderCalendar(a) {
  const cal = a.calendar;
  let mi = cal.months.findIndex(m => m.key === calMonthKey);
  if (mi < 0) mi = cal.months.length - 1;
  const m = cal.months[mi];
  calMonthKey = m.key;
  if (calDayKey && !a.days.some(d => d.key === calDayKey && d.key.startsWith(m.key))) calDayKey = null;

  const cols = cal.hasWeekend ? 7 : 5;
  const rows = m.weeks.filter(w => w.cells.slice(0, cols).some(c => c.inMonth));
  const maxAbs = maxOf(rows.flatMap(w => w.cells.slice(0, cols).map(c => (c.day ? Math.abs(c.day.net) : 0))), 0);
  const firstKey = (rows.flatMap(w => w.cells.slice(0, cols)).find(c => c.day) || { day: { key: '' } }).day.key;
  const tabKey = calDayKey || firstKey;

  let html = WEEKDAYS.slice(0, cols).map(w => `<div class="cal-head">${w}</div>`).join('') + '<div class="cal-head cal-head-week">Week</div>';
  rows.forEach((w, r) => {
    w.cells.slice(0, cols).forEach((c, col) => {
      const num = c.date.getUTCDate();
      if (!c.inMonth) { html += `<div class="cal-day out" aria-hidden="true"><span class="cal-date">${num}</span></div>`; return; }
      const d = c.day;
      if (!d) { html += `<div class="cal-day empty"><span class="cal-date">${num}</span></div>`; return; }
      const net = cents(d.net);
      const tone = net > 0 ? 'win' : net < 0 ? 'loss' : 'flat';
      const alpha = (0.16 + 0.4 * (maxAbs ? Math.abs(net) / maxAbs : 0)).toFixed(2);
      const p = dayMetricParts(d);
      const tip = `${WEEKDAYS[d.trades[0].weekday]}, ${d.label}\n${formatDayMetrics(d)}`;
      const selected = d.key === calDayKey;
      html += `<button type="button" class="cal-day ${tone}${d.key === cal.last ? ' latest' : ''}${selected ? ' selected' : ''}" style="--a:${alpha}"`
        + ` data-key="${esc(d.key)}" data-row="${r}" data-col="${col}" tabindex="${d.key === tabKey ? 0 : -1}" aria-pressed="${selected}"`
        + ` title="${esc(tip)}" aria-label="${esc(tip.replace('\n', ': '))}">`
        + `<span class="cal-date">${num}</span>`
        + `<span class="cal-line cal-net">${esc(p.net)}</span>`
        + `<span class="cal-line cal-tw"><span>${esc(p.trades)}</span><span class="cal-wl"> · ${esc(p.wl)}</span></span>`
        + `<span class="cal-line cal-pl">${esc(p.pl)}</span>`
        + `<span class="cal-line cal-eq">${esc(p.equity)}</span></button>`;
    });
    const wk = `Week ${r + 1}`;
    html += w.n
      ? `<div class="cal-week" title="${esc(`${wk}: ${plural(w.n, 'trade')} over ${plural(w.tradingDays, 'trading day')}`)}">`
        + `<span class="cal-week-label">${wk}</span><span class="cal-week-net ${signClass(w.net)}">${esc(money(w.net))}</span>`
        + `<span class="cal-week-meta">${w.n}T · ${w.tradingDays}D</span></div>`
      : `<div class="cal-week empty"><span class="cal-week-label">${wk}</span></div>`;
  });

  const grid = $('calGrid');
  grid.style.setProperty('--cal-cols', cols);
  grid.innerHTML = html;
  $('calTitle').textContent = m.label;
  $('calSummary').innerHTML = [
    ['Monthly P&L', `<span class="${signClass(m.net)}">${esc(money(m.net))}</span>`],
    ['Trades', String(m.n)],
    ['Win rate', esc(pct(m.winRate, 0))],
    ['Trading days', String(m.tradingDays)],
  ].map(([k, v]) => `<div class="cal-stat"><dt>${esc(k)}</dt><dd>${v}</dd></div>`).join('');

  const active = document.activeElement;
  $('calPrev').disabled = mi === 0;
  $('calNext').disabled = mi === cal.months.length - 1;
  if (active && active.disabled) (active.id === 'calPrev' ? $('calNext') : $('calPrev')).focus();

  renderCalendarDetail(a);
  updateCalendarHint();
}

function updateCalendarHint() {
  const box = $('calScroll');
  $('calScrollHint').hidden = box.scrollWidth <= box.clientWidth + 1;
}

/** Trade Log columns shown for a day's trades, in Trade Log order. Score and the videos show a dash when the file has none. */
const CAL_TRADE_KEYS = ['id', 'symbol', 'side', 'qty', 'entryVideo', 'exitVideo', 'rr', 'pnl', 'score', 'outcome'];

/** Day detail below the grid: the five metrics plus that day's trades in the Trade Log's table, totalled to the day's net. */
function renderCalendarDetail(a) {
  const box = $('calDetail');
  const d = calDayKey && a.days.find(x => x.key === calDayKey);
  box.hidden = !d;
  box.classList.remove('has-pinned-tip'); // a re-render drops any pinned score tooltip
  if (!d) { box.innerHTML = ''; return; }
  const p = dayMetricParts(d);
  const cols = TRADE_COLUMNS.filter(c => CAL_TRADE_KEYS.includes(c.key));
  const st = { rUnit: a.rUnit };
  const title = `${WEEKDAYS[d.trades[0].weekday]}, ${d.label} ${d.date.getUTCFullYear()}`;
  const metrics = [['Trades', p.trades], ['Wins / losses', p.wl], ['Gross P / L', p.pl], ['Net P&L', p.net], ['Equity', p.equity]];
  box.innerHTML = `<div class="cal-detail-head">
      <h4>${esc(title)}</h4>
      <button type="button" class="btn ghost cal-btn" id="calDetailClose" aria-label="Close day detail">Close</button>
    </div>
    <dl class="cal-detail-metrics">${metrics.map(([k, v]) => `<div class="cal-stat"><dt>${esc(k)}</dt><dd>${esc(v)}</dd></div>`).join('')}</dl>
    <div class="table-wrap tradelog-scroll"><table class="tbl" aria-label="${esc(`Trades on ${title}`)}"><thead><tr>${tradeHeadHtml(cols, st, false)}</tr></thead>`
    + `<tbody>${d.trades.map(t => tradeRowHtml(t, cols, st)).join('')}</tbody>${tradeFooterHtml(d.trades, cols, st, 'Day totals')}</table></div>`;
}

function selectCalendarDay(key) {
  if (!currentAnalytics) return;
  calDayKey = key === calDayKey ? null : key;
  document.querySelectorAll('#calGrid .cal-day[data-key]').forEach(el => {
    const on = el.dataset.key === calDayKey;
    el.classList.toggle('selected', on);
    el.setAttribute('aria-pressed', String(on));
  });
  renderCalendarDetail(currentAnalytics);
  if (calDayKey) $('calDetail').scrollIntoView({ block: 'nearest' });
}

/** Move the displayed month by `delta` among the months that have trades; returns false at either end. */
function stepCalendarMonth(delta) {
  if (!currentAnalytics) return false;
  const months = currentAnalytics.calendar.months;
  const next = months.findIndex(m => m.key === calMonthKey) + delta;
  if (next < 0 || next >= months.length) return false;
  calMonthKey = months[next].key;
  calDayKey = null;
  renderCalendar(currentAnalytics);
  return true;
}

function focusCalendarCell(el) {
  if (!el) return;
  $('calGrid').querySelectorAll('button.cal-day').forEach(b => { b.tabIndex = b === el ? 0 : -1; });
  el.focus();
}

function bindCalendar() {
  const panel = $('calendarPanel');
  const focusFirstDay = () => focusCalendarCell($('calGrid').querySelector('button.cal-day'));
  panel.addEventListener('click', e => {
    const day = e.target.closest('button.cal-day');
    if (day) { selectCalendarDay(day.dataset.key); return; }
    const btn = e.target.closest('button');
    if (!btn || !currentAnalytics) return;
    if (btn.id === 'calPrev') stepCalendarMonth(-1);
    else if (btn.id === 'calNext') stepCalendarMonth(1);
    else if (btn.id === 'calLatest') {
      const months = currentAnalytics.calendar.months;
      calMonthKey = months[months.length - 1].key;
      calDayKey = null;
      renderCalendar(currentAnalytics);
    } else if (btn.id === 'calDetailClose') {
      const key = calDayKey;
      selectCalendarDay(key);
      focusCalendarCell($('calGrid').querySelector(`button.cal-day[data-key="${key}"]`));
    }
  });
  panel.addEventListener('keydown', e => {
    if (!currentAnalytics) return;
    if (e.key === 'PageUp' || e.key === 'PageDown') {
      e.preventDefault();
      if (stepCalendarMonth(e.key === 'PageUp' ? -1 : 1)) focusFirstDay();
      return;
    }
    if (e.key === 'Escape' && calDayKey && !$('calDetail').classList.contains('has-pinned-tip')) {
      const key = calDayKey;
      selectCalendarDay(key);
      focusCalendarCell($('calGrid').querySelector(`button.cal-day[data-key="${key}"]`));
      return;
    }
    const cell = e.target.closest('button.cal-day');
    const dir = { ArrowLeft: -1, ArrowRight: 1, ArrowUp: -1, ArrowDown: 1 }[e.key];
    if (!cell || !dir) return;
    e.preventDefault();
    const cells = [...$('calGrid').querySelectorAll('button.cal-day')];
    if (e.key === 'ArrowLeft' || e.key === 'ArrowRight') { focusCalendarCell(cells[cells.indexOf(cell) + dir]); return; }
    const sameCol = cells.filter(c => c.dataset.col === cell.dataset.col && (+c.dataset.row - +cell.dataset.row) * dir > 0);
    focusCalendarCell(dir > 0 ? sameCol[0] : sameCol[sameCol.length - 1]);
  });
}

function groupTable(rows, firstCol) {
  return `<table class="tbl"><thead><tr>
      <th>${esc(firstCol)}</th><th class="r">Trades</th><th class="r">Win %</th><th class="r">Net P&L</th><th class="r">Avg / trade</th><th class="r">PF</th>
    </tr></thead><tbody>${rows.map(g => `<tr>
      <td>${esc(g.key)}</td><td class="r">${g.n}</td><td class="r">${isFinite(g.winRate) ? pct(g.winRate, 0) : '—'}</td>
      <td class="r ${signClass(g.net)}">${money(g.net, true)}</td><td class="r ${signClass(g.avg)}">${money(g.avg, true)}</td>
      <td class="r">${ratio(g.profitFactor)}</td></tr>`).join('')}</tbody></table>`;
}

function tradeTable(list) {
  return `<table class="tbl"><thead><tr>
      <th>#</th><th>Date</th><th>Symbol</th><th>Side</th><th class="r">Qty</th><th class="r">P&L</th><th>Notes</th>
    </tr></thead><tbody>${list.map(t => `<tr>
      <td>${t.id}</td><td>${dayLabel(t.date)}</td><td>${esc(t.symbol)}</td><td>${esc(t.side)}</td><td class="r">${t.qty}</td>
      <td class="r ${signClass(t.pnl)}"><strong>${money(t.pnl, true)}</strong></td><td class="note">${esc(t.notes || '—')}</td></tr>`).join('')}</tbody></table>`;
}

const cardClass = (c, isRec) => (isRec ? ({ High: 'bad', Medium: 'warn', Low: 'good' }[c.priority]) : c.level === 'info' ? '' : c.level);

function cardHtml(c, isRec) {
  const tag = isRec ? `<span class="tag ${c.priority.toLowerCase()}">${c.priority}</span>` : '';
  return `<div class="card ${cardClass(c, isRec)}"><h3>${tag}${esc(c.title)}</h3><p>${esc(isRec ? c.action : c.text)}</p>${isRec ? `<p class="evidence">Evidence: ${esc(c.evidence)}</p>` : ''}</div>`;
}

/** Show or hide the panel containing element `id` and give it the grid span class `span`. */
function setPanel(id, visible, span) {
  const panel = $(id).closest('.panel');
  panel.hidden = !visible;
  panel.className = panel.className.replace(/\bspan-\d+\b/, span);
}

function renderInsights(a, journal) {
  const { insights, recs } = buildInsights(a);
  $('insightGrid').innerHTML = insights.length ? insights.map(i => cardHtml(i, false)).join('') : '<p class="muted">No notable behavioural patterns detected.</p>';
  $('recGrid').innerHTML = recs.length ? recs.map(r => cardHtml(r, true)).join('') : '<p class="muted">No recommendations triggered.</p>';
  $('tagTable').innerHTML = groupTable(a.byTag, 'Behaviour tag');
  const li = x => `<li>${x.title ? `<strong>${esc(x.title)}:</strong> ` : ''}${mdInline(x.body)}</li>`;
  $('journalFindings').innerHTML = journal.findings.map(li).join('');
  $('journalRecs').innerHTML = journal.recommendations.map(li).join('');
  // A CSV carries no written findings or recommendations: hide that block, and let a lone panel take the full row.
  const hasFindings = journal.findings.length > 0, hasRecs = journal.recommendations.length > 0;
  setPanel('journalFindings', hasFindings, hasRecs ? 'span-6' : 'span-12');
  setPanel('journalRecs', hasRecs, hasFindings ? 'span-6' : 'span-12');
  $('journalNotes').hidden = !hasFindings && !hasRecs;
}

/* ==========================================================================
   5. RENDERING - Charts (Chart.js)
   ========================================================================== */

const charts = {};

function chartsAvailable() { return typeof Chart !== 'undefined'; }

/** Create the chart on canvas `id`, or update it in place when one of the same type exists (keeps filter changes cheap). */
function drawChart(id, config) {
  if (!chartsAvailable()) return;
  const chart = charts[id];
  if (chart && chart.config.type === config.type) {
    chart.data = config.data;
    chart.options = config.options;
    chart.update('none');
    return;
  }
  if (chart) chart.destroy();
  charts[id] = new Chart($(id), config);
}

function readThemeColors() {
  const style = getComputedStyle(document.documentElement);
  Object.entries(THEME_VARS).forEach(([key, name]) => {
    const v = style.getPropertyValue(name).trim();
    if (v) C[key] = v;
  });
}

/** Global look: dark grid, muted text, TradingView-style tooltips. */
function applyChartDefaults() {
  if (!chartsAvailable()) return;
  Chart.defaults.color = C.text;
  Chart.defaults.font.family = '-apple-system, "Segoe UI", Roboto, Arial, sans-serif';
  Chart.defaults.borderColor = C.grid;
  Chart.defaults.plugins.tooltip.backgroundColor = C.bg;
  Chart.defaults.plugins.tooltip.borderColor = C.border;
  Chart.defaults.plugins.tooltip.borderWidth = 1;
  Chart.defaults.plugins.tooltip.padding = 10;
  Chart.defaults.plugins.legend.labels.usePointStyle = true;
}

const moneyAxis = (extra = {}) => ({ grid: { color: C.grid }, ticks: { callback: v => (v < 0 ? '-$' : '$') + Math.abs(v) }, ...extra });
// Equity and drawdown share an x-axis, so their y-axes get the same width to keep the plots lined up.
const alignedMoneyAxis = (extra = {}) => moneyAxis({ afterFit: scale => { scale.width = 64; }, ...extra });
const catAxis = (extra = {}) => ({ grid: { display: false }, ...extra });
const signColors = values => values.map(v => (v >= 0 ? C.green : C.red));
const baseOpts = (extra = {}) => ({ responsive: true, maintainAspectRatio: false, ...extra });

/**
 * Split a trade list into runs of consecutive trades that share a trading day.
 * `offset` shifts indices when the chart has leading non-trade points (equity curve's "Start").
 */
function dayRuns(trades, offset = 0) {
  const runs = [];
  trades.forEach((t, i) => {
    const last = runs[runs.length - 1];
    if (last && last.key === t.dateKey) last.end = i + offset;
    else runs.push({ key: t.dateKey, label: `${WEEKDAYS[t.weekday]}, ${dayLabel(t.date)}`, start: i + offset, end: i + offset });
  });
  if (offset && runs.length) runs[0].start = 0; // the leading "Start" point joins day 1
  return runs;
}

const DAY_BAND_COLORS = ['rgba(41,98,255,0.13)', 'rgba(160,170,190,0.07)'];

/**
 * Chart.js plugin: paints alternating background bands behind the category slots of each trading day.
 * Runs in beforeDraw so grid lines, bars and lines render on top. Config: options.plugins.dayBands.runs.
 */
const dayBandsPlugin = {
  id: 'dayBands',
  beforeDraw(chart, _args, opts) {
    const runs = opts && opts.runs;
    if (!runs || !runs.length || chart.data.labels.length < 2) return;
    const { ctx, chartArea: area, scales: { x } } = chart;
    // Category slot width = distance between neighbouring tick centres.
    const half = Math.abs(x.getPixelForValue(1) - x.getPixelForValue(0)) / 2;
    ctx.save();
    ctx.font = '600 10px -apple-system, "Segoe UI", Roboto, Arial, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    runs.forEach((run, i) => {
      const left = Math.max(area.left, x.getPixelForValue(run.start) - half);
      const right = Math.min(area.right, x.getPixelForValue(run.end) + half);
      ctx.fillStyle = DAY_BAND_COLORS[i % DAY_BAND_COLORS.length];
      ctx.fillRect(left, area.top, right - left, area.bottom - area.top);
      // Skip the day label when the band is too narrow to hold it.
      if (right - left >= ctx.measureText(run.label).width + 8) {
        ctx.fillStyle = 'rgba(154,164,178,0.85)';
        ctx.fillText(run.label, (left + right) / 2, area.top + 4);
      }
    });
    ctx.restore();
  },
};

/** Generic P&L bar chart used for daily / weekly / monthly (and the group breakdowns). */
function pnlBar(id, groups, { horizontal = false } = {}) {
  const values = groups.map(g => g.net);
  drawChart(id, {
    type: 'bar',
    data: {
      labels: groups.map(g => g.label || g.key),
      datasets: [{ label: 'Net P&L', data: values, backgroundColor: signColors(values), borderRadius: 4, maxBarThickness: 46 }],
    },
    options: baseOpts({
      indexAxis: horizontal ? 'y' : 'x',
      plugins: {
        legend: { display: false },
        tooltip: {
          callbacks: {
            label: ctx => `Net: ${money(ctx.parsed[horizontal ? 'x' : 'y'], true)}`,
            afterLabel: ctx => { const g = groups[ctx.dataIndex]; return `${plural(g.n, 'trade')} · win rate ${pct(g.winRate, 0)}`; },
          },
        },
      },
      scales: horizontal ? { x: moneyAxis(), y: catAxis() } : { x: catAxis(), y: moneyAxis() },
    }),
  });
}

/**
 * Equity curve in two flavours sharing the same tooltip and axes:
 *   line - segments coloured green/red by sign, area filled to the $0 origin
 *   bar  - one bar per trade showing cumulative equity, coloured by sign
 * The dashed line is the running equity peak in both modes.
 */
function renderEquityChart(a, type) {
  const values = a.equity.map(p => p.value);
  const equityDataset = type === 'bar'
    ? { type: 'bar', label: 'Equity', data: values, backgroundColor: signColors(values), borderRadius: 2, maxBarThickness: 28, order: 2 }
    : {
      type: 'line', label: 'Equity', data: values, borderWidth: 2.2, tension: 0.15,
      pointRadius: 2.5, pointHoverRadius: 6,
      pointBackgroundColor: signColors(values),
      segment: { borderColor: ctx => (ctx.p1.parsed.y >= 0 ? C.green : C.red) },
      fill: { target: 'origin', above: C.greenFill, below: C.redFill },
    };
  drawChart('equityChart', {
    type: 'bar',
    plugins: [dayBandsPlugin],
    data: {
      labels: a.equity.map(p => p.label),
      datasets: [
        equityDataset,
        { type: 'line', label: 'Running peak', data: a.peaks, borderColor: C.grey, borderDash: [5, 4], borderWidth: 1, pointRadius: 0, fill: false, stepped: true, order: 1 },
      ],
    },
    options: baseOpts({
      interaction: { mode: 'index', intersect: false },
      plugins: {
        legend: { position: 'top', align: 'end' },
        dayBands: { runs: dayRuns(a.trades, 1) },
        tooltip: {
          callbacks: {
            title: items => { const t = a.equity[items[0].dataIndex].trade; return t ? `Trade #${t.id} · ${t.symbol} ${t.side} ${t.qty} · ${dayLabel(t.date)}` : 'Start'; },
            label: ctx => `${ctx.dataset.label}: ${money(ctx.parsed.y, true)}`,
            afterBody: items => { const t = a.equity[items[0].dataIndex].trade; return t ? [`Trade P&L: ${money(t.pnl, true)}`, t.notes ? `Note: ${t.notes}` : ''] : []; },
          },
        },
      },
      scales: { x: catAxis({ ticks: { maxRotation: 0, autoSkip: true, maxTicksLimit: 20 } }), y: alignedMoneyAxis() },
    }),
  });
}

/**
 * Per-trade P&L curve (not cumulative), same line/bar options as the equity curve.
 * The dashed line is the average P&L per trade (expectancy).
 */
function renderPnlCurveChart(a, type) {
  const trades = a.trades;
  const values = trades.map(t => t.pnl);
  const pnlDataset = type === 'bar'
    ? { type: 'bar', label: 'Trade P&L', data: values, backgroundColor: signColors(values), borderRadius: 2, maxBarThickness: 28, order: 2 }
    : {
      type: 'line', label: 'Trade P&L', data: values, borderWidth: 2.2, tension: 0.15,
      pointRadius: 2.5, pointHoverRadius: 6,
      pointBackgroundColor: signColors(values),
      segment: { borderColor: ctx => (ctx.p1.parsed.y >= 0 ? C.green : C.red) },
      fill: { target: 'origin', above: C.greenFill, below: C.redFill },
    };
  drawChart('pnlCurveChart', {
    type: 'bar',
    plugins: [dayBandsPlugin],
    data: {
      labels: trades.map(t => `#${t.id}`),
      datasets: [
        pnlDataset,
        { type: 'line', label: 'Avg per trade', hidden: true, data: trades.map(() => a.overall.avg), borderColor: C.amber, borderDash: [5, 4], borderWidth: 1.2, pointRadius: 0, fill: false, order: 1 },
      ],
    },
    options: baseOpts({
      interaction: { mode: 'index', intersect: false },
      plugins: {
        legend: { position: 'top', align: 'end' },
        dayBands: { runs: dayRuns(trades) },
        tooltip: {
          callbacks: {
            title: items => { const t = trades[items[0].dataIndex]; return `Trade #${t.id} · ${t.symbol} ${t.side} ${t.qty} · ${dayLabel(t.date)}`; },
            label: ctx => `${ctx.dataset.label}: ${money(ctx.parsed.y, true)}`,
            afterBody: items => {
              const i = items[0].dataIndex; // equity[0] is the "Start" point, so trade i maps to equity[i + 1]
              const lines = [`Equity: ${money(a.equity[i + 1].value, true)}`];
              if (trades[i].notes) lines.push(`Note: ${trades[i].notes}`);
              return lines;
            },
          },
        },
      },
      scales: { x: catAxis({ ticks: { maxRotation: 0, autoSkip: true, maxTicksLimit: 20 } }), y: moneyAxis() },
    }),
  });
}

function renderCharts(a) {
  applyChartDefaults();
  renderEquityChart(a, equityType);
  renderPnlCurveChart(a, pnlType);
  renderDrawdownChart(a);
  renderPeriodChart(a, periodType);
  renderOutcomeChart(a);
  renderRChart(a);
  renderRiskRewardChart(a);
  renderStreakChart(a);
  renderWeekdayChart(a);
  renderHourChart(a);
  renderBreakdownCharts(a);
  labelCharts(a);
}

/** Screen-reader summary per canvas; the numbers come from the same analytics the chart draws. */
function labelCharts(a) {
  const o = a.overall, last = a.equity[a.equity.length - 1].value;
  const labels = {
    equityChart: `Equity curve over ${plural(o.n, 'trade')}, ending at ${money(last, true)}`,
    drawdownChart: `Drawdown chart, maximum drawdown ${money(a.maxDD.value)}`,
    pnlCurveChart: `P&L per trade, ${plural(o.wins, 'win')} and ${plural(o.losses, 'loss', 'losses')}, average ${money(o.avg, true)}`,
    periodChart: `Net P&L by ${periodType} period, ${plural(PERIODS[periodType](a).length, 'period')}`,
    outcomeChart: `Outcome mix: ${o.wins} wins, ${o.losses} losses, ${o.n - o.wins - o.losses} breakeven`,
    rChart: `R-multiple distribution, expectancy ${a.expectancyR.toFixed(2)}R`,
    rrChart: `Average win ${money(o.avgWin)}, average loss ${money(-o.avgLoss)}`,
    streakChart: `Streak timeline, longest win streak ${a.streaks.maxWin ? a.streaks.maxWin.length : 0}, longest loss streak ${a.streaks.maxLoss ? a.streaks.maxLoss.length : 0}`,
    weekdayChart: `Net P&L and win rate by weekday: ${a.weekdays.map(d => `${d.label} ${money(d.net, true)}`).join(', ')}`,
    hourChart: `Net P&L and trade count by close hour, ${plural(a.hours.length, 'hour')} with trades`,
    symbolChart: `Net P&L by instrument: ${a.bySymbol.map(g => `${g.key} ${money(g.net, true)}`).join(', ')}`,
    setupChart: `Net P&L by setup: ${a.bySetup.map(g => `${g.key} ${money(g.net, true)}`).join(', ')}`,
  };
  Object.entries(labels).forEach(([id, text]) => $(id).setAttribute('aria-label', text));
}

function renderDrawdownChart(a) {
  drawChart('drawdownChart', {
    type: 'line',
    data: {
      labels: a.equity.map(p => p.label),
      datasets: [{ label: 'Drawdown', data: a.drawdown, borderColor: C.red, backgroundColor: C.redFill, borderWidth: 1.8, pointRadius: 0, pointHoverRadius: 4, fill: 'origin', tension: 0.1 }],
    },
    options: baseOpts({
      interaction: { mode: 'index', intersect: false },
      plugins: { legend: { display: false }, tooltip: { callbacks: { label: ctx => `Drawdown: ${money(ctx.parsed.y)}` } } },
      scales: { x: catAxis({ ticks: { maxRotation: 0, autoSkip: true, maxTicksLimit: 20 } }), y: alignedMoneyAxis({ suggestedMax: 0 }) },
    }),
  });

}

const PERIODS = { daily: a => a.days, weekly: a => a.weeks, monthly: a => a.months };

function renderPeriodChart(a, period) {
  pnlBar('periodChart', PERIODS[period](a));
}

function renderOutcomeChart(a) {
  const o = a.overall;
  const breakeven = o.n - o.wins - o.losses;
  drawChart('outcomeChart', {
    type: 'doughnut',
    data: { labels: ['Wins', 'Losses', 'Breakeven'], datasets: [{ data: [o.wins, o.losses, breakeven], backgroundColor: [C.green, C.red, C.grey], borderColor: C.panel, borderWidth: 3 }] },
    options: baseOpts({
      cutout: '68%',
      plugins: {
        legend: { position: 'bottom' },
        tooltip: { callbacks: { label: ctx => `${ctx.label}: ${ctx.parsed} (${pct(ctx.parsed / o.n, 1)})` } },
      },
    }),
  });

}

function renderRChart(a) {
  drawChart('rChart', {
    type: 'bar',
    data: {
      labels: a.rBins.map(b => `${b.lo}R to ${b.hi}R`),
      datasets: [{ label: 'Trades', data: a.rBins.map(b => b.count), backgroundColor: a.rBins.map(b => (b.lo >= 0 ? C.green : C.red)), borderRadius: 3 }],
    },
    options: baseOpts({
      plugins: { legend: { display: false }, tooltip: { callbacks: { title: i => i[0].label, label: ctx => `${plural(ctx.parsed.y, 'trade')} (1R = ${money(a.rUnit)})` } } },
      scales: { x: catAxis({ ticks: { maxRotation: 60, minRotation: 0 } }), y: { grid: { color: C.grid }, ticks: { precision: 0 }, title: { display: true, text: 'Trades' } } },
    }),
  });

}

function renderRiskRewardChart(a) {
  const o = a.overall;
  const best = a.best[0], worst = a.worst[0];
  const rr = [
    ['Avg win', o.avgWin], ['Avg loss', -o.avgLoss], ['Best', best ? best.pnl : 0], ['Worst', worst ? worst.pnl : 0],
  ];
  drawChart('rrChart', {
    type: 'bar',
    data: { labels: rr.map(r => r[0]), datasets: [{ data: rr.map(r => r[1]), backgroundColor: signColors(rr.map(r => r[1])), borderRadius: 4, maxBarThickness: 40 }] },
    options: baseOpts({
      indexAxis: 'y',
      plugins: { legend: { display: false }, tooltip: { callbacks: { label: ctx => money(ctx.parsed.x, true) } } },
      scales: { x: moneyAxis(), y: catAxis() },
    }),
  });

}

/** Streak timeline: wins plotted up, losses down. */
function renderStreakChart(a) {
  const st = a.streaks.streaks;
  drawChart('streakChart', {
    type: 'bar',
    data: {
      labels: st.map((s, i) => `${s.type}${i + 1}`),
      datasets: [{ data: st.map(s => (s.type === 'W' ? s.length : -s.length)), backgroundColor: st.map(s => (s.type === 'W' ? C.green : C.red)), borderRadius: 3 }],
    },
    options: baseOpts({
      plugins: {
        legend: { display: false },
        tooltip: {
          callbacks: {
            title: i => { const s = st[i[0].dataIndex]; return `${s.type === 'W' ? 'Win' : 'Loss'} streak: trades #${s.startId}–#${s.endId}`; },
            label: ctx => { const s = st[ctx.dataIndex]; return `${plural(s.length, 'trade')} · ${money(s.pnl, true)}`; },
          },
        },
      },
      scales: { x: catAxis({ ticks: { maxTicksLimit: 30 } }), y: { grid: { color: C.grid }, ticks: { precision: 0 }, title: { display: true, text: 'Length (trades)' } } },
    }),
  });

}

/** Weekday: P&L bars + win-rate line on a second axis. */
function renderWeekdayChart(a) {
  const wdNet = a.weekdays.map(d => d.net);
  drawChart('weekdayChart', {
    type: 'bar',
    data: {
      labels: a.weekdays.map(d => d.label),
      datasets: [
        { type: 'bar', label: 'Net P&L', data: wdNet, backgroundColor: signColors(wdNet), borderRadius: 4, maxBarThickness: 50, yAxisID: 'y' },
        { type: 'line', label: 'Win rate', data: a.weekdays.map(d => (d.n ? d.winRate * 100 : null)), borderColor: C.amber, backgroundColor: C.amber, pointRadius: 4, borderWidth: 2, yAxisID: 'y1' },
      ],
    },
    options: baseOpts({
      interaction: { mode: 'index', intersect: false },
      plugins: {
        legend: { position: 'top', align: 'end' },
        tooltip: {
          callbacks: {
            label: ctx => (ctx.dataset.yAxisID === 'y1' ? `Win rate: ${ctx.parsed.y.toFixed(1)}%` : `Net P&L: ${money(ctx.parsed.y, true)}`),
            afterBody: items => `${plural(a.weekdays[items[0].dataIndex].n, 'trade')}`,
          },
        },
      },
      scales: {
        x: catAxis(), y: moneyAxis(),
        y1: { position: 'right', min: 0, max: 100, grid: { drawOnChartArea: false }, ticks: { callback: v => v + '%' } },
      },
    }),
  });

}

function renderHourChart(a) {
  const hrs = [...a.hours].sort((x, y) => x.hour - y.hour);
  const hrNet = hrs.map(h => h.pnl);
  drawChart('hourChart', {
    type: 'bar',
    data: {
      labels: hrs.map(h => `${pad2(h.hour)}:00`),
      datasets: [
        { type: 'bar', label: 'Net P&L', data: hrNet, backgroundColor: signColors(hrNet), borderRadius: 4, maxBarThickness: 40, yAxisID: 'y' },
        { type: 'line', label: 'Trades', data: hrs.map(h => h.trades), borderColor: C.blue, backgroundColor: C.blue, pointRadius: 4, borderWidth: 2, yAxisID: 'y1' },
      ],
    },
    options: baseOpts({
      interaction: { mode: 'index', intersect: false },
      plugins: { legend: { position: 'top', align: 'end' }, tooltip: { callbacks: { label: ctx => (ctx.dataset.yAxisID === 'y1' ? `Trades: ${ctx.parsed.y}` : `Net P&L: ${money(ctx.parsed.y, true)}`) } } },
      scales: { x: catAxis(), y: moneyAxis(), y1: { position: 'right', beginAtZero: true, grid: { drawOnChartArea: false }, ticks: { precision: 0 } } },
    }),
  });

}

function renderBreakdownCharts(a) {
  pnlBar('symbolChart', a.bySymbol, { horizontal: true });
  pnlBar('setupChart', a.bySetup, { horizontal: true });
}

/* ==========================================================================
   6. FILTERS  -  state, matching (pure) and URL encoding
   Filters only select which trades are analysed. Trade ids, tags, setups and notes
   are computed once on the full data set and are never recomputed here.
   ========================================================================== */

const SIDES = ['all', 'buy', 'sell'];
const OUTCOMES = ['all', 'win', 'loss'];
const TAG_FILTERS = [['reentry', 'Re-entry'], ['sizeUp', 'Size increase'], ['scalp', 'Scalp'], ['rollover', 'Rollover'], ['longHold', 'Long hold']];
const DATE_PRESETS = [['all', 'All'], ['last7', 'Last 7 days'], ['last30', 'Last 30 days'], ['thisMonth', 'This month'], ['lastMonth', 'Last month']];
const FILTER_URL_KEYS = ['from', 'to', 'symbols', 'side', 'outcome', 'days', 'hourFrom', 'hourTo', 'setups', 'tags', 'holdMin', 'holdMax', 'pnlMin', 'pnlMax'];

function defaultFilters() {
  return {
    from: '', to: '',
    symbols: [], side: 'all', outcome: 'all', weekdays: [],
    hourFrom: null, hourTo: null,
    setups: [], tags: [],
    holdMin: null, holdMax: null,
    pnlMin: null, pnlMax: null,
  };
}

/** Date bounds in ascending order, so a reversed From/To still selects a range. */
const dateRange = f => (f.from && f.to && f.from > f.to ? [f.to, f.from] : [f.from, f.to]);
/** Inclusive bounds check where a null bound is open-ended. */
const within = (v, lo, hi) => (lo == null || v >= lo) && (hi == null || v <= hi);
const hasRange = (lo, hi) => lo != null || hi != null;

/** Trades that pass every active filter: AND across filter types, OR within a multi-select. */
function applyFilters(trades, f) {
  const [from, to] = dateRange(f);
  const symbols = new Set(f.symbols), setups = new Set(f.setups), weekdays = new Set(f.weekdays);
  const hourOn = hasRange(f.hourFrom, f.hourTo);
  const hFrom = f.hourFrom == null ? 0 : f.hourFrom, hTo = f.hourTo == null ? 23 : f.hourTo;
  const holdOn = hasRange(f.holdMin, f.holdMax);
  const pnlOn = hasRange(f.pnlMin, f.pnlMax);

  return trades.filter(t => {
    if (from && t.dateKey < from) return false;
    if (to && t.dateKey > to) return false;
    if (symbols.size && !symbols.has(t.symbol)) return false;
    if (f.side !== 'all' && String(t.side).toLowerCase() !== f.side) return false;
    if (f.outcome === 'win' && !(t.pnl > 0)) return false;
    if (f.outcome === 'loss' && !(t.pnl < 0)) return false;
    if (weekdays.size && !weekdays.has(t.weekday)) return false;
    if (hourOn) {
      if (!Number.isFinite(t.closeMs)) return false;
      const h = closeHour(t);
      // A range such as 22 -> 3 wraps past midnight.
      if (!(hFrom <= hTo ? h >= hFrom && h <= hTo : h >= hFrom || h <= hTo)) return false;
    }
    if (setups.size && !setups.has(t.setup)) return false;
    if (f.tags.length && !f.tags.some(k => t.tags && t.tags[k])) return false;
    if (holdOn && !(Number.isFinite(t.holdMin) && within(t.holdMin, f.holdMin, f.holdMax))) return false;
    if (pnlOn && !within(t.pnl, f.pnlMin, f.pnlMax)) return false;
    return true;
  });
}

/** Hour and hold-time filters need real open/close timestamps, which a journal .md does not have. */
const hasTimestamps = trades => trades.length > 0 && trades.every(t => Number.isFinite(t.openMs) && Number.isFinite(t.closeMs));

function countOptions(trades, key) {
  const counts = new Map();
  trades.forEach(t => counts.set(t[key], (counts.get(t[key]) || 0) + 1));
  return [...counts].map(([value, n]) => ({ value, n })).sort((a, b) => String(a.value).localeCompare(String(b.value)));
}

/** Everything the filter bar needs to know about the loaded file. */
function buildFilterContext(journal) {
  const trades = journal.trades;
  return {
    symbols: countOptions(trades, 'symbol'),
    setups: countOptions(trades, 'setup'),
    hasTimes: hasTimestamps(trades),
    latest: trades.reduce((max, t) => (t.dateKey > max ? t.dateKey : max), ''),
  };
}

const addDays = (key, n) => dateKey(new Date(Date.parse(`${key}T00:00:00Z`) + n * 86400000));
const monthStart = key => `${key.slice(0, 7)}-01`;

/** Date presets are relative to the latest trading day in the file, not today. */
function presetRange(name, latest) {
  switch (name) {
    case 'last7': return { from: addDays(latest, -6), to: '' };
    case 'last30': return { from: addDays(latest, -29), to: '' };
    case 'thisMonth': return { from: monthStart(latest), to: '' };
    case 'lastMonth': {
      const end = addDays(monthStart(latest), -1);
      return { from: monthStart(end), to: end };
    }
    default: return { from: '', to: '' };
  }
}

function rangeText(lo, hi, fmt) {
  if (lo != null && hi != null) return `${fmt(lo)} – ${fmt(hi)}`;
  return lo != null ? `≥ ${fmt(lo)}` : `≤ ${fmt(hi)}`;
}

/** One removable chip per active filter value: { label, key, value }. */
function describeFilters(f) {
  const chips = [];
  const add = (label, key, value) => chips.push({ label, key, value });
  const [from, to] = dateRange(f);
  if (from || to) add(from && to ? `Dates ${from} → ${to}` : from ? `From ${from}` : `Until ${to}`, 'dates');
  f.symbols.forEach(s => add(`Symbol ${s}`, 'symbols', s));
  if (f.side !== 'all') add(`Side ${f.side === 'buy' ? 'Buy' : 'Sell'}`, 'side');
  if (f.outcome !== 'all') add(f.outcome === 'win' ? 'Wins only' : 'Losses only', 'outcome');
  f.weekdays.forEach(i => add(WEEKDAYS[i], 'weekdays', i));
  if (hasRange(f.hourFrom, f.hourTo)) add(`Close hour ${pad2(f.hourFrom == null ? 0 : f.hourFrom)}–${pad2(f.hourTo == null ? 23 : f.hourTo)}`, 'hour');
  f.setups.forEach(s => add(`Setup ${s}`, 'setups', s));
  f.tags.forEach(k => add(`Tag ${(TAG_FILTERS.find(t => t[0] === k) || [k, k])[1]}`, 'tags', k));
  if (hasRange(f.holdMin, f.holdMax)) add(`Hold ${rangeText(f.holdMin, f.holdMax, v => `${v} min`)}`, 'hold');
  if (hasRange(f.pnlMin, f.pnlMax)) add(`P&L ${rangeText(f.pnlMin, f.pnlMax, v => money(v))}`, 'pnl');
  return chips;
}

/** Active filters as URL query values; defaults are omitted. */
function filtersToQuery(f) {
  const q = {};
  const put = (k, v) => {
    const text = Array.isArray(v) ? v.join(',') : v == null ? '' : String(v);
    if (text !== '') q[k] = text;
  };
  put('from', f.from); put('to', f.to);
  put('symbols', f.symbols);
  put('side', f.side === 'all' ? '' : f.side);
  put('outcome', f.outcome === 'all' ? '' : f.outcome);
  put('days', f.weekdays.map(i => WEEKDAYS[i].toLowerCase()));
  put('hourFrom', f.hourFrom); put('hourTo', f.hourTo);
  put('setups', f.setups);
  put('tags', f.tags);
  put('holdMin', f.holdMin); put('holdMax', f.holdMax);
  put('pnlMin', f.pnlMin); put('pnlMax', f.pnlMax);
  return q;
}

/** Rebuild filters from URLSearchParams, dropping anything the loaded file cannot honour. */
function filtersFromQuery(params, ctx) {
  const f = defaultFilters();
  const list = k => (params.get(k) || '').split(',').map(s => s.trim()).filter(Boolean);
  const known = (values, options) => [...new Set(values.filter(v => options.includes(v)))];
  const num = k => {
    const raw = (params.get(k) || '').trim();
    return raw !== '' && Number.isFinite(Number(raw)) ? Number(raw) : null;
  };
  const date = k => {
    const v = params.get(k) || '';
    const ms = Date.parse(`${v}T00:00:00Z`);
    return /^\d{4}-\d{2}-\d{2}$/.test(v) && Number.isFinite(ms) && dateKey(new Date(ms)) === v ? v : '';
  };
  const hour = k => {
    const n = num(k);
    return ctx.hasTimes && Number.isInteger(n) && n >= 0 && n <= 23 ? n : null;
  };
  const timed = k => (ctx.hasTimes ? num(k) : null);

  f.from = date('from'); f.to = date('to');
  f.symbols = known(list('symbols'), ctx.symbols.map(o => o.value));
  f.side = SIDES.includes(params.get('side')) ? params.get('side') : 'all';
  f.outcome = OUTCOMES.includes(params.get('outcome')) ? params.get('outcome') : 'all';
  f.weekdays = [...new Set(list('days').map(d => WEEKDAYS.findIndex(w => w.toLowerCase() === d.toLowerCase())).filter(i => i >= 0))].sort((a, b) => a - b);
  f.hourFrom = hour('hourFrom'); f.hourTo = hour('hourTo');
  f.setups = known(list('setups'), ctx.setups.map(o => o.value));
  f.tags = known(list('tags'), TAG_FILTERS.map(t => t[0]));
  f.holdMin = timed('holdMin'); f.holdMax = timed('holdMax');
  f.pnlMin = num('pnlMin'); f.pnlMax = num('pnlMax');
  return f;
}

/** Commission / swap totals for the filtered trades (the journal headline only covers the whole file). */
let lastCostsFor = null, lastCosts = null; // the footer asks twice per render with the same array
function costsOf(trades) {
  if (trades === lastCostsFor) return lastCosts;
  lastCosts = trades.every(t => Number.isFinite(t.commission) && Number.isFinite(t.swap))
    ? { commission: money(cents(sum(trades.map(t => t.commission)))), swap: money(cents(sum(trades.map(t => t.swap)))) }
    : { commission: null, swap: null };
  lastCostsFor = trades;
  return lastCosts;
}

/* ==========================================================================
   7. FILTER BAR UI
   ========================================================================== */

const MULTI_FILTERS = {
  symbols: { group: 'symbolFilter', btn: 'symbolBtn', menu: 'symbolMenu', all: 'All symbols' },
  setups: { group: 'setupFilter', btn: 'setupBtn', menu: 'setupMenu', all: 'All setups' },
};
// [input id, filter key, integer bounds]
const NUMBER_FIELDS = [
  ['fHourFrom', 'hourFrom', [0, 23]], ['fHourTo', 'hourTo', [0, 23]],
  ['fHoldMin', 'holdMin'], ['fHoldMax', 'holdMax'],
  ['fPnlMin', 'pnlMin'], ['fPnlMax', 'pnlMax'],
];
const CAPABILITY_GROUPS = [['hourGroup', ['fHourFrom', 'fHourTo']], ['holdGroup', ['fHoldMin', 'fHoldMax']]];
const NO_TIMES_REASON = 'Needs trade open/close times, which a journal .md does not contain.';

let filters = defaultFilters();
let filterCtx = null;
let urlFiltersPending = false;

const debounce = (fn, ms) => {
  let id;
  return (...args) => { clearTimeout(id); id = setTimeout(() => fn(...args), ms); };
};
const toggleValue = (list, v) => (list.includes(v) ? list.filter(x => x !== v) : [...list, v].sort((a, b) => (a < b ? -1 : a > b ? 1 : 0)));
const setPressed = (selector, isOn) => document.querySelectorAll(selector).forEach(b => b.setAttribute('aria-pressed', String(!!isOn(b))));
/** Do not overwrite a field while the user is typing in it. */
const setInputValue = (id, v) => { const el = $(id); if (document.activeElement !== el) el.value = v == null ? '' : v; };

function readNumber(input, bounds) {
  const raw = input.value.trim();
  const n = raw === '' ? NaN : Number(raw);
  if (!Number.isFinite(n)) return null;
  return bounds ? Math.min(bounds[1], Math.max(bounds[0], Math.round(n))) : n;
}

function chipButton(attrs, label) {
  return `<button type="button" class="opt-chip" ${attrs} aria-pressed="false">${esc(label)}</button>`;
}

/** Controls whose options never change with the loaded file. */
function buildStaticControls() {
  $('datePresets').innerHTML = DATE_PRESETS.map(([k, label]) => chipButton(`data-preset="${k}"`, label)).join('');
  $('weekdayChips').innerHTML = WEEKDAYS.map((w, i) => chipButton(`data-value="${i}"`, w)).join('');
  $('tagChips').innerHTML = TAG_FILTERS.map(([k, label]) => chipButton(`data-value="${k}"`, label)).join('');
}

function setMenuOpen(key, open) {
  const m = MULTI_FILTERS[key];
  $(m.menu).hidden = !open;
  $(m.btn).setAttribute('aria-expanded', String(open));
}

function closeMenus(target) {
  Object.entries(MULTI_FILTERS).forEach(([key, m]) => { if (!$(m.group).contains(target)) setMenuOpen(key, false); });
}

/** Symbol and setup option lists, rebuilt for every loaded file. */
function renderMultiOptions() {
  Object.entries(MULTI_FILTERS).forEach(([key, m]) => {
    $(m.menu).innerHTML = filterCtx[key].map(o => `<label class="ms-opt"><input type="checkbox" value="${esc(o.value)}"><span>${esc(o.value)}</span><span class="muted">${o.n}</span></label>`).join('');
    setMenuOpen(key, false);
  });
}

/** Disable (with an explanation) the filters this file cannot support. */
function applyCapabilities() {
  const off = !filterCtx.hasTimes;
  CAPABILITY_GROUPS.forEach(([groupId, inputIds]) => {
    const group = $(groupId);
    group.classList.toggle('is-disabled', off);
    group.querySelector('.f-note').hidden = !off;
    [group, ...inputIds.map($)].forEach(el => { if (off) el.title = NO_TIMES_REASON; else el.removeAttribute('title'); });
    inputIds.forEach(id => { $(id).disabled = off; });
  });
  $('hourNote').hidden = !off;
}

/** Push the filter state into every control, the chip row, the badge and the summary. */
function syncControls(chips, shown) {
  const f = filters;
  setInputValue('fDateFrom', f.from);
  setInputValue('fDateTo', f.to);
  $('dateMsg').textContent = f.from && f.to && f.from > f.to ? 'From is after To; the range is applied swapped.' : '';
  NUMBER_FIELDS.forEach(([id, key]) => setInputValue(id, f[key]));

  const preset = DATE_PRESETS.find(([k]) => { const r = presetRange(k, filterCtx.latest); return r.from === f.from && r.to === f.to; });
  setPressed('#datePresets button', b => preset && b.dataset.preset === preset[0]);
  setPressed('#sideToggle button', b => b.dataset.value === f.side);
  setPressed('#outcomeToggle button', b => b.dataset.value === f.outcome);
  setPressed('#weekdayChips button', b => f.weekdays.includes(Number(b.dataset.value)));
  setPressed('#tagChips button', b => f.tags.includes(b.dataset.value));
  Object.entries(MULTI_FILTERS).forEach(([key, m]) => {
    const picked = f[key];
    $(m.menu).querySelectorAll('input').forEach(cb => { cb.checked = picked.includes(cb.value); });
    $(m.btn).textContent = picked.length === 0 ? m.all : picked.length === 1 ? picked[0] : `${picked.length} selected`;
  });

  const groups = new Set(chips.map(c => c.key)).size;
  const summary = `Showing ${shown} of ${plural(fullJournal.trades.length, 'trade')}`;
  $('filterCount').textContent = groups;
  $('filterCount').hidden = groups === 0;
  $('filterSummary').textContent = summary;
  $('filterReset').disabled = chips.length === 0;
  $('activeChips').hidden = chips.length === 0;
  const chipsHtml = chipListHtml(chips);
  $('activeChips').innerHTML = chipsHtml;
  // The strip under the top bar mirrors the drawer chips and uses the same removal handler.
  $('filterStrip').hidden = chips.length === 0;
  $('stripCount').textContent = summary;
  $('stripChips').innerHTML = chipsHtml;
}

function chipListHtml(chips) {
  return chips.map(c => `<span class="tag fchip">${esc(c.label)}<button type="button" data-remove="${c.key}"${c.value == null ? '' : ` data-value="${esc(c.value)}"`} aria-label="Remove filter: ${esc(c.label)}">&times;</button></span>`).join('');
}

/** Filters change in bursts (typing, rapid chip clicks); coalesce them into one refresh per frame. */
let refreshQueued = false;
const afterRefresh = [];
function scheduleRefresh(after) {
  if (after) afterRefresh.push(after);
  if (refreshQueued) return;
  refreshQueued = true;
  requestAnimationFrame(() => {
    refreshQueued = false;
    refresh();
    afterRefresh.splice(0).forEach(fn => fn());
  });
}

function changeFilters(patch) {
  filters = { ...filters, ...patch };
  scheduleRefresh();
}

function resetFilters() {
  filters = defaultFilters();
  scheduleRefresh();
}

function removeFilter(key, value) {
  const drop = list => list.filter(x => String(x) !== value);
  const patch = {
    dates: { from: '', to: '' }, side: { side: 'all' }, outcome: { outcome: 'all' },
    hour: { hourFrom: null, hourTo: null }, hold: { holdMin: null, holdMax: null }, pnl: { pnlMin: null, pnlMax: null },
    symbols: { symbols: drop(filters.symbols) }, setups: { setups: drop(filters.setups) },
    weekdays: { weekdays: drop(filters.weekdays) }, tags: { tags: drop(filters.tags) },
  }[key];
  if (patch) changeFilters(patch);
}

const isDrawerOpen = () => $('filterBar').classList.contains('open');

function setDrawerOpen(open) {
  $('filterBar').classList.toggle('open', open);
  $('filterBackdrop').classList.toggle('open', open);
  $('filterToggle').setAttribute('aria-expanded', String(open));
  (open ? $('filterClose') : $('filterToggle')).focus();
}

/** Keep Tab cycling inside the open drawer. */
function trapFocus(e) {
  const items = [...$('filterBar').querySelectorAll('button, input')].filter(el => !el.disabled && el.offsetParent !== null);
  if (!items.length) return;
  const first = items[0], last = items[items.length - 1];
  if (e.shiftKey && document.activeElement === first) { e.preventDefault(); last.focus(); }
  else if (!e.shiftKey && document.activeElement === last) { e.preventDefault(); first.focus(); }
}

/** Publish the sticky top bar height (brand row, nav and filter strip) so anchor scrolling clears it. */
function syncStickyOffsets() {
  const h = document.querySelector('.topbar').offsetHeight;
  document.documentElement.style.setProperty('--sticky-h', `${h}px`);
  if (h !== spy.height) { spy.height = h; observeSections(); }
}

/** Keep the address bar in step with the filters, alongside any other query params (?file=). */
function syncUrl() {
  const params = new URLSearchParams(location.search);
  FILTER_URL_KEYS.forEach(k => params.delete(k));
  Object.entries(filtersToQuery(filters)).forEach(([k, v]) => params.set(k, v));
  const qs = params.toString().replace(/%2C/gi, ',');
  try {
    history.replaceState(null, '', `${location.pathname}${qs ? `?${qs}` : ''}${location.hash}`);
  } catch (err) {
    // Some browsers refuse history updates on file:// pages; the filters still work.
  }
}

function wireFilters() {
  buildStaticControls();
  $('filterToggle').addEventListener('click', () => setDrawerOpen(!isDrawerOpen()));
  ['filterClose', 'filterDone', 'filterBackdrop'].forEach(id => $(id).addEventListener('click', () => setDrawerOpen(false)));
  ['filterReset', 'filterEmptyReset'].forEach(id => $(id).addEventListener('click', resetFilters));
  // The strip hides itself on reset, so hand focus to the Filter button rather than losing it.
  $('stripReset').addEventListener('click', () => { resetFilters(); scheduleRefresh(() => $('filterToggle').focus()); });

  const onButton = (id, selector, handler) => $(id).addEventListener('click', e => {
    const b = e.target.closest(selector);
    if (b) handler(b);
  });
  onButton('datePresets', 'button[data-preset]', b => changeFilters(presetRange(b.dataset.preset, filterCtx.latest)));
  onButton('sideToggle', 'button[data-value]', b => changeFilters({ side: b.dataset.value }));
  onButton('outcomeToggle', 'button[data-value]', b => changeFilters({ outcome: b.dataset.value }));
  onButton('weekdayChips', 'button[data-value]', b => changeFilters({ weekdays: toggleValue(filters.weekdays, Number(b.dataset.value)) }));
  onButton('tagChips', 'button[data-value]', b => changeFilters({ tags: toggleValue(filters.tags, b.dataset.value) }));
  [['activeChips', 'filterClose'], ['stripChips', 'filterToggle']].forEach(([id, fallback]) => {
    onButton(id, 'button[data-remove]', b => {
      removeFilter(b.dataset.remove, b.dataset.value);
      // The chips are re-rendered by the refresh, so move focus once that has happened.
      scheduleRefresh(() => ($(id).querySelector('button') || $(fallback)).focus());
    });
  });

  $('fDateFrom').addEventListener('change', e => changeFilters({ from: e.target.value }));
  $('fDateTo').addEventListener('change', e => changeFilters({ to: e.target.value }));

  NUMBER_FIELDS.forEach(([id, key, bounds]) => {
    const input = $(id);
    input.addEventListener('input', debounce(() => changeFilters({ [key]: readNumber(input, bounds) }), 150));
    input.addEventListener('blur', () => {
      const v = readNumber(input, bounds);
      if (v !== filters[key]) changeFilters({ [key]: v });
      input.value = filters[key] == null ? '' : filters[key];
    });
  });

  Object.entries(MULTI_FILTERS).forEach(([key, m]) => {
    $(m.btn).addEventListener('click', () => setMenuOpen(key, $(m.menu).hidden));
    $(m.menu).addEventListener('change', () => changeFilters({ [key]: [...$(m.menu).querySelectorAll('input:checked')].map(cb => cb.value) }));
  });
  document.addEventListener('keydown', e => {
    if (!isDrawerOpen()) {
      const typing = e.target.closest && e.target.closest('input, textarea, select, [contenteditable]');
      if (e.key === 'f' && !e.ctrlKey && !e.metaKey && !e.altKey && !typing && !$('filterToggle').hidden) {
        e.preventDefault();
        setDrawerOpen(true);
      }
      return;
    }
    if (e.key === 'Tab') { trapFocus(e); return; }
    if (e.key !== 'Escape') return;
    // Escape closes an open dropdown first, then the drawer.
    const open = Object.values(MULTI_FILTERS).filter(m => !$(m.menu).hidden);
    if (!open.length) { setDrawerOpen(false); return; }
    open.forEach(m => { $(m.menu).hidden = true; $(m.btn).setAttribute('aria-expanded', 'false'); });
    $(open[0].btn).focus();
  });

  window.addEventListener('resize', () => { syncStickyOffsets(); updateCalendarHint(); });
  if (typeof ResizeObserver !== 'undefined') new ResizeObserver(syncStickyOffsets).observe(document.querySelector('.topbar'));
}

/* ==========================================================================
   8. TRADE LOG TABLE
   One row per filtered trade. Matching, sorting, row/footer HTML and CSV are pure functions of
   (trades, state); TRADE_COLUMNS drives the header, rows, footer, sorting, export and Columns menu.
   ========================================================================== */

const DASH = '—';
const NO_TRADE_DATA_REASON = 'Needs a broker CSV with trade times and costs.';
const tagLabels = t => TAG_FILTERS.filter(([k]) => t.tags && t.tags[k]).map(([, label]) => label);
const sideClass = s => ({ buy: 'side-buy', sell: 'side-sell' }[String(s).toLowerCase()] || '');
const cumOf = (t, st) => (st && st.cum ? st.cum.get(t) : undefined);
const rOf = (t, st) => (st && Number.isFinite(st.rUnit) && st.rUnit > 0 ? t.pnl / st.rUnit : undefined);
const rrText = r => (Number.isFinite(r) ? `1 : ${(Math.round(r * 100) / 100 || 0).toFixed(2)}` : DASH);
const costTotal = key => rows => [costsOf(rows)[key] || DASH, ''];
const timeText = ms => (Number.isFinite(ms) ? stampLabel(ms) : DASH);
const moneyOrDash = (v, signed) => (Number.isFinite(v) ? money(v, signed) : DASH);

/**
 * key, label, type ('number' | 'text', drives sorting and CSV escaping), visible (default), locked (cannot be hidden),
 * needs ('times' | 'costs': data a journal .md lacks), get (sort value), text (plain text), html / cls / total (optional).
 */
function videoColumn(field, label, short) {
  return {
    key: field, label: short, type: 'text', visible: true,
    cls: () => (field === 'entryVideo' ? 'vid-entry' : ''),
    get: t => t[field] || null,
    text: t => t[field] || DASH,
    html: t => (t[field]
      ? `<a class="video-link" href="${esc(t[field])}" target="_blank" rel="noopener noreferrer" title="${esc(label)}" aria-label="${esc(label)}">View</a>`
      : DASH),
  };
}

const OUTCOME_YES = '<span class="outcome outcome-yes" title="Meets strategy - take again" role="img" aria-label="Meets strategy"><svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="10"/><path d="M7.5 12.5l3 3 6-6.5"/></svg></span>';
const OUTCOME_NO = '<span class="outcome outcome-no" title="Does not meet strategy - avoid" role="img" aria-label="Does not meet strategy"><svg viewBox="0 0 24 24" aria-hidden="true"><circle cx="12" cy="12" r="10"/><path d="M8.5 8.5l7 7M15.5 8.5l-7 7"/></svg></span>';

const SCORE_LABELS = [['setup', 'Entry Setup Score'], ['risk', 'Risk Management Score'], ['stopLoss', 'Stop Loss Discipline Score'], ['exit', 'Exit Management Score'], ['emotion', 'Emotion Control Score']];
const hasScore = t => Number.isFinite(t.score);
const SCORE_MAX_TOTAL = 25; // five ratings, each 1-5
const SCORE_COLORS = { green: 'var(--green)', red: 'var(--red)', empty: '#d1d5db' };
const SCORE_TIP_LABELS = { stopLoss: 'Stop Loss Discipline' }; // shorter label used in the tooltip rows

/** Total score (sum of the five ratings), or null when any rating is missing/invalid. */
function calculateTotalScore(trade) {
  const sc = (trade && trade.scores) || {};
  const vals = SCORE_LABELS.map(([k]) => sc[k]);
  return vals.every(v => Number.isInteger(v) && v >= 1 && v <= 5) ? sum(vals) : null;
}

/** Colour tier of a total score: 15-25 green, below 15 red; '' when unknown. */
const scoreLevel = total => (!Number.isFinite(total) ? '' : total >= 15 ? 'green' : 'red');
const getScoreColor = total => SCORE_COLORS[scoreLevel(total)] || '';
const scoreClass = total => (scoreLevel(total) ? `score-${scoreLevel(total)}` : '');

/** Five stars for a 1-5 score: filled stars take the score's colour (3-5 green, 1-2 red), the rest are grey. */
function generateStars(score, max = 5) {
  const n = Number.isFinite(score) ? Math.max(0, Math.min(max, Math.round(score))) : 0;
  const color = n >= 3 ? SCORE_COLORS.green : SCORE_COLORS.red;
  let html = '';
  for (let i = 0; i < max; i++) {
    html += i < n ? `<span class="star" style="color:${color}">★</span>` : `<span class="star" style="color:${SCORE_COLORS.empty}">☆</span>`;
  }
  return `<span class="stars" aria-hidden="true">${html}</span>`;
}

/** Tooltip markup built from the trade's own scores (all values are numbers or fixed strings, labels are escaped). */
function scoreTipHtml(t, total) {
  const sc = t.scores || {};
  const rows = SCORE_LABELS.map(([k, label]) => {
    const v = Number.isFinite(sc[k]) ? sc[k] : null;
    return `<div class="score-row"><span class="score-name">${esc(SCORE_TIP_LABELS[k] || label)}</span>${generateStars(v)}<span class="score-num">(${v === null ? DASH : v}/5)</span></div>`;
  }).join('');
  const color = getScoreColor(total);
  return `<span class="score-tip" role="tooltip"><div class="score-title">Trade Quality Breakdown</div>${rows}<hr class="score-sep">`
    + `<div class="score-total">Total Score: <strong${color ? ` style="color:${color}"` : ''}>${total === null ? DASH : total}/25</strong></div></span>`;
}

const scoreHtml = t => {
  if (!t.scores || !Object.values(t.scores).some(Number.isFinite)) return DASH;
  const total = calculateTotalScore(t);
  const label = `${SCORE_LABELS.map(([k, l]) => `${l}: ${Number.isFinite(t.scores[k]) ? t.scores[k] : DASH}`).join(', ')}, Total: ${total === null ? DASH : total} / 25`;
  return `<span class="score-cell" tabindex="0" data-total="${total === null ? '' : total}" aria-label="${esc(label)}"><span class="score-val">${total === null ? DASH : total}</span><span class="score-info" aria-hidden="true">i</span>${scoreTipHtml(t, total)}</span>`;
};

const TRADE_COLUMNS = [
  { key: 'id', label: 'Trade No', type: 'number', visible: true, locked: true, get: t => t.id, text: t => String(t.id) },
  { key: 'date', label: 'Date', type: 'number', visible: true, get: t => t.date.getTime(), text: t => `${WEEKDAYS[t.weekday]} ${dayLabel(t.date)}` },
  { key: 'symbol', label: 'Symbol', type: 'text', visible: true, get: t => t.symbol, text: t => String(t.symbol) },
  {
    key: 'side', label: 'Side', type: 'text', visible: true, get: t => t.side, text: t => String(t.side),
    html: t => `<span class="${sideClass(t.side)}">${esc(t.side)}</span>`,
  },
  { key: 'qty', label: 'Qty', type: 'number', align: 'r', visible: true, get: t => t.qty, text: t => String(t.qty) },
  { key: 'open', label: 'Open', type: 'number', visible: false, needs: 'times', get: t => t.openMs, text: t => timeText(t.openMs) },
  { key: 'close', label: 'Close', type: 'number', visible: false, needs: 'times', get: t => t.closeMs, text: t => timeText(t.closeMs) },
  { key: 'hold', label: 'Hold (min)', type: 'number', align: 'r', visible: false, get: t => t.holdMin, text: t => (Number.isFinite(t.holdMin) ? t.holdMin.toFixed(1) : DASH) },
  { key: 'commission', label: 'Fee', type: 'number', align: 'r', visible: false, needs: 'costs', get: t => t.commission, text: t => moneyOrDash(t.commission), total: costTotal('commission') },
  { key: 'swap', label: 'Swap', type: 'number', align: 'r', visible: false, needs: 'costs', get: t => t.swap, text: t => moneyOrDash(t.swap), total: costTotal('swap') },
  videoColumn('entryVideo', 'Entry Chart Video', 'Entry Vid'),
  videoColumn('exitVideo', 'Exit Chart Video', 'Exit Vid'),
  {
    key: 'rr', label: 'Avg R:R', type: 'number', align: 'r', visible: false, get: rOf, text: (t, st) => rrText(rOf(t, st)),
    cls: (t, st) => signClass(rOf(t, st)),
    total: (rows, st) => {
      const rs = rows.map(t => rOf(t, st)).filter(Number.isFinite);
      if (!rs.length) return [DASH, ''];
      const avg = rs.reduce((s, v) => s + v, 0) / rs.length;
      return [rrText(avg), signClass(Math.round(avg * 100) / 100)];
    },
  },
  {
    key: 'pnl', label: 'Net P&L', type: 'number', align: 'r', visible: true, locked: true, get: t => t.pnl, text: t => money(t.pnl, true),
    cls: t => signClass(t.pnl),
    total: rows => { const net = summarize(rows).net; return [money(net, true), signClass(net)]; },
  },
  {
    key: 'cum', label: 'Equity', type: 'number', align: 'r', visible: false, get: cumOf, text: (t, st) => moneyOrDash(cumOf(t, st), true),
    cls: (t, st) => signClass(cumOf(t, st)),
  },
  { key: 'setup', label: 'Setup', type: 'text', visible: false, get: t => t.setup || null, text: t => t.setup || DASH },
  {
    key: 'tags', label: 'Tags', type: 'text', visible: false, get: t => tagLabels(t).join(', ') || null, text: t => tagLabels(t).join('; ') || DASH,
    html: t => (tagLabels(t).length ? `<span class="tl-tags">${tagLabels(t).map(l => `<span class="tag">${esc(l)}</span>`).join('')}</span>` : DASH),
  },
  { key: 'notes', label: 'Notes', type: 'text', visible: false, get: t => t.notes || null, text: t => t.notes || DASH, cls: () => 'note' },
  {
    key: 'score', label: 'Score', hint: 'Hover or focus a score to see the breakdown', type: 'number', align: 'r', visible: true, needs: 'scores',
    get: t => (hasScore(t) ? t.score : null),
    text: t => (hasScore(t) ? String(t.score) : DASH),
    html: scoreHtml,
    cls: t => scoreClass(t.score),
    total: rows => {
      const s = rows.filter(hasScore).map(t => t.score);
      if (!s.length) return [DASH, ''];
      const avg = sum(s) / s.length;
      return [pct(avg / SCORE_MAX_TOTAL), scoreClass(avg)];
    },
  },
  {
    key: 'outcome', label: 'Outcome', type: 'number', align: 'c', visible: true,
    get: t => (t.outcome === 0 || t.outcome === 1 ? t.outcome : null),
    text: t => (t.outcome === 1 ? 'Yes' : t.outcome === 0 ? 'No' : DASH),
    html: t => (t.outcome === 1 ? OUTCOME_YES : t.outcome === 0 ? OUTCOME_NO : DASH),
    // Sum of 1s (trades that meet the strategy) out of the trades that carry an outcome.
    total: rows => {
      const known = rows.filter(t => t.outcome === 0 || t.outcome === 1);
      if (!known.length) return [DASH, ''];
      const ok = known.filter(t => t.outcome === 1).length;
      return [`${ok} / ${known.length}`, signClass(ok * 2 - known.length)];
    },
  },
];

const defaultCols = () => new Set(TRADE_COLUMNS.filter(c => c.visible).map(c => c.key));
const colAvailable = (col, caps) => !col.needs || !!caps[col.needs];
const isMissing = v => v == null || (typeof v === 'number' && !Number.isFinite(v));

/** Columns to render, in natural order: chosen (or locked) and supported by the loaded file. */
const pickColumns = (visible, caps) => TRADE_COLUMNS.filter(c => (c.locked || visible.has(c.key)) && colAvailable(c, caps));

/**
 * Case-insensitive search over symbol, side, setup and notes, whether or not those columns are shown.
 * A query of the form "#<number>" (e.g. "#3") matches the Trade No exactly instead.
 */
function matchTrades(trades, text) {
  const q = String(text || '').trim().toLowerCase();
  if (!q) return trades;
  const idMatch = /^#\s*(\d+)$/.exec(q);
  if (idMatch) return trades.filter(t => Number(t.id) === Number(idMatch[1]));
  return trades.filter(t => [t.symbol, t.side, t.setup, t.notes].some(v => String(v == null ? '' : v).toLowerCase().includes(q)));
}

/** Sorted copy (newest trade first by default, then by the chosen column); missing values always go last. */
function sortTrades(trades, st) {
  const out = [...trades].sort((x, y) => y.id - x.id || y.seq - x.seq);
  const col = TRADE_COLUMNS.find(c => c.key === st.sortKey);
  if (!col) return out;
  const dir = st.sortDir === 'desc' ? -1 : 1;
  return out.sort((x, y) => {
    const vx = col.get(x, st), vy = col.get(y, st);
    const mx = isMissing(vx), my = isMissing(vy);
    if (mx || my) return mx === my ? 0 : mx ? 1 : -1;
    return (col.type === 'text' ? String(vx).localeCompare(String(vy)) : vx - vy) * dir;
  });
}

const tradeLogRows = (trades, st) => sortTrades(matchTrades(trades, st.query), st);

/** Ascending, then descending, then back to the default order. */
const nextSort = (key, dir, clicked) => (key !== clicked ? [clicked, 'asc'] : dir === 'asc' ? [clicked, 'desc'] : [null, 'asc']);

/** Page bounds for `total` rows; `size` 0 means all rows on one page. */
function pageWindow(total, pg, size) {
  const per = size > 0 ? size : Math.max(total, 1);
  const pages = Math.max(1, Math.ceil(total / per));
  const p = Math.min(pages, Math.max(1, pg));
  const start = (p - 1) * per;
  return { page: p, pages, start, end: Math.min(total, start + per) };
}

function tradeRowHtml(t, cols, st, day) {
  const rowCls = day ? ` class="${day.band ? 'day-b' : 'day-a'}${day.start ? ' day-start' : ''}"` : '';
  return `<tr${rowCls}>${cols.map(c => {
    const cls = [c.align, c.cls && c.cls(t, st)].filter(Boolean).join(' ');
    return `<td${cls ? ` class="${cls}"` : ''}>${c.html ? c.html(t, st) : esc(c.text(t, st))}</td>`;
  }).join('')}</tr>`;
}

/** Count under the first column, a label spanning the gap, then totals under their own columns. */
function tradeFooterHtml(rows, cols, st, label = 'Totals (all pages)') {
  const first = cols.findIndex(c => c.total);
  const cells = [`<td>${esc(plural(rows.length, 'trade'))}</td>`];
  if (first > 1) cells.push(`<td colspan="${first - 1}">${esc(label)}</td>`);
  cols.slice(Math.max(first, 1)).forEach(c => {
    if (!c.total) { cells.push('<td></td>'); return; }
    const [text, cls] = c.total(rows, st);
    cells.push(`<td class="${c.align || 'r'} ${cls}">${esc(text)}</td>`);
  });
  return `<tfoot><tr>${cells.join('')}</tr></tfoot>`;
}

/** Header cells; `sortable` false (calendar day detail) keeps the styling hook but drops the sort button. */
function tradeHeadHtml(cols, st, sortable = true) {
  return cols.map(c => {
    const sorted = sortable && c.key === st.sortKey;
    const aria = sorted ? ` aria-sort="${st.sortDir === 'desc' ? 'descending' : 'ascending'}"` : '';
    const hint = c.hint ? ` title="${esc(c.hint)}"` : '';
    const label = sortable
      ? `<button type="button" class="tl-sort" data-sort="${esc(c.key)}"${hint}>${esc(c.label)}</button>`
      : `<span data-sort="${esc(c.key)}"${hint}>${esc(c.label)}</span>`;
    return `<th scope="col"${c.align ? ` class="${c.align}"` : ''}${aria}>${label}</th>`;
  }).join('');
}

function tradeLogHtml(pageRows, rows, st) {
  const cols = st.cols;
  const head = tradeHeadHtml(cols, st);
  // Rows of the same trading day share a shade; it flips whenever the day changes in the displayed order.
  let band = 0, prevDay = null;
  const rowHtml = t => {
    const start = prevDay !== null && t.dateKey !== prevDay;
    if (start) band ^= 1;
    prevDay = t.dateKey;
    return tradeRowHtml(t, cols, st, { band, start });
  };
  const body = pageRows.length
    ? pageRows.map(rowHtml).join('')
    : `<tr><td colspan="${cols.length}" class="muted">No trades match your search</td></tr>`;
  return `<table class="tbl" aria-label="All trades"><thead><tr>${head}</tr></thead><tbody>${body}</tbody>${tradeFooterHtml(rows, cols, st)}</table>`;
}

/** Quote a CSV cell; text cells starting with = + - @ are neutralised against formula injection. */
function csvCell(value, isText) {
  let s = String(value);
  if (isText && /^[=+\-@\t\r]/.test(s)) s = `'${s}`;
  return /[",\r\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s;
}

/** Visible columns only, in on-screen order, so the file matches the table. */
function buildCsv(rows, st) {
  const lines = [st.cols.map(c => csvCell(c.label, true))];
  rows.forEach(t => lines.push(st.cols.map(c => csvCell(c.text(t, st), c.type === 'text'))));
  return lines.map(l => l.join(',')).join('\r\n');
}

/* ---- trade log state and DOM wiring ---- */

const STORE_COLS_OUTCOME = 'tj.tradeColsOutcome', STORE_COLS_SCORE = 'tj.tradeColsScore', STORE_COLS_VIDEO = 'tj.tradeColsVideo', STORE_COLS = 'tj.tradeCols', STORE_PAGE_SIZE = 'tj.tradePageSize', PAGE_SIZES = [0, 10, 25, 50, 100];

/** localStorage can be missing or blocked (file:// in some browsers, private mode); fall back to defaults silently. */
function storeGet(key) {
  try { return localStorage.getItem(key); } catch (err) { return null; }
}
function storeSet(key, value) {
  try { localStorage.setItem(key, value); } catch (err) { /* not persisted */ }
}

function savedCols() {
  try {
    const keys = JSON.parse(storeGet(STORE_COLS));
    const known = Array.isArray(keys) ? keys.filter(k => TRADE_COLUMNS.some(c => c.key === k)) : [];
    if (!known.length) return defaultCols();
    const set = new Set(known);
    // Columns added after the choice was saved (the chart video links) are switched on once.
    if (storeGet(STORE_COLS_VIDEO) === null) {
      ['entryVideo', 'exitVideo'].forEach(k => set.add(k));
      storeSet(STORE_COLS, JSON.stringify([...set]));
      storeSet(STORE_COLS_VIDEO, '1');
    }
    // One-off switch-on for the Outcome column.
    if (storeGet(STORE_COLS_OUTCOME) === null) {
      set.add('outcome');
      storeSet(STORE_COLS, JSON.stringify([...set]));
      storeSet(STORE_COLS_OUTCOME, '1');
    }
    // One-off switch-on for the Score column.
    if (storeGet(STORE_COLS_SCORE) === null) {
      set.add('score');
      storeSet(STORE_COLS, JSON.stringify([...set]));
      storeSet(STORE_COLS_SCORE, '1');
    }
    return set;
  } catch (err) {
    return defaultCols();
  }
}

function savedPageSize() {
  const n = Number(storeGet(STORE_PAGE_SIZE));
  return storeGet(STORE_PAGE_SIZE) !== null && PAGE_SIZES.includes(n) ? n : 10;
}

let visibleCols = savedCols(); // survives filter changes and new files; kept in localStorage, not the URL
let tradeCaps = { times: false, costs: false, scores: false };
let sortKey = null; // null = default order (by id, newest first)
let sortDir = 'asc';
let query = '';
let page = 1;
let pageSize = savedPageSize(); // 0 = all

const cumulativeCache = new WeakMap();
/** Running equity of the filtered set, so the column agrees with the Equity Curve. */
function cumulativeMap(a) {
  if (!cumulativeCache.has(a)) cumulativeCache.set(a, new Map(a.trades.map((t, i) => [t, a.equity[i + 1].value])));
  return cumulativeCache.get(a);
}

const tradeLogState = a => ({ query, sortKey, sortDir, cols: pickColumns(visibleCols, tradeCaps), cum: cumulativeMap(a), rUnit: a.rUnit });

function setColMenuOpen(open) {
  $('tradeColMenu').hidden = !open;
  $('tradeColBtn').setAttribute('aria-expanded', String(open));
}

function closeColMenu(target) {
  if (!$('tradeColFilter').contains(target)) setColMenuOpen(false);
}

/** Update checkbox states and the button label in place, so a focused checkbox keeps focus. */
function syncColumnMenu() {
  $('tradeColList').querySelectorAll('input').forEach(cb => {
    const col = TRADE_COLUMNS.find(c => c.key === cb.value);
    const ok = colAvailable(col, tradeCaps);
    const label = cb.closest('label');
    cb.disabled = col.locked || !ok;
    cb.checked = ok && (col.locked || visibleCols.has(col.key));
    label.classList.toggle('is-disabled', cb.disabled);
    if (!ok) label.title = NO_TRADE_DATA_REASON; else label.removeAttribute('title');
  });
  $('tradeColBtn').textContent = `Columns (${pickColumns(visibleCols, tradeCaps).length} of ${TRADE_COLUMNS.length})`;
}

function renderTradePager(win, total) {
  $('tradeLogStatus').textContent = total ? `Showing ${win.start + 1}–${win.end} of ${total}` : 'Showing 0 of 0';
  $('tradeLogPager').querySelector('[data-page="prev"]').disabled = win.page <= 1;
  $('tradeLogPager').querySelector('[data-page="next"]').disabled = win.page >= win.pages;
}

/** Render the current page of the trade log; `a` is the analytics of the filtered trades. */
function renderTradeLog(a) {
  const cols = pickColumns(visibleCols, tradeCaps);
  if (sortKey && !cols.some(c => c.key === sortKey)) { sortKey = null; sortDir = 'asc'; page = 1; }
  const st = tradeLogState(a);
  const rows = tradeLogRows(a.trades, st);
  const win = pageWindow(rows.length, page, pageSize);
  page = win.page;
  $('tradeLogTable').classList.remove('has-pinned-tip'); // a re-render drops any pinned tooltip
  $('tradeLogTable').innerHTML = tradeLogHtml(rows.slice(win.start, win.end), rows, st);
  renderTradePager(win, rows.length);
  syncColumnMenu();
}

/** New file: clear search, sort and page, and re-read what the file supports. */
function resetTradeLog() {
  query = ''; sortKey = null; sortDir = 'asc'; page = 1;
  $('tradeLogSearch').value = '';
  setColMenuOpen(false);
  tradeCaps = { times: filterCtx.hasTimes, costs: costsOf(fullJournal.trades).commission !== null, scores: fullJournal.trades.some(hasScore) };
}

function exportTradeCsv() {
  if (!currentAnalytics) return;
  const st = tradeLogState(currentAnalytics);
  downloadText('trades.csv', '\uFEFF' + buildCsv(tradeLogRows(currentAnalytics.trades, st), st), 'text/csv;charset=utf-8');
}

/**
 * Score breakdown popovers inside `box` (the trade log, the calendar day detail).
 * The popover is position:fixed (the table scrolls and would clip it); it is placed next to the hovered/focused cell.
 */
function wireScoreTips(box) {
  const placeTip = e => {
    const cell = e.target.closest && e.target.closest('.score-cell');
    const tip = cell && cell.querySelector('.score-tip');
    if (!tip) return;
    const r = cell.getBoundingClientRect();
    const w = tip.offsetWidth, h = tip.offsetHeight, gap = 8, margin = 8;
    // Prefer above the cell; flip below when there is no room, and keep the box inside the viewport.
    const above = r.top - h - gap >= margin;
    const top = above ? r.top - h - gap : Math.min(r.bottom + gap, window.innerHeight - h - margin);
    const left = Math.max(margin, Math.min(r.left + r.width / 2 - w / 2, window.innerWidth - w - margin));
    tip.style.top = `${Math.max(margin, top)}px`;
    tip.style.left = `${left}px`;
    tip.classList.toggle('below', !above);
  };
  const pinnedTip = () => box.querySelector('.score-cell.pinned');
  box.addEventListener('mouseover', e => { if (!pinnedTip()) placeTip(e); });
  box.addEventListener('focusin', e => { if (!pinnedTip()) placeTip(e); });

  // Click (or Enter/Space) pins the tooltip open; while one is pinned no other tooltip appears on hover.
  const unpinTip = () => {
    const p = pinnedTip();
    if (p) p.classList.remove('pinned');
    box.classList.remove('has-pinned-tip');
  };
  const togglePin = (cell, e) => {
    const wasPinned = cell.classList.contains('pinned');
    unpinTip();
    if (wasPinned) return;
    placeTip(e);
    cell.classList.add('pinned');
    box.classList.add('has-pinned-tip');
  };
  box.addEventListener('click', e => {
    const cell = e.target.closest('.score-cell');
    if (cell) togglePin(cell, e);
  });
  box.addEventListener('keydown', e => {
    const cell = e.target.closest && e.target.closest('.score-cell');
    if (cell && (e.key === 'Enter' || e.key === ' ')) { e.preventDefault(); togglePin(cell, { target: cell }); }
  });
  // Clicking elsewhere, pressing Escape or scrolling (the fixed tip would drift from its cell) closes it.
  document.addEventListener('click', e => { if (!e.target.closest || !e.target.closest('.score-cell')) unpinTip(); });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') unpinTip(); });
  document.addEventListener('scroll', unpinTip, true);
}

function wireTradeLog() {
  $('tradeColList').innerHTML = TRADE_COLUMNS.map(c => `<label class="ms-opt tl-opt"><input type="checkbox" value="${esc(c.key)}"><span>${esc(c.label)}</span></label>`).join('');
  const rerender = () => { if (currentAnalytics) renderTradeLog(currentAnalytics); };
  const setCols = keys => { visibleCols = new Set(keys); storeSet(STORE_COLS, JSON.stringify([...visibleCols])); rerender(); syncColumnMenu(); };

  const search = $('tradeLogSearch');
  search.addEventListener('input', debounce(() => { query = search.value; page = 1; rerender(); }, 150));
  $('tradeLogPageSize').value = pageSize === 0 ? 'all' : String(pageSize);
  $('tradeLogPageSize').addEventListener('change', e => {
    pageSize = e.target.value === 'all' ? 0 : Number(e.target.value);
    storeSet(STORE_PAGE_SIZE, String(pageSize));
    page = 1;
    rerender();
  });
  $('tradeLogExport').addEventListener('click', exportTradeCsv);

  $('tradeColBtn').addEventListener('click', () => setColMenuOpen($('tradeColMenu').hidden));
  $('tradeColAll').addEventListener('click', () => setCols(TRADE_COLUMNS.map(c => c.key)));
  $('tradeColReset').addEventListener('click', () => setCols(defaultCols()));
  $('tradeColList').addEventListener('change', e => {
    const cb = e.target.closest('input[type="checkbox"]');
    if (!cb) return;
    const next = new Set(visibleCols);
    if (cb.checked) next.add(cb.value); else next.delete(cb.value);
    setCols(next);
  });
  // The menu sits outside the filter drawer, so its Escape handling lives on its own wrapper.
  $('tradeColFilter').addEventListener('keydown', e => {
    if (e.key !== 'Escape' || $('tradeColMenu').hidden) return;
    setColMenuOpen(false);
    $('tradeColBtn').focus();
  });

  wireScoreTips($('tradeLogTable'));

  $('tradeLogTable').addEventListener('click', e => {
    const b = e.target.closest('button[data-sort]');
    if (!b || !currentAnalytics) return;
    const key = b.dataset.sort;
    [sortKey, sortDir] = nextSort(sortKey, sortDir, key);
    page = 1;
    rerender();
    const again = $('tradeLogTable').querySelector(`button[data-sort="${key}"]`);
    if (again) again.focus();
  });
  $('tradeLogPager').addEventListener('click', e => {
    const b = e.target.closest('button[data-page]');
    if (!b || b.disabled || !currentAnalytics) return;
    page += b.dataset.page === 'next' ? 1 : -1;
    rerender();
    // Keep keyboard focus when the clicked button has just been disabled.
    const open = b.disabled && $('tradeLogPager').querySelector('button:not(:disabled)');
    if (open) open.focus();
  });
}

/* ==========================================================================
   9. NAVIGATION  -  scroll-spy, back to top, collapsible sections, print
   ========================================================================== */

const STORE_COLLAPSED = 'tj.collapsed';
const spy = { ids: [], links: [], alias: {}, visible: new Set(), observer: null, atEnd: false, locked: false, lockTimer: 0, height: -1 };
const collapsedIds = new Set();

const prefersReducedMotion = () => window.matchMedia('(prefers-reduced-motion: reduce)').matches;

/** Centre the active link in the horizontally scrolling mobile nav. */
function scrollNavTo(link) {
  const nav = $('mainNav');
  if (nav.scrollWidth <= nav.clientWidth) return;
  const n = nav.getBoundingClientRect(), l = link.getBoundingClientRect();
  nav.scrollTo({ left: nav.scrollLeft + (l.left - n.left) - (n.width - l.width) / 2, behavior: prefersReducedMotion() ? 'auto' : 'smooth' });
}

function updateNavFade() {
  const nav = $('mainNav');
  nav.classList.toggle('fade-l', nav.scrollLeft > 4);
  nav.classList.toggle('fade-r', nav.scrollLeft + nav.clientWidth < nav.scrollWidth - 4);
}

function setActiveNav(id) {
  spy.links.forEach(a => {
    const on = a.hash === `#${id}`;
    a.classList.toggle('active', on);
    if (on) { a.setAttribute('aria-current', 'true'); scrollNavTo(a); } else a.removeAttribute('aria-current');
  });
}

function updateSpy() {
  if (spy.locked) return;
  // Targets can nest (#pnl sits inside #performance); the later id is the more specific one.
  const seen = new Set([...spy.visible].map(x => spy.alias[x] || x));
  const id = spy.atEnd ? spy.ids[spy.ids.length - 1] : [...spy.ids].reverse().find(x => seen.has(x));
  if (id) setActiveNav(id);
}

/**
 * Highlight the section crossing a thin line a little below the sticky bar. Rebuilt whenever the bar's height or
 * the viewport changes, because rootMargin cannot follow either on its own.
 */
function observeSections() {
  if (typeof IntersectionObserver === 'undefined' || !spy.ids.length) return;
  if (spy.observer) spy.observer.disconnect();
  spy.visible.clear();
  const vh = document.documentElement.clientHeight;
  const top = document.querySelector('.topbar').offsetHeight;
  // The band must be taller than the 16px gap between panels, or the line can fall in the gap and match only the parent section.
  const band = 24;
  const line = Math.min(vh - band, top + Math.round((vh - top) * 0.3));
  spy.observer = new IntersectionObserver(entries => {
    entries.forEach(e => { if (e.isIntersecting) spy.visible.add(e.target.id); else spy.visible.delete(e.target.id); });
    updateSpy();
  }, { rootMargin: `-${line}px 0px -${Math.max(0, vh - line - band)}px 0px` });
  spy.ids.concat(Object.keys(spy.alias)).forEach(id => { const el = $(id); if (el) spy.observer.observe(el); });
}

/** Hold the clicked highlight until the smooth scroll ends, so it does not flicker through the sections in between. */
function lockSpy() {
  spy.locked = true;
  clearTimeout(spy.lockTimer);
  const release = () => {
    clearTimeout(spy.lockTimer);
    window.removeEventListener('scrollend', release);
    spy.locked = false;
    updateSpy();
  };
  window.addEventListener('scrollend', release);
  spy.lockTimer = setTimeout(release, 1500);
}

function setCollapsed(id, isClosed) {
  if (isClosed) collapsedIds.add(id); else collapsedIds.delete(id);
  storeSet(STORE_COLLAPSED, JSON.stringify([...collapsedIds]));
}

/** Open the collapsed block that holds (or is) the target of a link, so the jump lands on visible content. */
function revealTarget(id) {
  const el = id ? document.getElementById(id) : null;
  const box = el && (el.matches('details') ? el : el.closest('details'));
  if (box && !box.open) { box.open = true; setCollapsed(box.id, false); }
}

function wireCollapsibles() {
  try { (JSON.parse(storeGet(STORE_COLLAPSED)) || []).forEach(id => collapsedIds.add(id)); } catch (err) { /* ignore a corrupt value */ }
  const boxes = [...document.querySelectorAll('details.collapsible')];
  boxes.forEach(box => {
    if (collapsedIds.has(box.id)) box.open = false;
    // The click runs before the browser toggles `open`, so the new state is the opposite of the current one.
    box.querySelector('summary').addEventListener('click', () => setCollapsed(box.id, box.open));
  });
  // Closed <details> content does not print, so open everything for the print job and restore afterwards.
  let before = [];
  window.addEventListener('beforeprint', () => { before = boxes.map(b => b.open); boxes.forEach(b => { b.open = true; }); });
  window.addEventListener('afterprint', () => boxes.forEach((b, i) => { b.open = before[i]; }));
}

function wireNav() {
  const nav = $('mainNav');
  spy.links = [...nav.querySelectorAll('a[href^="#"]')];
  spy.ids = spy.links.map(a => a.hash.slice(1));
  // data-also lists further sections that belong to a link (e.g. P&L By Period under P&L).
  spy.links.forEach(a => (a.dataset.also || '').split(' ').filter(Boolean).forEach(id => { spy.alias[id] = a.hash.slice(1); }));

  // Handles the nav and in-page links such as "All insights"; the browser still performs the smooth scroll.
  const onAnchor = e => {
    const a = e.target.closest('a[href^="#"]');
    if (!a || a.hash.length < 2) return;
    revealTarget(a.hash.slice(1));
    const section = $(a.hash.slice(1));
    const owner = section && [...spy.ids].reverse().find(id => $(id).contains(section));
    if (owner) { setActiveNav(owner); lockSpy(); }
  };
  nav.addEventListener('click', onAnchor);
  $('dashboardContent').addEventListener('click', onAnchor);
  window.addEventListener('hashchange', () => revealTarget(location.hash.slice(1)));

  document.querySelectorAll('a[href="#top"]').forEach(a => a.addEventListener('click', e => {
    e.preventDefault();
    window.scrollTo({ top: 0, behavior: prefersReducedMotion() ? 'auto' : 'smooth' });
  }));

  nav.addEventListener('scroll', updateNavFade, { passive: true });
  if (typeof ResizeObserver !== 'undefined') new ResizeObserver(updateNavFade).observe(nav);
  window.addEventListener('resize', debounce(observeSections, 200));
  if (typeof IntersectionObserver !== 'undefined') {
    // The last section can be too short to reach the highlight line, so reaching the footer selects it.
    new IntersectionObserver(([e]) => { spy.atEnd = e.isIntersecting; updateSpy(); }, { threshold: 1 }).observe(document.querySelector('.footer'));
  }
  wireCollapsibles();
}

/* ==========================================================================
   10. PAGE ORCHESTRATION
   ========================================================================== */

let fullJournal = null; // parsed once per file; filters never re-read or re-parse it
let sourceName = '';
let currentAnalytics = null;
let equityType = 'line'; // 'line' | 'bar', chosen via the Equity Curve toggle
let pnlType = 'bar';     // same options for the P&L Curve toggle
let periodType = 'daily'; // 'daily' | 'weekly' | 'monthly'
let calMonthKey = null;   // calendar month 'YYYY-MM'; kept across filter changes and file loads while that month exists
let calDayKey = null;     // trading day open in the calendar's detail panel; reset on file load
let deepLinkPending = false; // set in boot() for a ?file= load only

function syncToggle(id, key, value) {
  $(id).querySelectorAll('button').forEach(b => {
    const on = b.dataset[key] === value;
    b.classList.toggle('active', on);
    b.setAttribute('aria-pressed', String(on));
  });
}

function bindToggle(id, key, onPick) {
  $(id).addEventListener('click', e => {
    const b = e.target.closest('button');
    if (!b) return;
    onPick(b.dataset[key]);
    syncToggle(id, key, b.dataset[key]);
  });
}

function showError(msg) {
  const el = $('errorBanner');
  el.textContent = msg;
  el.hidden = !msg;
}

function destroyCharts() {
  Object.keys(charts).forEach(id => { charts[id].destroy(); delete charts[id]; });
}

function renderSubtitle(shown, filtered) {
  const total = fullJournal.trades.length;
  const openNote = fullJournal.openPositions ? ` · ${plural(fullJournal.openPositions, 'open position')} excluded` : '';
  const count = filtered ? `Showing ${shown} of ${plural(total, 'trade')}` : plural(total, 'trade');
  const text = `${sourceName}${fullJournal.period ? ' · ' + fullJournal.period : ''} · ${count}${openNote}`;
  $('subtitle').textContent = text;
  $('subtitle').title = text; // the bar truncates it with an ellipsis
}

/** Parse once, reset the filters (or restore them from the URL on the first load), then refresh. */
function loadFile(text, name) {
  try {
    const journal = /^\s*(?:[^,\r\n]*,)?\s*symbol\s*,/i.test(text) ? parseTradesCsv(text) : parseJournal(text);
    if (!journal.trades.length) throw new Error('No closed trades found. Expected a trades CSV (Symbol, Side, Open Date, Close Date, Entry Price, Exit Price, Qty, Fee, Swap Fees, Net P&L) or a journal .md with a "Trade-by-Trade Detail" section.');
    fullJournal = journal;
    sourceName = name;
    filterCtx = buildFilterContext(journal);
    filters = urlFiltersPending ? filtersFromQuery(new URLSearchParams(location.search), filterCtx) : defaultFilters();
    urlFiltersPending = false;

    $('emptyState').hidden = true;
    $('filterToggle').hidden = false;
    $('mainNav').hidden = false;
    $('dashboard').hidden = false;
    showError('');
    $('chartBanner').hidden = chartsAvailable();
    renderMultiOptions();
    applyCapabilities();
    resetTradeLog();
    calDayKey = null;
    refresh();
    syncStickyOffsets();
    updateNavFade();
    if (deepLinkPending) {
      // Old bookmarks such as #equity could not scroll while the dashboard was hidden.
      deepLinkPending = false;
      revealTarget(location.hash.slice(1));
      const target = document.getElementById(location.hash.slice(1));
      if (target) requestAnimationFrame(() => target.scrollIntoView());
    } else {
      // A file the user picks starts at Overview, not at a stale hash or restored scroll position.
      try { if (location.hash) history.replaceState(null, '', location.pathname + location.search); } catch (err) { /* file:// */ }
      window.scrollTo({ top: 0, behavior: 'instant' });
      setActiveNav(spy.ids[0]);
    }
  } catch (err) {
    console.error(err);
    showError(`Could not analyse journal: ${err.message}`);
  }
}

/** Filter -> analyse -> render. The full journal is never re-parsed; only the selected trades are re-analysed. */
function refresh() {
  if (!fullJournal) return;
  try {
    const trades = applyFilters(fullJournal.trades, filters);
    const chips = describeFilters(filters);
    const filtered = chips.length > 0;
    const empty = trades.length === 0;

    syncControls(chips, trades.length);
    syncUrl();
    renderSubtitle(trades.length, filtered);
    document.querySelectorAll('.filter-note:not(#hourNote)').forEach(n => { n.hidden = !filtered; });
    // Charts need a visible container to size themselves, so reveal the dashboard before drawing.
    $('filterEmpty').hidden = !empty;
    $('dashboardContent').hidden = empty;
    $('mainNav').hidden = empty;
    if (empty) {
      currentAnalytics = null;
      destroyCharts();
      return;
    }

    // Trades keep their full-file ids, tags and notes; only hours need recomputing (a .md has no times to group).
    const journal = { ...fullJournal, trades, hours: filterCtx.hasTimes ? hoursOf(trades) : fullJournal.hours };
    const a = analyze(journal);
    // The journal's headline table describes the whole file, so it can only be reconciled when unfiltered.
    const recon = filtered ? { checks: [], ok: false, costs: costsOf(trades) } : reconcile(journal, a);
    currentAnalytics = a;

    renderKPIs(a);
    renderDiscipline(a);
    renderOutcomeCard(a);
    renderDailyDiscipline(a);
    renderRiskStats(a, recon);
    renderStreakStats(a);
    renderCalendar(a);
    syncToggle('equityToggle', 'type', equityType);
    syncToggle('pnlToggle', 'type', pnlType);
    syncToggle('periodToggle', 'period', periodType);
    $('symbolTable').innerHTML = groupTable(a.bySymbol, 'Symbol');
    $('setupTable').innerHTML = groupTable(a.bySetup, 'Setup');
    $('bestTable').innerHTML = tradeTable(a.best);
    $('worstTable').innerHTML = tradeTable(a.worst);
    renderInsights(a, journal);
    page = 1;
    renderTradeLog(a);
    renderCharts(a);
  } catch (err) {
    console.error(err);
    showError(`Could not analyse journal: ${err.message}`);
  }
}

/** Deterministic demo trades (three weeks, three symbols) so the dashboard can be explored without a broker file. */
function sampleCsv() {
  let seed = 7;
  const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647;
  const stamp = ms => new Date(ms).toISOString().slice(0, 19).replace('T', ' ');
  const instruments = [['XAUUSD', 0.5], ['EURUSD', 1], ['NAS100', 0.2]];
  const rows = [CSV_HEADER];
  let positionId = 5000100;
  let tradeNo = 0;
  for (let week = 0; week < 3; week++) {
    for (let weekday = 0; weekday < 5; weekday++) {
      const day = Date.UTC(2026, 8, 7 + week * 7 + weekday); // 7 Sep 2026 is a Monday
      const count = 3 + Math.floor(rnd() * 5);
      for (let i = 0; i < count; i++) {
        const [symbol, qty] = instruments[Math.floor(rnd() * instruments.length)];
        const long = rnd() < 0.55;
        const open = day + (8 + Math.floor(rnd() * 11)) * 3600000 + Math.floor(rnd() * 60) * 60000;
        const close = open + (2 + Math.floor(rnd() * 70)) * 60000;
        const win = rnd() < 0.45;
        const profit = cents((win ? 6 + rnd() * 34 : -(5 + rnd() * 20)));
        const entry = 1000 + Math.floor(rnd() * 1000);
        const exit = cents(entry + (profit / qty) * (long ? 1 : -1));
        rows.push([++tradeNo, symbol, long ? 'Buy' : 'Sell', stamp(open), stamp(close), entry, exit, qty, 0.35, 0, cents(profit - 0.35)].join(','));
      }
    }
  }
  return rows.join('\n');
}

const CSV_HEADER = 'Trade No,Symbol,Side,Open Date,Close Date,Entry Price,Exit Price,Qty,Fee,Swap Fees,Net P&L,Entry Chart Video Link,Exit Chart Video Link,Outcome,Entry Setup Score,Risk Management Score,Stop Loss Discipline Score,Exit Management Score,Emotion Control Score,Entry Reason,Exit Reason';
const CSV_TEMPLATE = `${CSV_HEADER}\n1,XAUUSD,Buy,2026-10-05 09:30:00,2026-10-05 09:52:10,2650,2675.5,0.05,15,-5.5,234.5,,,1,4,5,4,4,4,Broke above resistance and retested,Hit take profit`;

function downloadText(filename, text, type) {
  const url = URL.createObjectURL(new Blob([text], { type }));
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

function readFile(file) {
  const reader = new FileReader();
  reader.onload = () => loadFile(String(reader.result), file.name);
  reader.onerror = () => showError('Could not read the selected file.');
  reader.readAsText(file);
}

function wireUi() {
  wireNav();
  wireFilters();
  wireTradeLog();
  wireCardPick('disciplineCard', 'discPick', 'discipline', renderDiscipline);
  wireCardPick('outcomeCard', 'ocPick', 'outcome', renderOutcomeCard);
  wireCardPick('dailyDisciplineCard', 'ddDay', 'daily', renderDailyDiscipline);
  // Click anywhere outside an open dropdown closes it (Columns menu and the symbol/setup filter menus).
  document.addEventListener('click', e => { closeColMenu(e.target); closeMenus(e.target); });
  bindToggle('equityToggle', 'type', v => { equityType = v; if (currentAnalytics) renderEquityChart(currentAnalytics, v); });
  bindToggle('pnlToggle', 'type', v => { pnlType = v; if (currentAnalytics) renderPnlCurveChart(currentAnalytics, v); });
  bindToggle('periodToggle', 'period', v => { periodType = v; if (currentAnalytics) { renderPeriodChart(currentAnalytics, v); labelCharts(currentAnalytics); } });
  bindCalendar();
  wireScoreTips($('calDetail'));

  $('sampleLoad').addEventListener('click', () => loadFile(sampleCsv(), 'sample-trades.csv'));
  $('templateDownload').addEventListener('click', () => downloadText('trades-template.csv', CSV_TEMPLATE, 'text/csv;charset=utf-8'));
  $('fileInput').addEventListener('change', e => { if (e.target.files[0]) readFile(e.target.files[0]); e.target.value = ''; });

  // Drag & drop a file anywhere on the page.
  let depth = 0;
  window.addEventListener('dragenter', e => { e.preventDefault(); depth++; $('dropOverlay').hidden = false; });
  window.addEventListener('dragleave', () => { if (--depth <= 0) { depth = 0; $('dropOverlay').hidden = true; } });
  window.addEventListener('dragover', e => e.preventDefault());
  window.addEventListener('drop', e => {
    e.preventDefault(); depth = 0; $('dropOverlay').hidden = true;
    if (e.dataTransfer.files[0]) readFile(e.dataTransfer.files[0]);
  });
}

async function boot() {
  readThemeColors();
  wireUi();
  const params = new URLSearchParams(location.search);
  urlFiltersPending = FILTER_URL_KEYS.some(k => params.has(k));
  // Over http, a same-origin file can be opened directly with index.html?file=name.csv
  const file = params.get('file');
  if (!file) return;
  deepLinkPending = !!location.hash;
  try {
    if (new URL(file, location.href).origin !== location.origin) throw new Error('only files next to this page can be opened');
    const res = await fetch(file, { cache: 'no-store' });
    if (!res.ok) throw new Error(res.statusText);
    loadFile(await res.text(), file);
  } catch (err) {
    showError(`Could not load ${file}: ${err.message}. Use "Open trades CSV" instead.`);
  }
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', boot);
}
if (typeof module !== 'undefined') {
  module.exports = { parseJournal, parseTradesCsv, analyze, reconcile, buildInsights, parseMoney, formatDayMetrics, applyFilters, defaultFilters, TRADE_COLUMNS, pickColumns, matchTrades, sortTrades, tradeLogRows, pageWindow, tradeRowHtml, tradeFooterHtml, buildCsv };
}
