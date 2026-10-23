// Turns a typed math problem into labelled answer rows written as TeX.
// Needs math.js loaded as the global `math`.
(function (global) {
  const EPS = 1e-9;

  const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a; };
  const isInt = (v) => Math.abs(v - Math.round(v)) < 1e-9;

  // [p, q] with q <= maxQ when v is (very nearly) p / q
  function toFraction(v, maxQ = 1000, tol = 1e-9) {
    for (let q = 1; q <= maxQ; q++) {
      const p = Math.round(v * q);
      if (Math.abs(p / q - v) < tol * Math.max(1, Math.abs(v))) return [p, q];
    }
    return null;
  }

  // ---------- TeX for numbers ----------
  function numTex(v) {
    if (!isFinite(v)) return v > 0 ? '\\infty' : v < 0 ? '-\\infty' : '\\text{undefined}';
    if (isInt(v)) return String(Math.round(v) || 0);
    const f = toFraction(v, 100);
    if (f) return `${f[0] < 0 ? '-' : ''}\\frac{${Math.abs(f[0])}}{${f[1]}}`;
    return math.format(v, { precision: 10 });
  }
  const decimal = (v) => math.format(v, { precision: 10 });

  function complexTex(re, im) {
    if (Math.abs(im) < EPS) return numTex(re);
    const mag = Math.abs(im);
    const imPart = isInt(mag) && Math.round(mag) === 1 ? 'i' : `${numTex(mag)}i`;
    if (Math.abs(re) < EPS) return (im < 0 ? '-' : '') + imPart;
    return `${numTex(re)} ${im < 0 ? '-' : '+'} ${imPart}`;
  }

  function valueTex(v) {
    if (typeof v === 'number') return numTex(v);
    if (typeof v === 'boolean') return `\\text{${v}}`;
    if (math.isComplex(v)) return complexTex(v.re, v.im);
    if (math.isNode(v)) return toTex(v);
    if (math.isFraction(v)) return numTex(math.number(v));
    try { return toTex(math.parse(math.format(v, { precision: 10 }))); } catch { return `\\text{${String(v)}}`; }
  }

  // TeX for a node, writing 6·x as 6x
  const toTex = (node) => node.toTex({ parenthesis: 'auto', implicit: 'hide' })
    .replace(/(\d)\s*\\cdot\s*(?=\{?\s*[a-zA-Z\\({])/g, '$1')
    .replace(/~/g, '');
  // ignore spacing/brace differences when deciding whether a row adds anything
  const same = (a, b) => a.replace(/\\cdot|[\s{}~]/g, '') === b.replace(/\\cdot|[\s{}~]/g, '');

  // ---------- polynomials ----------
  // coefficients lowest power first, or null when the expression isn't a polynomial in `name`
  function polynomial(node, name) {
    let r;
    try { r = math.rationalize(node, {}, true); } catch { return null; }
    if (r.denominator) return null;
    if (r.variables.length > 1 || (r.variables.length === 1 && r.variables[0] !== name)) return null;
    const c = r.variables.length ? r.coefficients.map(Number) : [math.number(node.evaluate())];
    while (c.length > 1 && Math.abs(c[c.length - 1]) < EPS) c.pop();
    return { coeffs: c, expanded: r.expression };
  }

  // scale to integer coefficients when every coefficient is a simple fraction
  function integerCoeffs(c) {
    const fr = c.map((v) => toFraction(v, 1000));
    if (fr.some((f) => !f)) return null;
    const lcm = fr.reduce((l, [, q]) => (l * q) / gcd(l, q), 1);
    const ints = fr.map(([p, q]) => (p * lcm) / q);
    const g = ints.reduce((a, b) => gcd(a, b), 0) || 1;
    return ints.map((v) => v / g);
  }

  const divisors = (n) => {
    n = Math.abs(n);
    const out = [];
    for (let d = 1; d * d <= n; d++) if (n % d === 0) { out.push(d); if (d * d !== n) out.push(n / d); }
    return out;
  };

  // is p/q a root of integer polynomial c? (exact, BigInt)
  function isRationalRoot(c, p, q) {
    const n = c.length - 1;
    let sum = 0n;
    for (let i = 0; i <= n; i++) sum += BigInt(c[i]) * BigInt(p) ** BigInt(i) * BigInt(q) ** BigInt(n - i);
    return sum === 0n;
  }

  // divide integer polynomial c by (q x - p)
  function divideLinear(c, p, q) {
    const hi = c.slice().reverse(), out = [];
    let prev = 0;
    for (let k = 0; k < hi.length - 1; k++) {
      prev = (hi[k] + p * prev) / q;
      out.push(prev);
    }
    return out.reverse();
  }

  const real = (v) => ({ re: v, im: 0 });

  // exact quadratic roots for integer c = [C, B, A], written with surds when needed
  function quadratic([C, B, A], exact) {
    const D = B * B - 4 * A * C;
    const sq = Math.sqrt(Math.abs(D));
    const roots = D >= 0
      ? [real((-B + sq) / (2 * A)), real((-B - sq) / (2 * A))]
      : [{ re: -B / (2 * A), im: sq / (2 * A) }, { re: -B / (2 * A), im: -sq / (2 * A) }];
    if (!exact || (D >= 0 && isInt(sq))) return roots;

    // |D| = k^2 m with m square-free
    let k = 1, m = Math.abs(D);
    for (let f = 2; f * f <= m; f++) while (m % (f * f) === 0) { m /= f * f; k *= f; }
    let b = -B, den = 2 * A;
    const g = gcd(gcd(b, k), den);
    b /= g; k /= g; den /= g;
    if (den < 0) { b = -b; k = -k; den = -den; }
    const surd = `${Math.abs(k) === 1 ? '' : Math.abs(k)}${m === 1 ? '' : `\\sqrt{${m}}`}${D < 0 ? 'i' : ''}`;
    for (const [i, sign] of [[0, '+'], [1, '-']]) {
      const s = k < 0 ? (sign === '+' ? '-' : '+') : sign;
      const num = b === 0 ? `${s === '-' ? '-' : ''}${surd}` : `${b} ${s} ${surd}`;
      roots[i].tex = den === 1 ? num : `\\frac{${num}}{${den}}`;
    }
    return roots;
  }

  // all complex roots numerically (Durand–Kerner, then Newton polish)
  function durandKerner(c) {
    const n = c.length - 1, lead = c[n];
    const a = c.map((v) => v / lead);
    const mul = (x, y) => ({ re: x.re * y.re - x.im * y.im, im: x.re * y.im + x.im * y.re });
    const div = (x, y) => { const d = y.re * y.re + y.im * y.im; return { re: (x.re * y.re + x.im * y.im) / d, im: (x.im * y.re - x.re * y.im) / d }; };
    const sub = (x, y) => ({ re: x.re - y.re, im: x.im - y.im });
    const evalAt = (z, coef) => coef.reduceRight((acc, v) => ({ re: acc.re * z.re - acc.im * z.im + v, im: acc.re * z.im + acc.im * z.re }), { re: 0, im: 0 });
    let z = Array.from({ length: n }, (_, k) => {
      let p = { re: 1, im: 0 };
      for (let j = 0; j < k; j++) p = mul(p, { re: 0.4, im: 0.9 });
      return p;
    });
    for (let iter = 0; iter < 800; iter++) {
      z = z.map((zi, i) => {
        let den = { re: 1, im: 0 };
        z.forEach((zj, j) => { if (j !== i) den = mul(den, sub(zi, zj)); });
        return sub(zi, div(evalAt(zi, a), den));
      });
    }
    const da = a.slice(1).map((v, i) => v * (i + 1));
    return z.map((zi) => {
      for (let k = 0; k < 20; k++) {
        const d = evalAt(zi, da);
        if (Math.hypot(d.re, d.im) < 1e-14) break;
        zi = sub(zi, div(evalAt(zi, a), d));
      }
      return zi;
    });
  }

  function polyRoots(coeffs) {
    let c = coeffs.slice();
    const roots = [];
    while (c.length > 1 && Math.abs(c[0]) < EPS) { roots.push(real(0)); c.shift(); }
    const ints = integerCoeffs(c);
    if (ints) {
      c = ints;
      // peel off rational roots until a quadratic (or less) remains
      let found = true;
      while (c.length > 3 && found && Math.abs(c[0]) <= 1e7 && Math.abs(c[c.length - 1]) <= 1e7) {
        found = false;
        search:
        for (const p of divisors(c[0])) for (const q of divisors(c[c.length - 1])) for (const sp of [p, -p]) {
          if (gcd(sp, q) === 1 && isRationalRoot(c, sp, q)) {
            roots.push(real(sp / q)); c = divideLinear(c, sp, q); found = true;
            break search;
          }
        }
      }
    }
    const deg = c.length - 1;
    if (deg === 1) roots.push(real(-c[0] / c[1]));
    else if (deg === 2) roots.push(...quadratic(c, !!ints));
    else if (deg > 2) {
      for (const z of durandKerner(c)) {
        const snap = (v) => { const f = toFraction(v, 100, 1e-7); return f ? f[0] / f[1] : v; };
        roots.push(Math.abs(z.im) < 1e-7 ? real(snap(z.re)) : { re: snap(z.re), im: snap(z.im) });
      }
    }
    return roots;
  }

  // merge repeated roots, real ones first and in order
  function groupRoots(roots) {
    const out = [];
    for (const r of roots) {
      const same = out.find((o) => Math.abs(o.re - r.re) < 1e-6 && Math.abs(o.im - r.im) < 1e-6);
      if (same) same.mult++; else out.push({ ...r, mult: 1 });
    }
    return out.sort((a, b) => (Math.abs(a.im) > EPS) - (Math.abs(b.im) > EPS) || a.re - b.re || b.im - a.im);
  }

  const rootTex = (r) => r.tex || complexTex(r.re, r.im);

  // a·(q₁x − p₁)^m₁ … when every root is real and rational
  function factoredTex(coeffs, groups, name) {
    const deg = coeffs.length - 1;
    if (deg < 2 || groups.some((g) => Math.abs(g.im) > EPS || g.tex)) return null;
    let k = coeffs[deg];
    const parts = [];
    for (const g of groups) {
      const f = toFraction(g.re, 1000);
      if (!f) return null;
      const [p, q] = f;
      k /= q ** g.mult;
      const lin = p === 0 ? name : `${q === 1 ? '' : q}${name} ${p < 0 ? '+' : '-'} ${Math.abs(p)}`;
      const wrap = p === 0 ? lin : `\\left(${lin}\\right)`;
      parts.push(g.mult > 1 ? `${wrap}^{${g.mult}}` : wrap);
    }
    if (parts.length === 1 && groups[0].mult === 1) return null;
    const lead = isInt(k) && Math.round(k) === 1 ? '' : isInt(k) && Math.round(k) === -1 ? '-' : numTex(k);
    return lead + parts.join('');
  }

  // ---------- numeric fallback for anything else ----------
  function numericRoots(node, name) {
    const f = node.compile();
    const at = (x) => {
      try { const y = f.evaluate({ [name]: x }); return typeof y === 'number' ? y : NaN; } catch { return NaN; }
    };
    const xs = [];
    for (let i = -2000; i <= 2000; i++) xs.push(i / 20);
    for (let i = 101; i <= 10000; i++) { xs.push(i); xs.push(-i); }
    xs.sort((a, b) => a - b);
    const roots = [];
    const add = (r) => {
      if (!(Math.abs(at(r)) < 1e-6)) return;
      r = Math.round(r * 1e10) / 1e10;
      if (!roots.some((s) => Math.abs(s - r) < 1e-7)) roots.push(r);
    };
    for (let i = 0; i < xs.length - 1; i++) {
      let a = xs[i], b = xs[i + 1], fa = at(a);
      const fb = at(b);
      if (fa === 0) { add(a); continue; }
      if (!isFinite(fa) || !isFinite(fb) || fa * fb > 0) continue;
      for (let k = 0; k < 80; k++) {
        const m = (a + b) / 2, fm = at(m);
        if (fa * fm <= 0) b = m; else { a = m; fa = fm; }
      }
      add((a + b) / 2);
    }
    return roots;
  }

  // ---------- rows ----------
  function rootRows(node, name, label) {
    const poly = polynomial(node, name);
    if (!poly) {
      const roots = numericRoots(node, name);
      if (!roots.length) return [{ label, tex: '\\text{no real solution}' }];
      const shown = roots.slice().sort((a, b) => Math.abs(a) - Math.abs(b)).slice(0, 6).sort((a, b) => a - b);
      const tex = shown.map((r) => {
        const f = toFraction(r, 100, 1e-10);
        return f && Math.abs(node.evaluate({ [name]: f[0] / f[1] })) < 1e-12
          ? `${name} = ${numTex(f[0] / f[1])}` : `${name} \\approx ${decimal(r)}`;
      }).join(',\\quad ');
      return [{ label: roots.length > shown.length ? `${label} (closest to 0)` : label, tex }];
    }
    const { coeffs } = poly;
    if (coeffs.length === 1) {
      return [{ label, tex: Math.abs(coeffs[0]) < EPS ? `\\text{every } ${name} \\text{ works}` : '\\text{no solution}' }];
    }
    const groups = groupRoots(polyRoots(coeffs));
    const realG = groups.filter((g) => Math.abs(g.im) < EPS), cplx = groups.filter((g) => Math.abs(g.im) >= EPS);
    const rows = [];
    const list = (gs) => gs.map((g) => `${name} = ${rootTex(g)}`).join(',\\quad ');
    const plural = (n) => (n > 1 ? `${label}s` : label);
    if (realG.length) rows.push({ label: plural(realG.length), tex: list(realG) });
    if (realG.some((g) => g.tex)) {
      rows.push({ label: 'Decimal', tex: realG.map((g) => `${name} \\approx ${decimal(g.re)}`).join(',\\quad ') });
    }
    if (cplx.length) rows.push({ label: realG.length ? 'Complex' : `Complex ${plural(cplx.length).toLowerCase()}`, tex: list(cplx) });
    const factored = factoredTex(coeffs, groups, name);
    return { rows, factored, expanded: poly.expanded };
  }

  function unknowns(nodes) {
    const names = new Set();
    for (const n of nodes) n.traverse((c, path, parent) => {
      if (c.isSymbolNode && !(parent && parent.isFunctionNode && path === 'fn') && !(c.name in math)) names.add(c.name);
    });
    return [...names].sort((a, b) => (b === 'x') - (a === 'x'));
  }

  function solve(raw) {
    const text = raw.trim()
      .replace(/[×·]/g, '*').replace(/÷/g, '/').replace(/[−–]/g, '-')
      .replace(/²/g, '^2').replace(/³/g, '^3').replace(/π/g, 'pi').replace(/√/g, 'sqrt');
    const parts = text.split('=');
    if (parts.length > 2) throw new Error('Use at most one = sign');
    if (parts.some((p) => !p.trim())) throw new Error('Something is missing next to the = sign');
    const sides = parts.map((p) => math.parse(p));
    const problem = sides.map(toTex).join(' = ');
    const vars = unknowns(sides);
    const rows = [];

    if (vars.length > 1) {
      if (sides.length === 2) throw new Error(`Use one unknown, like x (found ${vars.join(', ')})`);
      const simp = toTex(math.simplify(sides[0]));
      rows.push(same(simp, problem)
        ? { label: 'Simplified', tex: '\\text{already as simple as it gets}' }
        : { label: 'Simplified', tex: simp });
      return { problem, rows };
    }

    if (sides.length === 1 && !vars.length) {
      const v = sides[0].evaluate();
      rows.push({ label: 'Answer', tex: valueTex(v) });
      if (typeof v === 'number' && !isInt(v) && isFinite(v) && toFraction(v, 100)) rows.push({ label: 'Decimal', tex: decimal(v) });
      return { problem, rows };
    }

    if (sides.length === 2 && !vars.length) {
      const ok = math.equal(sides[0].evaluate(), sides[1].evaluate());
      rows.push({ label: 'Check', tex: ok ? '\\text{true}' : '\\text{false}' });
      return { problem, rows };
    }

    const name = vars[0];
    if (sides.length === 1) {
      // an expression in x: tidy it up, factor it, find where it is 0
      const node = sides[0];
      const res = rootRows(node, name, 'Root');
      if (Array.isArray(res)) {
        const simp = toTex(math.simplify(node));
        if (!same(simp, problem)) rows.push({ label: 'Simplified', tex: simp });
        rows.push(...res);
      } else {
        const exp = toTex(res.expanded);
        if (!same(exp, problem)) rows.push({ label: 'Expanded', tex: exp });
        if (res.factored) rows.push({ label: 'Factored', tex: res.factored });
        rows.push(...res.rows);
      }
      try {
        const d = math.derivative(node, name);
        let dTex;
        try { dTex = toTex(math.rationalize(d)); } catch { dTex = toTex(math.simplify(d)); }
        rows.push({ label: 'Derivative', tex: `\\frac{d}{d${name}} = ${dTex}` });
      } catch {}
      return { problem, rows };
    }

    // an equation: move everything to one side and solve
    const node = math.parse(`(${parts[0]}) - (${parts[1]})`);
    const res = rootRows(node, name, 'Solution');
    if (Array.isArray(res)) {
      rows.push(...res);
    } else {
      rows.push({ label: 'Rearranged', tex: `${res.factored || toTex(res.expanded)} = 0` });
      rows.push(...res.rows);
    }
    return { problem, rows };
  }

  global.solveProblem = solve;
})(typeof window !== 'undefined' ? window : globalThis);
