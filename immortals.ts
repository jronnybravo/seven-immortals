/**
 * Reference enumerator for the bounded-inbreeding pedigree problem (sexless nodes).
 *
 * Nodes are founders 0..n-1 (the paper's founders 1..n) or children {P, Q} of two
 * distinct nodes. rel(x, y) is the additive relationship of x and y (twice their
 * coancestry); the child Z of P and Q is legal iff F_Z = rel(P, Q) / 2 <= f. Legality
 * depends only on the ancestry of P and Q, so the closure below does not depend on
 * mating order. Running the file calls verify(), which asserts the computational
 * claims listed in the Appendix. Needs Node.js 22.18 or later, and no packages.
 */

/** Exact rational p/q in lowest terms, with q > 0. */
class Frac {
    readonly p: bigint;
    readonly q: bigint;
    constructor(p: bigint, q: bigint = 1n) {
        if (q < 0n) [p, q] = [-p, -q];
        let [a, b] = [p < 0n ? -p : p, q];
        while (b) [a, b] = [b, a % b];
        this.p = p / a;
        this.q = q / a;
    }
    add(o: Frac): Frac { return new Frac(this.p * o.q + o.p * this.q, this.q * o.q); }
    sub(o: Frac): Frac { return new Frac(this.p * o.q - o.p * this.q, this.q * o.q); }
    mul(o: Frac): Frac { return new Frac(this.p * o.p, this.q * o.q); }
    div(o: Frac): Frac { return new Frac(this.p * o.q, this.q * o.p); }
    cmp(o: Frac): number { const d = this.p * o.q - o.p * this.q; return d < 0n ? -1 : d > 0n ? 1 : 0; }
    eq(o: Frac): boolean { return this.p === o.p && this.q === o.q; }
    abs(): Frac { return this.p < 0n ? new Frac(-this.p, this.q) : this; }
}
const frac = (p: number, q = 1): Frac => new Frac(BigInt(p), BigInt(q));
const ZERO = frac(0), ONE = frac(1), HALF = frac(1, 2);
const maxOf = (xs: Frac[]): Frac => xs.reduce((a, x) => (x.cmp(a) > 0 ? x : a));

const range = (a: number, b: number): number[] => Array.from({ length: Math.max(0, b - a) }, (_, i) => a + i);
const pop = (m: number): number => { let c = 0; for (; m; m &= m - 1) c++; return c; };
/** m!!, with m!! = 1 for m <= 0. */
const doubleFactorial = (m: number): number => { let p = 1; for (let i = m; i > 0; i -= 2) p *= i; return p; };
const factorial = (m: number): number => doubleFactorial(m) * doubleFactorial(m - 1);
const comb = (n: number, k: number): number => { let c = 1; for (let i = 1; i <= k; i++) c = (c * (n - k + i)) / i; return c; };

function check(ok: boolean, claim: string): void {
    if (!ok) throw new Error(`claim failed: ${claim}`);
}

/**
 * Close n founders under legal matings. A[i] holds the relationships of node i with
 * nodes 0..i, so the matrix is stored once and is symmetric by construction.
 * ordered = true is the hermaphroditic variant: (P, Q) and (Q, P) are different children.
 * The run stops at the first legal mating with F > 0 and returns N = Infinity: by
 * Theorem 2 such a mating needs f >= 2^-n, and Theorem 1 then gives infinitely many
 * nodes. Every mating performed therefore has F = 0, so every node lies in S_0(n),
 * and doubles are exact: each coefficient is a dyadic rational with denominator
 * <= 2^(2n-2), so the test rel(P, Q) <= 2f needs no tolerance.
 */
function saturate(n: number, f: number, ordered = false) {
    const A: Float64Array[] = [];
    const sup: number[] = [];                                  // bitmask of founder support
    for (let i = 0; i < n; i++) {
        A.push(new Float64Array(i + 1));
        A[i][i] = 1;
        sup.push(1 << i);
    }
    const rel = (i: number, j: number): number => (i >= j ? A[i][j] : A[j][i]);
    const tol = 2 * f;                                         // legal iff rel(P, Q) <= 2f
    const qP: number[] = [], qQ: number[] = [];
    for (let i = 0; i < n; i++)
        for (let j = 0; j < n; j++)
            if (i < j || (ordered && i !== j)) { qP.push(i); qQ.push(j); }
    for (let t = 0; t < qP.length; t++) {                      // the queue grows while we iterate
        const P = qP[t], Q = qQ[t];
        check((sup[P] & sup[Q]) === 0, "every mating performed has F = 0");
        const z = A.length;
        const row = new Float64Array(z + 1);                   // relationship of the child to everyone
        for (let x = 0; x < z; x++) row[x] = (rel(P, x) + rel(Q, x)) / 2;
        row[z] = 1 + rel(P, Q) / 2;
        A.push(row);
        sup.push(sup[P] | sup[Q]);
        for (let x = 0; x < z; x++) {
            if (row[x] > tol) continue;                        // the new node may mate with x
            if (row[x] > 0) return { N: Infinity, A, sup, inbredF: row[x] / 2 };
            qP.push(z); qQ.push(x);
            if (ordered) { qP.push(x); qQ.push(z); }
        }
    }
    return { N: A.length, A, sup, inbredF: 0 };
}

/**
 * On every pair of S_0(n): Lemma 1 (A > 0 iff supports meet), Lemma 2
 * (A >= 2^-(|supp X u supp Y| - 1) when they meet) and denominators <= 2^(2n-2).
 * The pairs j <= i cover every ordered pair, because the matrix is symmetric.
 */
function pairChecks(A: Float64Array[], sup: number[], n: number) {
    const bound = range(0, 1 << n).map((m) => 2 ** -(pop(m) - 1));
    const scale = 2 ** (2 * n - 2);
    let lemmas = true, dyadic = true, low = Infinity;
    for (let i = 0; i < A.length; i++) {
        const row = A[i];
        for (let j = 0; j <= i; j++) {
            const a = row[j], meet = (sup[i] & sup[j]) !== 0;
            if (a > 0 !== meet || (meet && a < bound[sup[i] | sup[j]])) lemmas = false;
            if (!Number.isInteger(a * scale)) dyadic = false;
            if (a > 0 && a < low) low = a;
        }
    }
    return { lemmas, dyadic, low };
}

/** Exact relationship matrix of n founders, and mate(p, q), which appends their child. */
function pedigree(n: number) {
    const A: Frac[][] = range(0, n).map((i) => range(0, n).map((j) => (i === j ? ONE : ZERO)));
    function mate(p: number, q: number): [number, Frac] {      // append the child {p, q}; return [index, F]
        const F = A[p][q].mul(HALF);
        const row = A.map((_, x) => A[p][x].add(A[q][x]).mul(HALF));
        row.forEach((r, x) => A[x].push(r));
        A.push([...row, ONE.add(F)]);
        return [A.length - 1, F];
    }
    return { A, mate };
}

/**
 * Theorem 1's chain c_1, ..., c_steps in exact arithmetic. Returns the F of each
 * mating, and whether every mating after c_1 used a founder least related to the
 * current node. Code founder i is the paper's founder i + 1.
 */
function chain(n: number, steps: number): [Frac[], boolean] {
    const { A, mate } = pedigree(n);
    let [cur, F] = mate(0, 1);                                 // c_1 = {1, 2}
    const founders = [...range(2, n), 0];
    for (let s = 0; s < steps; s++) founders.push(...range(1, n), 0);
    const Fs = [F];                                            // Fs[k-1] = F of c_k
    let greedy = true;
    for (const j of founders.slice(0, steps - 1)) {            // founders 3..n, then 1, then 2..n, 1, ...
        const least = A[cur].slice(0, n).reduce((a, x) => (x.cmp(a) < 0 ? x : a));
        greedy &&= A[cur][j].eq(least);
        [cur, F] = mate(cur, j);
        Fs.push(F);
    }
    return [Fs, greedy];
}

/**
 * Shepherd and Woolliams' dam line on n founders: founder 1 is the dam and
 * founders 2..n are sires used in rotation. Returns the F of each mating.
 */
function frozenSemenLine(n: number, steps: number): Frac[] {
    const { mate } = pedigree(n);
    let cur = 0;
    const Fs: Frac[] = [];
    for (let t = 0; t < steps; t++) {
        const [child, F] = mate(cur, 1 + (t % (n - 1)));
        cur = child;
        Fs.push(F);
    }
    return Fs;
}

/** Proposition 1: sum_k C(n,k) (2k-3)!!, with (-1)!! = 1. */
const L0 = (n: number): number => range(1, n + 1).reduce((s, k) => s + comb(n, k) * doubleFactorial(2 * k - 3), 0);

/** Hermaphroditic variant (Section 5): sum_k C(n,k) (2k-2)!/(k-1)!. */
const L0Hermaphroditic = (n: number): number =>
    range(1, n + 1).reduce((s, k) => s + (comb(n, k) * factorial(2 * k - 2)) / factorial(k - 1), 0);

/** The checks on S_0(n) behind one row of Table 2; returns L(n, 0) and the smallest positive A. */
function zeroPopulation(n: number) {
    const { N, A, sup } = saturate(n, 0);
    check(N === L0(n), `Proposition 1, n=${n}`);
    const perSupport = range(1, n + 1).map((k) => sup.filter((s) => pop(s) === k).length);
    const expected = range(1, n + 1).map((k) => comb(n, k) * doubleFactorial(2 * k - 3));
    check(perSupport.join() === expected.join(), `Proposition 1, count per support size, n=${n}`);
    const { lemmas, dyadic, low } = pairChecks(A, sup, n);
    check(lemmas, `Lemmas 1 and 2, n=${n}`);
    check(low === 2 ** -(n - 1), `Lemma 2 is tight, n=${n}`);
    check(dyadic, `Section 6: denominators <= 2^(2n-2), n=${n}`);
    return { N, low };                                         // the matrix is freed on return
}

/** Assert the checks behind one row of Table 2 (Section 6); return the row. */
function tableRow(n: number): string {
    const { N, low } = zeroPopulation(n);
    const below = saturate(n, 2 ** -n * (1 - 1e-7)).N;         // with the min-A check above,
    check(below === N, `Theorem 2, n=${n}`);                   // this covers every f < 2^-n
    const at = saturate(n, 2 ** -n);
    check(at.N === Infinity && at.inbredF === 2 ** -n, `inbred mating legal at f = 2^-n, n=${n}`);
    return `${n}  ${String(N).padEnd(7)} ${String(low).padEnd(9)} ${"hold".padEnd(7)} ${String(below).padEnd(11)} inf (F = ${at.inbredF})`;
}

/** Assert the computational claims listed in the Appendix; print Table 2 of Section 6. */
function verify(): void {
    check(range(2, 8).map(L0).join() === "3,9,37,225,1881,19873", "Table 1 of Section 3 (OEIS A220452)");
    check(range(2, 8).map(L0Hermaphroditic).join() === "4,21,184,2425,42396,916909",
        "hermaphroditic counts of Section 5 (OEIS A224500)");

    {
        const { A, mate } = pedigree(3);                       // Section 2 reference values
        const [q1] = mate(0, 1), [q2] = mate(0, 2);
        check(A[0][q1].mul(HALF).eq(frac(1, 4)) && A[q1][q2].mul(HALF).eq(frac(1, 8)),
            "Section 2: parent-child F = 1/4, half-sibling F = 1/8");
    }

    const b = range(0, 13).map((k) => frac(doubleFactorial(2 * k - 3), factorial(k)));
    for (let k = 1; k < 13; k++) {                             // Section 3: B = 1 - sqrt(1 - 2x)
        let sqrtCoef = ONE;
        for (let i = 0; i < k; i++) sqrtCoef = sqrtCoef.mul(HALF.sub(frac(i)));
        sqrtCoef = sqrtCoef.div(frac(factorial(k))).mul(frac((-2) ** k));
        check(ZERO.sub(sqrtCoef).eq(b[k]), `Section 3: coefficient of x^${k}`);
        if (k >= 2) {
            const sum = range(1, k).reduce((s, i) => s.add(b[i].mul(b[k - i])), ZERO);
            check(b[k].eq(sum.mul(HALF)), `Section 3: B = x + B^2/2 at x^${k}`);
        }
    }

    console.log("n  L(n,0)  min A>0   Lemmas  below 2^-n  at 2^-n");
    for (let n = 2; n <= 7; n++) console.log(tableRow(n));
    check([1 / 16, 1 / 14, 1 / 12].every((f) => saturate(3, f).N === 9), "Section 6: n = 3 examples");
    check([1 / 32, 1 / 24].every((f) => saturate(4, f).N === 37), "Section 6: n = 4 examples");

    for (let n = 2; n < 6; n++) {                              // hermaphroditic variant (Sec. 5 remark)
        const { N, A, sup } = saturate(n, 0, true);
        check(N === L0Hermaphroditic(n) && pairChecks(A, sup, n).lemmas, `hermaphroditic S_0, n=${n}`);
        check(saturate(n, 2 ** -n * (1 - 1e-7), true).N === N, `hermaphroditic Theorem 2, n=${n}`);
        const at = saturate(n, 2 ** -n, true);
        check(at.N === Infinity && at.inbredF === 2 ** -n, `hermaphroditic inbred mating at f = 2^-n, n=${n}`);
    }

    {
        const { mate } = pedigree(1);                          // Sec. 5 remark: self once, then backcross
        let [cur, F] = mate(0, 0);
        const Fs = [F];
        for (let t = 0; t < 30; t++) {
            [cur, F] = mate(cur, 0);
            Fs.push(F);
        }
        check(Fs.every((x) => x.eq(HALF)), "Section 5: selfing once, then backcrossing to the founder, keeps F = 1/2");
    }

    {
        const { A, mate } = pedigree(3);                       // Sec. 5 remark: X = {{1,2},3}, Y = {{1,3},2}
        const [x12] = mate(0, 1), [x13] = mate(0, 2);
        const [X] = mate(x12, 2), [Y] = mate(x13, 1);
        const terms = range(0, 3).map((i) => A[X][i].mul(A[Y][i]).mul(HALF));  // one path per shared founder
        const total = terms.reduce((s, x) => s.add(x), ZERO);
        check(A[X][Y].mul(HALF).eq(total) && total.eq(frac(5, 32)) && maxOf(terms).eq(frac(1, 16)),
            "Section 5: several paths are needed");
    }

    const within = (x: Frac, y: Frac, bits: number): boolean =>  // |x - y| < 2^-bits
        x.sub(y).abs().cmp(new Frac(1n, 1n << BigInt(bits))) < 0;
    for (let n = 2; n < 8; n++) {                              // Theorem 1's chain, exact
        const [Fs, greedy] = chain(n, 40 * n);
        check(Fs.slice(0, n - 1).every((F) => F.eq(ZERO)), `c_1..c_(n-1) have F = 0, n=${n}`);
        check(Fs[n - 1].eq(maxOf(Fs)) && Fs[n - 1].eq(frac(1, 2 ** n)), `Theorem 1, n=${n}`);
        check(Fs[n].eq(frac(1, 2 ** (n + 1))), `F(c_(n+1)) in Sec. 4, n=${n}`);
        const after = maxOf(Fs.slice(n));                      // Sec. 6: every mating after c_n
        check(after.eq(frac(2 ** (n - 1) + 1, 2 ** (2 * n))), `max F after c_n = (1 + 2^-(n-1))/2^(n+1), n=${n}`);
        const q = n === 3 ? 12 : n === 4 ? 24 : 0;             // Sec. 6: f = 1/12 for n = 3, 1/24 for n = 4
        if (q) check(after.cmp(frac(1, q)) <= 0 && Fs[n - 1].cmp(frac(1, q)) > 0,
            `Section 6: at f = 1/${q} every chain mating except c_n is legal`);
        check(within(Fs[Fs.length - 1], frac(1, 2 ** (n + 1) - 2), 30 * n), `chain limit, n=${n}`);
        check(greedy, `least related founder, n=${n}`);
        const Fsw = frozenSemenLine(n, 40 * n);
        const first = Fsw.find((F) => !F.eq(ZERO));
        check(first !== undefined && first.eq(frac(1, 2 ** n)), `frozen-semen first F, n=${n}`);
        const rising = Fsw.filter((F) => !F.eq(ZERO));
        check(rising.every((F, i) => i === 0 || rising[i - 1].cmp(F) <= 0), `frozen-semen F rises, n=${n}`);
        const top = maxOf(Fsw);
        check(top.cmp(frac(1, 2 ** n)) > 0 && top.cmp(frac(1, 2 ** n - 2)) <= 0, `frozen-semen maximum, n=${n}`);
        check(within(Fsw[Fsw.length - 1], frac(1, 2 ** n - 2), 30 * n), `frozen-semen limit, n=${n}`);
    }

    for (let m = 1; m <= 4096; m++) {                          // Corollary 1 at f = 1/m
        let least = 2;                                         // least n >= 2 with 2^-n <= f
        while (2 ** least < m) least++;
        const bitLength = m === 1 ? 0 : 32 - Math.clz32(m - 1); // ceil(log2 m)
        check(least === Math.max(2, bitLength), `n_min, f = 1/${m}`);
    }
    console.log("All claims verified.");
}

verify();
