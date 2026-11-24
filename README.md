# The least prime in a residue class under GRH in Lean

E. Bach and J. Sorenson (*Explicit bounds for primes in residue classes*, Math. Comp. 65 (1996),
1717–1735) proved, assuming the Extended Riemann Hypothesis, that if `gcd(a, q) = 1` the least
prime `p ≡ a (mod q)` is less than `2 (q log q)²`, and asymptotically at most
`(1 + o(1)) (φ(q) log q)²`. Unconditionally only Linnik-type bounds `p ≪ q^L` are known
(Xylouris: `L = 5`).

**Literature status: RH-consequence.** The GRH ⇒ `2 (q log q)²` bound is Bach–Sorenson (1996,
constant 2). This is a Lean proof that GRH implies a bound of this shape, following Bach and
Sorenson; our constant `7/2` is weaker than their `2`. It is not new mathematics.

This repository proves, assuming GRH for Dirichlet L-functions
(`Erdos985.DirichletLNonvanishingRightOfHalf`, copied verbatim from
[leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
`src/Statements.lean`):

```lean
def BachSorenson.BachSorensonBound (c : ℝ) : Prop :=
  ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2

theorem BachSorenson.bachSorenson_of_GRH (hGRH : DirichletLNonvanishingRightOfHalf) :
    BachSorensonBound (7 / 2)
```

So, under GRH, **for every `q ≥ 2` and every `a` coprime to `q` there is a prime `p ≡ a (mod q)`
with `p < 3.5 (q log q)²`**. This is Bach–Sorenson's theorem with the constant `2` replaced by
`7/2` (see "Deviations from the literature"). `BachSorensonBound 2`, the literature statement,
is not proved. There is no `sorry`.

## Tier and provenance

| Theorem | Tier | Hypotheses |
|---|---|---|
| `BachSorenson.bachSorenson_of_GRH` | C | `DirichletLNonvanishingRightOfHalf` (erdos-985, copied verbatim from riemann-hypothesis) |
| `bachSorenson_unconditional` (`Unconditional/`) | U | none |

`BachSorenson/Statement.lean` holds the target `BachSorensonBound c`; `c = 2` is the paper's
constant. The requirement `2 ≤ q` is there because for `q = 1` the right-hand side is
`c (1 · log 1)² = 0`. formal-conjectures has no statement of this theorem.

## Axioms

Real output of `#print axioms` (`lake env lean`, 2026-11-24, after `lake build`):

```
'BachSorenson.bachSorenson_of_GRH' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BachSorenson.chunk_ok_0._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_1._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_10._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_11._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_12._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_13._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_14._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_15._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_2._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_3._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_4._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_5._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_6._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_7._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_8._native.native_decide.ax_1_1,
 BachSorenson.chunk_ok_9._native.native_decide.ax_1_1]
'BachSorenson.bachSorenson_of_numericOK' depends on axioms: [propext, Classical.choice, Quot.sound]
'BachSorenson.numericOK_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The 16 `native_decide` axioms come from the finite computation for `2 ≤ q < 2^15`. Each one
asserts that the compiled evaluation of the core-Lean checker `checkRange` on one chunk of 2048
moduli agrees with its definition. The checker builds a table of the primes below `8·10^6` by
trial division and then, for every `a < q` coprime to `q`, walks `a, a + q, a + 2q, …` until it
hits a table prime below `⌊(7/2) q² (⌊log₂ q⁸⌋ log 2 / 8)²⌋`. Its soundness
(`BachSorenson.Checker.exists_prime_of_checkRange`) is proved in Lean. The chunks take 8 to 40 s
each, about 6.5 CPU-minutes in total. The analytic half (`q ≥ 2^15`) uses only the standard
three axioms. ankeny-grh's own `native_decide` axioms do not appear: only its analytic modules
are imported.

## Proof outline

The analytic toolkit (weighted explicit formula, zero-sum bound under GRH, principal-character
bound) is [erdos-985](https://github.com/senamakel/erdos-985); the primitive-character bound and
the prime-power lemmas come from [ankeny-grh](https://github.com/senamakel/ankeny-grh). Both are
lake dependencies. The full blueprint, with each step's Lean statement, is
[`docs/BLUEPRINT.md`](docs/BLUEPRINT.md). Write `w(n) = 1 − n/x`.

1. `BachSorenson/Character.lean`: for any non-trivial `χ` mod `q` and `x ≥ 144`,
   `‖Σ_{n<x} Λ(n) χ(n) w(n)‖ ≤ B(q, x) = (√x + 2 + 3/x)(2/3)(log q + 5/3) + log x + 1.6`.
   This is `Ankeny.norm_bachSum_le` for the inducing primitive character plus the prime powers
   of primes dividing `q` but not the conductor, absorbed as in `Ankeny.key_inequality`.
2. `BachSorenson/Orthogonality.lean`: with `T(a, x) = Σ_{n<x, n≡a} Λ(n) w(n)`,
   `φ(q) T(a, x) = Σ_χ χ(a⁻¹) Σ_{n<x} Λ(n) χ(n) w(n)`, hence
   `φ(q) T(a, x) ≥ x/2 − √x/20 − 3 − ω(q) log x − (φ(q) − 1) B(q, x)`.
3. `BachSorenson/PrimePowers.lean`: prime powers that are not primes contribute at most
   `ψ(x) − θ(x) ≤ log 4 · (√x + x^{1/3} + x^{1/4} log x / log 2)` (Mathlib's Chebyshev bounds).
4. `BachSorenson/Large.lean`: with `x = ⌊c (q log q)²⌋`, if no prime below `x` is `≡ a`, then
   `x/2 − √x/20 − 3 − ω(q) log x ≤ q (B(q, x) + log 4 · (…))`.
5. `BachSorenson/Numerics.lean`: for `c = 7/2` and `q ≥ 2^15` that inequality fails (a quadratic
   in `s = √x` with leading coefficient `0.4892 < 1/2`).
6. `BachSorensonCheck.lean`, `BachSorenson/Checker.lean`, `BachSorenson/Compute*.lean`: every
   `2 ≤ q < 2^15` by the verified computation.
7. `BachSorenson/Main.lean`: assembly.

## Layout

| File | Content |
|---|---|
| `BachSorenson/Statement.lean` | target `BachSorensonBound c` (fixed) |
| `BachSorenson/Character.lean` | bound for a non-principal character of any modulus |
| `BachSorenson/Orthogonality.lean` | the class sum via orthogonality, lower bound under GRH |
| `BachSorenson/PrimePowers.lean` | `ψ(x) − θ(x)` bound |
| `BachSorenson/Large.lean` | `NumericOK c q` implies the bound at `q` |
| `BachSorenson/Numerics.lean` | `NumericOK (7/2) q` for `q ≥ 2^15` |
| `BachSorensonCheck.lean` | executable checker (core Lean, precompiled) |
| `BachSorenson/Checker.lean` | checker soundness, `bound q ≤ (7/2)(q log q)²` |
| `BachSorenson/Compute.lean`, `Compute/Chunk*.lean` | the 16 `native_decide` chunks |
| `BachSorenson/Main.lean` | `bachSorenson_of_GRH` |
| `Unconditional/BachSorensonUnconditional.lean` | GRH discharged by riemann-hypothesis |

## Deviations from the literature

The constant is `7/2` rather than Bach–Sorenson's `2`. The zero-sum bound available from
erdos-985 is `Σ_ρ 1/|ρ(ρ+1)| ≤ (2/3)(log f + 5/3)`, so each non-principal character costs
`(2/3)√x log q`, and the non-prime prime powers cost about `log 4 · √x` (Chebyshev's
`θ(y) ≤ y log 4`). Against the main term `x/(2φ(q))` this needs
`√c > (4/3)(1 + O(1/log q))`: `c > 16/9` in the limit, and the lower-order terms push the
modulus beyond which a given `c` works up fast. Sized outside Lean with the bounds used here:

| c  | 5   | 4    | 3.6    | 3.5    | 3.4    | 3.2    | 3       | 2         |
|----|-----|------|--------|--------|--------|--------|---------|-----------|
| q₀ | 670 | 3477 | 11 251 | 16 518 | 25 560 | 74 761 | 321 956 | ~10^28    |

Every `q < Q₀` must be covered by computation, which costs about `Σ_{q<Q₀} φ(q)` progression
walks: `2·10^9` table lookups at `Q₀ = 2^15`, growing like `Q₀²`. `c = 2` would need the sharper
explicit formula Bach and Sorenson use (a different weight, sharper zero-sum and gamma-factor
estimates). Redoing the erdos-985 analytic layer that way was out of scope.

The statement requires `2 ≤ q`, which the paper leaves implicit; for `q = 1` its bound is `0`.
The bound is strict, as in the paper.

## Building

```
lake exe cache get
lake build
```

Lean `v4.36.0`, Mathlib `fc4f59e5` (via erdos-985 `9538edb` and ankeny-grh `129ad57`).
Measured 2026-11-24 on a 95-core box with a warm Mathlib cache: building the erdos-985 and
ankeny-grh modules used took 1 min 21 s wall (255 CPU-s); the 16 `native_decide` chunks took
8, 9, 12, 14, 15, 20, 21, 23, 26, 25, 30, 33, 37, 39, 40 and 39 s (about 6.5 CPU-minutes);
`BachSorenson.Numerics` takes about 40 CPU-s.

## Unconditional version

`Unconditional/BachSorensonUnconditional.lean` imports [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)
(commit `507a75d`) and closes the hypothesis with its theorem `LFunction_ne_zero_of_half_lt_re`:

| Theorem | Statement | Axioms |
|---|---|---|
| `bachSorenson_unconditional` | `BachSorenson.BachSorensonBound (7 / 2)` | standard three + 16 `native_decide` |

Checked 2026-11-24 with `scripts/check-unconditional.sh` against riemann-hypothesis `507a75d91d`: the build succeeded and `#print axioms bachSorenson_unconditional` printed exactly `propext`, `Classical.choice`, `Quot.sound` and the 16 `BachSorenson.chunk_ok_N._native.native_decide.ax_1_1` axioms (no `sorryAx`). The run took 9 min wall, dominated by importing riemann-hypothesis.

To check it:

```bash
scripts/check-unconditional.sh /path/to/riemann-hypothesis   # cloned there if missing
```

The script uses that project's community cache, about 93 GB. The import opens around 900,000
module files and needs about 19 GB of RAM. Raise the open-file limit first; on Linux, for
example `sudo prlimit --pid $$ --nofile=2000000:2000000`; on macOS
`sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000`.

The riemann-hypothesis proof adds no axioms of its own. The cache contains outputs of untrusted
builds, so this links the proofs but does not re-verify the RH/GRH proof, whose independent
verification is still pending.

## Credits

No files are vendored. The analytic layer is used as lake dependencies:
[senamakel/erdos-985](https://github.com/senamakel/erdos-985) at `9538edb` and
[senamakel/ankeny-grh](https://github.com/senamakel/ankeny-grh) at `129ad57`.
`BachSorenson/Character.lean` follows `Ankeny.key_inequality` (ankeny-grh, `Ankeny/Split.lean`)
closely, adapted from a lower bound on the real part to a norm bound.
