# Blueprint: the least prime in a residue class under GRH

Target (`BachSorenson/Statement.lean`, fixed):

```lean
def BachSorensonBound (c : ℝ) : Prop :=
  ∀ q a : ℕ, 2 ≤ q → a.Coprime q →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * ((q : ℝ) * Real.log q) ^ 2
```

Bach–Sorenson (Math. Comp. 65 (1996)) state it with `c = 2`. Proved here: `c = 7/2`.

Notation: `w(n) = 1 − n/x`, `bachSum χ x = Σ_{n<x} Λ(n) χ(n) w(n)` (erdos-985),
`T(a, x) = Σ_{n<x, n ≡ a} Λ(n) w(n)`, `B(q, x) = (√x + 2 + 3/x)(2/3)(log q + 5/3) + log x + 1.6`.

## Steps

1. **Primitive characters** (ankeny-grh `Ankeny.norm_bachSum_le`, reused). For `ψ` primitive
   non-trivial mod `f`, under GRH, `‖bachSum ψ x‖ ≤ (√x + 2 + 3/x)(2/3)(log f + 5/3) + log x + 1.6`.

2. **Any non-principal character** (`BachSorenson/Character.lean`).
   ```lean
   theorem norm_bachSum_le_charBound (hGRH) {q} [NeZero q] (χ : DirichletCharacter ℂ q)
       (hχ : χ ≠ 1) (x : ℕ) (hx : 144 ≤ x) : ‖bachSum χ x‖ ≤ charBound q x
   ```
   `bachSum χ − bachSum ψ` lives on prime powers `p^k`, `p | q`, `p ∤ f`: at most
   `(2/3)√x Σ_{p∈R} log p` (`Nat.log p x ≤ (2/3)√x` for `x ≥ 144`), absorbed by
   `log f + Σ_{p∈R} log p ≤ log q`.

3. **Orthogonality** (`BachSorenson/Orthogonality.lean`).
   ```lean
   lemma classSum_orthogonality (ha : IsUnit a) (x) :
       (q.totient : ℂ) * classSum q a x = ∑ χ, χ a⁻¹ * bachSum χ x
   theorem totient_mul_classSum_ge (hGRH) (ha : IsUnit a) (x) (hx : 144 ≤ x) :
       x/2 − √x/20 − 3 − ω(q) log x − (φ(q) − 1) B(q, x) ≤ φ(q) T(a, x)
   ```
   Principal character: erdos-985 `bach_principal_of_GRH`
   (`|Σ_{n<x} Λ(n) w(n) − x/2| ≤ √x/20 + 3`) minus the `n` not coprime to `q` (`≤ ω(q) log x`).

4. **Prime powers that are not primes** (`BachSorenson/PrimePowers.lean`).
   ```lean
   theorem ppSum_le (x) (hx : 2 ≤ x) : ppSum x ≤ ppBound x
   -- ppBound x = log 4 · (√x + x^{1/3} + x^{1/4} log x / log 2)
   ```
   `ψ − θ = Σ_{2≤k≤log₂ x} θ(x^{1/k})` (Mathlib `psi_eq_theta_add_sum_theta`) and
   `θ(y) ≤ y log 4` (Mathlib `theta_le_log4_mul_x`).

5. **One modulus** (`BachSorenson/Large.lean`). With `x = ⌊c (q log q)²⌋`, if no prime `p < x` is
   `≡ a`, then `T(a, x) ≤ ppSum x`, and with `φ(q) ≤ q`:
   `x/2 − √x/20 − 3 − ω log x ≤ q (B(q, x) + ppBound x)`. `NumericOK c q` is the negation.
   ```lean
   theorem bachSorenson_of_numericOK (hGRH) (hc : 0 ≤ c) (hq : 2 ≤ q) (hnum : NumericOK c q)
       (ha : a.Coprime q) : ∃ p, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) < c * (q * log q) ^ 2
   ```

6. **Numerics** (`BachSorenson/Numerics.lean`): `numericOK_of_ge : 2^15 ≤ q → NumericOK (7/2) q`.
   Bounds used: `s = √x ≥ 637000`, `1.8708 q log q < s + 1`, `L + 5/3 ≤ 1.1604 L`,
   `x^{1/3} ≤ s/86`, `x^{1/4} log x ≤ 0.03434 s` (tangent of `log` at `512`), `ω(q) ≤ q`. The
   result is a quadratic in `s` with leading coefficient `0.4892 < 1/2`.

7. **Checker soundness** (`BachSorensonCheck.lean`, `BachSorenson/Checker.lean`).
   ```lean
   theorem exists_prime_of_checkRange (h : checkRange N lo n = true) (hq1 : lo ≤ q)
       (hq2 : q < lo + n) (hq : 2 ≤ q) (ha : a.Coprime q) :
       ∃ p, p.Prime ∧ p ≡ a [MOD q] ∧ p < bound q
   lemma bound_le (q) (hq : q ≠ 0) : (bound q : ℝ) ≤ 7/2 * (q * log q) ^ 2
   ```
   Prime table by trial division (sound: a `true` entry is prime, via `Nat.minFac_sq_le_self`);
   for each `a < q` coprime to `q` the walk `a, a + q, …` below `bound q` hits a table prime.
   `bound q = ⌊(7/2) q² (⌊log₂ q⁸⌋ · 0.6931471803 / 8)²⌋`.

8. **Finite range** (`BachSorenson/Compute.lean`): 16 `native_decide` chunks of 2048 moduli
   cover `q < 2^15`, prime table of size `8·10^6` (the largest least prime needed is below it).

9. **Assembly** (`BachSorenson/Main.lean`): `bachSorenson_of_GRH : BachSorensonBound (7/2)`.

## Sizing (outside Lean, `exact` real arithmetic)

Smallest `q` beyond which the inequality of step 5 holds for every larger `q`, with the bounds of
steps 2–4 and exact `ω(q)`:

| c   | 8  | 6   | 5   | 4    | 3.8  | 3.6   | 3.5   | 3.4   | 3.2   | 3      | 2         |
|-----|----|-----|-----|------|------|-------|-------|-------|-------|--------|-------------|
| q₀  | 143| 464 | 670 | 3477 | 5884 | 11251 | 16518 | 25560 | 74761 | 321956 | ~10^28    |

The finite check costs about `Σ_{q<Q₀} φ(q) · (steps per class)`: `1.2·10^8` table lookups for
`Q₀ = 2^13`, about `2·10^9` for `2^15`. At `2^15` the Lean-provable margin (uniform constants
for all `q ≥ Q₀`) is comfortable for `c = 7/2` (leading coefficient `0.489`).

Asymptotically the argument compares `x/(2φ)` with `(2/3)√x log q + log 4 · √x` per unit, so it
needs `√c > (4/3)(1 + O(1/log q))`: `c > 16/9` in the limit, and `c = 2` only once
`log q ≳ 64` (`q ≳ 10^28`). Reaching Bach–Sorenson's `2` for all `q` would need their sharper explicit
formula; see the README.
