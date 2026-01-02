import Mathlib

open scoped BigOperators
open Filter

namespace ErdosTuran

/-- `HasKAP A k` means `A ⊆ ℕ` contains a *nontrivial* `k`-term arithmetic progression,
i.e. there exist `a d` with `d > 0` and `a + i*d ∈ A` for all `i < k`. -/
def HasKAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i : Fin k, a + i.1 * d ∈ A

/-- The “harmonic series on `A`” as a full `ℕ`-series (terms outside `A` are `0`). -/
def harmonicTerm (A : Set ℕ) (n : ℕ) : ℝ :=
  if n ∈ A then (1 : ℝ) / n else 0

/-- Divergence of the harmonic series on `A`. -/
def HarmonicDiverges (A : Set ℕ) : Prop :=
  ¬ Summable (harmonicTerm A)

/-- Count of elements of `A` in the initial segment `[1..N]`. -/
def countUpTo (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).filter (fun n => n ∈ A)).card

/-- A monotonicity helper: if `B ⊆ A` and `B` has a `k`-AP then so does `A`. -/
lemma HasKAP.mono {A B : Set ℕ} {k : ℕ} (hBA : B ⊆ A) (hB : HasKAP B k) : HasKAP A k := by
  rcases hB with ⟨a, d, hdpos, hi⟩
  refine ⟨a, d, hdpos, ?_⟩
  intro i
  exact hBA (hi i)

/-
A condensation-style lemma you’ll use in the main proof.

Informal: If for large `m` we have `countUpTo A (2^(m+1)) ≤ C_m`,
then the partial harmonic sums up to `2^(M+1)` are bounded by
`∑_{m ≤ M} (C_m / 2^m)`, because on the block `[2^m, 2^(m+1))` we have `1/n ≤ 1/2^m`.

You can keep this lemma as a `sorry` initially and let Aristotle try to prove it,
or prove it yourself later and keep the main theorem clean.
-/
lemma summable_harmonic_of_dyadic_count_bound
    (A : Set ℕ) (C : ℕ → ℝ)
    (hC : ∀ᶠ m in atTop, (countUpTo A (2^(m+1)) : ℝ) ≤ C m)
    (hCsumm : Summable (fun m : ℕ => C m / (2^m : ℝ))) :
    Summable (harmonicTerm A) := by
  sorry

/--
**Erdős–Turán reduction (dyadic, conditional on an `r_k`-type bound).**

PROVIDED SOLUTION
Let `rBound : ℕ → ℕ` play the role of `r_k(N)` (largest size of a subset of `[1..N]`
with no nontrivial `k`-term AP). We assume the standard contrapositive formulation:

  (h_rBound) If `B ⊆ [1..N]` and `B` has no `k`-AP, then `card B ≤ rBound N`.

Goal: show that if the harmonic series on `A` diverges and `rBound` is sufficiently
small on dyadic scales, then `A` must contain a `k`-term AP.

Proof idea:
1) Assume for contradiction `hno : ¬ HasKAP A k`.
2) For each `N`, let `B_N := ([1..N] ∩ A)` as a finset:
     `B_N = (Finset.Icc 1 N).filter (fun n => n ∈ A)`.
   Then `B_N` has no `k`-AP (since `B_N ⊆ A`), so by `h_rBound` we get
     `countUpTo A N = card B_N ≤ rBound N`.
3) Specialize to dyadic `N = 2^(m+1)` and combine with the dyadic growth hypothesis
   `hpow : rBound (2^(m+1)) ≤ 2^(m+1)/(m+1)^2` eventually.
   Conclude:
     `countUpTo A (2^(m+1)) ≤ 2^(m+1)/(m+1)^2` eventually.
4) Set `C m := 2^(m+1)/(m+1)^2`. Then
     `C m / 2^m = 2 / (m+1)^2`,
   and `∑ 2/(m+1)^2` is summable (p-series).
5) Apply `summable_harmonic_of_dyadic_count_bound` with this `C` to deduce
   `Summable (harmonicTerm A)`, contradicting `HarmonicDiverges A`.
6) Therefore `HasKAP A k`.

Possible approaches (probably wrong, but its worth a shot):
- Use `by_contra hno;` then aim to build `Summable (harmonicTerm A)`.
- Define `B N : Finset ℕ := (Finset.Icc 1 N).filter (fun n => n ∈ A)`.
- Show `¬ HasKAP (fun n => n ∈ B N) k` from `hno` using `HasKAP.mono`.
- For summability of `fun m => (2 : ℝ) / (m+1)^2`, use `summable_mul_left_iff`
  plus a standard lemma for `∑ 1/(n+1)^2` (search “pSeries” / “summable_nat_add_iff”).
-/
theorem erdos_turan_of_dyadic_rBound
    (k : ℕ)
    (A : Set ℕ)
    (rBound : ℕ → ℕ)
    (h_rBound :
      ∀ {N : ℕ} {B : Finset ℕ},
        B ⊆ Finset.Icc 1 N →
        (¬ HasKAP (fun n => n ∈ B) k) →
        B.card ≤ rBound N)
    (hdiv : HarmonicDiverges A)
    (hpow :
      ∀ᶠ m in atTop,
        (rBound (2^(m+1)) : ℝ) ≤ (2^(m+1) : ℝ) / ((m+1 : ℝ)^2)) :
    HasKAP A k := by
  by_contra hno

  -- Step 1: bound `countUpTo A (2^(m+1))` by `rBound (2^(m+1))` using `h_rBound`.
  have hcount_le_r :
      ∀ᶠ m in atTop,
        (countUpTo A (2^(m+1)) : ℝ) ≤ (rBound (2^(m+1)) : ℝ) := by
    -- Let `B := ([1..N] ∩ A)`; show it has no `k`-AP because `A` has no `k`-AP.
    -- Then apply `h_rBound`.
    sorry

  -- Step 2: combine with the dyadic smallness hypothesis.
  have hcount_le_C :
      ∀ᶠ m in atTop,
        (countUpTo A (2^(m+1)) : ℝ) ≤ (2^(m+1) : ℝ) / ((m+1 : ℝ)^2) := by
    filter_upwards [hcount_le_r, hpow] with m hm1 hm2
    exact le_trans hm1 hm2

  -- Step 3: define the dyadic majorant `C` and prove its dyadic series is summable.
  let C : ℕ → ℝ := fun m => (2^(m+1) : ℝ) / ((m+1 : ℝ)^2)

  have hCsumm : Summable (fun m : ℕ => C m / (2^m : ℝ)) := by
    -- Here `C m / 2^m = 2 / (m+1)^2`, so it’s a p-series.
    -- Try: `simp [C, pow_succ]` and use a p-series lemma.
    sorry

  -- Step 4: condensation lemma => harmonic series on `A` is summable, contradiction.
  have : Summable (harmonicTerm A) :=
    summable_harmonic_of_dyadic_count_bound A C hcount_le_C hCsumm

  exact hdiv this

end ErdosTuran
