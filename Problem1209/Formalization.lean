import Mathlib

set_option maxHeartbeats 800000

/-!
# Diagonal construction for Erdős Problem #1209, Parts (1) and (2)

We formalize the key lemma underlying the diagonal construction in Theorem 1 of the paper:
for any nonzero integer `m`, there exists an arbitrarily large prime `b` such that
`b + m` is divisible by a perfect square `q²` with `q` prime and `b + m > q²`.
This makes `b + m` simultaneously composite (not prime) and not squarefree.

By applying this lemma to each nonzero shift `m` in turn, one can construct a strictly
increasing sequence of primes `b₁ < b₂ < ⋯` for which `n = 0` is the unique shift
making all `n + bₖ` prime, and also the unique shift making all `n + bₖ` squarefree.
-/

open Nat

/-
For any nonzero integer `m` and bound `N`, there exist primes `b > N` and `q`
    with `q² ∣ (b + m)` and `b + m > q²`, making `b + m` composite and not squarefree.
-/
theorem exists_prime_killing_shift (m : ℤ) (hm : m ≠ 0) (N : ℕ) :
    ∃ b : ℕ, b > N ∧ Nat.Prime b ∧
      ∃ q : ℕ, Nat.Prime q ∧ (q : ℤ) ^ 2 ∣ ((b : ℤ) + m) ∧ ((b : ℤ) + m) > (q : ℤ) ^ 2 := by
  -- Choose a prime $q > \max(|m|, N)$.
  obtain ⟨q, hq_prime, hq_gt⟩ : ∃ q : ℕ, Nat.Prime q ∧ q > max (Int.natAbs m) N := by
    exact Exists.imp ( by tauto ) ( Nat.exists_infinite_primes ( Max.max m.natAbs N + 1 ) );
  -- Choose a prime $b$ such that $b \equiv -m \pmod{q^2}$ and $b > \max(N, q^2 + |m|)$.
  obtain ⟨b, hb_prime, hb_mod⟩ : ∃ b : ℕ, Nat.Prime b ∧ b ≡ -m [ZMOD q^2] ∧ b > max N (q^2 + m.natAbs) := by
    have h_dirichlet : ∀ n : ℕ, ∃ p > n, Nat.Prime p ∧ p ≡ -m [ZMOD q^2] := by
      intro n
      have h_dirichlet : ∀ (a : ZMod (q^2)), IsUnit a → ∃ p > n, Nat.Prime p ∧ (p : ZMod (q^2)) = a := by
        have := @Nat.forall_exists_prime_gt_and_eq_mod ( q^2 ) ?_;
        · exact fun a ha => this ha n;
        · exact ⟨ pow_ne_zero 2 hq_prime.ne_zero ⟩;
      convert h_dirichlet ( -m : ZMod ( q ^ 2 ) ) _;
      · erw [ ← ZMod.intCast_eq_intCast_iff ] ; aesop;
      · have h_coprime : Nat.Coprime (Int.natAbs m) (q^2) := by
          exact Nat.Coprime.pow_right _ <| Nat.Coprime.symm <| hq_prime.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt ( Int.natAbs_pos.mpr hm ) <| lt_of_le_of_lt ( le_max_left _ _ ) hq_gt;
        have h_coprime : IsUnit (Int.natAbs m : ZMod (q^2)) := by
          exact (ZMod.isUnit_iff_coprime m.natAbs (q ^ 2)).mpr h_coprime;
        cases m <;> aesop;
    exact Exists.elim ( h_dirichlet ( max N ( q ^ 2 + m.natAbs ) ) ) fun p hp => ⟨ p, hp.2.1, hp.2.2, hp.1 ⟩;
  exact ⟨ b, lt_of_le_of_lt ( le_max_left _ _ ) hb_mod.2, hb_prime, q, hq_prime, by simpa using hb_mod.1.symm.dvd, by cases abs_cases m <;> push_cast [ ← @Nat.cast_lt ℤ ] at * <;> nlinarith [ le_max_right N ( q ^ 2 + Int.natAbs m ) ] ⟩

/-
For any nonzero shift, the killing lemma produces a prime `b` with `b + m` not prime.
-/
theorem shift_not_prime_of_killing (m : ℤ) (hm : m ≠ 0) (N : ℕ) :
    ∃ b : ℕ, b > N ∧ Nat.Prime b ∧ ¬ Nat.Prime ((b : ℤ) + m).toNat := by
  obtain ⟨ b, hb₁, hb₂, q, hq₁, hq₂, hq₃ ⟩ := exists_prime_killing_shift m hm N;
  refine' ⟨ b, hb₁, hb₂, _ ⟩;
  obtain ⟨ k, hk ⟩ := hq₂;
  rcases k with ⟨ _ | _ | k ⟩ <;> simp_all +decide [ sq ];
  · norm_cast;
    rw [ Nat.prime_mul_iff ] ; aesop;
  · grind

/-
For any nonzero shift, the killing lemma produces a prime `b` with `b + m` not squarefree.
-/
theorem shift_not_squarefree_of_killing (m : ℤ) (hm : m ≠ 0) (N : ℕ) :
    ∃ b : ℕ, b > N ∧ Nat.Prime b ∧ ¬ Squarefree ((b : ℤ) + m).toNat := by
  obtain ⟨ b, hb, hb₁, q, hq, hq₁, hq₂ ⟩ := exists_prime_killing_shift m hm N;
  refine' ⟨ b, hb, hb₁, _ ⟩;
  rw [ @Squarefree ];
  simp +zetaDelta at *;
  refine' ⟨ q, _, hq.ne_one ⟩;
  convert Int.natCast_dvd_natCast.mp ( show ( q : ℤ ) ^ 2 ∣ ( b + m |> Int.toNat ) from ?_ ) using 1;
  · ring;
  · grind

-- -------- FORMALIZATION OF SOLUTION 3 ----------

/-!
# No universal prime shift for doubly exponential sequences

We prove that there is no integer `n` such that `n + 2^(2^k)` is prime for every `k ≥ 0`.

The proof splits into cases:
- **Even case**: If `n` is even, then `n + 2^(2^k)` is even and > 2 for large `k`.
- **Case n = 1**: The fifth Fermat number `2^32 + 1` is divisible by 641.
- **Odd case (n ≥ 3)**: A multiplicative order argument shows that if `p = n + 2^(2^r)`
  is prime (where `r = v₂(n-1)`), then `p` divides `n + 2^(2^(r+L))` for some `L ≥ 1`,
  making that term composite.
-/

open ZMod Nat

/-! ## Case n = 1: Fermat number F₅ is composite -/

/-- 641 divides 2^32 + 1 -/
lemma dvd_fermat5 : 641 ∣ 2 ^ 32 + 1 := by native_decide

/-- The fifth Fermat number is not prime -/
lemma not_prime_fermat5 : ¬ Nat.Prime (1 + 2 ^ 2 ^ 5) := by
  show ¬ Nat.Prime (2 ^ 32 + 1)
  intro hp
  have h641 := dvd_fermat5
  have := hp.eq_one_or_self_of_dvd 641 h641
  omega

/-! ## Even case -/

/-- If n is even and n ≥ 2, then n + 2 is even and ≥ 4, hence not prime -/
lemma even_not_prime (n : ℕ) (hn : 2 ∣ n) (hn2 : n ≥ 2) : ¬ Nat.Prime (n + 2 ^ 2 ^ 0) := by
  simp only [Nat.pow_zero, pow_one]
  intro hp
  have hdvd : 2 ∣ n + 2 := by omega
  have hge : n + 2 ≥ 4 := by omega
  have := hp.eq_one_or_self_of_dvd 2 hdvd
  omega

/-! ## Auxiliary lemmas for the odd case -/

/-- In ZMod p for odd prime p, 2 is nonzero -/
lemma two_ne_zero_zmod (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  change ¬ ((2 : ℕ) : ZMod p) = 0
  rw [CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  have := hp.out.two_le
  have := Nat.le_of_dvd (by omega) h
  omega

/-- The order of 2 in ZMod p divides p - 1 for odd prime p -/
lemma orderOf_two_dvd (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    orderOf (2 : ZMod p) ∣ p - 1 := by
  apply orderOf_dvd_of_pow_eq_one
  apply ZMod.pow_card_sub_one_eq_one
  exact two_ne_zero_zmod p hp2

/-
The order of 2 in ZMod p is positive for odd prime p
-/
lemma orderOf_two_pos (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) :
    0 < orderOf (2 : ZMod p) := by
  rw [ orderOf_pos_iff ];
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨ p - 1, Nat.sub_pos_of_lt hp.1.one_lt, by haveI := Fact.mk hp.1; rw [ ZMod.pow_card_sub_one_eq_one ] ; exact two_ne_zero_zmod p hp2 ⟩

/-- If `a ^ n = a` in a monoid and `n ≥ 1`, derived from order dividing `n - 1`. -/
lemma pow_eq_self_of_orderOf_dvd {G : Type*} [Monoid G] (a : G) (n : ℕ) (hn : n ≥ 1)
    (h : orderOf a ∣ n - 1) : a ^ n = a := by
  have : n = n - 1 + 1 := by omega
  rw [this, pow_add, pow_one, orderOf_dvd_iff_pow_eq_one.mp h, one_mul]

/-
Key arithmetic: if M is odd and positive, then there exists L ≥ 1 with M ∣ 2^L - 1
-/
lemma exists_dvd_pow_sub_one (M : ℕ) (hM : M > 0) (hM_odd : ¬ 2 ∣ M) :
    ∃ L : ℕ, L ≥ 1 ∧ M ∣ 2 ^ L - 1 := by
  use φ M;
  refine' ⟨ Nat.pos_of_ne_zero _, _ ⟩;
  · finiteness;
  · rw [ ← Nat.modEq_zero_iff_dvd ];
    simpa [ Nat.modEq_iff_dvd ] using Nat.ModEq.pow_totient ( Nat.coprime_comm.mp <| Nat.Coprime.gcd_eq_one <| Nat.Coprime.symm <| Nat.prime_two.coprime_iff_not_dvd.mpr hM_odd )

/-- The 2-adic valuation of `n - 1` for odd `n ≥ 3` -/
noncomputable def v2 (n : ℕ) : ℕ := (n - 1).factorization 2

/-
For odd n ≥ 3, v₂(n-1) ≥ 1
-/
lemma v2_pos (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n) : v2 n ≥ 1 := by
  exact Nat.pos_of_ne_zero ( Finsupp.mem_support_iff.mp ( by exact Nat.mem_primeFactors.mpr ⟨ Nat.prime_two, Nat.dvd_of_mod_eq_zero <| by omega, by omega ⟩ ) )

/-
For odd n ≥ 3, 2^(v₂(n-1)) divides n-1
-/
lemma pow_v2_dvd (n : ℕ) (_hn : n ≥ 3) (_hn_odd : ¬ 2 ∣ n) : 2 ^ v2 n ∣ n - 1 := by
  convert Nat.ordProj_dvd ( n - 1 ) 2 using 1

/-
2^t > t for all t ≥ 1
-/
lemma two_pow_gt (t : ℕ) (_ht : t ≥ 1) : 2 ^ t > t := by
  exact Nat.lt_two_pow_self

/-- v₂(n-1) < 2^(v₂(n-1)) for odd n ≥ 3 -/
lemma v2_lt_pow_v2 (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n) : v2 n < 2 ^ v2 n := by
  exact two_pow_gt (v2 n) (v2_pos n hn hn_odd)

/-
For odd n ≥ 3, if r = v₂(n-1), then v₂((n-1) + 2^(2^r)) = r.
    This is because v₂(n-1) = r and v₂(2^(2^r)) = 2^r > r.
-/
lemma v2_sum (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n) :
    ((n - 1 + 2 ^ 2 ^ v2 n) : ℕ).factorization 2 = v2 n := by
  -- Let $r := v2 n$, then $n - 1 = 2^{r}k$ for some odd $k$.
  set r := v2 n with hr
  obtain ⟨k, hk⟩ : ∃ k, n - 1 = 2 ^ r * k ∧ Odd k := by
    refine' ⟨ ( n - 1 ) / 2 ^ r, _, _ ⟩;
    · exact Eq.symm ( Nat.mul_div_cancel' ( Nat.ordProj_dvd _ _ ) );
    · exact Nat.odd_iff.mpr ( Nat.mod_two_ne_zero.mp fun h => absurd ( Nat.dvd_of_mod_eq_zero h ) ( Nat.not_dvd_ordCompl ( by norm_num ) <| by omega ) );
  -- Then $n - 1 + 2^{2^r} = 2^r(k + 2^{2^r - r})$.
  have h_decomp : n - 1 + 2 ^ (2 ^ r) = 2 ^ r * (k + 2 ^ (2 ^ r - r)) := by
    rw [ hk.1, mul_add, ← pow_add, add_tsub_cancel_of_le ( v2_lt_pow_v2 n hn hn_odd |> le_of_lt ) ];
  rw [ h_decomp, Nat.factorization_mul ] <;> norm_num;
  exact Nat.factorization_eq_zero_of_not_dvd ( by rw [ Nat.dvd_add_left ( dvd_pow_self _ ( Nat.sub_ne_zero_of_lt ( by linarith [ v2_lt_pow_v2 n hn ( by simpa using hn_odd ) ] ) ) ) ] ; simpa [ ← even_iff_two_dvd, parity_simps ] using hk.2 )

/-
For odd n ≥ 3 and r = v₂(n-1), the value p = n + 2^(2^r) is odd
-/
lemma p_odd (n : ℕ) (_hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n) : ¬ 2 ∣ (n + 2 ^ 2 ^ v2 n) := by
  grind +revert

/-
The order of (2 : ZMod p)^(2^r) where r = v₂(n-1) is odd,
    when p = n + 2^(2^r) is an odd prime.
-/
lemma orderOf_pow_odd (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n)
    (hp : Nat.Prime (n + 2 ^ 2 ^ v2 n)) :
    ¬ 2 ∣ orderOf ((2 : ZMod (n + 2 ^ 2 ^ v2 n)) ^ 2 ^ v2 n) := by
  -- Let $d = orderOf (2 : ZMod p)$. By orderOf_two_dvd, $d \mid p - 1$.
  set d := orderOf (2 : ZMod (n + 2 ^ 2 ^ v2 n));
  -- By orderOf_pow', the order of $2^{2^r}$ is $d / \gcd(d, 2^r)$.
  have h_order_pow : orderOf ((2 : ZMod (n + 2 ^ 2 ^ v2 n)) ^ (2 ^ v2 n)) = d / Nat.gcd d (2 ^ v2 n) := by
    rw [ orderOf_pow' ];
    aesop;
  -- Since $d.factorization 2 \leq r$, the gcd of $d$ and $2^r$ is $2^{d.factorization 2}$.
  have h_gcd : Nat.gcd d (2 ^ v2 n) = 2 ^ (d.factorization 2) := by
    have h_gcd : d.factorization 2 ≤ v2 n := by
      have h_factorization : d ∣ (n - 1) + 2 ^ 2 ^ v2 n := by
        have h_div : d ∣ (n + 2 ^ 2 ^ v2 n - 1) := by
          rw [ orderOf_dvd_iff_pow_eq_one ];
          have h_fermat : 2 ^ (Nat.totient (n + 2 ^ 2 ^ v2 n)) ≡ 1 [MOD (n + 2 ^ 2 ^ v2 n)] := by
            exact Nat.ModEq.pow_totient <| Nat.prime_two.coprime_iff_not_dvd.mpr <| by simpa [ ← even_iff_two_dvd, parity_simps ] using hn_odd;
          simp_all +decide [ ← ZMod.natCast_eq_natCast_iff, Nat.totient_prime hp ];
        rwa [ tsub_add_eq_add_tsub ( by linarith ) ];
      have h_factorization_le : Nat.factorization d 2 ≤ Nat.factorization ((n - 1) + 2 ^ 2 ^ v2 n) 2 := by
        obtain ⟨ k, hk ⟩ := h_factorization;
        rw [ hk, Nat.factorization_mul ] <;> norm_num;
        · intro h; simp_all +decide [ orderOf_eq_zero_iff ];
        · rintro rfl; linarith [ Nat.sub_pos_of_lt ( by linarith : 1 < n ), Nat.one_le_pow ( 2 ^ v2 n ) 2 zero_lt_two ];
      exact h_factorization_le.trans ( by rw [ v2_sum n hn hn_odd ] );
    refine' Nat.dvd_antisymm _ _;
    · rw [ ← Nat.factorization_le_iff_dvd ] <;> norm_num;
      rw [ Nat.factorization_gcd ] <;> norm_num;
      · intro i; by_cases hi : 2 = i <;> aesop;
      · rw [ orderOf_eq_zero_iff ];
        haveI := Fact.mk hp; exact not_not.mpr ( isOfFinOrder_iff_pow_eq_one.mpr ⟨ φ ( n + 2 ^ 2 ^ v2 n ), Nat.totient_pos.mpr hp.pos, by simpa [ ← ZMod.natCast_eq_natCast_iff ] using Nat.ModEq.pow_totient <| Nat.coprime_comm.mp <| hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two <| by linarith [ Nat.pow_le_pow_right two_pos <| show 2 ^ v2 n ≥ 1 from Nat.one_le_pow _ _ zero_lt_two ] ⟩ ) ;
    · exact Nat.dvd_gcd ( Nat.ordProj_dvd _ _ ) ( pow_dvd_pow _ h_gcd );
  rw [ h_order_pow, h_gcd, Nat.dvd_div_iff_mul_dvd ];
  · rw [ ← pow_succ, Nat.Prime.pow_dvd_iff_le_factorization ] <;> norm_num;
    rw [ orderOf_eq_zero_iff ];
    haveI := Fact.mk hp; exact not_not_intro <| isOfFinOrder_iff_pow_eq_one.mpr ⟨ φ ( n + 2 ^ 2 ^ v2 n ), Nat.totient_pos.mpr hp.pos, by simpa [ ← ZMod.natCast_eq_natCast_iff ] using Nat.ModEq.pow_totient <| Nat.coprime_comm.mp <| hp.coprime_iff_not_dvd.mpr <| Nat.not_dvd_of_pos_of_lt Nat.zero_lt_two <| by linarith [ Nat.pow_le_pow_right two_pos <| show 2 ^ v2 n ≥ 1 from Nat.one_le_pow _ _ zero_lt_two ] ⟩ ;
  · exact Nat.ordProj_dvd _ _

/-
The key divisibility: if p = n + 2^(2^r) is prime and n is odd ≥ 3,
    then p divides n + 2^(2^k) for some k > r
-/
lemma divisibility_from_order (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n)
    (hp : Nat.Prime (n + 2 ^ 2 ^ v2 n)) :
    ∃ k : ℕ, k > v2 n ∧ (n + 2 ^ 2 ^ v2 n) ∣ (n + 2 ^ 2 ^ k) := by
  -- Let `M = orderOf ((2 : ZMod (n + 2 ^ 2 ^ v2 n)) ^ 2 ^ v2 n)`.
  set M : ℕ := orderOf ((2 : (ZMod (n + 2 ^ 2 ^ v2 n))) ^ 2 ^ v2 n);
  -- By exists_dvd_pow_sub_one M (M > 0) (¬ 2 ∣ M), get L ≥ 1 with M ∣ 2^L - 1.
  obtain ⟨L, hL_pos, hL_div⟩ : ∃ L : ℕ, L ≥ 1 ∧ M ∣ 2 ^ L - 1 := by
    -- By definition of order, $M$ is odd and $M > 0$.
    have hM_odd : ¬(2 ∣ M) := by
      exact orderOf_pow_odd n hn hn_odd hp
    have hM_pos : M > 0 := by
      exact Nat.pos_of_ne_zero fun h => hM_odd <| h.symm ▸ dvd_zero _;
    exact exists_dvd_pow_sub_one M hM_pos hM_odd;
  refine' ⟨ v2 n + L, _, _ ⟩;
  · linarith;
  · -- In ZMod p, we have that $(2^{2^r})^{2^L} = 2^{2^{r+L}}$.
    have h_exp : ((2 : (ZMod (n + 2 ^ 2 ^ v2 n))) ^ 2 ^ v2 n) ^ 2 ^ L = (2 : (ZMod (n + 2 ^ 2 ^ v2 n))) ^ 2 ^ v2 n := by
      have h_exp : ((2 : (ZMod (n + 2 ^ 2 ^ v2 n))) ^ 2 ^ v2 n) ^ (2 ^ L - 1) = 1 := by
        rw [ ← orderOf_dvd_iff_pow_eq_one ] ; aesop;
      rw [ ← Nat.sub_add_cancel ( Nat.one_le_pow L 2 zero_lt_two ), pow_add, pow_one, h_exp, one_mul ];
    simp_all +decide [ ← ZMod.natCast_eq_zero_iff, pow_add, pow_mul ];
    norm_cast;
    rw [ ZMod.natCast_eq_zero_iff ]

/-
The odd case: for odd n ≥ 3, not all n + 2^(2^k) are prime
-/
lemma odd_case (n : ℕ) (hn : n ≥ 3) (hn_odd : ¬ 2 ∣ n) :
    ∃ k : ℕ, ¬ Nat.Prime (n + 2 ^ 2 ^ k) := by
  -- Let's assume for contradiction that for every k, n + 2 ^ 2 ^ k is prime.
  by_contra h_prime;
  obtain ⟨ k, hk ⟩ := divisibility_from_order n hn hn_odd ( by aesop );
  simp_all +decide [ Nat.prime_dvd_prime_iff_eq ];
  linarith

/-! ## Main theorem -/

/-
There is no natural number n such that n + 2^(2^k) is prime for every k ≥ 0.
-/
theorem no_universal_prime_shift : ∀ n : ℕ, ∃ k : ℕ, ¬ Nat.Prime (n + 2 ^ 2 ^ k) := by
  intro n;
  by_contra! h;
  -- Consider the case where n is even.
  by_cases h_even : 2 ∣ n;
  · cases' h_even with k hk;
    cases Nat.Prime.eq_two_or_odd ( h 0 ) <;> cases Nat.Prime.eq_two_or_odd ( h 1 ) <;> simp_all +arith +decide;
  · -- Consider the case where n is odd and n ≥ 3.
    by_cases h_ge_3 : n ≥ 3;
    · exact absurd ( odd_case n h_ge_3 ( by simpa using h_even ) ) ( by aesop );
    · interval_cases n <;> specialize h 5 <;> norm_num at *

/-
There is no integer n such that n + 2^(2^k) is a positive prime for every k ≥ 0.
    Here `.toNat` maps negative integers to 0, which is not prime, so the statement
    correctly captures the number-theoretic notion of positive primality.
-/
theorem no_universal_prime_shift_int :
    ∀ n : ℤ, ∃ k : ℕ, ¬ Nat.Prime (n + (2 : ℤ) ^ (2 ^ k)).toNat := by
  intro n;
  -- Consider two cases: $n \geq 0$ and $n < 0$.
  by_cases hn_nonneg : 0 ≤ n;
  · -- Since $n$ is non-negative, we can write $n = m$ for some $m \in \mathbb{N}$.
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := by
      exact Int.eq_ofNat_of_zero_le hn_nonneg;
    convert no_universal_prime_shift m using 1;
  · use 0;
    rcases n with ( _ | _ | n ) <;> norm_num at *;
    · decide;
    · erw [ Int.negSucc_eq ] ; norm_num;
      ring_nf;
      erw [ Int.toNat_of_nonpos ] <;> norm_num

/-! ## Factored-out consequences of the killing property -/

/-
A positive integer divisible by p² for prime p and strictly greater than p² is not prime.
-/
lemma not_prime_of_prime_sq_dvd (x : ℤ) (q : ℕ) (hq : Nat.Prime q)
    (hdvd : (q : ℤ) ^ 2 ∣ x) (hgt : x > (q : ℤ) ^ 2) :
    ¬ Nat.Prime x.toNat := by
  by_contra h;
  cases x <;> simp_all +decide [ sq ];
  norm_cast at *;
  rw [ Nat.dvd_prime h ] at hdvd ; aesop

/-
A positive integer divisible by p² for prime p is not squarefree.
-/
lemma not_squarefree_of_prime_sq_dvd (x : ℤ) (q : ℕ) (hq : Nat.Prime q)
    (hdvd : (q : ℤ) ^ 2 ∣ x) (hgt : x > (q : ℤ) ^ 2) :
    ¬ Squarefree x.toNat := by
  obtain ⟨ k, hk ⟩ := hdvd;
  rcases k with ( _ | _ | k ) <;> simp_all +decide [ sq, mul_assoc ];
  · norm_cast at *;
    rw [ Nat.squarefree_mul_iff ];
    simp +decide [ hq.coprime_iff_not_dvd ];
  · nlinarith;
  · grind

/-- Combined killing: for any nonzero m and bound N, there exists a prime b > N
    such that b + m is neither prime nor squarefree. -/
theorem exists_prime_killing_both (m : ℤ) (hm : m ≠ 0) (N : ℕ) :
    ∃ b : ℕ, b > N ∧ Nat.Prime b ∧
      ¬ Nat.Prime (((b : ℤ) + m).toNat) ∧
      ¬ Squarefree (((b : ℤ) + m).toNat) := by
  obtain ⟨b, hb, hbp, q, hq, hdvd, hgt⟩ := exists_prime_killing_shift m hm N
  exact ⟨b, hb, hbp,
    not_prime_of_prime_sq_dvd _ q hq hdvd hgt,
    not_squarefree_of_prime_sq_dvd _ q hq hdvd hgt⟩

/-! ## Enumeration of nonzero integers -/

/-- Enumeration of all nonzero integers: 1, -1, 2, -2, 3, -3, ... -/
def enumNonzeroInt (k : ℕ) : ℤ :=
  if k % 2 = 0 then (↑(k / 2) + 1) else -(↑(k / 2) + 1)

lemma enumNonzeroInt_ne_zero (k : ℕ) : enumNonzeroInt k ≠ 0 := by
  unfold enumNonzeroInt; split_ifs <;> omega;

lemma enumNonzeroInt_surj (m : ℤ) (hm : m ≠ 0) : ∃ k, enumNonzeroInt k = m := by
  by_cases hm_pos : 0 < m;
  · use 2 * (m.toNat - 1);
    unfold enumNonzeroInt;
    grind;
  · use 2 * Int.toNat ( -m ) - 1;
    unfold enumNonzeroInt; cases m <;> norm_num at *; omega;
    grind

/-! ## Diagonal sequence construction -/

/-- Recursive construction of the diagonal sequence: at step k, choose a prime
    that kills shift `enumNonzeroInt k`, larger than `g k` and all previous terms. -/
noncomputable def diagonalSeq (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => (exists_prime_killing_both (enumNonzeroInt 0) (enumNonzeroInt_ne_zero 0) (g 0)).choose
  | n + 1 => (exists_prime_killing_both (enumNonzeroInt (n + 1)) (enumNonzeroInt_ne_zero (n + 1))
      (max (g (n + 1)) (diagonalSeq g n))).choose

private lemma diagonalSeq_spec_zero (g : ℕ → ℕ) :
    diagonalSeq g 0 > g 0 ∧
    Nat.Prime (diagonalSeq g 0) ∧
    ¬ Nat.Prime (((diagonalSeq g 0 : ℤ) + enumNonzeroInt 0).toNat) ∧
    ¬ Squarefree (((diagonalSeq g 0 : ℤ) + enumNonzeroInt 0).toNat) :=
  (exists_prime_killing_both (enumNonzeroInt 0) (enumNonzeroInt_ne_zero 0) (g 0)).choose_spec

private lemma diagonalSeq_spec_succ (g : ℕ → ℕ) (n : ℕ) :
    diagonalSeq g (n + 1) > max (g (n + 1)) (diagonalSeq g n) ∧
    Nat.Prime (diagonalSeq g (n + 1)) ∧
    ¬ Nat.Prime (((diagonalSeq g (n + 1) : ℤ) + enumNonzeroInt (n + 1)).toNat) ∧
    ¬ Squarefree (((diagonalSeq g (n + 1) : ℤ) + enumNonzeroInt (n + 1)).toNat) :=
  (exists_prime_killing_both (enumNonzeroInt (n + 1)) (enumNonzeroInt_ne_zero (n + 1))
    (max (g (n + 1)) (diagonalSeq g n))).choose_spec

lemma diagonalSeq_prime (g : ℕ → ℕ) (k : ℕ) : Nat.Prime (diagonalSeq g k) := by
  induction' k with k ih;
  · exact diagonalSeq_spec_zero g |>.2.1;
  · exact diagonalSeq_spec_succ g k |>.2.1

lemma diagonalSeq_gt (g : ℕ → ℕ) (k : ℕ) : diagonalSeq g k > g k := by
  induction' k with k ih;
  · exact diagonalSeq_spec_zero g |>.1;
  · exact lt_of_le_of_lt ( le_max_left _ _ ) ( diagonalSeq_spec_succ g k |>.1 )

lemma diagonalSeq_strictMono (g : ℕ → ℕ) : StrictMono (diagonalSeq g) := by
  exact strictMono_nat_of_lt_succ fun n => by have := diagonalSeq_spec_succ g n; aesop;

lemma diagonalSeq_kills_prime (g : ℕ → ℕ) (k : ℕ) :
    ¬ Nat.Prime (((diagonalSeq g k : ℤ) + enumNonzeroInt k).toNat) := by
  induction' k with k ih;
  · exact diagonalSeq_spec_zero g |>.2.2.1;
  · exact diagonalSeq_spec_succ g k |>.2.2.1

lemma diagonalSeq_kills_squarefree (g : ℕ → ℕ) (k : ℕ) :
    ¬ Squarefree (((diagonalSeq g k : ℤ) + enumNonzeroInt k).toNat) := by
  induction' k with k ih;
  · exact diagonalSeq_spec_zero g |>.2.2.2;
  · exact ( diagonalSeq_spec_succ g k ) |>.2.2.2

/-! ## Theorem 2.1: Main Diagonal Construction -/

/-
**Theorem 2.1** (Main Diagonal Construction).
    For any growth function `g : ℕ → ℕ`, there exists a strictly increasing sequence
    of primes `B` with `B k > g k` for all `k`, such that `n = 0` is the unique integer
    shift making all `B k + n` prime, and also the unique shift making all `B k + n`
    squarefree.
-/
theorem main_diagonal (g : ℕ → ℕ) :
    ∃ B : ℕ → ℕ,
      (∀ k, Nat.Prime (B k)) ∧
      (StrictMono B) ∧
      (∀ k, B k > g k) ∧
      (∀ n : ℤ, (∀ k, Nat.Prime (((B k : ℤ) + n).toNat)) ↔ n = 0) ∧
      (∀ n : ℤ, (∀ k, Squarefree (((B k : ℤ) + n).toNat)) ↔ n = 0) := by
  use diagonalSeq g;
  refine' ⟨ _, _, _, _, _ ⟩;
  · exact fun k => diagonalSeq_prime g k;
  · exact diagonalSeq_strictMono g;
  · exact fun k => diagonalSeq_gt g k;
  · intro n; constructor;
    · contrapose!;
      intro hn;
      obtain ⟨ k, hk ⟩ := enumNonzeroInt_surj n hn;
      exact ⟨ k, by simpa [ hk ] using diagonalSeq_kills_prime g k ⟩;
    · intro hn k; simp +decide [ hn, diagonalSeq_prime ] ;
  · intro n;
    constructor <;> intro hn;
    · contrapose! hn;
      exact enumNonzeroInt_surj n hn |> fun ⟨ k, hk ⟩ => ⟨ k, by simpa [ hk ] using diagonalSeq_kills_squarefree g k ⟩;
    · intro k; rw [ hn ] ; exact Nat.prime_iff.mp ( diagonalSeq_prime g k ) |> fun h => h.squarefree;

/-! ## Corollary 2.2: Negative answers to Problems (1) and (2) -/

/-
**Corollary 2.2**. The answers to Problems (1) and (2) are negative.
    For any growth function `h`, there exists a strictly increasing sequence `A`
    with `A k > h k`, for which there is exactly one shift `n` making all `n + A k`
    prime, and exactly one shift making all `n + A k` squarefree.
-/
theorem corollary_unique_shift (h : ℕ → ℕ) :
    ∃ A : ℕ → ℕ,
      (∀ k, A k > h k) ∧
      (∃! n : ℤ, ∀ k, Nat.Prime ((n + ↑(A k)).toNat)) ∧
      (∃! n : ℤ, ∀ k, Squarefree ((n + ↑(A k)).toNat)) := by
  -- Set A = B (i.e. A k = B k). Then A k > h k.
  obtain ⟨B, hB⟩ := main_diagonal (fun k => h k)
  use B;
  simp_all +decide [ add_comm ]