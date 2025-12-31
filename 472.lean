/-
We proved the modular invariance of Ulam prime sequences starting with [2, p] where p is 1 mod m and m is even.
The main theorem is `ulam_seq_2_p_mod_even`.
We used helper lemmas:
- `mod_m_sum_minus_one`: modular arithmetic helper.
- `ulam_step_2_is_composite`: shows that adding 2 to a 1 mod m (m even) number results in a composite number (if > 2).
- `ulam_mod_m_candidates`: shows that all prime candidates generated are 1 mod m.
The proof proceeds by strong induction on n.
-/


/-
We formalized the Ulam sequence definition and properties. We proved that the sequence starting with `[2, 5]` terminates immediately. We investigated the sequence starting with `[2, 19]`, which is conjectured to be infinite. We proved that if this sequence never generates `0` (i.e., always finds a prime candidate), then it satisfies the Ulam Conjecture. We formalized the hypothesis `Ulam2_19_Prime_Candidates_Hypothesis` capturing the non-termination condition and proved `UlamConjecture` conditionally on this hypothesis. We also proved that under this hypothesis, all terms `q_n` for `n ≥ 1` satisfy `q_n ≡ 1 [MOD 18]`.
-/


/-
We investigated the Ulam prime sequence starting with 2, 19. We proved that for this sequence, every term $q_n$ (for $n \ge 1$) satisfies $q_n \equiv 1 \pmod{18}$. This property suggests that the sequence avoids small prime factors and has a structure that might support infinite growth, unlike sequences such as 2, 5 which terminate immediately. We also proved that for any prime $p > 3$ with $p \equiv 2 \pmod{3}$, the sequence starting with 2, p terminates immediately.
-/

import Mathlib

set_option linter.mathlibStandardSet false

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-
The next Ulam prime is the smallest prime of the form q_n + q_i - 1. A sequence is an Ulam prime sequence if it starts with the given list and follows the rule.
-/
def min_nat (l : List ℕ) : Option ℕ :=
  l.foldr (fun x acc => match acc with
    | none => some x
    | some y => some (min x y)) none

def next_ulam_prime (l : List ℕ) : Option ℕ :=
  match l.getLast? with
  | none => none
  | some q_n =>
    let candidates := l.map (fun q_i => q_n + q_i - 1)
    let primes := candidates.filter Nat.Prime
    min_nat primes

def IsUlamPrimeSeq (q : ℕ → ℕ) (start : List ℕ) : Prop :=
  (∀ i < start.length, start.get? i = some (q i)) ∧
  (∀ n ≥ start.length - 1,
    let current_list := (List.range (n + 1)).map q
    match next_ulam_prime current_list with
    | some p => q (n + 1) = p
    | none => False)

/-
The Ulam prime sequence starting with 3, 5 continues 3, 5, 7, 11, 13, 17.
-/
theorem ulam_seq_3_5_extends :
  next_ulam_prime [3] = some 5 ∧
  next_ulam_prime [3, 5] = some 7 ∧
  next_ulam_prime [3, 5, 7] = some 11 ∧
  next_ulam_prime [3, 5, 7, 11] = some 13 ∧
  next_ulam_prime [3, 5, 7, 11, 13] = some 17 := by
    native_decide +revert

/-
The Ulam prime sequence starting with 5 terminates immediately.
-/
theorem ulam_seq_5_terminates :
  next_ulam_prime [5] = none := by
    native_decide +revert

/-
The Ulam prime sequence starting with 2 continues 2, 3, 5, 7.
-/
theorem ulam_seq_2_extends :
  next_ulam_prime [2] = some 3 ∧
  next_ulam_prime [2, 3] = some 5 ∧
  next_ulam_prime [2, 3, 5] = some 7 := by
    native_decide +revert

/-
The Ulam prime sequence starting with 2, 5 terminates immediately.
-/
theorem ulam_seq_2_5_terminates :
  next_ulam_prime [2, 5] = none := by
    native_decide +revert

/-
The Ulam prime sequence starting with 3, 5 continues 19, 23, 29, 31, 37.
-/
theorem ulam_seq_3_5_extends_further :
  next_ulam_prime [3, 5, 7, 11, 13, 17] = some 19 ∧
  next_ulam_prime [3, 5, 7, 11, 13, 17, 19] = some 23 ∧
  next_ulam_prime [3, 5, 7, 11, 13, 17, 19, 23] = some 29 ∧
  next_ulam_prime [3, 5, 7, 11, 13, 17, 19, 23, 29] = some 31 ∧
  next_ulam_prime [3, 5, 7, 11, 13, 17, 19, 23, 29, 31] = some 37 := by
    -- Let's calculate each step explicitly.
    simp +decide [next_ulam_prime]

/-
The Ulam Conjecture states that there exists an initial finite sequence of primes such that the resulting Ulam prime sequence is infinite.
-/
def UlamConjecture : Prop :=
  ∃ (start : List ℕ),
    (∀ p ∈ start, p.Prime) ∧
    start.Sorted (· < ·) ∧
    ∃ (q : ℕ → ℕ), IsUlamPrimeSeq q start


def iterate_ulam_seq (start : List ℕ) (n : ℕ) : List ℕ :=
  match n with
  | 0 => start
  | k + 1 =>
    let current := iterate_ulam_seq start k
    match next_ulam_prime current with
    | some p => current ++ [p]
    | none => current

#eval iterate_ulam_seq [3] 50
#eval iterate_ulam_seq [2] 50

#check UlamConjecture

#eval (iterate_ulam_seq [3] 100).length
#eval (iterate_ulam_seq [3] 200).length

#eval (iterate_ulam_seq [3] 500).length
#eval (iterate_ulam_seq [2] 500).length

#eval (iterate_ulam_seq [19] 50).length

#eval (iterate_ulam_seq [3, 5] 100).length
#eval (iterate_ulam_seq [2, 3] 100).length
#eval (iterate_ulam_seq [2, 7] 100).length
#eval (iterate_ulam_seq [2, 11] 100).length
#eval (iterate_ulam_seq [2, 13] 100).length
#eval (iterate_ulam_seq [2, 17] 100).length
#eval (iterate_ulam_seq [2, 19] 100).length

#eval iterate_ulam_seq [2, 19] 10

/-
If x is 1 mod 18 and x >= 19, then x + 1 is not prime.
-/
lemma mod_18_add_one_not_prime (x : ℕ) (h1 : x % 18 = 1) (h2 : x ≥ 19) : ¬ Nat.Prime (x + 1) := by
  exact fun h => by have := Nat.Prime.eq_two_or_odd h; omega;

/-
If x and y are 1 mod 18, then x + y - 1 is 1 mod 18.
-/
lemma mod_18_sum_minus_one (x y : ℕ) (h1 : x % 18 = 1) (h2 : y % 18 = 1) : (x + y - 1) % 18 = 1 := by
  grind

/-
If a list satisfies the UlamMod18 property and its last element is >= 19, then the next Ulam prime is 1 mod 18.
-/
def UlamMod18 (l : List ℕ) : Prop :=
  l.head? = some 2 ∧ ∀ x ∈ l.tail, x % 18 = 1

lemma ulam_mod_18_step (l : List ℕ) (h_mod : UlamMod18 l) (q_n : ℕ) (h_last : l.getLast? = some q_n) (h_ge : q_n ≥ 19) (p : ℕ) (h_next : next_ulam_prime l = some p) :
  p % 18 = 1 := by
    -- Since `l` satisfies `UlamMod18 l`, all elements except the first are 1 mod 18.
    -- `next_ulam_prime` returns the minimum of candidates from `l`. Candidates come from `q_n + q_i - 1`.
    -- If `q_i = 2`, the candidate `p = q_n + 1` is not prime since `q_n % 18 = 1`.
    -- Thus, `p` comes from a candidate `q_i` in `l.tail`.
    -- Since `q_i` is 1 mod 18, the candidate `q_n + q_i - 1` is also 1 mod 18.
    -- Hence `p % 18 = 1`.
    obtain ⟨i, hi⟩ : ∃ i ∈ l, p = q_n + i - 1 ∧ Nat.Prime p := by
      have h_candidates : ∃ candidates, candidates = l.map (fun q_i => q_n + q_i - 1) ∧ p ∈ candidates.filter Nat.Prime := by
        have h_next_ulam_def : next_ulam_prime l = match l.getLast? with | none => none | some q_n => let candidates := l.map (fun q_i => q_n + q_i - 1); let primes := candidates.filter Nat.Prime; min_nat primes := by
          exact?
        -- By definition of `min_nat`, if `min_nat primes = some p`, then `p` is in `primes`.
        have h_min_nat : ∀ {l : List ℕ}, min_nat l = some p → p ∈ l := by
          -- We'll use induction on the list to prove that if `min_nat l = some p`, then `p` is in `l`.
          intro l hl
          induction' l with l_head l_tail ih
          generalize_proofs at *; (
          -- By definition of `min_nat`, if `min_nat [] = some p`, then `p` must be in the empty list, which is impossible.
          cases hl.symm.trans (by rfl : min_nat [] = none));
          -- By definition of `min_nat`, if `min_nat (l_head :: l_tail) = some p`, then `p` is the minimum of `l_head` and the minimum of `l_tail`.
          have h_min_nat_def : min_nat (l_head :: l_tail) = match min_nat l_tail with | none => some l_head | some y => some (min l_head y) := by
            exact?;
          cases h : min_nat l_tail <;> simp_all +decide [ min_def ];
          split_ifs at hl <;> aesop ( simp_config := { singlePass := true } ) ;
        generalize_proofs at *; (
        exact ⟨ _, rfl, h_min_nat <| h_next_ulam_def ▸ h_next |> fun h => by rw [ h_last ] at h; exact h ⟩ ;)
      generalize_proofs at *;
      grind;
    -- Since `l` satisfies `UlamMod18 l`, all elements except the first are 1 mod 18. Therefore, `i` must be 1 mod 18.
    have hi_mod : i % 18 = 1 ∨ i = 2 := by
      rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide [ UlamMod18 ];
      grind +ring;
    have hp_mod : q_n % 18 = 1 := by
      have h_qn_mod : q_n ∈ l.tail := by
        rcases l with ( _ | ⟨ _, _ | l ⟩ ) <;> simp_all +decide [ List.getLast? ];
        · cases h_mod ; aesop ( simp_config := { decide := true } );
        · induction ‹List ℕ› using List.reverseRecOn <;> aesop ( simp_config := { decide := true } );
      have := h_mod.2 q_n h_qn_mod; aesop;
    have := Nat.Prime.eq_two_or_odd hi.2.2; omega;

/-
If min_nat l returns some p, then p is in l.
-/
lemma min_nat_mem (l : List ℕ) (p : ℕ) (hp : min_nat l = some p) : p ∈ l := by
  -- By induction on the list l.
  induction' l with x xs ih generalizing p; simp_all +decide [ min_nat ];
  -- By definition of `min_nat`, we know that `min_nat (x :: xs)` is either `some x` or `some y` where `y` is the minimum element of `xs`.
  have h_min_def : min_nat (x :: xs) = match min_nat xs with | none => some x | some y => some (min x y) := by
    exact?;
  -- By definition of `min_nat`, we know that `min_nat (x :: xs)` is either `some x` or `some y` where `y` is the minimum element of `xs`. We consider both cases.
  cases' h : min_nat xs with y <;> simp_all +decide [ List.mem_cons ];
  cases le_total x y <;> aesop ( simp_config := { decide := true } )

/-
All terms in the Ulam sequence starting with 2, 19 are at least 2.
-/
lemma q_ge_2 (q : ℕ → ℕ) (h : IsUlamPrimeSeq q [2, 19]) : ∀ n, q n ≥ 2 := by
  -- By definition of IsUlamPrimeSeq, we know that q 0 = 2 and q 1 = 19.
  have h_base : q 0 = 2 ∧ q 1 = 19 := by
    have h0 : q 0 = 2 := by
      have := h.1 0; aesop;
    have h1 : q 1 = 19 := by
      have := h.1 1 ( by decide ) ; aesop;
    exact ⟨h0, h1⟩;
  -- For all n ≥ 2, q n is prime, hence q n ≥ 2.
  have h_prime : ∀ n ≥ 2, Nat.Prime (q n) := by
    -- By definition of IsUlamPrimeSeq, for all n ≥ 1, q (n + 1) is a prime number.
    have h_prime : ∀ n ≥ 1, Nat.Prime (q (n + 1)) := by
      intro n hn
      have h_next : next_ulam_prime (List.map q (List.range (n + 1))) = some (q (n + 1)) := by
        have := h.2 n; aesop;
      -- By definition of min_nat, if min_nat (candidates.filter Nat.Prime) = some (q (n + 1)), then q (n + 1) is in the list of primes.
      have h_min_nat_prime : ∀ l : List ℕ, min_nat (l.filter Nat.Prime) = some (q (n + 1)) → Nat.Prime (q (n + 1)) := by
        intros l hl; have := min_nat_mem ( List.filter ( fun b => Nat.Prime b ) l ) ( q ( n + 1 ) ) hl; aesop;
      generalize_proofs at *; (
      unfold next_ulam_prime at *; aesop;);
    exact fun n hn => by cases n <;> aesop;
  exact fun n => if hn : n < 2 then by interval_cases n <;> norm_num [ h_base ] else Nat.Prime.two_le ( h_prime n ( le_of_not_gt hn ) )

/-
If all elements in a list are greater than C, then the minimum of the list is greater than C.
-/
lemma min_nat_gt (l : List ℕ) (C : ℕ) (h : ∀ x ∈ l, x > C) (p : ℕ) (hp : min_nat l = some p) : p > C := by
  -- Since p is in l and every element in l is greater than C, we can apply h to p to get p > C.
  have hp_mem : p ∈ l := min_nat_mem l p hp
  exact h p hp_mem

#eval (iterate_ulam_seq [3] 100).length
#eval (iterate_ulam_seq [2, 19] 100).length

/-
If all elements in l are >= 2, then any candidate q_n + q_i - 1 is strictly greater than q_n.
-/
lemma ulam_candidates_gt (l : List ℕ) (q_n : ℕ) (h_ge_2 : ∀ x ∈ l, x ≥ 2) :
  ∀ c ∈ l.map (fun q_i => q_n + q_i - 1), c > q_n := by
    grind

/-
Arithmetic inequality for Ulam sequence.
-/
lemma ulam_arithmetic_gt (q_n q_i : ℕ) (h_ge_2 : q_i ≥ 2) : q_n + q_i - 1 > q_n := by
  exact lt_tsub_iff_left.mpr ( by linarith ) ;

/-
If all elements in l are >= 2, then the next Ulam prime is strictly greater than the last element.
-/
lemma ulam_next_gt_last (l : List ℕ) (q_n : ℕ) (h_last : l.getLast? = some q_n) (h_ge_2 : ∀ x ∈ l, x ≥ 2) (p : ℕ) (h_next : next_ulam_prime l = some p) :
  p > q_n := by
    -- Since $p$ is a prime in the set of candidates and all candidates are greater than $q_n$, we have $p > q_n$.
    have h_p_gt_qn : ∀ x ∈ (l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime, x > q_n := by
      simp +zetaDelta at *;
      exact fun x hx hx' => lt_tsub_iff_left.mpr ( by linarith [ h_ge_2 x hx ] )
    generalize_proofs at *;
    exact h_p_gt_qn p (by
    -- By definition of `next_ulam_prime`, if `next_ulam_prime l = some p`, then `p` is the minimum of the primes in the candidates.
    have h_min : min_nat ((l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime) = some p := by
      unfold next_ulam_prime at h_next; aesop;
    generalize_proofs at *; (
    -- By definition of `min_nat`, if `min_nat l = some p`, then `p` is in `l`.
    apply min_nat_mem; assumption
    skip))

/-
If all elements in a list are greater than C, then the minimum of any filtered sublist is also greater than C.
-/
lemma min_nat_filter_gt_of_all_gt (l : List ℕ) (P : ℕ → Prop) [DecidablePred P] (C : ℕ) (h_gt : ∀ x ∈ l, x > C) (p : ℕ) (h_min : min_nat (l.filter P) = some p) : p > C := by
  exact min_nat_gt _ _ ( fun x hx => h_gt x <| List.mem_of_mem_filter hx ) p h_min |> fun h => by simpa using h;

/-
If the start list has elements >= 2, then the Ulam sequence has elements >= 2.
-/
lemma q_ge_2_general (q : ℕ → ℕ) (start : List ℕ) (h_start : ∀ x ∈ start, x ≥ 2) (h : IsUlamPrimeSeq q start) :
  ∀ n, q n ≥ 2 := by
    -- For n less than the length of the start list, since start elements are ≥2, q n is in start, so q n ≥2.
    have h_lt : ∀ n < start.length, q n ≥ 2 := by
      -- By definition of IsUlamPrimeSeq, for n < start.length, q n is the nth element of the start list.
      have h_eq_start : ∀ n < start.length, q n = start.get! n := by
        intro n hn; have := h.1 n hn; aesop;
      generalize_proofs at *; (
      aesop? ( simp_config := { singlePass := true } ) ;);
    -- For n greater than or equal to the length of the start list, since the next Ulam prime is the minimum prime in a list of numbers of the form q_n + q_i - 1, and each q_i is at least 2, the next Ulam prime is at least 2.
    have h_ge : ∀ n ≥ start.length - 1, q (n + 1) ≥ 2 := by
      intro n hn
      obtain ⟨p, hp⟩ : ∃ p, next_ulam_prime ((List.range (n + 1)).map q) = some p ∧ q (n + 1) = p := by
        have := h.2 n hn; cases h : next_ulam_prime ( List.map q ( List.range ( n + 1 ) ) ) <;> aesop;
      -- Since $p$ is the minimum prime in the list of candidates, and each candidate is of the form $q_n + q_i - 1$, we have $p \geq 2$.
      have hp_prime : Nat.Prime p := by
        -- By definition of `next_ulam_prime`, if `next_ulam_prime l = some p`, then `p` is a prime number.
        have hp_prime : ∀ l : List ℕ, ∀ p : ℕ, next_ulam_prime l = some p → Nat.Prime p := by
          intros l p hp
          have h_candidates : p ∈ (l.map (fun q_i => (l.getLast?.getD 0) + q_i - 1)).filter Nat.Prime := by
            have h_candidates : p ∈ (l.map (fun q_i => (l.getLast?.getD 0) + q_i - 1)).filter Nat.Prime := by
              have h_min_nat : min_nat ((l.map (fun q_i => (l.getLast?.getD 0) + q_i - 1)).filter Nat.Prime) = some p := by
                unfold next_ulam_prime at hp; aesop;
              exact min_nat_mem _ _ h_min_nat |> fun x => by simpa using x;
            generalize_proofs at *;
            exact h_candidates
          generalize_proofs at *;
          rw [ List.mem_filter ] at h_candidates; aesop;
        exact hp_prime _ _ hp.1
      exact Nat.Prime.two_le hp_prime |> le_trans <| by linarith [hp.right] ;
    intro n; rcases n with ( _ | n ) <;> simp_all +arith +decide;
    · rcases start with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide [ IsUlamPrimeSeq ] ;
      specialize h 0 ; simp_all +arith +decide [ List.range_succ, next_ulam_prime ] ;
      rcases k : q 0 with ( _ | _ | k ) <;> simp_all +arith +decide [ min_nat ];
    · by_cases h : start.length ≤ n + 1 <;> aesop

/-
For the Ulam sequence starting with 2, 19, q n >= 19 for all n >= 1.
-/
lemma q_n_ge_19 (q : ℕ → ℕ) (h : IsUlamPrimeSeq q [2, 19]) : ∀ n ≥ 1, q n ≥ 19 := by
  -- By definition of IsUlamPrimeSeq, we know that q 1 = 19.
  have h_q1 : q 1 = 19 := by
    have := h.1 1; simp_all +decide ;
  -- By induction on $n$, we can show that $q n \geq 19$ for all $n \geq 1$.
  intro n hn
  induction' hn with n hn ih;
  · linarith;
  · -- By definition of IsUlamPrimeSeq, we know that q (n + 1) is the smallest prime of the form q n + q i - 1 where i < n + 1.
    have h_q_succ : q (n + 1) > q n := by
      -- By definition of IsUlamPrimeSeq, we know that q (n + 1) is the smallest prime of the form q n + q i - 1 where i < n + 1. Hence, q (n + 1) > q n.
      have h_q_succ : next_ulam_prime ((List.range (n + 1)).map q) = some (q (n + 1)) := by
        have := h.2 n ( by cases n <;> aesop ) ; aesop;
      apply_rules [ ulam_next_gt_last ];
      · cases n <;> simp_all +decide [ List.range_succ ];
      · exact fun x hx => by obtain ⟨ i, hi, rfl ⟩ := List.mem_map.mp hx; exact q_ge_2 q h i; ;
    linarith

/-
If l satisfies UlamMod18 and q_n is 1 mod 18 and >= 19, then any prime candidate generated is 1 mod 18.
-/
lemma ulam_mod_18_candidates (l : List ℕ) (h_mod : UlamMod18 l) (q_n : ℕ) (h_qn_mod : q_n % 18 = 1) (h_qn_ge : q_n ≥ 19) :
  ∀ c ∈ (l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime, c % 18 = 1 := by
    -- Since $l$ satisfies the UlamMod18 property, all elements in $l.tail$ are 1 mod 18. Also, $q_n$ is 1 mod 18 and >= 19.
    have h_tail_mod : ∀ q_i ∈ l.tail, q_i % 18 = 1 := by
      -- By definition of UlamMod18, all elements in the tail of l are 1 mod 18.
      intros q_i hq_i
      apply h_mod.right q_i hq_i;
    rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide;
    · cases h_mod ; simp_all ( config := { decide := Bool.true } ) [ Nat.add_mod, Nat.mul_mod ];
      rw [ Nat.prime_def_lt' ] ; norm_num [ Nat.add_mod, h_qn_mod ];
      exact fun _ => ⟨ 2, by norm_num, by linarith, Nat.dvd_of_mod_eq_zero ( by omega ) ⟩;
    · -- Since $x = 2$, we have $q_n + x - 1 = q_n + 1$. But $q_n$ is 1 mod 18 and ≥ 19, so $q_n + 1$ is even and greater than 2, hence not prime.
      have h_x : q_n + 2 - 1 = q_n + 1 := by
        rfl
      have h_not_prime_x : ¬Nat.Prime (q_n + 1) := by
        exact fun h => by have := Nat.Prime.eq_two_or_odd h; omega;
      exact ⟨fun h => by
        cases h_mod ; aesop;, fun h => by
        exact mod_18_sum_minus_one q_n y ( by aesop ) ( by aesop ), fun a ha h_prime => by
        rw [ ← Nat.mod_add_div ( q_n + a ) 18 ] ; norm_num [ Nat.add_mod, Nat.mul_mod, h_qn_mod, h_tail_mod.2 a ha ] ;⟩

/-
The Ulam sequence starting with 2, 19 satisfies q_n = 1 mod 18 for n >= 1.
-/
theorem ulam_seq_2_19_mod_18 (q : ℕ → ℕ) (h : IsUlamPrimeSeq q [2, 19]) :
  ∀ n ≥ 1, q n % 18 = 1 := by
    -- Let's prove the base case first.
    have base : ∀ n ≥ 1, q n ≥ 19 := by
      -- By definition of `IsUlamPrimeSeq`, we know that `q` satisfies the Ulam prime sequence property starting with 2 and 19.
      intros n hn
      apply q_n_ge_19 q h n hn;
    -- By definition of $UlamMod18$, we know that the list $[q 0, ..., q n]$ satisfies $UlamMod18$ for all $n \geq 1$.
    have h_ulam_mod_18 : ∀ n ≥ 1, UlamMod18 (List.map q (List.range (n + 1))) := by
      intro n hn_ge_one; induction' n, hn_ge_one using Nat.le_induction with n hn ih <;> simp_all +decide [ List.range_succ ] ;
      · have := h.1 0; have := h.1 1; simp_all +decide [ IsUlamPrimeSeq ] ;
        exact ⟨ by norm_num [ ← h.1 0 ( by decide ) ], by norm_num [ ← h.1 0 ( by decide ), ← h.1 1 ( by decide ) ] ⟩;
      · -- By definition of $IsUlamPrimeSeq$, we know that $q (n + 1)$ is the smallest prime of the form $q n + q i - 1$ for $i < n$.
        obtain ⟨p, hp⟩ : ∃ p, next_ulam_prime (List.map q (List.range (n + 1))) = some p ∧ q (n + 1) = p := by
          have := h.2 n ( by
            exact Nat.le_trans ( by decide ) hn ) ; aesop;
        have h_p_mod : p % 18 = 1 := by
          apply_rules [ ulam_mod_18_step ] ; aesop;
          simpa [ List.range_succ ] using hp.1;
        cases n <;> simp_all +decide [ List.range_succ, UlamMod18 ];
        cases h : List.range ‹_› <;> aesop ( simp_config := { decide := true } ) ;
    -- By definition of $UlamMod18$, we know that the list $[q 0, ..., q n]$ satisfies $UlamMod18$ for all $n \geq 1$. Hence, $q n \equiv 1 \pmod{18}$ for all $n \geq 1$.
    intros n hn
    specialize h_ulam_mod_18 n hn
    have h_last : q n % 18 = 1 := by
      have := h_ulam_mod_18.2; simp_all +decide [ List.range_succ ] ;
      rcases n with ( _ | _ | n ) <;> simp_all +arith +decide [ List.range_succ_eq_map ]
    exact h_last

/-
If l satisfies UlamMod18 and the last element is 1 mod 18 and >= 19, then the next Ulam prime is 1 mod 18.
-/
lemma ulam_mod_18_next (l : List ℕ) (h_mod : UlamMod18 l) (q_n : ℕ) (h_last : l.getLast? = some q_n) (h_qn_mod : q_n % 18 = 1) (h_qn_ge : q_n ≥ 19) (p : ℕ) (h_next : next_ulam_prime l = some p) :
  p % 18 = 1 := by
    exact?

/-
The last element of (List.range (n+1)).map q is q n.
-/
lemma list_range_map_last (q : ℕ → ℕ) (n : ℕ) : ((List.range (n + 1)).map q).getLast? = some (q n) := by
  grind

/-
The head of (List.range (n+1)).map q is q 0.
-/
lemma list_range_map_head (q : ℕ → ℕ) (n : ℕ) : ((List.range (n + 1)).map q).head? = some (q 0) := by
  cases n <;> simp +arith +decide [ List.range_succ_eq_map ]

/-
The Ulam prime sequence starting with 2 and a prime p > 3 with p = 2 mod 3 terminates immediately.
-/
theorem ulam_2_p_terminates (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : p > 3) (hp_mod : p % 3 = 2) :
  next_ulam_prime [2, p] = none := by
    -- Since $p \equiv 2 \pmod{3}$, we have $p + 2 - 1 = p + 1 \equiv 0 \pmod{3}$ and $p + p - 1 = 2p - 1 \equiv 0 \pmod{3}$.
    have h_candidates : (p + 2 - 1) % 3 = 0 ∧ (p + p - 1) % 3 = 0 := by
      omega;
    -- Since both candidates are divisible by 3 and greater than 3, they are not prime.
    have h_not_prime : ¬Nat.Prime (p + 2 - 1) ∧ ¬Nat.Prime (p + p - 1) := by
      exact ⟨ fun h => by have := Nat.dvd_of_mod_eq_zero h_candidates.1; rw [ h.dvd_iff_eq ] at this <;> omega, fun h => by have := Nat.dvd_of_mod_eq_zero h_candidates.2; rw [ h.dvd_iff_eq ] at this <;> omega ⟩;
    unfold next_ulam_prime; aesop;

/-
The Ulam sequence starting with 2, 19 satisfies q_n = 1 mod 18 for n >= 1.
-/
theorem ulam_seq_2_19_mod_18_proven (q : ℕ → ℕ) (h : IsUlamPrimeSeq q [2, 19]) :
  ∀ n ≥ 1, q n % 18 = 1 := by
    exact?

/-
If q satisfies the inductive hypothesis up to m, then the list of q values up to m satisfies UlamMod18.
-/
lemma ulam_mod_18_list (q : ℕ → ℕ) (h : IsUlamPrimeSeq q [2, 19]) (m : ℕ) (hm : m ≥ 1) (ih : ∀ k, 1 ≤ k ∧ k ≤ m → q k % 18 = 1) :
  UlamMod18 ((List.range (m + 1)).map q) := by
    -- By definition of `IsUlamPrimeSeq`, we know that `q 0 = 2` and `q k % 18 = 1` for all `1 ≤ k ≤ m`.
    have h_head : q 0 = 2 := by
      have := h.1 0; aesop;
    have h_tail : ∀ k, 1 ≤ k ∧ k ≤ m → q k % 18 = 1 := by
      exact ih
    exact ⟨by
    cases m <;> simp_all +decide [ List.range_succ_eq_map ], by
      -- The tail of the list [q 0, q 1, ..., q m] is [q 1, ..., q m], and we know from h_tail that for any k in 1 ≤ k ≤ m, q k % 18 = 1.
      intros x hx
      obtain ⟨k, hk⟩ : ∃ k, 1 ≤ k ∧ k ≤ m ∧ x = q k := by
        simp_all +decide [ List.range_succ_eq_map ];
        exact ⟨ _, Nat.succ_pos _, Nat.succ_le_of_lt hx.choose_spec.1, hx.choose_spec.2.symm ⟩
      exact h_tail k ⟨hk.left, hk.right.left⟩ ▸ hk.right.right.symm ▸ rfl⟩


#eval (iterate_ulam_seq [3] 50).length
#eval (iterate_ulam_seq [2] 50).length
#eval (iterate_ulam_seq [2, 19] 50).length
#eval (iterate_ulam_seq [2, 5] 50).length

#eval iterate_ulam_seq [3] 20
#eval iterate_ulam_seq [2, 19] 20
#eval iterate_ulam_seq [2, 3] 20

theorem ulam_seq_2_5_terminates_proven : next_ulam_prime [2, 5] = none := by
  native_decide

#eval (iterate_ulam_seq [3] 200).length
#eval (iterate_ulam_seq [2, 19] 200).length
#eval (iterate_ulam_seq [2, 3] 200).length

def get_gaps (l : List ℕ) : List ℕ :=
  (l.zip l.tail).map (fun (a, b) => b - a)

#eval get_gaps (iterate_ulam_seq [2, 19] 50)
#eval get_gaps (iterate_ulam_seq [3, 5] 50)

#eval (iterate_ulam_seq [3] 30)
#eval (iterate_ulam_seq [2, 19] 30)

#check iterate_ulam_seq
#eval (iterate_ulam_seq [3, 5] 500).length
#eval (iterate_ulam_seq [2, 19] 500).length

#eval (iterate_ulam_seq [2, 19] 1000).length

def ulam_seq (start : List ℕ) (n : ℕ) : ℕ :=
  if h : n < start.length then
    start.get ⟨n, h⟩
  else
    let prev := (List.range n).attach.map (fun ⟨i, hi⟩ =>
      ulam_seq start i)
    match next_ulam_prime prev with
    | some p => p
    | none => 0
termination_by n
decreasing_by
  simp_wf
  exact List.mem_range.mp hi

lemma mod_18_add_one_not_prime_v2 (x : ℕ) (h1 : x % 18 = 1) (h2 : x ≥ 19) : ¬ Nat.Prime (x + 1) := by
  -- By definition of UlamMod18, if x is 1 mod 18 and x ≥ 19, then x + 1 is divisible by 18 and hence not prime.
  apply mod_18_add_one_not_prime x h1 h2

def ulam_2_19_seq := ulam_seq [2, 19]

lemma ulam_2_19_candidates_mod_18 (l : List ℕ) (h_mod : UlamMod18 l) (q_n : ℕ) (h_last : l.getLast? = some q_n) (h_qn_mod : q_n % 18 = 1) (h_qn_ge : q_n ≥ 19) :
  ∀ c ∈ (l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime, c % 18 = 1 := by
    -- Since all elements in l are congruent to 1 modulo 18, any candidate generated by adding q_n to them and subtracting 1 will also be congruent to 1 modulo 18. Therefore, any prime candidate will be 1 modulo 18.
    intros c hc
    obtain ⟨q_i, hq_i, hc⟩ : ∃ q_i ∈ l, c = q_n + q_i - 1 := by
      grind;
    rcases l with ( _ | ⟨ _ | l, _ ⟩ ) <;> simp_all +arith +decide;
    · cases h_mod ; aesop;
    · rcases hq_i with ( rfl | hq_i ) <;> simp_all +arith +decide [ UlamMod18 ];
      · have := Nat.Prime.eq_two_or_odd hc; omega;
      · grind

lemma ulam_2_19_candidates_mod_18_v2 (l : List ℕ) (h_mod : UlamMod18 l) (q_n : ℕ) (h_last : l.getLast? = some q_n) (h_qn_mod : q_n % 18 = 1) (h_qn_ge : q_n ≥ 19) :
  ∀ c ∈ (l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime, c % 18 = 1 := by
    -- Apply the lemma that states if l satisfies UlamMod18 and q_n is 1 mod 18 and >= 19, then any prime candidate generated is 1 mod 18.
    apply ulam_mod_18_candidates; assumption; assumption; assumption

#eval iterate_ulam_seq [2, 11] 10
#eval iterate_ulam_seq [2, 19] 10

lemma ulam_2_19_recurrence (n : ℕ) (h : n ≥ 2) :
  ulam_2_19_seq n =
    let prev := (List.range n).attach.map (fun ⟨i, hi⟩ => ulam_2_19_seq i)
    match next_ulam_prime prev with
    | some p => p
    | none => 0 := by
      -- By definition of `ulam_seq`, for `n ≥ 2`, the sequence is built by taking the last element of the previous sequence and adding 18.
      have h_def : ∀ n ≥ 2, ulam_2_19_seq n = match next_ulam_prime ((List.range n).attach.map (fun ⟨i, hi⟩ => ulam_2_19_seq i)) with | some p => p | none => 0 := by
        intros n hn
        rw [show ulam_2_19_seq n = ulam_seq [2, 19] n from rfl];
        rw [ulam_seq];
        rcases n with ( _ | _ | n ) <;> simp_all +arith +decide;
        unfold ulam_2_19_seq; aesop;
      exact h_def n h

#eval iterate_ulam_seq [2, 3] 30

theorem ulam_2_p_terminates_v2 (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : p > 3) (hp_mod : p % 3 = 2) :
  next_ulam_prime [2, p] = none := by
    -- Apply the theorem that states the next Ulam prime for [2, p] is none.
    apply ulam_2_p_terminates p hp hp_gt_3 hp_mod

lemma ulam_2_19_seq_eq_start (n : ℕ) (h : n < 2) : ulam_2_19_seq n = [2, 19].get ⟨n, h⟩ := by
  -- For n < 2, we can check the values directly.
  interval_cases n <;> simp [ulam_2_19_seq];
  · -- By definition of `ulam_seq`, when `n = 0`, it returns the first element of the start list, which is `2`.
    simp [ulam_seq];
  · -- By definition of `ulam_seq`, when `n = 1`, it returns the second element of the list `[2, 19]`, which is `19`.
    simp [ulam_seq]

lemma ulam_2_19_seq_eq_next (n : ℕ) (h : n ≥ 2) :
  ulam_2_19_seq n =
    let prev := (List.range n).attach.map (fun ⟨i, hi⟩ => ulam_2_19_seq i)
    match next_ulam_prime prev with
    | some p => p
    | none => 0 := by
      -- Apply the definition of `ulam_2_19_seq` to conclude the proof.
      apply ulam_2_19_recurrence; assumption

lemma ulam_2_19_ge_2_aux (n : ℕ) : ulam_2_19_seq n = 0 ∨ ulam_2_19_seq n ≥ 2 := by
  have h_val : ∀ n, ulam_2_19_seq n ≥ 2 ∨ ulam_2_19_seq n = 0 := by
    intro n
    by_cases h : n < 2;
    · interval_cases n <;> native_decide;
    · -- By definition of `ulam_2_19_seq`, if `n ≥ 2`, then `ulam_2_19_seq n` is either the next Ulam prime or 0.
      have h_def : ulam_2_19_seq n = let prev := (List.range n).attach.map (fun ⟨i, hi⟩ => ulam_2_19_seq i); match next_ulam_prime prev with | some p => p | none => 0 := by
        -- By definition of `ulam_2_19_seq`, if `n ≥ 2`, then `ulam_2_19_seq n` is defined as the next Ulam prime after the previous terms or 0. This follows directly from the recursive definition.
        apply ulam_2_19_seq_eq_next;
        exact le_of_not_gt h;
      rcases h_def' : next_ulam_prime ( List.map ( fun x => match x with | ⟨ i, hi ⟩ => ulam_2_19_seq i ) ( List.attach ( List.range n ) ) ) with ( _ | p ) <;> simp_all +decide;
      -- Since p is a prime number, it must be at least 2.
      have h_prime : Nat.Prime p := by
        unfold next_ulam_prime at h_def';
        have h_prime : ∀ {l : List ℕ}, (∀ x ∈ l, Nat.Prime x) → ∀ p, min_nat l = some p → Nat.Prime p := by
          intros l hl p hp; exact (by
          have h_prime : p ∈ l := by
            exact?;
          exact hl p h_prime);
        grind;
      exact Or.inl h_prime.two_le;
  exact Or.symm ( h_val n )

theorem ulam_2_p_terminates_correct (p : ℕ) (hp : Nat.Prime p) (hp_gt_3 : p > 3) (hp_mod : p % 3 = 2) :
  next_ulam_prime [2, p] = none := by
    -- Apply the lemma that states the next Ulam prime for [2, p] is none when p is a prime greater than 3 and congruent to 2 modulo 3.
    apply ulam_2_p_terminates p hp hp_gt_3 hp_mod

#eval (iterate_ulam_seq [2, 19] 2000).length

#eval (iterate_ulam_seq [2, 3] 100).length
#eval (iterate_ulam_seq [2, 3] 500).length

def check_ulam_2_19_conjecture (n : ℕ) : Bool :=
  let ulam := iterate_ulam_seq [2, 19] n
  let primes_mod_18 := (List.range (ulam.getLast! + 1)).filter (fun x => x.Prime ∧ x % 18 = 1)
  -- Check if ulam (excluding 2) is exactly primes_mod_18
  let ulam_tail := ulam.tail
  ulam_tail == primes_mod_18

#eval check_ulam_2_19_conjecture 50
#eval check_ulam_2_19_conjecture 100

#eval iterate_ulam_seq [3, 5] 20

#eval iterate_ulam_seq [3, 5] 30

def Ulam2_19_Prime_Candidates_Hypothesis : Prop :=
  ∀ n, ulam_2_19_seq n ≠ 0 →
    ∃ p, next_ulam_prime ((List.range (n + 1)).attach.map (fun ⟨i, hi⟩ => ulam_2_19_seq i)) = some p

theorem ulam_2_19_infinite_conditional (h_hyp : Ulam2_19_Prime_Candidates_Hypothesis) (n : ℕ) :
  ulam_2_19_seq n ≠ 0 := by
    -- Apply the hypothesis `h_hyp` to `n` to obtain the existence of `p` such that the next Ulam prime is `p`.
    apply Classical.byContradiction
    intro h_zero;
    induction' n using Nat.strong_induction_on with n ih;
    rcases n with ( _ | _ | n ) <;> simp_all +decide [ ulam_2_19_seq_eq_start, ulam_2_19_seq_eq_next ];
    cases h : next_ulam_prime ( List.map ulam_2_19_seq ( List.range ( n + 1 + 1 ) ) ) <;> simp_all +decide;
    · specialize h_hyp ( n + 1 ) ; aesop;
    · unfold next_ulam_prime at h;
      rcases h' : List.getLast? ( List.map ulam_2_19_seq ( List.range ( n + 1 + 1 ) ) ) with ( _ | ⟨ q_n, _ | ⟨ q_n, _ | h ⟩ ⟩ ) <;> simp_all +decide;
      · grind;
      · have := min_nat_mem _ _ h; simp_all +decide ;

theorem UlamConjecture_Conditional (h_hyp : Ulam2_19_Prime_Candidates_Hypothesis) : UlamConjecture := by
  use [2, 19];
  -- By definition of UlamConjecture, we need to show that there exists a start list and a q function such that the Ulam sequence generated by q and start is infinite. We can take q = ulam_2_19_seq.
  use by norm_num, by norm_num, ulam_2_19_seq;
  constructor;
  · native_decide;
  · intro n hn;
    -- Apply the hypothesis `h_hyp` to `n` to obtain the existence of `p` such that `next_ulam_prime (List.map ulam_2_19_seq (List.range (n + 1))) = some p`.
    obtain ⟨p, hp⟩ := h_hyp n (by
    exact?);
    rw [ ulam_2_19_seq_eq_next ];
    · aesop;
    · exact Nat.succ_le_succ hn

lemma ulam_2_19_mod_18_conditional (h_hyp : Ulam2_19_Prime_Candidates_Hypothesis) (n : ℕ) :
  n ≥ 1 → ulam_2_19_seq n % 18 = 1 := by
    -- Apply the hypothesis `h_mod_18` directly.
    intros hn
    apply (ulam_seq_2_19_mod_18_proven ulam_2_19_seq (by
    constructor;
    · native_decide +revert;
    · rintro ( _ | _ | n ) <;> simp +arith +decide;
      · unfold ulam_2_19_seq;
        unfold ulam_seq; simp +arith +decide [ List.range_succ ] ;
        unfold ulam_seq; simp +decide [ List.range_succ ] ;
        unfold next_ulam_prime; simp +decide [ List.range_succ ] ;
        unfold min_nat; simp +decide [ List.range_succ ] ;
      · rw [ ulam_2_19_seq_eq_next ];
        · cases h_hyp ( n + 2 ) ( by
            exact? ) ; aesop;
        · linarith)) n hn


/-
If a and b are 1 mod m, then a + b - 1 is 1 mod m.
-/
lemma mod_m_sum_minus_one (a b m : ℕ) (ha : a % m = 1) (hb : b % m = 1) : (a + b - 1) % m = 1 := by
  rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.add_mod ];
  · grind;
  · rw [ ← Nat.mod_add_div a ( m + 2 ), ← Nat.mod_add_div b ( m + 2 ), ha, hb ];
    norm_num [ add_assoc, Nat.add_mod, Nat.mul_mod ]

/-
If q_n is 1 mod m (where m is even) and q_n >= 2, then q_n + 2 - 1 is not prime.
-/
lemma ulam_step_2_is_composite (q_n m : ℕ) (hm : 2 ∣ m) (h_mod : q_n % m = 1) (h_ge_2 : q_n ≥ 2) : ¬ Nat.Prime (q_n + 2 - 1) := by
  -- Since $m$ is even, $q_n \equiv 1 \pmod{2}$, which means $q_n$ is odd.
  have hq_n_odd : q_n % 2 = 1 := by
    rcases hm with ⟨ k, rfl ⟩;
    rw [ ← Nat.mod_mod_of_dvd q_n ( dvd_mul_right 2 k ), h_mod ];
  rw [ show q_n + 2 - 1 = 2 * ( q_n / 2 + 1 ) by omega ] ; rw [ Nat.prime_mul_iff ] ; aesop;

/-
If a list starts with 2 and the rest are 1 mod m, and the last element is 1 mod m, then any prime sum of last + element - 1 is 1 mod m.
-/
lemma ulam_mod_m_candidates
  (m : ℕ) (hm : 2 ∣ m)
  (l : List ℕ)
  (h_head : l.head? = some 2)
  (h_tail : ∀ x ∈ l.tail, x % m = 1)
  (q_n : ℕ) (h_last : l.getLast? = some q_n)
  (h_qn_mod : q_n % m = 1)
  (h_qn_ge : q_n ≥ 2) :
  ∀ c ∈ (l.map (fun q_i => q_n + q_i - 1)).filter Nat.Prime, c % m = 1 := by
    intro c hc;
    -- Since $c$ is in the list of candidates, it must be of the form $q_n + q_i - 1$ for some $q_i$ in $l$.
    obtain ⟨q_i, hq_i, hc_eq⟩ : ∃ q_i ∈ l, c = q_n + q_i - 1 := by
      rw [ List.mem_filter ] at hc; aesop;
    -- If $q_i = 2$, then $c = q_n + 1$. Since $q_n \geq 2$, $c \geq 3$. But $c$ is prime, so $c$ must be 3. However, $3 \not\equiv 1 \pmod{m}$ because $m$ is even.
    by_cases hq_i_two : q_i = 2;
    · rcases m with ( _ | _ | m ) <;> simp_all +arith +decide [ Nat.add_mod, Nat.mod_eq_of_lt ];
      cases Nat.Prime.eq_two_or_odd hc.2 <;> cases Nat.mod_two_eq_zero_or_one q_n <;> simp_all +arith +decide [ Nat.add_mod ];
      have := Nat.mod_mod_of_dvd q_n ( show 2 ∣ m + 2 from dvd_add hm ( dvd_refl 2 ) ) ; simp_all +decide ;
    · -- Since $q_i \neq 2$, we have $q_i \in l.tail$.
      have hq_i_tail : q_i ∈ l.tail := by
        cases l <;> aesop;
      have := h_tail q_i hq_i_tail; rw [ hc_eq ] ; rw [ ← Nat.mod_add_div ( q_n + q_i ) m ] ; simp +decide [ *, Nat.add_mod, Nat.mul_mod ] ;
      rcases m with ( _ | _ | _ | m ) <;> simp_all +arith +decide [ Nat.mod_eq_of_lt ];
      grind

/-
The Ulam sequence starting with 2, p (where p is 1 mod m and m is even) is always 1 mod m for n >= 1.
-/
theorem ulam_seq_2_p_mod_even
    (m p : ℕ)
    (hm : 2 ∣ m)
    (hp : Nat.Prime p)
    (hp_mod : p % m = 1)
    (q : ℕ → ℕ)
    (h : IsUlamPrimeSeq q [2, p]) :
    ∀ n ≥ 1, q n % m = 1 := by
  -- Use strong induction on n to show that the sequence values are 1 mod m for n ≥ 1.
  intro n hn
  induction' n using Nat.strong_induction_on with n ih;
  rcases n with ( _ | _ | n ) <;> simp_all +decide;
  · have := h.1 1; aesop;
  · -- Let $L = (List.range (n + 2)).map q$. By the definition of IsUlamPrimeSeq, $q (n + 2)$ is the minimum of the prime candidates generated from $L$.
    set L := (List.range (n + 2)).map q with hL_def
    have hL_last : L.getLast? = some (q (n + 1)) := by
      grind
    have hL_head : L.head? = some 2 := by
      have := h.1 0; simp_all +decide ;
      norm_num [ ← this, List.range_succ_eq_map ] at *
    have hL_tail : ∀ x ∈ L.tail, x % m = 1 := by
      simp_all +decide [ List.range_succ_eq_map ]
    have hL_qn_mod : q (n + 1) % m = 1 := by
      exact ih _ ( Nat.lt_succ_self _ ) ( Nat.succ_pos _ )
    have hL_qn_ge : q (n + 1) ≥ 2 := by
      apply q_ge_2_general;
      rotate_right;
      exacts [ [ 2, p ], by norm_num; linarith [ hp.two_le ], h ]
    have hL_prime_candidates : ∀ c ∈ (L.map (fun q_i => q (n + 1) + q_i - 1)).filter Nat.Prime, c % m = 1 := by
      apply_rules [ ulam_mod_m_candidates ];
      · linarith;
      · linarith
    have hL_min_prime_candidate : ∃ p, next_ulam_prime L = some p := by
      exact Option.ne_none_iff_exists'.mp ( by have := h.2 ( n + 1 ) ( by norm_num ) ; aesop )
    have hL_min_prime_candidate_mod : ∃ p, next_ulam_prime L = some p ∧ p % m = 1 := by
      obtain ⟨ p, hp ⟩ := hL_min_prime_candidate;
      have hL_min_prime_candidate_mod : p ∈ (L.map (fun q_i => q (n + 1) + q_i - 1)).filter Nat.Prime := by
        have hL_min_prime_candidate_mod : min_nat ((L.map (fun q_i => q (n + 1) + q_i - 1)).filter Nat.Prime) = some p := by
          unfold next_ulam_prime at hp; aesop;
        exact min_nat_mem _ _ hL_min_prime_candidate_mod;
      exact ⟨ p, hp, hL_prime_candidates p hL_min_prime_candidate_mod ⟩
    obtain ⟨p, hp_next, hp_mod⟩ := hL_min_prime_candidate_mod
    have hL_qn_plus_2 : q (n + 2) = p := by
      have := h.2 ( n + 1 ) ?_ <;> aesop
    rw [hL_qn_plus_2, hp_mod]
