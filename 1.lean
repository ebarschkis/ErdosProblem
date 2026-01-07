import Mathlib


open Filter

open scoped Topology Real

namespace Erdos1

/--
A finite set of naturals $A$ is said to be a sum-distinct set for $N \in \mathbb{N}$ if
$A\subseteq\{1, ..., N\}$ and the sums  $\sum_{a\in S}a$ are distinct for all $S\subseteq A$
-/
def IsSumDistinctSet (A : Finset ℕ) (N : ℕ) : Prop :=
    A ⊆ Finset.Icc 1 N ∧
      Function.Injective (fun (⟨S, _⟩ : A.powerset) => S.sum id)

/-
If $A\subseteq\{1, ..., N\}$ with $|A| = n$ is such that the subset sums $\sum_{a\in S}a$ are
distinct for all $S\subseteq A$ then
$$
  N \gg 2 ^ n.
$$
The powers of 2 achieve $N \leq 2^n - 1$, so this would be asymptotically optimal up to a constant.
-/
theorem sum_distinct_set_lower_bound :
    ∃ C > (0 : ℝ),
      ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
        N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
The trivial lower bound is $N \gg 2^n / n$.
-/
theorem sum_distinct_set_trivial_lower_bound :
    ∃ C > (0 : ℝ),
      ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),
        N ≠ 0 → C * 2 ^ A.card / A.card < N := by
  have := @sum_distinct_set_lower_bound;
  obtain ⟨ C, hC₀, hC ⟩ := this;
  refine' ⟨ C / 2, half_pos hC₀, fun N A hA hN ↦ _ ⟩ ; specialize hC N A hA hN ; rcases A.eq_empty_or_nonempty with ( rfl | ⟨ a, ha ⟩ ) <;> norm_num at *;
  · positivity;
  · rw [ div_lt_iff₀ ] <;> nlinarith [ show ( A.card : ℝ ) ≥ 1 by exact_mod_cast Finset.card_pos.mpr ⟨ a, ha ⟩, pow_pos ( zero_lt_two' ℝ ) A.card ]

/-
Erdős and Moser [Er56] proved
$$
  N \geq (\tfrac{1}{4} - o(1)) \frac{2^n}{\sqrt{n}}.
$$

[Er56] Erdős, P., _Problems and results in additive number theory_. Colloque sur la Th\'{E}orie des Nombres, Bruxelles, 1955 (1956), 127-137.
-/
noncomputable section AristotleLemmas

/-
The sum of squared deviations of subset sums from their mean is proportional to the sum of squares of the elements.
-/
lemma sum_sq_subset_sum_sub_mean (A : Finset ℕ) :
  ∑ S ∈ A.powerset, ((S.sum (fun x => (x : ℝ))) - (A.sum (fun x => (x : ℝ))) / 2) ^ 2 = 2 ^ A.card * (∑ x ∈ A, (x : ℝ) ^ 2) / 4 := by
    induction A using Finset.induction <;> simp_all +decide [ Finset.sum_powerset_insert ];
    rename_i k hk₁ hk₂;
    rw [ ← Finset.sum_add_distrib ];
    rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.sum_insert ( Finset.notMem_mono ( Finset.mem_powerset.mp hx ) hk₁ ) ] ];
    ring_nf at *;
    simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, mul_assoc ] ; ring;
    norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] at * ; linarith

/-
The sum of squared deviations of a set of distinct integers from their mean is minimized when the integers are consecutive.
-/
lemma sum_sq_dist_ge_of_distinct_int {Y : Finset ℝ} (hY : ∀ y ∈ Y, ∃ n : ℤ, y = n) :
  ∑ y ∈ Y, (y - (∑ z ∈ Y, z) / Y.card) ^ 2 ≥ Y.card * ((Y.card : ℝ) ^ 2 - 1) / 12 := by
    -- Let $m = |Y|$. Since elements of $Y$ are distinct integers, we can list them as $y_1 < y_2 < \dots < y_m$.
    set m := Y.card with hm
    have h_sorted : ∃ y : Fin m → ℝ, StrictMono y ∧ ∀ i, y i ∈ Y := by
      exact ⟨ fun i => Y.orderEmbOfFin rfl i, by simp +decide [ StrictMono ], fun i => Y.orderEmbOfFin_mem rfl _ ⟩;
    -- We have $y_{j} - y_{i} \ge j - i$ for $j > i$.
    obtain ⟨y, hy_mono, hy_mem⟩ : ∃ y : Fin m → ℝ, StrictMono y ∧ ∀ i, y i ∈ Y := h_sorted
    have h_diff : ∀ i j : Fin m, i < j → y j - y i ≥ j - i := by
      choose! n hn using hY;
      -- Since $y$ is strictly monotone, we have $n(y_j) > n(y_i)$ for $i < j$.
      have h_n_mono : ∀ i j : Fin m, i < j → n (y j) > n (y i) := by
        exact fun i j hij => by have := hy_mono hij; exact_mod_cast ( by linarith [ hn ( y i ) ( hy_mem i ), hn ( y j ) ( hy_mem j ) ] : ( n ( y i ) : ℝ ) < n ( y j ) ) ;
      -- By induction on $j - i$, we can show that $n(y_j) - n(y_i) \geq j - i$.
      have h_ind : ∀ i j : Fin m, i < j → n (y j) - n (y i) ≥ j - i := by
        intro i j hij; induction' j with j hj generalizing i; induction' i with i hi; norm_num at *;
        induction hij <;> norm_num at *;
        · linarith [ h_n_mono ⟨ i, hi ⟩ ⟨ i + 1, hj ⟩ ( Nat.lt_succ_self _ ) ];
        · linarith [ ‹∀ ( hj : _ < m ), ( _ : ℤ ) ≤ n ( y ⟨ _, hj ⟩ ) - n ( y ⟨ i, hi ⟩ ) + i› ( Nat.lt_of_succ_lt hj ), h_n_mono ⟨ _, Nat.lt_of_succ_lt hj ⟩ ⟨ _, hj ⟩ ( Nat.lt_succ_self _ ) ];
      intro i j hij; specialize h_ind i j hij; rw [ hn ( y j ) ( hy_mem j ), hn ( y i ) ( hy_mem i ) ] ; norm_cast at *;
    -- We use the identity $\sum_{y \in Y} (y - \bar{y})^2 = \frac{1}{2m} \sum_{y, z \in Y} (y - z)^2$.
    have h_identity : ∑ y ∈ Y, (y - (∑ z ∈ Y, z) / (m : ℝ)) ^ 2 = (1 / (2 * m : ℝ)) * ∑ i : Fin m, ∑ j : Fin m, (y i - y j) ^ 2 := by
      have h_identity : ∑ y ∈ Y, (y - (∑ z ∈ Y, z) / (m : ℝ)) ^ 2 = (1 / (2 * m : ℝ)) * ∑ y ∈ Y, ∑ z ∈ Y, (y - z) ^ 2 := by
        by_cases hm : m = 0 <;> simp_all +decide [ Finset.sum_add_distrib, sub_sq, Finset.mul_sum _ _ _, Finset.sum_mul ];
        · rw [ eq_comm ] at * ; aesop;
        · norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ] ; ring;
          simpa [ sq, mul_assoc, ne_of_gt ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hm ) ) ] using by ring;
      have h_image : Finset.image y Finset.univ = Y := by
        exact Finset.eq_of_subset_of_card_le ( Finset.image_subset_iff.mpr fun i _ => hy_mem i ) ( by rw [ Finset.card_image_of_injective _ hy_mono.injective, Finset.card_fin ] );
      rw [ h_identity, ← h_image, Finset.sum_image <| by simp +decide [ hy_mono.injective.eq_iff ] ];
      rw [ Finset.sum_congr rfl fun i hi => Finset.sum_image <| by intros a ha b hb hab; exact hy_mono.injective hab ];
    -- Using the inequality $y_j - y_i \ge j - i$, we can bound the sum $\sum_{i < j} (y_j - y_i)^2$.
    have h_bound : ∑ i : Fin m, ∑ j : Fin m, (y i - y j) ^ 2 ≥ ∑ i : Fin m, ∑ j : Fin m, (i - j : ℝ) ^ 2 := by
      refine' Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => _;
      rcases lt_trichotomy i j with hij | rfl | hij <;> norm_num at *;
      · nlinarith only [ h_diff i j hij, show ( i : ℝ ) < j from Nat.cast_lt.mpr hij ];
      · nlinarith only [ show ( i : ℝ ) ≥ j + 1 by exact_mod_cast hij, h_diff _ _ hij ];
    -- Evaluating the sum $\sum_{i < j} (i - j)^2$, we get $\frac{m(m^2 - 1)}{12}$.
    have h_sum : ∑ i : Fin m, ∑ j : Fin m, (i - j : ℝ) ^ 2 = (m : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) / 6 := by
      norm_num [ sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ];
      norm_num [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      -- Evaluating the sum $\sum_{i=0}^{m-1} i^2$, we get $\frac{(m-1)m(2m-1)}{6}$.
      have h_sum_sq : ∑ i : Fin m, (i : ℝ) ^ 2 = (m * (m - 1) * (2 * m - 1) : ℝ) / 6 := by
        exact Nat.recOn m ( by norm_num ) fun n ih => by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith;
      rw [ h_sum_sq ] ; rw [ show ( ∑ i : Fin m, ( i : ℝ ) ) = m * ( m - 1 ) / 2 from Nat.recOn m ( by norm_num ) fun n ih ↦ by norm_num [ Fin.sum_univ_castSucc ] at * ; linarith ] ; ring;
    rcases m with ( _ | _ | m ) <;> norm_num at *;
    · linarith;
    · exact Finset.sum_nonneg fun _ _ => sq_nonneg _;
    · nlinarith [ inv_mul_cancel_left₀ ( by linarith : ( m : ℝ ) + 1 + 1 ≠ 0 ) ( ∑ i : Fin ( m + 1 + 1 ), ∑ j : Fin ( m + 1 + 1 ), ( y i - y j ) ^ 2 ) ]

/-
If a set has distinct subset sums, the sum of squares of its elements is at least $(4^n - 1)/3$.
-/
lemma sum_sq_ge_of_sum_distinct {N : ℕ} {A : Finset ℕ} (h : Erdos1.IsSumDistinctSet A N) :
  ∑ x ∈ A, (x : ℝ) ^ 2 ≥ ((4 : ℝ) ^ A.card - 1) / 3 := by
    -- By the properties of the sum of squares and the variance, we have:
    have h_var : (∑ S ∈ A.powerset, ((S.sum (fun x => (x : ℝ))) - (A.sum (fun x => (x : ℝ))) / 2) ^ 2) ≥ (∑ y ∈ Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset, (y - (Finset.sum (Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset) (fun y => y)) / (Finset.card (Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset))) ^ 2) := by
      have h_var : (∑ S ∈ A.powerset, ((S.sum (fun x => (x : ℝ))) - (A.sum (fun x => (x : ℝ))) / 2) ^ 2) = (∑ y ∈ Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset, (y - (A.sum (fun x => (x : ℝ))) / 2) ^ 2) := by
        rw [ Finset.sum_image ];
        -- Since $A$ is a sum-distinct set, the sums of different subsets of $A$ are distinct.
        have h_inj : ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → (∑ x ∈ S, (x : ℝ)) = (∑ x ∈ T, (x : ℝ)) → S = T := by
          have := h.2;
          contrapose! this;
          norm_num [ Function.Injective ];
          obtain ⟨ S, T, hS, hT, hsum, hne ⟩ := this; use S, hS, T, hT; norm_cast at *;
          exact ⟨ by rw [ ← @Nat.cast_inj ℝ ] ; aesop, hne ⟩;
        exact fun S hS T hT hST => h_inj S T ( Finset.mem_powerset.mp hS ) ( Finset.mem_powerset.mp hT ) hST;
      rw [h_var];
      have h_var : ∀ (Y : Finset ℝ) (μ : ℝ), (∑ y ∈ Y, (y - μ) ^ 2) ≥ (∑ y ∈ Y, (y - (∑ y ∈ Y, y) / Y.card) ^ 2) := by
        intros Y μ
        have h_var : ∑ y ∈ Y, (y - μ) ^ 2 = ∑ y ∈ Y, (y - (Finset.sum Y (fun y => y)) / Y.card) ^ 2 + Y.card * (μ - (Finset.sum Y (fun y => y)) / Y.card) ^ 2 := by
          by_cases hY : Y = ∅ <;> simp +decide [ hY, sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul ] ; ring;
          simpa [ ← Finset.sum_mul _ _ _, ← Finset.mul_sum, ← Finset.sum_div, sq, mul_assoc, mul_comm, mul_left_comm, hY, ne_of_gt ( Finset.card_pos.mpr ( Finset.nonempty_of_ne_empty hY ) ) ] using by ring;
        exact h_var.symm ▸ le_add_of_nonneg_right ( mul_nonneg ( Nat.cast_nonneg _ ) ( sq_nonneg _ ) );
      exact h_var _ _;
    -- Since the subset sums are distinct, the image of the subset sums under the map $S \mapsto \sum_{x \in S} x$ is also distinct.
    have h_distinct : Finset.card (Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset) = 2 ^ A.card := by
      have := h.2;
      rw [ Finset.card_image_of_injOn, Finset.card_powerset ];
      exact fun x hx y hy hxy => by simpa [ Subtype.ext_iff ] using @this ⟨ x, hx ⟩ ⟨ y, hy ⟩ <| by simpa [ ← @Nat.cast_inj ℝ ] using hxy;
    have h_sum_sq_dist_ge_of_distinct_int : ∑ y ∈ Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset, (y - (Finset.sum (Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset) (fun y => y)) / (Finset.card (Finset.image (fun S => S.sum (fun x => (x : ℝ))) A.powerset))) ^ 2 ≥ (2 ^ A.card : ℝ) * (((2 ^ A.card : ℝ) ^ 2 - 1) / 12) := by
      convert sum_sq_dist_ge_of_distinct_int _ using 1;
      · rw [ h_distinct ] ; push_cast ; ring;
      · simp +zetaDelta at *;
        exact fun a ha => ⟨ ∑ x ∈ a, x, by push_cast; rfl ⟩;
    have := sum_sq_subset_sum_sub_mean A;
    rw [ show ( 4 : ℝ ) ^ A.card = ( 2 ^ A.card ) ^ 2 by norm_num [ sq, ← mul_pow ] ] ; nlinarith [ pow_pos ( zero_lt_two' ℝ ) A.card ]

end AristotleLemmas

theorem sum_distinct_set_erdos_moser_lower_bound :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
        (1 / 4 - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  refine' ⟨ _, _, _ ⟩;
  exact fun k => 0;
  · norm_num [ Asymptotics.isLittleO_iff_tendsto ];
  · intro N A hA
    have h_sum_sq : ∑ x ∈ A, (x : ℝ) ^ 2 ≥ ((4 : ℝ) ^ A.card - 1) / 3 := by
      convert sum_sq_ge_of_sum_distinct hA using 1;
    -- Since $A \subseteq \{1, \dots, N\}$, we have $x \le N$ for all $x \in A$, so $\sum x^2 \le n N^2$.
    have h_sum_sq_le : ∑ x ∈ A, (x : ℝ) ^ 2 ≤ A.card * N ^ 2 := by
      exact le_trans ( Finset.sum_le_sum fun x hx => pow_le_pow_left₀ ( Nat.cast_nonneg _ ) ( Nat.cast_le.mpr ( hA.1 hx |> Finset.mem_Icc.mp |>.2 ) ) 2 ) ( by norm_num );
    rcases A with ⟨ ⟨ l, hl ⟩ ⟩ <;> norm_num at *;
    rw [ div_le_iff₀ ] <;> try positivity;
    rw [ ← Real.sqrt_sq ( Nat.cast_nonneg N ) ];
    rw [ ← Real.sqrt_mul <| by positivity ] ; refine' Real.le_sqrt_of_sq_le _ ; ring_nf at * ; norm_num at *;
    norm_num [ pow_mul' ] at * ; linarith [ pow_le_pow_right₀ ( by norm_num : ( 1 : ℝ ) ≤ 4 ) ( show List.length ‹_› ≥ 0 by norm_num ) ]

/--
A number of improvements of the constant $\frac{1}{4}$ have been given, with the current
record $\sqrt{2 / \pi}$ first provied in unpublished work of Elkies and Gleason.
-/
theorem sum_distinct_set_elkies_gleason_lower_bound :
    ∃ (o : ℕ → ℝ) (_ : o =o[atTop] (1 : ℕ → ℝ)),
      ∀ (N : ℕ) (A : Finset ℕ) (h : IsSumDistinctSet A N),
        (√(2 / π) - o A.card) * 2 ^ A.card / (A.card : ℝ).sqrt ≤ N := by
  sorry

/--
A finite set of real numbers is said to be sum-distinct if all the subset sums differ by
at least $1$.
-/
def IsSumDistinctRealSet (A : Finset ℝ) (N : ℕ) : Prop :=
    (A : Set ℝ) ⊆ Set.Ioc 0 N ∧
      (A.powerset : Set (Finset ℝ)).Pairwise fun S₁ S₂ =>
        1 ≤ dist (S₁.sum id) (S₂.sum id)

/--
A generalisation of the problem to sets $A \subseteq (0, N]$ of real numbers, such that the subset
sums all differ by at least $1$ is proposed in [Er73] and [ErGr80].

[Er73] Erdős, P., _Problems and results on combinatorial number theory_. A survey of combinatorial theory (Proc. Internat. Sympos., Colorado State Univ., Fort Collins, Colo., 1971) (1973), 117-138.

[ErGr80] Erdős, P. and Graham, R., _Old and new problems and results in combinatorial number theory_. Monographies de L'Enseignement Mathematique (1980).
-/
theorem sum_distinct_real_set_lower_bound :
    ∃ C > (0 : ℝ),
      ∀ (N : ℕ) (A : Finset ℝ) (_ : IsSumDistinctRealSet A N),
        N ≠ 0 → C * 2 ^ A.card < N := by
  sorry

/--
The minimal value of $N$ such that there exists a sum-distinct set with three
elements is $4$.

https://oeis.org/A276661
-/
theorem sum_distinct_set_card_three_min_N :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 3 } 4 := by
  refine ⟨⟨{1, 2, 4}, ?_⟩, ?_⟩
  · simp
    refine ⟨by decide, ?_⟩
    let P := Finset.powerset {1, 2, 4}
    have : Finset.univ.image (fun p : P ↦ ∑ x ∈ p, x) = {0, 1, 2, 4, 3, 5, 6, 7} := by
      refine Finset.ext_iff.mpr (fun n => ?_)
      simp [show P = {{}, {1}, {2}, {4}, {1, 2}, {1, 4}, {2, 4}, {1, 2, 4}} by decide]
      omega
    rw [← Set.injOn_univ, ← Finset.coe_univ]
    have :
        (Finset.univ.image (fun p : P ↦ ∑ x ∈ p.1, x)).card =
          (Finset.univ (α := P)).card := by
      rw [this]; aesop
    exact Finset.injOn_of_card_image_eq this
  · simp [IsSumDistinctSet, mem_lowerBounds]
    intro n S h h_inj hcard3
    by_contra hn
    interval_cases n; aesop; aesop
    · have := Finset.card_le_card h
      aesop
    · absurd h_inj
      rw [(Finset.subset_iff_eq_of_card_le (Nat.le_of_eq (by rw [hcard3]; decide))).mp h]
      decide

/--
The minimal value of $N$ such that there exists a sum-distinct set with five
elements is $13$.

https://oeis.org/A276661
-/
theorem sum_distinct_set_card_five_min_N :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 5 } 13 := by
  constructor;
  · -- Consider the set $A = \{6, 9, 11, 12, 13\}$.
    use {6, 9, 11, 12, 13};
    simp +arith +decide [ Erdos1.IsSumDistinctSet ];
  · intro N hN
    obtain ⟨A, hA_set, hA_card⟩ := hN
    have hA_subset : A ⊆ Finset.Icc 1 N := hA_set.left
    have hA_distinct : Function.Injective (fun (⟨S, _⟩ : A.powerset) => S.sum id) := hA_set.right;
    -- Let's assume for contradiction that $N < 13$.
    by_contra h_contra;
    -- Since $N < 13$, we have $A \subseteq \{1, 2, ..., 12\}$.
    have hA_subset_12 : A ⊆ Finset.Icc 1 12 := by
      exact Finset.Subset.trans hA_subset ( Finset.Icc_subset_Icc_right ( by linarith ) );
    -- Let's enumerate all possible subsets of $\{1, 2, ..., 12\}$ with 5 elements and check if any of them satisfy the sum-distinct condition.
    have h_enum : ∀ A ⊆ Finset.Icc 1 12, A.card = 5 → ¬Function.Injective (fun (⟨S, _⟩ : A.powerset) => S.sum id) := by
      native_decide +revert;
    exact h_enum A hA_subset_12 hA_card hA_distinct

/--
The minimal value of $N$ such that there exists a sum-distinct set with nine
elements is $161$.

https://oeis.org/A276661
-/
theorem sum_distinct_set_card_nine_min_N :
    IsLeast { N | ∃ A, IsSumDistinctSet A N ∧ A.card = 9 } 161 := by
  sorry

end Erdos1
