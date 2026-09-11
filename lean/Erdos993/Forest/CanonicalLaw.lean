import Erdos993.Forest.Specification

/-!
# Finite identities for the canonical hard-core law

This module extends the finite-law vocabulary from `Forest.Specification`.
All sums below are finite, and canonical activity is retained as explicit data:
no existence or uniqueness theorem is asserted here.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

namespace FiniteLatticeLaw

variable {α : Type u} [Fintype α]

/-- A rank above a uniform bound for the statistic has zero mass. -/
theorem rankMass_eq_zero_of_stat_le (L : FiniteLatticeLaw α) (n k : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) (hnk : n < k) :
    L.rankMass k = 0 := by
  unfold rankMass
  apply Finset.sum_eq_zero
  intro a ha
  have hak : L.stat a = k := (Finset.mem_filter.mp ha).2
  have := hstat a
  omega

/-- Total rank mass is one when summed over any range containing the statistic. -/
theorem sum_rankMass_range_eq_one (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) :
    ∑ k ∈ Finset.range (n + 1), L.rankMass k = 1 := by
  simp_rw [L.rankMass_eq_sum_probability]
  rw [Finset.sum_comm]
  calc
    (∑ a, ∑ k ∈ Finset.range (n + 1),
        if L.stat a = k then L.probability a else 0) =
        ∑ a, L.probability a := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [eq_comm, Finset.mem_range, hstat a]
    _ = 1 := L.probability_sum

/-- Grouping a weighted expectation by the fibers of the statistic. -/
theorem sum_probability_mul_eq_sum_rankMass (L : FiniteLatticeLaw α)
    (n : ℕ) (hstat : ∀ a, L.stat a ≤ n) (f : ℕ → ℝ) :
    (∑ a, L.probability a * f (L.stat a)) =
      ∑ k ∈ Finset.range (n + 1), L.rankMass k * f k := by
  simp_rw [L.rankMass_eq_sum_probability, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp [eq_comm, Finset.mem_range, hstat a]

/-- The mean can be computed from the finitely supported rank law. -/
theorem mean_eq_sum_rankMass (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) :
    L.mean = ∑ k ∈ Finset.range (n + 1), L.rankMass k * (k : ℝ) := by
  exact L.sum_probability_mul_eq_sum_rankMass n hstat (fun k => (k : ℝ))

/-- The second moment can be computed from the finitely supported rank law. -/
theorem secondMoment_eq_sum_rankMass (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) :
    L.secondMoment =
      ∑ k ∈ Finset.range (n + 1), L.rankMass k * (k : ℝ) ^ 2 := by
  exact L.sum_probability_mul_eq_sum_rankMass n hstat
    (fun k => (k : ℝ) ^ 2)

/-- Variance is the centered second moment of the rank-mass sequence. -/
theorem variance_eq_sum_rankMass (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) :
    L.variance =
      ∑ k ∈ Finset.range (n + 1),
        L.rankMass k * ((k : ℝ) - L.mean) ^ 2 := by
  exact L.sum_probability_mul_eq_sum_rankMass n hstat
    (fun k => ((k : ℝ) - L.mean) ^ 2)

/-- Rearranged mean/variance identity. -/
theorem secondMoment_eq_variance_add_sq_mean (L : FiniteLatticeLaw α) :
    L.secondMoment = L.variance + L.mean ^ 2 := by
  rw [L.variance_eq_secondMoment_sub_sq_mean]
  ring

/-- A bounded natural statistic has mean at most its support bound. -/
theorem mean_le_of_stat_le (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) : L.mean ≤ (n : ℝ) := by
  rw [mean]
  calc
    (∑ a, L.probability a * (L.stat a : ℝ)) ≤
        ∑ a, L.probability a * (n : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (L.probability_nonneg a)
      exact_mod_cast hstat a
    _ = (n : ℝ) := by
      rw [← Finset.sum_mul, L.probability_sum, one_mul]

/-- A bounded natural statistic has second moment at most the squared bound. -/
theorem secondMoment_le_sq_of_stat_le (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) : L.secondMoment ≤ (n : ℝ) ^ 2 := by
  rw [secondMoment]
  calc
    (∑ a, L.probability a * (L.stat a : ℝ) ^ 2) ≤
        ∑ a, L.probability a * (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (L.probability_nonneg a)
      have hnonneg : (0 : ℝ) ≤ L.stat a := Nat.cast_nonneg _
      have hle : (L.stat a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hstat a
      nlinarith
    _ = (n : ℝ) ^ 2 := by
      rw [← Finset.sum_mul, L.probability_sum, one_mul]

/-- Coarse finite-support variance bound. -/
theorem variance_le_sq_of_stat_le (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) : L.variance ≤ (n : ℝ) ^ 2 := by
  rw [L.variance_eq_secondMoment_sub_sq_mean]
  have hsecond := L.secondMoment_le_sq_of_stat_le n hstat
  nlinarith [sq_nonneg L.mean]

end FiniteLatticeLaw

variable {V : Type u} [Fintype V]

/-- Point probabilities of the finite hard-core law are nonnegative. -/
theorem hardCoreLaw_probability_nonneg (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (s : IndepFinset G) :
    0 ≤ (hardCoreLaw G z hz).probability s :=
  (hardCoreLaw G z hz).probability_nonneg s

/-- The finite hard-core law is normalized on actual independent finsets. -/
theorem hardCoreLaw_sum_probability_eq_one (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s = 1 :=
  (hardCoreLaw G z hz).probability_sum

/-- The hard-core statistic is bounded by the number of vertices. -/
theorem hardCoreLaw_stat_le_order (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (s : IndepFinset G) :
    (hardCoreLaw G z hz).stat s ≤ Fintype.card V := by
  change s.val.card ≤ Fintype.card V
  exact Finset.card_le_univ s.val

/-- The hard-core rank law is supported on ranks at most the graph order. -/
theorem hardCoreLaw_rankMass_eq_zero_of_order_lt (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) (k : ℕ) (hk : Fintype.card V < k) :
    (hardCoreLaw G z hz).rankMass k = 0 :=
  FiniteLatticeLaw.rankMass_eq_zero_of_stat_le _ _ _
    (hardCoreLaw_stat_le_order G z hz) hk

/-- Expanded coefficient form of the hard-core rank mass. -/
theorem hardCoreLaw_rankMass_eq_coefficient (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) (k : ℕ) :
    (hardCoreLaw G z hz).rankMass k =
      independenceCoefficients G k * z ^ k / independenceEval G z := by
  simpa [tiltedMass] using hardCoreLaw_rankMass_eq G z hz k

/-- A positive coefficient gives positive mass under every positive activity. -/
theorem hardCoreLaw_rankMass_pos_of_coefficient_pos (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) (k : ℕ)
    (hk : 0 < independenceCoefficients G k) :
    0 < (hardCoreLaw G z hz).rankMass k := by
  rw [hardCoreLaw_rankMass_eq_coefficient]
  exact div_pos (mul_pos hk (pow_pos hz k)) (independenceEval_pos G hz)

/-- Positive rank mass is equivalent to a positive independence coefficient. -/
theorem hardCoreLaw_rankMass_pos_iff_coefficient_pos (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) (k : ℕ) :
    0 < (hardCoreLaw G z hz).rankMass k ↔
      0 < independenceCoefficients G k := by
  constructor
  · intro hmass
    rw [hardCoreLaw_rankMass_eq_coefficient] at hmass
    have hproduct : 0 < independenceCoefficients G k * z ^ k :=
      (div_pos_iff_of_pos_right (independenceEval_pos G hz)).mp hmass
    exact pos_of_mul_pos_left hproduct (pow_nonneg hz.le k)
  · exact hardCoreLaw_rankMass_pos_of_coefficient_pos G z hz k

/-- The hard-core rank masses have total mass one on the natural order range. -/
theorem hardCoreLaw_sum_rankMass_eq_one (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    ∑ k ∈ Finset.range (Fintype.card V + 1),
      (hardCoreLaw G z hz).rankMass k = 1 :=
  FiniteLatticeLaw.sum_rankMass_range_eq_one _ _
    (hardCoreLaw_stat_le_order G z hz)

/-- Coefficient formula for the mean occupation count. -/
theorem hardCoreLaw_mean_eq_sum_coefficients (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (independenceCoefficients G k * z ^ k / independenceEval G z) * (k : ℝ) := by
  rw [FiniteLatticeLaw.mean_eq_sum_rankMass _ _
    (hardCoreLaw_stat_le_order G z hz)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hardCoreLaw_rankMass_eq_coefficient]

/-- Coefficient formula for the second moment of the occupation count. -/
theorem hardCoreLaw_secondMoment_eq_sum_coefficients (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).secondMoment =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (independenceCoefficients G k * z ^ k / independenceEval G z) *
          (k : ℝ) ^ 2 := by
  rw [FiniteLatticeLaw.secondMoment_eq_sum_rankMass _ _
    (hardCoreLaw_stat_le_order G z hz)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hardCoreLaw_rankMass_eq_coefficient]

/-- Coefficient formula for the variance of the occupation count. -/
theorem hardCoreLaw_variance_eq_sum_coefficients (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).variance =
      ∑ k ∈ Finset.range (Fintype.card V + 1),
        (independenceCoefficients G k * z ^ k / independenceEval G z) *
          ((k : ℝ) - (hardCoreLaw G z hz).mean) ^ 2 := by
  rw [FiniteLatticeLaw.variance_eq_sum_rankMass _ _
    (hardCoreLaw_stat_le_order G z hz)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hardCoreLaw_rankMass_eq_coefficient]

/-- The hard-core mean is bounded by the number of vertices. -/
theorem hardCoreLaw_mean_le_order (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean ≤ (Fintype.card V : ℝ) :=
  FiniteLatticeLaw.mean_le_of_stat_le _ _ (hardCoreLaw_stat_le_order G z hz)

/-- Coarse graph-order bound for hard-core variance. -/
theorem hardCoreLaw_variance_le_order_sq (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).variance ≤ (Fintype.card V : ℝ) ^ 2 :=
  FiniteLatticeLaw.variance_le_sq_of_stat_le _ _
    (hardCoreLaw_stat_le_order G z hz)

/-! ## Canonical-state adapters -/

/-- Predicate form of the saddle-point equation.  Its use keeps existence and
uniqueness of canonical activity explicit. -/
def IsCanonicalActivity (G : SimpleGraph V) (index : ℕ) (z : ℝ) : Prop :=
  ∃ hz : 0 < z, (hardCoreLaw G z hz).mean = (index : ℝ)

namespace CanonicalFirstRecoveryState

variable {G : SimpleGraph V}

@[simp] theorem law_stat (C : CanonicalFirstRecoveryState G) (s : IndepFinset G) :
    C.law.stat s = s.val.card := rfl

@[simp] theorem law_probability (C : CanonicalFirstRecoveryState G)
    (s : IndepFinset G) :
    C.law.probability s =
      C.activity ^ s.val.card / independenceEval G C.activity := rfl

/-- The stored activity satisfies the explicit canonical-activity predicate. -/
theorem isCanonicalActivity (C : CanonicalFirstRecoveryState G) :
    IsCanonicalActivity G C.index C.activity :=
  ⟨C.activity_pos, C.mean_eq_index⟩

@[simp] theorem law_mean (C : CanonicalFirstRecoveryState G) :
    C.law.mean = (C.index : ℝ) :=
  C.mean_eq_index

/-- Canonical rank mass in coefficient form. -/
theorem law_rankMass_eq_coefficient (C : CanonicalFirstRecoveryState G) (k : ℕ) :
    C.law.rankMass k =
      independenceCoefficients G k * C.activity ^ k /
        independenceEval G C.activity := by
  exact hardCoreLaw_rankMass_eq_coefficient G C.activity C.activity_pos k

/-- Canonical rank mass vanishes above the graph order. -/
theorem law_rankMass_eq_zero_of_order_lt (C : CanonicalFirstRecoveryState G)
    (k : ℕ) (hk : C.order < k) :
    C.law.rankMass k = 0 := by
  exact hardCoreLaw_rankMass_eq_zero_of_order_lt G C.activity C.activity_pos k hk

/-- Total mass of the canonical rank law. -/
theorem sum_law_rankMass_eq_one (C : CanonicalFirstRecoveryState G) :
    ∑ k ∈ Finset.range (C.order + 1), C.law.rankMass k = 1 := by
  exact hardCoreLaw_sum_rankMass_eq_one G C.activity C.activity_pos

/-- A first-recovery index is an actual rank of the finite graph. -/
theorem index_le_order (C : CanonicalFirstRecoveryState G) : C.index ≤ C.order := by
  have hcoeff : 0 < independenceCoeff G C.index := by
    have hc := C.center_coeff_pos
    change (0 : ℝ) < (independenceCoeff G C.index : ℝ) at hc
    exact_mod_cast hc
  rw [independenceCoeff] at hcoeff
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcoeff
  have hcard : s.val.card = C.index := (Finset.mem_filter.mp hs).2
  rw [← hcard]
  exact Finset.card_le_univ s.val

/-- The central canonical rank has strictly positive probability. -/
theorem center_rankMass_pos (C : CanonicalFirstRecoveryState G) :
    0 < C.law.rankMass C.index :=
  hardCoreLaw_rankMass_pos_of_coefficient_pos G C.activity C.activity_pos C.index
    C.center_coeff_pos

/-- The canonical recovery index is bounded by graph order also at the level
of the real-valued mean. -/
theorem index_cast_le_order (C : CanonicalFirstRecoveryState G) :
    (C.index : ℝ) ≤ (C.order : ℝ) := by
  exact_mod_cast C.index_le_order

/-- The second moment is variance plus the square of the recovery index. -/
theorem law_secondMoment_eq_variance_add_index_sq
    (C : CanonicalFirstRecoveryState G) :
    C.law.secondMoment = C.variance + (C.index : ℝ) ^ 2 := by
  rw [FiniteLatticeLaw.secondMoment_eq_variance_add_sq_mean, law_mean]
  rfl

/-- Centered rank-mass formula for canonical variance. -/
theorem variance_eq_sum_rankMass (C : CanonicalFirstRecoveryState G) :
    C.variance =
      ∑ k ∈ Finset.range (C.order + 1),
        C.law.rankMass k * ((k : ℝ) - (C.index : ℝ)) ^ 2 := by
  have hstat : ∀ s, C.law.stat s ≤ C.order := by
    intro s
    exact hardCoreLaw_stat_le_order G C.activity C.activity_pos s
  simpa only [law_mean] using
    (FiniteLatticeLaw.variance_eq_sum_rankMass C.law C.order hstat)

/-- Coefficient form of canonical variance. -/
theorem variance_eq_sum_coefficients (C : CanonicalFirstRecoveryState G) :
    C.variance =
      ∑ k ∈ Finset.range (C.order + 1),
        (independenceCoefficients G k * C.activity ^ k /
          independenceEval G C.activity) *
            ((k : ℝ) - (C.index : ℝ)) ^ 2 := by
  rw [C.variance_eq_sum_rankMass]
  apply Finset.sum_congr rfl
  intro k hk
  rw [C.law_rankMass_eq_coefficient]

/-- Coarse order bound for the canonical variance. -/
theorem variance_le_order_sq (C : CanonicalFirstRecoveryState G) :
    C.variance ≤ (C.order : ℝ) ^ 2 :=
  hardCoreLaw_variance_le_order_sq G C.activity C.activity_pos

end CanonicalFirstRecoveryState

end
end Forest
end Erdos993
