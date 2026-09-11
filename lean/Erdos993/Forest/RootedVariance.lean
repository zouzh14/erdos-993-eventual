import Erdos993.RootedRecurrence
import Erdos993.Forest.Interfaces

/-!
# Elementary rooted variance inequalities

This module works only with the numeric observables declared in
`Forest.Interfaces`.  It does not construct those observables from a rooted
forest and does not prove the martingale variance decomposition stored in the
record.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

namespace CanonicalFirstRecoveryState

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The variance in a canonical state is nonnegative. -/
theorem variance_nonneg (C : CanonicalFirstRecoveryState G) : 0 <= C.variance :=
  C.law.variance_nonneg

end CanonicalFirstRecoveryState

namespace RootedForestObservables

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
  {C : CanonicalFirstRecoveryState G}

/-- The conditional vacancy probability `q_v = 1 - p_v`. -/
def vacancyProbability (R : RootedForestObservables C) (v : V) : Real :=
  1 - R.occupationProbability v

/-- The coefficient `a_v p_v q_v` multiplying the squared displacement. -/
def varianceWeight (R : RootedForestObservables C) (v : V) : Real :=
  R.parentAbsentProbability v * R.occupationProbability v * R.vacancyProbability v

theorem vacancyProbability_nonneg (R : RootedForestObservables C) (v : V) :
    0 <= R.vacancyProbability v := by
  exact sub_nonneg.mpr (R.occupationProbability_le_one v)

theorem vacancyProbability_le_one (R : RootedForestObservables C) (v : V) :
    R.vacancyProbability v <= 1 := by
  dsimp [vacancyProbability]
  linarith [R.occupationProbability_nonneg v]

theorem occupation_add_vacancy (R : RootedForestObservables C) (v : V) :
    R.occupationProbability v + R.vacancyProbability v = 1 := by
  simp [vacancyProbability]

theorem varianceWeight_nonneg (R : RootedForestObservables C) (v : V) :
    0 <= R.varianceWeight v := by
  exact mul_nonneg
    (mul_nonneg (R.parentAbsentProbability_nonneg v)
      (R.occupationProbability_nonneg v))
    (R.vacancyProbability_nonneg v)

/-- The elementary Bernoulli bound `p(1-p) <= 1/4`. -/
theorem occupation_mul_vacancy_le_quarter (R : RootedForestObservables C) (v : V) :
    R.occupationProbability v * R.vacancyProbability v <= (1 : Real) / 4 := by
  dsimp [vacancyProbability]
  nlinarith [sq_nonneg (R.occupationProbability v - (1 : Real) / 2)]

/-- Since `0 <= a_v <= 1`, the full variance weight is also at most `1/4`. -/
theorem varianceWeight_le_quarter (R : RootedForestObservables C) (v : V) :
    R.varianceWeight v <= (1 : Real) / 4 := by
  have hpq_nonneg :
      0 <= R.occupationProbability v * R.vacancyProbability v :=
    mul_nonneg (R.occupationProbability_nonneg v) (R.vacancyProbability_nonneg v)
  calc
    R.varianceWeight v <=
        1 * (R.occupationProbability v * R.vacancyProbability v) := by
      dsimp [varianceWeight]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_right (R.parentAbsentProbability_le_one v) hpq_nonneg
    _ <= (1 : Real) / 4 := by
      simpa using R.occupation_mul_vacancy_le_quarter v

theorem contribution_eq_varianceWeight_mul_sq
    (R : RootedForestObservables C) (v : V) :
    R.contribution v = R.varianceWeight v * R.conditionalMeanDifference v ^ 2 := by
  rfl

/-- Every individual contribution is bounded by one quarter of its squared
conditional-mean displacement. -/
theorem contribution_le_quarter_mul_sq (R : RootedForestObservables C) (v : V) :
    R.contribution v <= (1 / 4 : Real) * R.conditionalMeanDifference v ^ 2 := by
  rw [R.contribution_eq_varianceWeight_mul_sq v]
  exact mul_le_mul_of_nonneg_right (R.varianceWeight_le_quarter v) (sq_nonneg _)

/-- Nonnegative summands in the supplied variance decomposition are each at
most the total variance. -/
theorem contribution_le_variance (R : RootedForestObservables C) (v : V) :
    R.contribution v <= C.variance := by
  calc
    R.contribution v <= Finset.univ.sum (fun w => R.contribution w) := by
      exact Finset.single_le_sum
        (fun w _ => R.contribution_nonneg w) (Finset.mem_univ v)
    _ = C.variance := R.sum_contribution

/-- The lower displacement estimate in Theorem 4.2.  This is exactly the
consequence of `g(v) >= c V` and `a_v p_v q_v <= 1/4`. -/
theorem sq_displacement_lower_bound_of_macroscopic_contribution
    (R : RootedForestObservables C) (v : V) (c : Real)
    (hmacro : c * C.variance <= R.contribution v) :
    4 * c * C.variance <= R.conditionalMeanDifference v ^ 2 := by
  have hquarter := R.contribution_le_quarter_mul_sq v
  linarith

/-- Square-root form of the lower displacement estimate. -/
theorem abs_displacement_lower_bound_of_macroscopic_contribution
    (R : RootedForestObservables C) (v : V) (c : Real) (hc : 0 <= c)
    (hmacro : c * C.variance <= R.contribution v) :
    2 * Real.sqrt (c * C.variance) <= |R.conditionalMeanDifference v| := by
  have hvariance : 0 <= C.variance := C.variance_nonneg
  have hproduct : 0 <= c * C.variance := mul_nonneg hc hvariance
  have hsqrt := Real.sq_sqrt hproduct
  have hsq := R.sq_displacement_lower_bound_of_macroscopic_contribution v c hmacro
  apply (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
  rw [sq_abs]
  nlinarith

/-- A lower bound on the variance weight turns `g(v) <= V` into the generic
upper displacement estimate. -/
theorem sq_displacement_upper_bound_of_weight
    (R : RootedForestObservables C) (v : V) (alpha : Real) (halpha : 0 < alpha)
    (hweight : alpha <= R.varianceWeight v) :
    R.conditionalMeanDifference v ^ 2 <= C.variance / alpha := by
  apply (le_div_iff₀ halpha).2
  calc
    R.conditionalMeanDifference v ^ 2 * alpha <=
        R.conditionalMeanDifference v ^ 2 * R.varianceWeight v :=
      mul_le_mul_of_nonneg_left hweight (sq_nonneg _)
    _ = R.contribution v := by
      rw [mul_comm]
      exact (R.contribution_eq_varianceWeight_mul_sq v).symm
    _ <= C.variance := R.contribution_le_variance v

/-- The numerical upper bound in Theorem 4.2, isolated from the analytic facts
that supply `a_v p_v q_v >= rho/784`. -/
theorem sq_displacement_upper_bound_of_rho
    (R : RootedForestObservables C) (v : V) (rho : Real) (hrho : 0 < rho)
    (hweight : rho / 784 <= R.varianceWeight v) :
    R.conditionalMeanDifference v ^ 2 <= (784 / rho) * C.variance := by
  have h := R.sq_displacement_upper_bound_of_weight v (rho / 784) (by positivity) hweight
  calc
    R.conditionalMeanDifference v ^ 2 <= C.variance / (rho / 784) := h
    _ = (784 / rho) * C.variance := by
      field_simp

/-- Pointwise form of equation (4.4): a macroscopic contribution, the lower
variance scale, and the upper order scale force displacement linear in order. -/
theorem linear_displacement_lower_bound
    (R : RootedForestObservables C) (v : V) (c cV CV cN CN : Real)
    (hc : 0 < c) (hcV : 0 < cV) (hCN : 0 < CN)
    (hmacro : c * C.variance <= R.contribution v)
    (hscale : FirstRecoveryScaleAt C cV CV cN CN) :
    (2 * Real.sqrt (c * cV) / CN) * (C.order : Real) <=
      |R.conditionalMeanDifference v| := by
  have hvariance_scale := hscale.1
  have horder_scale := hscale.2.2.2
  have hsq := R.sq_displacement_lower_bound_of_macroscopic_contribution v c hmacro
  have hscaled_variance :
      4 * c * (cV * (C.index : Real) ^ 2) <= 4 * c * C.variance :=
    mul_le_mul_of_nonneg_left hvariance_scale (by positivity)
  have hccV : 0 <= c * cV := mul_nonneg hc.le hcV.le
  have hsqrt := Real.sq_sqrt hccV
  have hindex_nonneg : 0 <= (C.index : Real) := Nat.cast_nonneg _
  have hindex_displacement :
      2 * Real.sqrt (c * cV) * (C.index : Real) <=
        |R.conditionalMeanDifference v| := by
    apply (sq_le_sq₀ (by positivity) (abs_nonneg _)).mp
    rw [sq_abs]
    nlinarith
  have hfactor_nonneg : 0 <= 2 * Real.sqrt (c * cV) / CN := by positivity
  have horder_multiplied := mul_le_mul_of_nonneg_left horder_scale hfactor_nonneg
  calc
    (2 * Real.sqrt (c * cV) / CN) * (C.order : Real) <=
        (2 * Real.sqrt (c * cV) / CN) * (CN * (C.index : Real)) :=
      horder_multiplied
    _ = 2 * Real.sqrt (c * cV) * (C.index : Real) := by
      field_simp
    _ <= |R.conditionalMeanDifference v| := hindex_displacement

/-- Existential equation-(4.4) consequence of the named macroscopic
contribution predicate and the first-recovery scale predicate. -/
theorem exists_linear_displacement_of_macroscopic_contribution
    (R : RootedForestObservables C) (c cV CV cN CN : Real)
    (hc : 0 < c) (hcV : 0 < cV) (hCN : 0 < CN)
    (hmacro : HasMacroscopicVarianceContribution R c)
    (hscale : FirstRecoveryScaleAt C cV CV cN CN) :
    exists v, (2 * Real.sqrt (c * cV) / CN) * (C.order : Real) <=
      |R.conditionalMeanDifference v| := by
  obtain ⟨v, hv⟩ := hmacro
  exact ⟨v, R.linear_displacement_lower_bound v c cV CV cN CN
    hc hcV hCN hv hscale⟩

end RootedForestObservables

end
end Forest
end Erdos993
