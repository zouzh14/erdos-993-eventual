import Erdos993.Forest.ActualRootedVariance
import Erdos993.Forest.CanonicalLaw
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual large-displacement contribution

This module formalizes Appendix C, equations C.6--C.25 and Lemma C.2, for the
actual component rootings constructed in `ActualRootedVariance`.  Every local
partition function and conditional law retains the global activity carried by
`C`; no local first-recovery state is introduced.
-/

open scoped BigOperators Topology
open Filter Set

namespace Erdos993
namespace ActualRootedVariance

noncomputable section

universe u

noncomputable local instance finiteSubtypeW22 {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

namespace ComponentRooting

open Forest

variable {V : Type u} [Fintype V]

/-- Appendix C's large-displacement contribution `G(b)`, on an actual
component rooting. -/
noncomputable def G {Γ : SimpleGraph V}
    (C : CanonicalFirstRecoveryState Γ) (R : ComponentRooting Γ) (b : ℝ) : ℝ :=
  ∑ u, if b < |R.conditionalMeanDifference (G := Γ) C u| then
    R.vertexVarianceContribution (G := Γ) C u else 0

/-- Appendix C's parameter `χ = 784 V / b²`. -/
noncomputable def chi {Γ : SimpleGraph V}
    (C : CanonicalFirstRecoveryState Γ) (b : ℝ) : ℝ :=
  784 * C.variance / b ^ 2

variable {G : SimpleGraph V}

/-- The variance of every canonical first-recovery state is strictly positive.
This is derived from the strict rise at the recovery index and the actual
hard-core law, rather than added as a hypothesis to C.18 or C.19. -/
theorem canonicalFirstRecovery_variance_pos
    (C : CanonicalFirstRecoveryState G) : 0 < C.variance := by
  classical
  have hrise := C.firstRecovery.isRecovery.2
  have hcoeff0 : 0 ≤ independenceCoefficients G C.index := Nat.cast_nonneg _
  have hcoeff : 0 < independenceCoefficients G (C.index + 1) :=
    lt_of_le_of_lt hcoeff0 hrise
  have hcoeffNat : 0 < independenceCoeff G (C.index + 1) := by
    change (0 : ℝ) < (independenceCoeff G (C.index + 1) : ℝ) at hcoeff
    exact_mod_cast hcoeff
  rw [independenceCoeff] at hcoeffNat
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcoeffNat
  have hsCard : s.val.card = C.index + 1 := (Finset.mem_filter.mp hs).2
  have hsProb : 0 < C.law.probability s := by
    rw [Forest.CanonicalFirstRecoveryState.law_probability]
    exact div_pos (pow_pos C.activity_pos _) (independenceEval_pos G C.activity_pos)
  have hsTerm :
      0 < C.law.probability s *
        ((C.law.stat s : ℝ) - C.law.mean) ^ 2 := by
    rw [CanonicalFirstRecoveryState.law_stat,
      CanonicalFirstRecoveryState.law_mean, hsCard]
    norm_num at *
    exact hsProb
  unfold Forest.CanonicalFirstRecoveryState.variance
  unfold Forest.FiniteLatticeLaw.variance
  have hle :
      C.law.probability s * ((C.law.stat s : ℝ) - C.law.mean) ^ 2 ≤
        ∑ t, C.law.probability t * ((C.law.stat t : ℝ) - C.law.mean) ^ 2 := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun t => C.law.probability t *
        ((C.law.stat t : ℝ) - C.law.mean) ^ 2)
      (fun t _ => mul_nonneg (C.law.probability_nonneg t) (sq_nonneg _))
      (Finset.mem_univ s)
  exact lt_of_lt_of_le hsTerm hle

/-- Actual conditional occupation is strictly positive. -/
theorem occupationProbability_pos
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    0 < R.occupationProbability (G := G) C u := by
  unfold occupationProbability
  exact div_pos (R.rootedA_pos (G := G) C u) (R.rootedP_pos (G := G) C u)

/-- Actual conditional vacancy is strictly positive. -/
theorem vacancyProbability_pos
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    0 < R.vacancyProbability (G := G) C u := by
  unfold vacancyProbability
  exact div_pos (R.rootedQ_pos (G := G) C u) (R.rootedP_pos (G := G) C u)

/-- Actual occupation odds recurrence, Appendix C equation C.6. -/
theorem occupationOdds_eq_activity_mul_prod_children
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupationProbability (G := G) C u /
        R.vacancyProbability (G := G) C u =
      C.activity * ∏ v ∈ R.children (G := G) u,
        R.vacancyProbability (G := G) C v := by
  classical
  unfold occupationProbability vacancyProbability
  rw [div_div_div_cancel_right₀ (ne_of_gt (R.rootedP_pos (G := G) C u))]
  rw [R.rootedA_eq_activity_mul_prod_rootedQ (G := G) C u,
    R.rootedQ_eq_prod_rootedP (G := G) C u]
  rw [mul_div_assoc, Finset.prod_div_distrib]

/-- Under the activity cap, every actual conditional vacancy exceeds `1/28`. -/
theorem one_div_twentyEight_lt_vacancyProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    (1 : ℝ) / 28 < R.vacancyProbability (G := G) C u := by
  have hp := R.occupationProbability_pos (G := G) C u
  have hq := R.vacancyProbability_pos (G := G) C u
  have hprod :
      (∏ v ∈ R.children (G := G) u,
        R.vacancyProbability (G := G) C v) ≤ 1 := by
    classical
    apply Finset.prod_le_one
    · intro v hv
      exact (R.vacancyProbability_pos (G := G) C v).le
    · intro v hv
      have hs := R.occupationProbability_add_vacancyProbability (G := G) C v
      linarith [R.occupationProbability_nonneg (G := G) C v]
  have hodds := R.occupationOdds_eq_activity_mul_prod_children (G := G) C u
  have hodds_lt :
      R.occupationProbability (G := G) C u /
          R.vacancyProbability (G := G) C u < 27 := by
    rw [hodds]
    have hz0 := C.activity_pos.le
    nlinarith [mul_le_mul_of_nonneg_left hprod hz0]
  have hpq := R.occupationProbability_add_vacancyProbability (G := G) C u
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 28)).2
  apply (div_lt_iff₀ hq).mp at hodds_lt
  nlinarith

/-- Under the activity cap, every actual occupation probability is below
`27/28`. -/
theorem occupationProbability_lt_twentySeven_div_twentyEight
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    R.occupationProbability (G := G) C u < (27 : ℝ) / 28 := by
  have hq := R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz u
  have hpq := R.occupationProbability_add_vacancyProbability (G := G) C u
  linarith

/-- Actual parent-absence marginals exceed `1/28` at every vertex.  For a
nonroot this is C.9 plus the vacancy bound; a component root has value one. -/
theorem one_div_twentyEight_lt_parentAbsentProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    (1 : ℝ) / 28 < R.parentAbsentProbability (G := G) C u := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · rw [hu, R.parentAbsentProbability_rootOf (G := G) C]
    norm_num
  · let p := R.selectedParent (G := G) u hu
    have hpu : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hu
    rw [R.parentAbsentProbability_child (G := G) C hpu]
    have ha := R.parentAbsentProbability_le_one (G := G) C p
    have hp := R.occupationProbability_nonneg (G := G) C p
    have hq := R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz p
    have hpq := R.occupationProbability_add_vacancyProbability (G := G) C p
    nlinarith

/-- Actual vertex contributions are nonnegative. -/
theorem vertexVarianceContribution_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    0 ≤ R.vertexVarianceContribution (G := G) C u := by
  unfold vertexVarianceContribution
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (R.parentAbsentProbability_nonneg (G := G) C u)
        (R.occupationProbability_nonneg (G := G) C u))
      (R.vacancyProbability_pos (G := G) C u).le)
    (sq_nonneg _)

/-- Actual subtree variance masses are nonnegative. -/
theorem subtreeVarianceMass_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    0 ≤ R.subtreeVarianceMass (G := G) C u := by
  unfold subtreeVarianceMass subtreeVariance vacantVariance
  have ha0 := R.parentAbsentProbability_nonneg (G := G) C u
  have ha1 := R.parentAbsentProbability_le_one (G := G) C u
  exact add_nonneg
    (mul_nonneg ha0 (Forest.FiniteLatticeLaw.variance_nonneg _))
    (mul_nonneg (sub_nonneg.mpr ha1) (Forest.FiniteLatticeLaw.variance_nonneg _))

/-- C.13, first inequality: a vertex contribution is at most its contextual
subtree variance mass. -/
theorem vertexVarianceContribution_le_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vertexVarianceContribution (G := G) C u ≤
      R.subtreeVarianceMass (G := G) C u := by
  rw [R.subtreeVarianceMass_eq_vertexContribution_add_sum_children (G := G) C u]
  exact le_add_of_nonneg_right <| by
    apply Finset.sum_nonneg
    intro v hv
    exact R.subtreeVarianceMass_nonneg (G := G) C v

/-- C.13, second inequality: every contextual subtree variance mass is at most
the global variance. -/
theorem subtreeVarianceMass_le_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.subtreeVarianceMass (G := G) C u ≤ C.variance := by
  rw [R.subtreeVarianceMass_eq_sum_descendants (G := G) C u,
    ← R.sum_vertexVarianceContribution_eq_variance (G := G) C]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun v _ _ => R.vertexVarianceContribution_nonneg (G := G) C v)

/-- Every individual actual contribution is at most the global variance. -/
theorem vertexVarianceContribution_le_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vertexVarianceContribution (G := G) C u ≤ C.variance :=
  le_trans (R.vertexVarianceContribution_le_subtreeVarianceMass (G := G) C u)
    (R.subtreeVarianceMass_le_variance (G := G) C u)

/-- C.14: actual conditional subtree variance is at most `28 E(u)`. -/
theorem subtreeVariance_le_twentyEight_mul_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    R.subtreeVariance (G := G) C u ≤
      28 * R.subtreeVarianceMass (G := G) C u := by
  have ha := R.one_div_twentyEight_lt_parentAbsentProbability (G := G) C hz u
  have hvP : 0 ≤ R.subtreeVariance (G := G) C u := by
    unfold subtreeVariance
    exact Forest.FiniteLatticeLaw.variance_nonneg _
  have hvQ : 0 ≤ R.vacantVariance (G := G) C u := by
    unfold vacantVariance
    exact Forest.FiniteLatticeLaw.variance_nonneg _
  have ha1 := R.parentAbsentProbability_le_one (G := G) C u
  unfold subtreeVarianceMass
  have hpart :
      R.parentAbsentProbability (G := G) C u *
          R.subtreeVariance (G := G) C u ≤
        R.parentAbsentProbability (G := G) C u *
            R.subtreeVariance (G := G) C u +
          (1 - R.parentAbsentProbability (G := G) C u) *
            R.vacantVariance (G := G) C u :=
    le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ha1) hvQ)
  nlinarith

/-- Finite weighted Cauchy--Schwarz in exactly the form used in C.20. -/
theorem weightedCauchySchwarz
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (p q y : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i) :
    (∑ i ∈ s, p i * y i) ^ 2 ≤
      (∑ i ∈ s, p i / q i) *
        ∑ i ∈ s, p i * q i * y i ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => Real.sqrt (p i / q i))
    (fun i => Real.sqrt (p i * q i) * y i)
  calc
    (∑ i ∈ s, p i * y i) ^ 2 =
        (∑ i ∈ s, Real.sqrt (p i / q i) *
          (Real.sqrt (p i * q i) * y i)) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hpi := hp i hi
      have hqi := hq i hi
      have hratio : 0 ≤ p i / q i := div_nonneg hpi hqi.le
      have hpq : 0 ≤ p i * q i := mul_nonneg hpi hqi.le
      have hmul : (p i / q i) * (p i * q i) = p i ^ 2 := by
        field_simp [hqi.ne']
      symm
      rw [← mul_assoc, ← Real.sqrt_mul hratio, hmul,
        Real.sqrt_sq_eq_abs, abs_of_nonneg hpi]
    _ ≤ (∑ i ∈ s, (Real.sqrt (p i / q i)) ^ 2) *
        ∑ i ∈ s, (Real.sqrt (p i * q i) * y i) ^ 2 := hcs
    _ = (∑ i ∈ s, p i / q i) *
        ∑ i ∈ s, p i * q i * y i ^ 2 := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        exact Real.sq_sqrt (div_nonneg (hp i hi) (hq i hi).le)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [mul_pow, Real.sq_sqrt (mul_nonneg (hp i hi) (hq i hi).le)]

/-- Actual child-weighted Cauchy inequality, Appendix C equation C.20. -/
theorem weightedChildCauchy
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (u : V) (y : V → ℝ) :
    (∑ v ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C v * y v) ^ 2 ≤
      (∑ v ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C v /
          R.vacancyProbability (G := G) C v) *
      ∑ v ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v * y v ^ 2 := by
  classical
  exact weightedCauchySchwarz (R.children (G := G) u)
    (fun v => R.occupationProbability (G := G) C v)
    (fun v => R.vacancyProbability (G := G) C v) y
    (fun v _ => R.occupationProbability_nonneg (G := G) C v)
    (fun v _ => R.vacancyProbability_pos (G := G) C v)

/-- Pointwise odds are controlled by minus the log vacancy under the activity
cap.  This elementary inequality is the input to C.21. -/
theorem occupationOdds_le_neg_twentyEight_mul_log_vacancy
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    R.occupationProbability (G := G) C u /
        R.vacancyProbability (G := G) C u ≤
      -28 * Real.log (R.vacancyProbability (G := G) C u) := by
  let p := R.occupationProbability (G := G) C u
  let q := R.vacancyProbability (G := G) C u
  have hp : 0 ≤ p := R.occupationProbability_nonneg (G := G) C u
  have hq : 0 < q := R.vacancyProbability_pos (G := G) C u
  have hq28 := R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz u
  have hpq := R.occupationProbability_add_vacancyProbability (G := G) C u
  have hratio : p / q ≤ 28 * p := by
    apply (div_le_iff₀ hq).2
    nlinarith
  have hlog0 := Real.log_le_sub_one_of_pos hq
  change p / q ≤ -28 * Real.log q
  change p + q = 1 at hpq
  nlinarith

/-- C.21: logarithmic estimate for the sum of the actual child odds. -/
theorem sum_child_occupationOdds_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    (∑ v ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C v /
          R.vacancyProbability (G := G) C v) ≤
      28 * Real.log
        (27 / R.occupationProbability (G := G) C u) := by
  classical
  let p : V → ℝ := fun v => R.occupationProbability (G := G) C v
  let q : V → ℝ := fun v => R.vacancyProbability (G := G) C v
  let s := R.children (G := G) u
  have hsum : (∑ v ∈ s, p v / q v) ≤
      ∑ v ∈ s, -28 * Real.log (q v) := by
    exact Finset.sum_le_sum fun v hv =>
      R.occupationOdds_le_neg_twentyEight_mul_log_vacancy (G := G) C hz v
  have hqne : ∀ v ∈ s, q v ≠ 0 := fun v _ =>
    (R.vacancyProbability_pos (G := G) C v).ne'
  have hprodpos : 0 < ∏ v ∈ s, q v := by
    exact Finset.prod_pos fun v hv => R.vacancyProbability_pos (G := G) C v
  have hp : 0 < p u := R.occupationProbability_pos (G := G) C u
  have hqu : 0 < q u := R.vacancyProbability_pos (G := G) C u
  have hqu1 : q u ≤ 1 := by
    have h := R.occupationProbability_add_vacancyProbability (G := G) C u
    have hp0 := R.occupationProbability_nonneg (G := G) C u
    change p u + q u = 1 at h
    linarith
  have hrec := R.occupationOdds_eq_activity_mul_prod_children (G := G) C u
  change p u / q u = C.activity * ∏ v ∈ s, q v at hrec
  have hpEq : p u = C.activity * (∏ v ∈ s, q v) * q u := by
    apply (div_eq_iff hqu.ne').mp
    simpa [mul_assoc] using hrec
  have hinv : (∏ v ∈ s, q v)⁻¹ ≤ 27 / p u := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hprodpos hp).2
    rw [hpEq]
    simp only [one_mul]
    have hzq : C.activity * q u ≤ 27 := by
      have hmul := mul_le_mul_of_nonneg_left hqu1 C.activity_pos.le
      nlinarith
    calc
      (C.activity * (∏ v ∈ s, q v)) * q u =
          (C.activity * q u) * (∏ v ∈ s, q v) := by ring
      _ ≤ 27 * (∏ v ∈ s, q v) :=
        mul_le_mul_of_nonneg_right hzq hprodpos.le
  have hinvpos : 0 < (∏ v ∈ s, q v)⁻¹ := inv_pos.mpr hprodpos
  have h27p : 0 < 27 / p u := div_pos (by norm_num) hp
  have hlog := Real.strictMonoOn_log.monotoneOn hinvpos h27p hinv
  have hlogs :
      (∑ v ∈ s, -28 * Real.log (q v)) =
        28 * Real.log ((∏ v ∈ s, q v)⁻¹) := by
    calc
      (∑ v ∈ s, -28 * Real.log (q v)) =
          -28 * ∑ v ∈ s, Real.log (q v) := by
        rw [Finset.mul_sum]
      _ = -28 * Real.log (∏ v ∈ s, q v) := by
        rw [Real.log_prod hqne]
      _ = 28 * Real.log ((∏ v ∈ s, q v)⁻¹) := by
        rw [Real.log_inv]
        ring
  change (∑ v ∈ s, p v / q v) ≤ 28 * Real.log (27 / p u)
  rw [hlogs] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left hlog (by norm_num))

/-- C.22: a counted vertex has occupation probability below `χ`. -/
theorem occupationProbability_lt_chi_of_counted
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {b : ℝ} (hb : 1 < b) (u : V)
    (hu : b < |R.conditionalMeanDifference (G := G) C u|) :
    R.occupationProbability (G := G) C u < chi C b := by
  let p := R.occupationProbability (G := G) C u
  let q := R.vacancyProbability (G := G) C u
  let a := R.parentAbsentProbability (G := G) C u
  let d := R.conditionalMeanDifference (G := G) C u
  have hp : 0 < p := R.occupationProbability_pos (G := G) C u
  have hq : (1 : ℝ) / 28 < q :=
    R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz u
  have ha : (1 : ℝ) / 28 < a :=
    R.one_div_twentyEight_lt_parentAbsentProbability (G := G) C hz u
  have haq : (1 : ℝ) / 784 < a * q := by nlinarith
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hdsq : b ^ 2 < d ^ 2 := by
    change b < |d| at hu
    nlinarith [sq_abs d]
  have hsmall : b ^ 2 / 784 < (a * q) * d ^ 2 := by
    have h1 : b ^ 2 / 784 < (a * q) * b ^ 2 := by
      nlinarith [sq_pos_of_pos hb0]
    exact h1.trans_le (mul_le_mul_of_nonneg_left hdsq.le (by nlinarith [ha.le, hq.le]))
  have hg : p * (b ^ 2 / 784) <
      R.vertexVarianceContribution (G := G) C u := by
    unfold vertexVarianceContribution
    change p * (b ^ 2 / 784) < a * p * q * d ^ 2
    calc
      p * (b ^ 2 / 784) < p * ((a * q) * d ^ 2) :=
        mul_lt_mul_of_pos_left hsmall hp
      _ = a * p * q * d ^ 2 := by ring
  have hgV := R.vertexVarianceContribution_le_variance (G := G) C u
  unfold chi
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  apply (lt_div_iff₀ hb2).2
  nlinarith [hg.trans_le hgV]

/-- C.23: monotonicity comparison for `t log(27/t)` on `(0,1)`. -/
theorem mul_log_twentySeven_div_mono
    {p x : ℝ} (hp : 0 < p) (hpx : p ≤ x) (hx : x < 1) :
    p * Real.log (27 / p) ≤ x * Real.log (27 / x) := by
  let f : ℝ → ℝ := fun t => t * (Real.log 27 - Real.log t)
  have hpos : ∀ t ∈ Set.Icc p x, 0 < t := fun t ht => lt_of_lt_of_le hp ht.1
  have hcont : ContinuousOn f (Set.Icc p x) := by
    intro t ht
    exact (continuousAt_id.mul
      (continuousAt_const.sub (Real.continuousAt_log (hpos t ht).ne'))).continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Set.Icc p x)) := by
    intro t ht
    have htmem : t ∈ Set.Icc p x := interior_subset ht
    exact ((hasDerivAt_id t).mul
      ((hasDerivAt_const t (Real.log 27)).sub
        (Real.hasDerivAt_log (hpos t htmem).ne'))).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ interior (Set.Icc p x), 0 ≤ deriv f t := by
    intro t ht
    have htmem : t ∈ Set.Icc p x := interior_subset ht
    have ht0 := hpos t htmem
    have htx : t < 1 := lt_of_le_of_lt htmem.2 hx
    have hd : HasDerivAt f
        (1 * (Real.log 27 - Real.log t) + t * (0 - t⁻¹)) t := by
      simpa only [f, id_eq, Pi.sub_apply] using
        (hasDerivAt_id t).mul
          ((hasDerivAt_const t (Real.log 27)).sub
            (Real.hasDerivAt_log ht0.ne'))
    rw [hd.deriv]
    have h27 : 1 < Real.log 27 := by
      rw [← Real.log_exp 1]
      exact Real.strictMonoOn_log (Real.exp_pos 1) (by norm_num)
        (lt_trans Real.exp_one_lt_d9 (by norm_num))
    have hlt : Real.log t < 0 := Real.log_neg ht0 htx
    field_simp [ht0.ne']
    nlinarith
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc p x) hcont hdiff hderiv
  have hfx : f p ≤ f x := hm (left_mem_Icc.mpr hpx) (right_mem_Icc.mpr hpx) hpx
  dsimp [f] at hfx
  rw [Real.log_div (by norm_num) hp.ne',
    Real.log_div (by norm_num) (hp.trans_le hpx).ne']
  exact hfx

/-- In C.20 the parent vacancy is bounded by every child's actual
parent-absence marginal; this is where contextual mixing cancels exactly. -/
theorem vacancyProbability_le_parentAbsentProbability_of_child
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {u v : V} (hchild : R.IsChild (G := G) u v) :
    R.vacancyProbability (G := G) C u ≤
      R.parentAbsentProbability (G := G) C v := by
  rw [R.parentAbsentProbability_child (G := G) C hchild]
  have ha := R.parentAbsentProbability_le_one (G := G) C u
  have hp := R.occupationProbability_nonneg (G := G) C u
  have hpq := R.occupationProbability_add_vacancyProbability (G := G) C u
  nlinarith

/-- The weighted child square-sum in C.20 is absorbed by actual child
contributions after multiplication by the parent's vacancy. -/
theorem vacancy_mul_sum_child_weightedSquares_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vacancyProbability (G := G) C u *
        (∑ v ∈ R.children (G := G) u,
          R.occupationProbability (G := G) C v *
            R.vacancyProbability (G := G) C v *
              R.conditionalMeanDifference (G := G) C v ^ 2) ≤
      ∑ v ∈ R.children (G := G) u,
        R.vertexVarianceContribution (G := G) C v := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hvchild : R.IsChild (G := G) u v := (Finset.mem_filter.mp hv).2
  unfold vertexVarianceContribution
  have hα := R.vacancyProbability_le_parentAbsentProbability_of_child
    (G := G) C hvchild
  have hp := R.occupationProbability_nonneg (G := G) C v
  have hq := R.vacancyProbability_pos (G := G) C v
  have hd := sq_nonneg (R.conditionalMeanDifference (G := G) C v)
  calc
    R.vacancyProbability (G := G) C u *
        (R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v *
            R.conditionalMeanDifference (G := G) C v ^ 2) ≤
      R.parentAbsentProbability (G := G) C v *
        (R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v *
            R.conditionalMeanDifference (G := G) C v ^ 2) :=
      mul_le_mul_of_nonneg_right hα
        (mul_nonneg (mul_nonneg hp hq.le) hd)
    _ = R.parentAbsentProbability (G := G) C v *
        R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v *
            R.conditionalMeanDifference (G := G) C v ^ 2 := by ring

/-- The sum of actual child contributions is bounded by the parent's contextual
subtree variance mass. -/
theorem sum_child_vertexVarianceContribution_le_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ v ∈ R.children (G := G) u,
      R.vertexVarianceContribution (G := G) C v) ≤
      R.subtreeVarianceMass (G := G) C u := by
  calc
    (∑ v ∈ R.children (G := G) u,
      R.vertexVarianceContribution (G := G) C v) ≤
        ∑ v ∈ R.children (G := G) u,
          R.subtreeVarianceMass (G := G) C v := by
      exact Finset.sum_le_sum fun v _ =>
        R.vertexVarianceContribution_le_subtreeVarianceMass (G := G) C v
    _ ≤ R.subtreeVarianceMass (G := G) C u := by
      rw [R.subtreeVarianceMass_eq_vertexContribution_add_sum_children (G := G) C u]
      exact le_add_of_nonneg_left
        (R.vertexVarianceContribution_nonneg (G := G) C u)

/-- The elementary large-displacement amplification inequality used in C.25. -/
theorem displacement_sq_le_ratio_sq_mul_sq
    {b d z : ℝ} (hb : 1 < b) (hd : b < |d|) (heq : d = 1 - z) :
    d ^ 2 ≤ (b / (b - 1)) ^ 2 * z ^ 2 := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hb1 : 0 < b - 1 := sub_pos.mpr hb
  have hrev0 := abs_sub_abs_le_abs_sub d 1
  have hrev : |d| - 1 ≤ |z| := by
    calc
      |d| - 1 = |d| - |(1 : ℝ)| := by norm_num
      _ ≤ |d - 1| := hrev0
      _ = |z| := by rw [heq]; simp
  have hlin : (b - 1) * |d| ≤ b * |z| := by
    have h1 : 0 ≤ b * (|z| - (|d| - 1)) :=
      mul_nonneg hb0.le (sub_nonneg.mpr hrev)
    have h2 : 0 ≤ |d| - b := sub_nonneg.mpr hd.le
    nlinarith
  have habs : |d| ≤ (b / (b - 1)) * |z| := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hb1).2 (by simpa [mul_comm] using hlin)
  calc
    d ^ 2 = |d| ^ 2 := by rw [sq_abs]
    _ ≤ ((b / (b - 1)) * |z|) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (abs_nonneg d) habs
    _ = (b / (b - 1)) ^ 2 * z ^ 2 := by
      rw [mul_pow, sq_abs]

/-- C.25: pointwise large-displacement estimate for an actual rooted vertex. -/
theorem pointwise_largeDisplacement_estimate
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {b : ℝ} (hb : 1 < b)
    (hchi : chi C b < 1) (u : V)
    (hu : b < |R.conditionalMeanDifference (G := G) C u|) :
    R.vertexVarianceContribution (G := G) C u ≤
      (b / (b - 1)) ^ 2 * 28 * chi C b *
        Real.log (27 / chi C b) *
          (∑ v ∈ R.children (G := G) u,
            R.vertexVarianceContribution (G := G) C v) := by
  classical
  let p : V → ℝ := fun v => R.occupationProbability (G := G) C v
  let q : V → ℝ := fun v => R.vacancyProbability (G := G) C v
  let d : V → ℝ := fun v => R.conditionalMeanDifference (G := G) C v
  let a : V → ℝ := fun v => R.parentAbsentProbability (G := G) C v
  let s := R.children (G := G) u
  let z := ∑ v ∈ s, p v * d v
  let A := ∑ v ∈ s, p v / q v
  let B := ∑ v ∈ s, p v * q v * d v ^ 2
  let H := ∑ v ∈ s, R.vertexVarianceContribution (G := G) C v
  let r := b / (b - 1)
  let χ := chi C b
  have hp : 0 < p u := R.occupationProbability_pos (G := G) C u
  have hq : 0 < q u := R.vacancyProbability_pos (G := G) C u
  have ha0 : 0 ≤ a u := R.parentAbsentProbability_nonneg (G := G) C u
  have ha1 : a u ≤ 1 := R.parentAbsentProbability_le_one (G := G) C u
  have hq1 : q u ≤ 1 := by
    have h := R.occupationProbability_add_vacancyProbability (G := G) C u
    have hp0 := R.occupationProbability_nonneg (G := G) C u
    change p u + q u = 1 at h
    linarith
  have hdrec := R.conditionalMeanDifference_eq_one_sub_sum
    (G := G) C u
  change d u = 1 - z at hdrec
  have hdsq : d u ^ 2 ≤ r ^ 2 * z ^ 2 :=
    displacement_sq_le_ratio_sq_mul_sq hb hu hdrec
  have hr0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hA0 : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro v hv
    exact div_nonneg (R.occupationProbability_nonneg (G := G) C v)
      (R.vacancyProbability_pos (G := G) C v).le
  have hB0 : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (mul_nonneg (R.occupationProbability_nonneg (G := G) C v)
        (R.vacancyProbability_pos (G := G) C v).le)
      (sq_nonneg _)
  have hzsq : z ^ 2 ≤ A * B := by
    exact R.weightedChildCauchy (G := G) C u d
  have hqB : q u * B ≤ H :=
    R.vacancy_mul_sum_child_weightedSquares_le (G := G) C u
  have hAlog : A ≤ 28 * Real.log (27 / p u) :=
    R.sum_child_occupationOdds_le (G := G) C hz u
  have hχp : p u < χ :=
    R.occupationProbability_lt_chi_of_counted (G := G) C hz hb u hu
  have hχ0 : 0 < χ := lt_trans hp hχp
  have hplog : p u * Real.log (27 / p u) ≤
      χ * Real.log (27 / χ) :=
    mul_log_twentySeven_div_mono hp hχp.le hchi
  have hlogp0 : 0 ≤ Real.log (27 / p u) := by
    exact (Real.log_pos (by
      apply (lt_div_iff₀ hp).2
      have hp1 := R.occupationProbability_lt_twentySeven_div_twentyEight
        (G := G) C hz u
      nlinarith)).le
  have hH0 : 0 ≤ H := by
    apply Finset.sum_nonneg
    intro v hv
    exact R.vertexVarianceContribution_nonneg (G := G) C v
  have hmain : a u * p u * q u * d u ^ 2 ≤
      r ^ 2 * 28 * (p u * Real.log (27 / p u)) * H := by
    calc
      a u * p u * q u * d u ^ 2 ≤ p u * q u * (r ^ 2 * z ^ 2) := by
        have hleft := mul_le_mul_of_nonneg_left hdsq
          (mul_nonneg (mul_nonneg ha0 hp.le) hq.le)
        have haDrop : a u * p u * q u * (r ^ 2 * z ^ 2) ≤
            p u * q u * (r ^ 2 * z ^ 2) := by
          have hap : a u * p u ≤ p u := by
            calc
              a u * p u ≤ 1 * p u := mul_le_mul_of_nonneg_right ha1 hp.le
              _ = p u := one_mul _
          have hapq : a u * p u * q u ≤ p u * q u :=
            mul_le_mul_of_nonneg_right hap hq.le
          exact mul_le_mul_of_nonneg_right hapq
            (mul_nonneg hr0 (sq_nonneg z))
        exact hleft.trans haDrop
      _ ≤ p u * q u * (r ^ 2 * (A * B)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzsq hr0)
          (mul_nonneg hp.le hq.le)
      _ = r ^ 2 * p u * A * (q u * B) := by ring
      _ ≤ r ^ 2 * p u * A * H := by
        exact mul_le_mul_of_nonneg_left hqB
          (mul_nonneg (mul_nonneg hr0 hp.le) hA0)
      _ ≤ r ^ 2 * p u * (28 * Real.log (27 / p u)) * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAlog (mul_nonneg hr0 hp.le)) hH0
      _ = r ^ 2 * 28 * (p u * Real.log (27 / p u)) * H := by ring
  unfold vertexVarianceContribution
  change a u * p u * q u * d u ^ 2 ≤
    r ^ 2 * 28 * χ * Real.log (27 / χ) * H
  exact hmain.trans <| by
    have hr28 : 0 ≤ r ^ 2 * (28 : ℝ) :=
      mul_nonneg hr0 (by norm_num)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hplog hr28) hH0
    convert hh using 1 <;> ring

/-- Across an actual component rooting, child sets have no multiplicity: every
vertex has at most one parent. -/
theorem sum_sum_children_le_sum
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ u, ∑ v ∈ R.children (G := G) u, f v) ≤ ∑ v, f v := by
  classical
  have hinner : ∀ v : V,
      (∑ u, if R.IsChild (G := G) u v then f v else 0) ≤ f v := by
    intro v
    by_cases hv : v = R.rootOf (G := G) v
    · have hnone : ∀ u : V, ¬ R.IsChild (G := G) u v :=
        fun u => R.not_isChild_of_eq_root (G := G) hv
      simp [hnone, hf v]
    · let p := R.selectedParent (G := G) v hv
      have hp : R.IsChild (G := G) p v :=
        R.selectedParent_isChild (G := G) v hv
      have heq : (∑ u, if R.IsChild (G := G) u v then f v else 0) = f v := by
        rw [Finset.sum_eq_single p]
        · simp [hp]
        · intro w hw hwp
          split
          · rename_i hwc
            exact False.elim (hwp (R.isChild_unique (G := G) C.isForest hwc hp))
          · rfl
        · intro hpnot
          exact False.elim (hpnot (Finset.mem_univ p))
      rw [heq]
  calc
    (∑ u, ∑ v ∈ R.children (G := G) u, f v) =
        ∑ u, ∑ v, if R.IsChild (G := G) u v then f v else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [children, Finset.sum_filter]
    _ = ∑ v, ∑ u, if R.IsChild (G := G) u v then f v else 0 :=
      Finset.sum_comm
    _ ≤ ∑ v, f v := Finset.sum_le_sum fun v hv => hinner v

/-- Exact finite Appendix C.18 for an actual component rooting. -/
theorem largeDisplacementContribution_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (b : ℝ)
    (hz : C.activity < 27) (hb : 1 < b) (hchi : chi C b < 1) :
    ComponentRooting.G C R b / C.variance ≤
      (b / (b - 1)) ^ 2 * 28 * chi C b * Real.log (27 / chi C b) := by
  classical
  let K := (b / (b - 1)) ^ 2 * 28 * chi C b * Real.log (27 / chi C b)
  have hV : 0 < C.variance := canonicalFirstRecovery_variance_pos C
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hχ0 : 0 < chi C b := by
    unfold chi
    exact div_pos (mul_pos (by norm_num) hV) (sq_pos_of_pos hb0)
  have hlog : 0 < Real.log (27 / chi C b) := Real.log_pos <| by
    apply (lt_div_iff₀ hχ0).2
    nlinarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ u : V,
      (if b < |R.conditionalMeanDifference (G := G) C u| then
          R.vertexVarianceContribution (G := G) C u else 0) ≤
        K * ∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v := by
    intro u
    split
    · rename_i hu
      exact R.pointwise_largeDisplacement_estimate (G := G) C hz hb hchi u hu
    · exact mul_nonneg hK <| by
        apply Finset.sum_nonneg
        intro v hv
        exact R.vertexVarianceContribution_nonneg (G := G) C v
  have hraw : ComponentRooting.G C R b ≤ K * C.variance := by
    unfold ComponentRooting.G
    calc
      (∑ u, if b < |R.conditionalMeanDifference (G := G) C u| then
          R.vertexVarianceContribution (G := G) C u else 0) ≤
          ∑ u, K * ∑ v ∈ R.children (G := G) u,
            R.vertexVarianceContribution (G := G) C v :=
        Finset.sum_le_sum fun u hu => hpoint u
      _ = K * ∑ u, ∑ v ∈ R.children (G := G) u,
            R.vertexVarianceContribution (G := G) C v := by
        rw [Finset.mul_sum]
      _ ≤ K * ∑ v, R.vertexVarianceContribution (G := G) C v := by
        exact mul_le_mul_of_nonneg_left
          (R.sum_sum_children_le_sum C
            (fun v => R.vertexVarianceContribution (G := G) C v)
            (fun v => R.vertexVarianceContribution_nonneg (G := G) C v)) hK
      _ = K * C.variance := by
        rw [R.sum_vertexVarianceContribution_eq_variance (G := G) C]
  exact (div_le_iff₀ hV).2 hraw

/-- Named Appendix equation C.18, retaining the exact public signature. -/
theorem C18
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (b : ℝ)
    (hz : C.activity < 27) (hb : 1 < b) (hchi : chi C b < 1) :
    ComponentRooting.G C R b / C.variance ≤
      (b / (b - 1)) ^ 2 * 28 * chi C b * Real.log (27 / chi C b) :=
  R.largeDisplacementContribution_le C b hz hb hchi

/-- The scalar analytic limit behind C.19. -/
theorem tendsto_mul_log_twentySeven_div
    {α : Type*} {l : Filter α} (x : α → ℝ)
    (hx : Tendsto x l (𝓝 0)) (hxpos : ∀ᶠ n in l, 0 < x n) :
    Tendsto (fun n => x n * Real.log (27 / x n)) l (𝓝 0) := by
  have hxgt : Tendsto x l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hx, hxpos⟩
  have hlogmul0 : Tendsto (fun n => x n * Real.log (x n)) l (𝓝 0) := by
    have h := (tendsto_log_mul_rpow_nhdsGT_zero (r := (1 : ℝ)) one_pos).comp hxgt
    simpa only [Function.comp_apply, Real.rpow_one, mul_comm] using h
  have hconst : Tendsto (fun n => x n * Real.log 27) l (𝓝 0) := by
    simpa using hx.mul_const (Real.log 27)
  have hsub : Tendsto (fun n => x n * Real.log 27 - x n * Real.log (x n)) l (𝓝 0) := by
    simpa using hconst.sub hlogmul0
  refine hsub.congr' ?_
  filter_upwards [hxpos] with n hn
  rw [Real.log_div (by norm_num) hn.ne']
  ring

/-- Exact uniform Appendix C.19 for genuinely varying finite forests. -/
theorem C19
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (Γ : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (Γ n))
    (R : ∀ n, ComponentRooting (Γ n)) (b : ℕ → ℝ)
    (hz : ∀ n, (C n).activity < 27)
    (hb : Tendsto b atTop atTop)
    (hvar : Tendsto (fun n => (C n).variance / (b n) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ComponentRooting.G (C n) (R n) (b n) / (C n).variance)
      atTop (𝓝 0) := by
  let χ : ℕ → ℝ := fun n => chi (C n) (b n)
  have hχ : Tendsto χ atTop (𝓝 0) := by
    have h := hvar.const_mul (784 : ℝ)
    convert h using 1
    · funext n
      dsimp [χ, chi]
      ring
    · simp
  have hb2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ b n := (tendsto_atTop.1 hb) 2
  have hχpos : ∀ᶠ n in atTop, 0 < χ n := by
    filter_upwards [hb2] with n hn
    dsimp [χ, chi]
    exact div_pos (mul_pos (by norm_num) (canonicalFirstRecovery_variance_pos (C n)))
      (sq_pos_of_pos (by linarith))
  have hχlog : Tendsto (fun n => χ n * Real.log (27 / χ n)) atTop (𝓝 0) :=
    tendsto_mul_log_twentySeven_div χ hχ hχpos
  have hupper : Tendsto (fun n => 112 * (χ n * Real.log (27 / χ n)))
      atTop (𝓝 0) := by
    simpa using hχlog.const_mul (112 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun n => by
      exact div_nonneg (by
        unfold ComponentRooting.G
        apply Finset.sum_nonneg
        intro v hv
        split
        · exact (R n).vertexVarianceContribution_nonneg (G := Γ n) (C n) v
        · norm_num) (canonicalFirstRecovery_variance_pos (C n)).le
  · filter_upwards [hb2, hχpos,
      hχ.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
      with n hbn hχn hχlt
    have hb1 : 1 < b n := by linarith
    have hC18 := (R n).largeDisplacementContribution_le (G := Γ n)
      (C n) (b n) (hz n) hb1 hχlt
    have hr0 : 0 ≤ b n / (b n - 1) :=
      div_nonneg (by linarith) (by linarith)
    have hr2 : b n / (b n - 1) ≤ 2 := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith
    have hrsq : (b n / (b n - 1)) ^ 2 ≤ 4 := by nlinarith
    have hlog0 : 0 ≤ Real.log (27 / χ n) :=
      (Real.log_pos (by
        apply (lt_div_iff₀ hχn).2
        nlinarith)).le
    change ComponentRooting.G (C n) (R n) (b n) / (C n).variance ≤
      112 * (χ n * Real.log (27 / χ n))
    calc
      ComponentRooting.G (C n) (R n) (b n) / (C n).variance ≤
          (b n / (b n - 1)) ^ 2 * 28 * χ n * Real.log (27 / χ n) := hC18
      _ ≤ 4 * 28 * χ n * Real.log (27 / χ n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hrsq (by norm_num)) hχn.le) hlog0
      _ = 112 * (χ n * Real.log (27 / χ n)) := by ring

end ComponentRooting
end
end ActualRootedVariance
end Erdos993
