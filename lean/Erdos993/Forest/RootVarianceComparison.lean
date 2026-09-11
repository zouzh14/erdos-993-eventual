import Erdos993.Forest.SmallFrequencyCurvature

/-!
# Root variance comparison for Appendix A

This module supplies the arbitrary-activity form of the P/Q/R variance identities and
begins the depth-free estimates (A.29).  The exact variance decompositions are proved in
`ActualRootedVariance`; here they are combined with the uniform activity bounds.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance
open UniformFourthMoment

universe u

noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

abbrev subtreeVarianceAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  (R.subtreeLawAt z hz u).variance

abbrev rootVacantVarianceAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  R.vacantVarianceAt z hz u

abbrev rootOccupiedVarianceAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  R.occupiedVarianceAt z hz u

@[simp] theorem occupationProbabilityAt_eq_rooted
    (R : ComponentRooting G) (z : ℝ) (u : V) :
    R.occupationProbabilityAt z u = rootedOccupationProbabilityAt R z u := by
  rfl

@[simp] theorem vacancyProbabilityAt_eq_rooted
    (R : ComponentRooting G) (z : ℝ) (u : V) :
    R.vacancyProbabilityAt z u = rootedVacancyProbabilityAt R z u := by
  rfl

noncomputable def rootVarianceUpperConstant (Z : ℝ) : ℝ := 1 + 3 * Z
noncomputable def rootVarianceRConstant (Z : ℝ) : ℝ := 1 + Z

/-- The lower half of (A.29), directly from total variance. -/
theorem vacancy_mul_rootVacantVarianceAt_le_subtreeVarianceAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedVacancyProbabilityAt R z u * rootVacantVarianceAt R z hz u ≤
      subtreeVarianceAt R z hz u := by
  change rootedVacancyProbabilityAt R z u * R.vacantVarianceAt z hz u ≤
    (R.subtreeLawAt z hz u).variance
  rw [R.subtreeVarianceAt_law_total_variance z hz u]
  simp only [vacancyProbabilityAt_eq_rooted, occupationProbabilityAt_eq_rooted]
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ rootedVacancyProbabilityAt R z u := by
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hVR0 : 0 ≤ rootOccupiedVarianceAt R z hz u :=
    FiniteLatticeLaw.variance_nonneg _
  have hd0 : 0 ≤ R.conditionalMeanDifferenceAt z hz u ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg hb0 hVR0, mul_nonneg (mul_nonneg hb0 hq0) hd0]

/-- The root-occupied remainder variance is at most `(1+Z)` times the
root-vacant child-forest variance.  This is the second inequality of (A.29). -/
theorem rootOccupiedVarianceAt_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootOccupiedVarianceAt R z hz u ≤
      rootVarianceRConstant Z * rootVacantVarianceAt R z hz u := by
  change R.occupiedVarianceAt z hz u ≤
    rootVarianceRConstant Z * R.vacantVarianceAt z hz u
  rw [R.occupiedVarianceAt_eq_sum_vacantVarianceAt hG z hz u,
    R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u]
  unfold rootVarianceRConstant
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hq := one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
    hG R z Z hz hzZ v
  have hlow := vacancy_mul_rootVacantVarianceAt_le_subtreeVarianceAt R z hz v
  have hZ : 0 < 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  have hQ0 : 0 ≤ R.vacantVarianceAt z hz v := FiniteLatticeLaw.variance_nonneg _
  have hscaled := mul_le_mul_of_nonneg_right hq hQ0
  have hdiv : R.vacantVarianceAt z hz v ≤
      (1 + Z) * (rootedVacancyProbabilityAt R z v *
        R.vacantVarianceAt z hz v) := by
    calc
      R.vacantVarianceAt z hz v =
          (1 + Z) * ((1 / (1 + Z)) * R.vacantVarianceAt z hz v) := by
        field_simp
      _ ≤ (1 + Z) * (rootedVacancyProbabilityAt R z v *
          R.vacantVarianceAt z hz v) :=
        mul_le_mul_of_nonneg_left hscaled hZ.le
  exact hdiv.trans (mul_le_mul_of_nonneg_left hlow hZ.le)

/-- Finite Bernoulli product-ratio estimate used in (A.28).  It is the
probability that exactly one coordinate succeeds, bounded by total mass. -/
theorem prod_mul_sum_div_le_one
    {ι : Type*} (s : Finset ι) (b q : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hqpos : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i ≤ 1) (hbq : ∀ i, b i + q i = 1) :
    (∏ i ∈ s, q i) * (∑ i ∈ s, b i / q i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hP0 : 0 ≤ ∏ i ∈ s, q i := by
        exact Finset.prod_nonneg fun i hi => (hqpos i).le
      have hP1 : (∏ i ∈ s, q i) ≤ 1 :=
        Finset.prod_le_one (fun i hi => (hqpos i).le) (fun i hi => hq1 i)
      have hfirst : b a * (∏ i ∈ s, q i) ≤ b a :=
        mul_le_of_le_one_right (hb0 a) hP1
      have hsecond : q a *
          ((∏ i ∈ s, q i) * (∑ i ∈ s, b i / q i)) ≤ q a := by
        simpa using mul_le_mul_of_nonneg_left ih (hqpos a).le
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      calc
        (q a * ∏ i ∈ s, q i) * (b a / q a + ∑ i ∈ s, b i / q i) =
            b a * (∏ i ∈ s, q i) +
              q a * ((∏ i ∈ s, q i) * (∑ i ∈ s, b i / q i)) := by
          field_simp [ne_of_gt (hqpos a)]
        _ ≤ b a + q a := add_le_add hfirst hsecond
        _ = 1 := hbq a

/-- Equation (A.28): the root occupation probability times the sum of child
occupation/vacancy odds is uniformly bounded by the activity ceiling. -/
theorem rootedOccupation_mul_childOddsSum_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedOccupationProbabilityAt R z u *
        (∑ v ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z v /
            rootedVacancyProbabilityAt R z v) ≤ Z := by
  let s := R.children (G := G) u
  let b : V → ℝ := fun v => rootedOccupationProbabilityAt R z v
  let q : V → ℝ := fun v => rootedVacancyProbabilityAt R z v
  have hb0 (v : V) : 0 ≤ b v := (rootedOccupationProbabilityAt_pos R z hz v).le
  have hqpos (v : V) : 0 < q v := by
    dsimp [q]
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)
  have hq1 (v : V) : q v ≤ 1 := by
    dsimp [q, b] at *
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz v,
      rootedOccupationProbabilityAt_pos R z hz v]
  have hbq (v : V) : b v + q v = 1 := by
    exact rootedOccupationProbabilityAt_add_vacancy R z hz v
  have hratio :
      (∏ v ∈ s, q v) * (∑ v ∈ s, b v / q v) ≤ 1 :=
    prod_mul_sum_div_le_one s b q hb0 hqpos hq1 hbq
  have hroot : rootedOccupationProbabilityAt R z u ≤ z * ∏ v ∈ s, q v := by
    simpa [s, q] using
      rootedOccupationProbabilityAt_le_z_mul_prod_child_vacancy hG R z hz u
  have hsum0 : 0 ≤ ∑ v ∈ s, b v / q v := by
    apply Finset.sum_nonneg
    intro v hv
    exact div_nonneg (hb0 v) (hqpos v).le
  calc
    rootedOccupationProbabilityAt R z u * (∑ v ∈ s, b v / q v) ≤
        (z * ∏ v ∈ s, q v) * (∑ v ∈ s, b v / q v) :=
      mul_le_mul_of_nonneg_right hroot hsum0
    _ = z * ((∏ v ∈ s, q v) * (∑ v ∈ s, b v / q v)) := by ring
    _ ≤ z * 1 := mul_le_mul_of_nonneg_left hratio hz.le
    _ ≤ Z := by simpa using hzZ

/-- The Bernoulli root energy is one nonnegative summand of the exact
law-of-total-variance decomposition. -/
theorem rootedEnergyAt_le_subtreeVarianceAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedEnergyAt R z hz u ≤ subtreeVarianceAt R z hz u := by
  change rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u *
      R.conditionalMeanDifferenceAt z hz u ^ 2 ≤
    (R.subtreeLawAt z hz u).variance
  rw [R.subtreeVarianceAt_law_total_variance z hz u]
  simp only [vacancyProbabilityAt_eq_rooted, occupationProbabilityAt_eq_rooted]
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ rootedVacancyProbabilityAt R z u := by
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hQ0 : 0 ≤ R.vacantVarianceAt z hz u := FiniteLatticeLaw.variance_nonneg _
  have hR0 : 0 ≤ R.occupiedVarianceAt z hz u := FiniteLatticeLaw.variance_nonneg _
  nlinarith [mul_nonneg hq0 hQ0, mul_nonneg hb0 hR0]

/-- Weighted Cauchy--Schwarz in the exact form used in the root comparison:
`(sum b_v d_v)^2 ≤ (sum b_v/q_v) (sum b_v q_v d_v^2)`. -/
theorem child_occupation_displacement_sum_sq_le_odds_mul_energy
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    (∑ v ∈ R.children (G := G) u,
      rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v) ^ 2 ≤
      (∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v /
          rootedVacancyProbabilityAt R z v) *
      ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro v hv
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le
      (by
        unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
        exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le)
  · intro v hv
    unfold rootedEnergyAt
    have hq0 : 0 ≤ rootedVacancyProbabilityAt R z v := by
      unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
      exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
    exact mul_nonneg
      (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le hq0)
      (sq_nonneg _)
  · intro v hv
    unfold rootedEnergyAt
    have hqne : rootedVacancyProbabilityAt R z v ≠ 0 := by
      unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
      exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).ne'
    field_simp [hqne]

/-- The sum of child Bernoulli energies is bounded by the variance of the
root-vacant child forest. -/
theorem child_energy_sum_le_rootVacantVarianceAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ≤
      rootVacantVarianceAt R z hz u := by
  change (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ≤
    R.vacantVarianceAt z hz u
  rw [R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u]
  apply Finset.sum_le_sum
  intro v hv
  exact rootedEnergyAt_le_subtreeVarianceAt R z hz v

/-- The root Bernoulli energy is controlled by the root-vacant variance and the
root occupation mass.  This is the displacement estimate used in (A.29). -/
theorem rootedEnergyAt_le_two_mul_occupation_add
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedEnergyAt R z hz u ≤
      2 * rootedOccupationProbabilityAt R z u +
        2 * Z * rootVacantVarianceAt R z hz u := by
  let b := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let d := rootedDisplacementAt R z hz u
  let S := ∑ v ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v
  let O := ∑ v ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z v / rootedVacancyProbabilityAt R z v
  let E := ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v
  let VQ := rootVacantVarianceAt R z hz u
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hq1 : q ≤ 1 := by
    dsimp [q, b]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
      rootedOccupationProbabilityAt_pos R z hz u]
  have hE0 : 0 ≤ E := by
    dsimp [E]
    apply Finset.sum_nonneg
    intro v hv
    unfold rootedEnergyAt
    have hqv0 : 0 ≤ rootedVacancyProbabilityAt R z v := by
      unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
      exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
    exact mul_nonneg
      (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le hqv0)
      (sq_nonneg _)
  have hVQ0 : 0 ≤ VQ := by
    dsimp [VQ, rootVacantVarianceAt]
    exact FiniteLatticeLaw.variance_nonneg _
  have hZ0 : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
  have hCS : S ^ 2 ≤ O * E := by
    simpa [S, O, E] using
      child_occupation_displacement_sum_sq_le_odds_mul_energy R z hz u
  have hrec : d = 1 - S := by
    simpa [d, S] using rootedDisplacementAt_eq_one_sub_sum hG R z hz u
  have hdiff : (1 - d) ^ 2 ≤ O * E := by
    calc
      (1 - d) ^ 2 = S ^ 2 := by rw [hrec]; ring
      _ ≤ O * E := hCS
  have hOdds : b * O ≤ Z := by
    simpa [b, O] using rootedOccupation_mul_childOddsSum_le hG R Z z hz hzZ u
  have hEle : E ≤ VQ := by
    simpa [E, VQ] using child_energy_sum_le_rootVacantVarianceAt hG R z hz u
  have hscaled : b * (1 - d) ^ 2 ≤ Z * VQ := by
    calc
      b * (1 - d) ^ 2 ≤ b * (O * E) :=
        mul_le_mul_of_nonneg_left hdiff hb0
      _ = (b * O) * E := by ring
      _ ≤ Z * E := mul_le_mul_of_nonneg_right hOdds hE0
      _ ≤ Z * VQ := mul_le_mul_of_nonneg_left hEle hZ0
  have hdsq : d ^ 2 ≤ 2 + 2 * (1 - d) ^ 2 := by
    nlinarith [sq_nonneg (d - 2)]
  have hbq : b * q ≤ b := mul_le_of_le_one_right hb0 hq1
  have hdelta0 : 0 ≤ (1 - d) ^ 2 := sq_nonneg _
  have hbd : (b * q) * (1 - d) ^ 2 ≤ b * (1 - d) ^ 2 :=
    mul_le_mul_of_nonneg_right hbq hdelta0
  change b * q * d ^ 2 ≤ 2 * b + 2 * Z * VQ
  have hfirst := mul_le_mul_of_nonneg_left hdsq (mul_nonneg hb0 hq0)
  nlinarith

/-- The upper half of (A.29): subtree variance is controlled, with constants
independent of depth, by the root-vacant child-forest variance plus the root
occupation mass. -/
theorem subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    subtreeVarianceAt R z hz u ≤
      rootVarianceUpperConstant Z * rootVacantVarianceAt R z hz u +
        2 * rootedOccupationProbabilityAt R z u := by
  let b := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let VQ := rootVacantVarianceAt R z hz u
  let VR := rootOccupiedVarianceAt R z hz u
  let e := rootedEnergyAt R z hz u
  have hZ : 0 < 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  have hZ0 : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hq1 : q ≤ 1 := by
    dsimp [q, b]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
      rootedOccupationProbabilityAt_pos R z hz u]
  have hVQ0 : 0 ≤ VQ := by
    dsimp [VQ, rootVacantVarianceAt]
    exact FiniteLatticeLaw.variance_nonneg _
  have hVR0 : 0 ≤ VR := by
    dsimp [VR, rootOccupiedVarianceAt]
    exact FiniteLatticeLaw.variance_nonneg _
  have hqVQ : q * VQ ≤ VQ := mul_le_of_le_one_left hVQ0 hq1
  have hbcap : b ≤ Z / (1 + Z) := by
    simpa [b] using rootedOccupationProbabilityAt_le_ceiling_ratio
      hG R z Z hz hzZ u
  have hVR : VR ≤ (1 + Z) * VQ := by
    simpa [VR, VQ, rootVarianceRConstant] using
      rootOccupiedVarianceAt_le hG R Z z hz hzZ u
  have hbVR : b * VR ≤ Z * VQ := by
    calc
      b * VR ≤ (Z / (1 + Z)) * VR :=
        mul_le_mul_of_nonneg_right hbcap hVR0
      _ ≤ (Z / (1 + Z)) * ((1 + Z) * VQ) := by
        exact mul_le_mul_of_nonneg_left hVR (div_nonneg hZ0 hZ.le)
      _ = Z * VQ := by field_simp
  have he : e ≤ 2 * b + 2 * Z * VQ := by
    simpa [e, b, VQ] using
      rootedEnergyAt_le_two_mul_occupation_add hG R Z z hz hzZ u
  change (R.subtreeLawAt z hz u).variance ≤
    rootVarianceUpperConstant Z * VQ + 2 * b
  rw [R.subtreeVarianceAt_law_total_variance z hz u]
  simp only [vacancyProbabilityAt_eq_rooted, occupationProbabilityAt_eq_rooted]
  change q * VQ + b * VR + e ≤ rootVarianceUpperConstant Z * VQ + 2 * b
  unfold rootVarianceUpperConstant
  nlinarith

/-- The logarithmic root barrier appearing in (A.30). -/
noncomputable def rootVarianceLogBarrierAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  ∑ v ∈ R.children (G := G) u,
    -Real.log (rootedVacancyProbabilityAt R z v)

/-- Equation (A.30): applying the upper root comparison to every child
controls the Q-variance by the R-variance plus the exact logarithmic vacancy
barrier. -/
theorem rootVacantVarianceAt_le_rootVarianceUpperConstant_mul_occupied_add_log
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootVacantVarianceAt R z hz u ≤
      rootVarianceUpperConstant Z * rootOccupiedVarianceAt R z hz u +
        2 * rootVarianceLogBarrierAt R z u := by
  change R.vacantVarianceAt z hz u ≤
    rootVarianceUpperConstant Z * R.occupiedVarianceAt z hz u +
      2 * rootVarianceLogBarrierAt R z u
  rw [R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u,
    R.occupiedVarianceAt_eq_sum_vacantVarianceAt hG z hz u]
  calc
    (∑ v ∈ R.children (G := G) u, (R.subtreeLawAt z hz v).variance) ≤
        ∑ v ∈ R.children (G := G) u,
          (rootVarianceUpperConstant Z * R.vacantVarianceAt z hz v +
            2 * rootedOccupationProbabilityAt R z v) := by
      apply Finset.sum_le_sum
      intro v hv
      exact subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
        hG R Z z hz hzZ v
    _ = rootVarianceUpperConstant Z *
          (∑ v ∈ R.children (G := G) u, R.vacantVarianceAt z hz v) +
        2 * (∑ v ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z v) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ rootVarianceUpperConstant Z *
          (∑ v ∈ R.children (G := G) u, R.vacantVarianceAt z hz v) +
        2 * rootVarianceLogBarrierAt R z u := by
      have hsum : (∑ v ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z v) ≤
          rootVarianceLogBarrierAt R z u := by
        unfold rootVarianceLogBarrierAt
        apply Finset.sum_le_sum
        intro v hv
        have hqpos : 0 < rootedVacancyProbabilityAt R z v := by
          unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
          exact div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)
        have hlog := Real.log_le_sub_one_of_pos hqpos
        linarith [rootedOccupationProbabilityAt_add_vacancy R z hz v]
      linarith

end
end AppendixA
end Forest
end Erdos993
