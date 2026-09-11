import Erdos993.Forest.AppendixDMacroscopicContribution

/-!
# Appendix D: retained marginal, covariance, and predictable variation

This module continues the constructive Appendix D development from the first
remaining gap.  Every marginal below is a marginal of the original global
`CanonicalFirstRecoveryState.law`; no retained graph or descendant branch is
assigned canonical or first-recovery data.
-/

open scoped BigOperators

namespace Erdos993
namespace ActualRootedVariance

noncomputable section

set_option maxHeartbeats 800000

universe u

noncomputable local instance finiteSubtypeAppendixDSpine
    {α : Type*} [Fintype α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable local instance classicalDecidableEqAppendixDSpine
    (α : Type*) : DecidableEq α := Classical.decEq α

namespace ComponentRooting

open Forest

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Children omitted from an ancestor-closed retained set. -/
noncomputable def omittedChildren (R : ComponentRooting G)
    (S : Finset V) (u : V) : Finset V := by
  classical
  exact R.children (G := G) u \ S

/-- The activity induced at a retained vertex after integrating all omitted
child branches.  This uses the unchanged activity of the original global law. -/
noncomputable def effectiveActivity (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (S : Finset V) (u : V) : ℝ :=
  C.activity * ∏ w ∈ R.omittedChildren (G := G) S u,
    R.vacancyProbability (G := G) C w

/-- Every retained effective activity is strictly positive. -/
theorem effectiveActivity_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (S : Finset V) (u : V) :
    0 < R.effectiveActivity (G := G) C S u := by
  unfold effectiveActivity
  exact mul_pos C.activity_pos (Finset.prod_pos fun w hw =>
    R.vacancyProbability_pos (G := G) C w)

/-- Integrating omitted branches can only decrease the original activity. -/
theorem effectiveActivity_le_activity (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (S : Finset V) (u : V) :
    R.effectiveActivity (G := G) C S u ≤ C.activity := by
  unfold effectiveActivity
  have hprod_nonneg : 0 ≤ ∏ w ∈ R.omittedChildren (G := G) S u,
      R.vacancyProbability (G := G) C w := by
    exact Finset.prod_nonneg fun w hw =>
      le_of_lt (R.vacancyProbability_pos (G := G) C w)
  have hprod_le : (∏ w ∈ R.omittedChildren (G := G) S u,
      R.vacancyProbability (G := G) C w) ≤ 1 := by
    exact Finset.prod_le_one (fun w hw =>
      le_of_lt (R.vacancyProbability_pos (G := G) C w)) (fun w hw => by
      rw [R.vacancyProbability_eq_one_sub_occupationProbability (G := G) C w]
      linarith [R.occupationProbability_nonneg (G := G) C w])
  nlinarith [C.activity_pos]

/-- D.55 branch-integration precursor: the partition function of the actual
allowed outside graph is the product of the actual exposed branch partition
functions.  This is an identity inside the original global law. -/
theorem independenceEval_allowedOutside_eq_prod_exposedAllowedPiece
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    independenceEval (ActualMartingaleProjection.AllowedOutsideGraph S I)
        C.activity =
      ∏ w ∈ R.exposedBoundary (G := G) S,
        independenceEval
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I w})
          C.activity := by
  classical
  change independenceEval
      (G.induce {x | x ∈
        ActualMartingaleProjection.allowedOutsideVertices S I}) C.activity = _
  rw [R.allowedOutsideVertices_eq_exposedAllowedUnion_D25 (G := G) C hS I]
  unfold exposedAllowedUnion
  exact independenceEval_induceFinset_biUnion G
    (R.exposedBoundary (G := G) S)
    (fun w => R.exposedAllowedPiece (G := G) I w)
    (R.exposedAllowedPiece_pairwiseDisjoint (G := G) C hS I)
    (R.exposedAllowedPiece_noCrossEdges (G := G) C hS I)
    C.activity

/-- One exposed branch contributes `P_w` when its observed parent is vacant
and `Q_w` when that parent is occupied. -/
theorem independenceEval_exposedAllowedPiece
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (w : V) :
    independenceEval
        (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I w}) C.activity =
      if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
        R.rootedP (G := G) C w else R.rootedQ (G := G) C w := by
  classical
  by_cases hzero :
      ActualMartingaleProjection.parentOccupationIndicator R I w = 0
  · have hpiece : R.exposedAllowedPiece (G := G) I w =
        R.descendants (G := G) w := by
      unfold exposedAllowedPiece
      rw [if_pos hzero]
    rw [if_pos hzero, hpiece]
    rfl
  · have hpiece : R.exposedAllowedPiece (G := G) I w =
        R.properDescendants (G := G) w := by
      unfold exposedAllowedPiece
      rw [if_neg hzero]
    rw [if_neg hzero, hpiece]
    unfold rootedQ
    exact (UniformFourthMoment.independenceEval_graphIso
      (R.deleteSubtreeRootIsoProperDescendants (G := G) w)
      C.activity).symm

/-- D.55 omitted-descendant integration in its exact global-law form. -/
theorem independenceEval_allowedOutside_eq_prod_boundary_PQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    independenceEval (ActualMartingaleProjection.AllowedOutsideGraph S I)
        C.activity =
      ∏ w ∈ R.exposedBoundary (G := G) S,
        if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
          R.rootedP (G := G) C w else R.rootedQ (G := G) C w := by
  rw [R.independenceEval_allowedOutside_eq_prod_exposedAllowedPiece
    (G := G) C hS I]
  apply Finset.prod_congr rfl
  intro w hw
  exact R.independenceEval_exposedAllowedPiece (G := G) C I w

/-- Exact D.55 point-mass formula for the marginal of the original global
canonical law.  The left side is literally the mass of the global restriction
fiber; the right side integrates every omitted descendant branch as `P` or
`Q` according to its observed retained parent. -/
theorem restrictionFiberMass_eq_activity_pow_mul_prod_boundary_PQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    ActualMartingaleProjection.restrictionFiberMass C S I =
      C.activity ^ (ActualMartingaleProjection.restriction S I).card *
        (∏ w ∈ R.exposedBoundary (G := G) S,
          if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
            R.rootedP (G := G) C w else R.rootedQ (G := G) C w) /
        independenceEval G C.activity := by
  rw [ActualMartingaleProjection.restrictionFiberMass_eq_allowedOutsideFiberFactor]
  unfold ActualMartingaleProjection.allowedOutsideFiberFactor
  rw [R.independenceEval_allowedOutside_eq_prod_boundary_PQ (G := G) C hS I]

/-- The preceding point mass is explicitly the sum of probabilities under the
one original global law. -/
theorem globalLaw_restrictionFiber_sum_eq_activity_pow_mul_prod_boundary_PQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    (∑ J ∈ ActualMartingaleProjection.restrictionFiber S I,
      C.law.probability J) =
      C.activity ^ (ActualMartingaleProjection.restriction S I).card *
        (∏ w ∈ R.exposedBoundary (G := G) S,
          if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
            R.rootedP (G := G) C w else R.rootedQ (G := G) C w) /
        independenceEval G C.activity := by
  change ActualMartingaleProjection.restrictionFiberMass C S I = _
  exact R.restrictionFiberMass_eq_activity_pow_mul_prod_boundary_PQ
    (G := G) C hS I

/-- Deterministic local coefficient in the predictable quadratic variation. -/
noncomputable def predictableQuadraticCoefficient
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) : ℝ :=
  R.occupationProbability (G := G) C u *
    R.vacancyProbability (G := G) C u *
    R.conditionalMeanDifference (G := G) C u ^ 2

/-- D.57: the intrinsic predictable quadratic variation of the parent-before-
child martingale on `S`.  It is evaluated on configurations of the original
global law. -/
noncomputable def predictableQuadraticVariation
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (I : IndepFinset G) : ℝ :=
  ∑ u ∈ S, R.predictableQuadraticCoefficient (G := G) C u *
    (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)

/-- D.58 expectation identity: the mean predictable quadratic variation is
the actual rooted variance contribution retained on `S`. -/
theorem lawExpectation_predictableQuadraticVariation_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    ActualMartingaleProjection.lawExpectation C
        (R.predictableQuadraticVariation (G := G) C S) =
      ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
  classical
  unfold ActualMartingaleProjection.lawExpectation predictableQuadraticVariation
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        ∑ u ∈ S, R.predictableQuadraticCoefficient (G := G) C u *
          (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)) =
      ∑ I : IndepFinset G, ∑ u ∈ S,
        C.law.probability I *
          (R.predictableQuadraticCoefficient (G := G) C u *
            (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)) := by
              apply Finset.sum_congr rfl
              intro I hI
              rw [Finset.mul_sum]
    _ = ∑ u ∈ S, ∑ I : IndepFinset G,
        C.law.probability I *
          (R.predictableQuadraticCoefficient (G := G) C u *
            (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)) := by
              rw [Finset.sum_comm]
    _ = ∑ u ∈ S, R.predictableQuadraticCoefficient (G := G) C u *
        (∑ I : IndepFinset G, C.law.probability I *
          (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)) := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro I hI
            ring
    _ = ∑ u ∈ S, R.predictableQuadraticCoefficient (G := G) C u *
        R.parentAbsentProbability (G := G) C u := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [ActualMartingaleProjection.expectation_one_sub_parentOccupationIndicator]
    _ = ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
          apply Finset.sum_congr rfl
          intro u hu
          unfold predictableQuadraticCoefficient vertexVarianceContribution
          ring

/-- D.61: the random PQV coefficient is at most `28` times the corresponding
variance contribution when the global activity is below `27`. -/
theorem predictableQuadraticCoefficient_le_twentyEight_mul_contribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    R.predictableQuadraticCoefficient (G := G) C u ≤
      28 * R.vertexVarianceContribution (G := G) C u := by
  have ha := R.one_div_twentyEight_lt_parentAbsentProbability
    (G := G) C hz u
  have hp := R.occupationProbability_nonneg (G := G) C u
  have hq := le_of_lt (R.vacancyProbability_pos (G := G) C u)
  have hd := sq_nonneg (R.conditionalMeanDifference (G := G) C u)
  unfold predictableQuadraticCoefficient vertexVarianceContribution
  nlinarith [mul_nonneg (mul_nonneg hp hq) hd]

/-- Mean of a single occupation indicator under the original global law. -/
noncomputable def occupationMean (C : CanonicalFirstRecoveryState G) (x : V) : ℝ :=
  ActualMartingaleProjection.lawExpectation C
    (fun I => ActualMartingaleProjection.occupationIndicator I x)

/-- Covariance of two occupation indicators under the original global law. -/
noncomputable def occupationCovariance
    (C : CanonicalFirstRecoveryState G) (x y : V) : ℝ :=
  ActualMartingaleProjection.lawExpectation C (fun I =>
    (ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
    (ActualMartingaleProjection.occupationIndicator I y - occupationMean C y))

/-- Occupation covariance is symmetric. -/
theorem occupationCovariance_comm (C : CanonicalFirstRecoveryState G)
    (x y : V) : occupationCovariance C x y = occupationCovariance C y x := by
  unfold occupationCovariance ActualMartingaleProjection.lawExpectation
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- An occupation outside the descendant branch at `u` is orthogonal to the
actual innovation at `u`. -/
theorem expectation_centeredOccupation_mul_eta_eq_zero_of_not_isDescendant
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {x u : V} (hxu : ¬ R.IsDescendant (G := G) u x) :
    ActualMartingaleProjection.lawExpectation C (fun I =>
      (ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
        ActualMartingaleProjection.eta C R I u) = 0 := by
  classical
  let S := ActualMartingaleProjection.descendantComplement R u
  let g : Finset V → ℝ := fun T =>
    (if x ∈ T then 1 else 0) - occupationMean C x
  have hxS : x ∈ S := by
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, by
      simpa only [ComponentRooting.mem_descendants] using hxu⟩
  have huS : u ∉ S := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (R.self_mem_descendants (G := G) u)
  have hg (I : IndepFinset G) :
      g (ActualMartingaleProjection.restriction S I) =
        ActualMartingaleProjection.occupationIndicator I x - occupationMean C x := by
    unfold g ActualMartingaleProjection.restriction
      ActualMartingaleProjection.occupationIndicator
    simp [hxS]
  unfold ActualMartingaleProjection.lawExpectation
  rw [show (∑ I : IndepFinset G, C.law.probability I *
      ((ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
        ActualMartingaleProjection.eta C R I u)) =
      ∑ I : IndepFinset G, C.law.probability I *
        (g (ActualMartingaleProjection.restriction S I) *
          ActualMartingaleProjection.eta C R I u) by
      apply Finset.sum_congr rfl
      intro I hI
      rw [hg I]]
  rw [← ActualMartingaleProjection.lawExpectation_restriction_mul_conditionalExpectation]
  apply Finset.sum_eq_zero
  intro I hI
  rw [ActualMartingaleProjection.conditionalExpectation_eta_eq_zero_of_unobserved
    C R S (ActualMartingaleProjection.descendantComplement_ancestorClosed R u)
    u huS I]
  ring

/-- Along a rooted child edge, the occupation mean satisfies the exact cavity
recursion. -/
theorem occupationMean_child (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) {p u : V} (hpu : R.IsChild (G := G) p u) :
    occupationMean C u = R.occupationProbability (G := G) C u *
      (1 - occupationMean C p) := by
  unfold occupationMean ActualMartingaleProjection.lawExpectation
  rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
  rw [R.parentAbsentProbability_child (G := G) C hpu]
  rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
  ring

/-- Exact affine innovation decomposition across one rooted child edge. -/
theorem centeredOccupationIndicator_child (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) {p u : V} (hpu : R.IsChild (G := G) p u)
    (I : IndepFinset G) :
    ActualMartingaleProjection.occupationIndicator I u - occupationMean C u =
      ActualMartingaleProjection.eta C R I u -
        R.occupationProbability (G := G) C u *
          (ActualMartingaleProjection.occupationIndicator I p - occupationMean C p) := by
  have hu : u ≠ R.rootOf (G := G) u := by
    intro h
    exact R.not_isChild_of_eq_root (G := G) h hpu
  unfold ActualMartingaleProjection.eta
  rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent C R I hu]
  rw [R.selectedParent_eq_of_isChild (G := G) C hpu hu]
  rw [R.occupationMean_child (G := G) C hpu]
  ring

/-- Exact covariance regression across a child edge, valid whenever the other
endpoint is outside the child's descendant branch. -/
theorem occupationCovariance_child (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) {x p u : V} (hpu : R.IsChild (G := G) p u)
    (hxu : ¬ R.IsDescendant (G := G) u x) :
    occupationCovariance C x u =
      -R.occupationProbability (G := G) C u * occupationCovariance C x p := by
  unfold occupationCovariance ActualMartingaleProjection.lawExpectation
  simp_rw [R.centeredOccupationIndicator_child (G := G) C hpu]
  have hzero := R.expectation_centeredOccupation_mul_eta_eq_zero_of_not_isDescendant
    (G := G) C hxu
  unfold ActualMartingaleProjection.lawExpectation at hzero
  rw [show (∑ I : IndepFinset G, C.law.probability I *
      ((ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
        (ActualMartingaleProjection.eta C R I u -
          R.occupationProbability (G := G) C u *
            (ActualMartingaleProjection.occupationIndicator I p - occupationMean C p)))) =
      (∑ I : IndepFinset G, C.law.probability I *
        ((ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
          ActualMartingaleProjection.eta C R I u)) -
      R.occupationProbability (G := G) C u *
        (∑ I : IndepFinset G, C.law.probability I *
          ((ActualMartingaleProjection.occupationIndicator I x - occupationMean C x) *
            (ActualMartingaleProjection.occupationIndicator I p - occupationMean C p))) by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro I hI
      ring]
  rw [hzero]
  ring

/-- The diagonal occupation covariance is the Bernoulli variance. -/
theorem occupationCovariance_self_eq
    (C : CanonicalFirstRecoveryState G) (x : V) :
    occupationCovariance C x x = occupationMean C x * (1 - occupationMean C x) := by
  classical
  unfold occupationCovariance ActualMartingaleProjection.lawExpectation
  let μ := occupationMean C x
  have hmean : (∑ I : IndepFinset G, C.law.probability I *
      ActualMartingaleProjection.occupationIndicator I x) = μ := rfl
  have hsquare : (∑ I : IndepFinset G, C.law.probability I *
      ActualMartingaleProjection.occupationIndicator I x ^ 2) = μ := by
    simpa only [ActualMartingaleProjection.occupationIndicator_sq] using hmean
  have hprob : (∑ I : IndepFinset G, C.law.probability I) = 1 :=
    C.law.probability_sum
  change (∑ I : IndepFinset G, C.law.probability I *
      ((ActualMartingaleProjection.occupationIndicator I x - μ) *
        (ActualMartingaleProjection.occupationIndicator I x - μ))) = μ * (1 - μ)
  rw [show (∑ I : IndepFinset G, C.law.probability I *
      ((ActualMartingaleProjection.occupationIndicator I x - μ) *
        (ActualMartingaleProjection.occupationIndicator I x - μ))) =
      (∑ I : IndepFinset G, C.law.probability I *
        ActualMartingaleProjection.occupationIndicator I x ^ 2) -
      2 * μ * (∑ I : IndepFinset G, C.law.probability I *
        ActualMartingaleProjection.occupationIndicator I x) +
      μ ^ 2 * (∑ I : IndepFinset G, C.law.probability I) by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro I hI
        ring]
  rw [hsquare, hmean, hprob]
  ring

/-- A single-site occupation mean is nonnegative. -/
theorem occupationMean_nonneg (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (x : V) : 0 ≤ occupationMean C x := by
  unfold occupationMean ActualMartingaleProjection.lawExpectation
  rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
  exact mul_nonneg
    (R.parentAbsentProbability_nonneg (G := G) C x)
    (R.occupationProbability_nonneg (G := G) C x)

/-- A single-site occupation mean is at most one. -/
theorem occupationMean_le_one (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (x : V) : occupationMean C x ≤ 1 := by
  unfold occupationMean ActualMartingaleProjection.lawExpectation
  rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
  calc
    R.parentAbsentProbability (G := G) C x *
        R.occupationProbability (G := G) C x ≤
      1 * R.occupationProbability (G := G) C x :=
        mul_le_mul_of_nonneg_right
          (R.parentAbsentProbability_le_one (G := G) C x)
          (R.occupationProbability_nonneg (G := G) C x)
    _ ≤ 1 := by simpa using R.occupationProbability_le_one (G := G) C x

/-- The diagonal occupation covariance is nonnegative. -/
theorem occupationCovariance_self_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (x : V) :
    0 ≤ occupationCovariance C x x := by
  rw [occupationCovariance_self_eq]
  exact mul_nonneg (R.occupationMean_nonneg (G := G) C x)
    (sub_nonneg.mpr (R.occupationMean_le_one (G := G) C x))

/-- Every diagonal occupation covariance is at most `1/4`. -/
theorem occupationCovariance_self_le_one_quarter
    (C : CanonicalFirstRecoveryState G) (x : V) :
    occupationCovariance C x x ≤ (1 : ℝ) / 4 := by
  rw [occupationCovariance_self_eq]
  nlinarith [sq_nonneg (occupationMean C x - (1 : ℝ) / 2)]

/-- A covariance-peeling derivation records the successive endpoint removals
along a rooted forest path.  Each constructor is one exact cavity-regression
step; no probabilistic assumption is stored in this relation. -/
inductive CovariancePeeling (R : ComponentRooting G) : V → V → ℕ → Prop
  | refl (x : V) : CovariancePeeling R x x 0
  | right {x p u : V} {n : ℕ}
      (hpu : R.IsChild (G := G) p u)
      (hout : ¬ R.IsDescendant (G := G) u x)
      (h : CovariancePeeling R x p n) : CovariancePeeling R x u (n + 1)
  | left {p u y : V} {n : ℕ}
      (hpu : R.IsChild (G := G) p u)
      (hout : ¬ R.IsDescendant (G := G) u y)
      (h : CovariancePeeling R p y n) : CovariancePeeling R u y (n + 1)

/-- D.59 path regression on an explicit covariance-peeling path: every edge
contributes one factor at most `27/28`. -/
theorem abs_occupationCovariance_le_of_covariancePeeling
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {x y : V} {n : ℕ}
    (hxy : CovariancePeeling R x y n) :
    |occupationCovariance C x y| ≤
      (1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ n := by
  induction hxy with
  | refl x =>
      rw [abs_of_nonneg (R.occupationCovariance_self_nonneg (G := G) C x)]
      simpa using occupationCovariance_self_le_one_quarter C x
  | @right x p u n hpu hout h ih =>
      rw [R.occupationCovariance_child (G := G) C hpu hout]
      have hp0 := R.occupationProbability_nonneg (G := G) C u
      have hp := le_of_lt
        (R.occupationProbability_lt_twentySeven_div_twentyEight
          (G := G) C hz u)
      rw [abs_mul, abs_neg, abs_of_nonneg hp0]
      calc
        R.occupationProbability (G := G) C u * |occupationCovariance C x p| ≤
            ((27 : ℝ) / 28) *
              ((1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ n) := by
                exact mul_le_mul hp ih (abs_nonneg _) (by norm_num)
        _ = (1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ (n + 1) := by
              rw [pow_succ]
              ring
  | @left p u y n hpu hout h ih =>
      rw [occupationCovariance_comm C u y,
        R.occupationCovariance_child (G := G) C hpu hout,
        occupationCovariance_comm C y p]
      have hp0 := R.occupationProbability_nonneg (G := G) C u
      have hp := le_of_lt
        (R.occupationProbability_lt_twentySeven_div_twentyEight
          (G := G) C hz u)
      rw [abs_mul, abs_neg, abs_of_nonneg hp0]
      calc
        R.occupationProbability (G := G) C u * |occupationCovariance C p y| ≤
            ((27 : ℝ) / 28) *
              ((1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ n) := by
                exact mul_le_mul hp ih (abs_nonneg _) (by norm_num)
        _ = (1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ (n + 1) := by
              rw [pow_succ]
              ring

/-- Reroot the component containing `x` at `x`, leaving all other component
roots unchanged. -/
noncomputable def rerootAt (R : ComponentRooting G) (x : V) : ComponentRooting G := by
  classical
  exact {
    root := fun c => if c = G.connectedComponentMk x then x else R.root c
    root_mem := by
      intro c
      split_ifs with h
      · subst c
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      · exact R.root_mem c }

/-- In the rerooted component, every vertex reachable from `x` has root `x`. -/
theorem rerootAt_rootOf_eq_of_reachable (R : ComponentRooting G) {x y : V}
    (hxy : G.Reachable x y) :
    (R.rerootAt (G := G) x).rootOf (G := G) y = x := by
  unfold rerootAt rootOf
  rw [← SimpleGraph.ConnectedComponent.sound hxy]
  simp

/-- A descendant chain from a component root gives a covariance peeling whose
length is the rooted depth. -/
theorem covariancePeeling_of_root_isDescendant
    (R : ComponentRooting G) {x y : V}
    (hxroot : x = R.rootOf (G := G) x)
    (hxy : R.IsDescendant (G := G) x y) :
    CovariancePeeling R x y (R.depth (G := G) y) := by
  classical
  generalize hn : R.depth (G := G) y = n
  induction n using Nat.strong_induction_on generalizing y with
  | h n ih =>
      by_cases hyx : y = x
      · subst y
        have hdepth : R.depth (G := G) x = 0 := by
          unfold depth
          rw [← hxroot]
          simp
        rw [hdepth] at hn
        subst n
        exact CovariancePeeling.refl (R := R) x
      · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hxy with hEq | ⟨p, hxp, hpy⟩
        · exact (hyx hEq).elim
        · have hpdepth := R.depth_child (G := G) hpy
          have hplt : R.depth (G := G) p < n := by omega
          have ihp := ih (R.depth (G := G) p) hplt hxp rfl
          have hout : ¬ R.IsDescendant (G := G) y x := by
            intro hyxdesc
            have hle := R.depth_le_of_isDescendant (G := G) hyxdesc
            have hxdepth : R.depth (G := G) x = 0 := by
              unfold depth
              rw [← hxroot]
              simp
            omega
          have hstep := CovariancePeeling.right hpy hout ihp
          rw [hpdepth] at hn
          simpa [hn] using hstep

/-- Every reachable pair admits an exact covariance peeling of graph-distance
length, by rerooting its component at the first endpoint. -/
theorem covariancePeeling_dist (R : ComponentRooting G) {x y : V}
    (hxy : G.Reachable x y) :
    CovariancePeeling (R.rerootAt (G := G) x) x y (G.dist x y) := by
  let R' := R.rerootAt (G := G) x
  have hrootY : R'.rootOf (G := G) y = x :=
    R.rerootAt_rootOf_eq_of_reachable (G := G) hxy
  have hrootX : R'.rootOf (G := G) x = x :=
    R.rerootAt_rootOf_eq_of_reachable (G := G) (SimpleGraph.Reachable.refl x)
  have hdesc : R'.IsDescendant (G := G) x y := by
    rw [← hrootY]
    exact R'.root_isDescendant (G := G) y
  have hpeel := R'.covariancePeeling_of_root_isDescendant (G := G)
    hrootX.symm hdesc
  change CovariancePeeling R' x y (G.dist x y)
  simpa [R', depth, hrootY] using hpeel

/-- D.59 in the required arbitrary-pair graph-distance form.  Disconnected
pairs are treated by rerooting the component of `x` and using exact
outside-branch centering at the other component root. -/
theorem abs_occupationCovariance_le_dist
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (x y : V) :
    |occupationCovariance C x y| ≤
      (1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ (G.dist x y) := by
  by_cases hxy : G.Reachable x y
  · exact (R.rerootAt (G := G) x).abs_occupationCovariance_le_of_covariancePeeling
      (G := G) C hz (R.covariancePeeling_dist (G := G) hxy)
  · have hzero : occupationCovariance C x y = 0 := by
      let R' := R.rerootAt (G := G) y
      have hyroot : y = R'.rootOf (G := G) y :=
        (R.rerootAt_rootOf_eq_of_reachable (G := G)
          (SimpleGraph.Reachable.refl y)).symm
      have hout : ¬ R'.IsDescendant (G := G) y x := by
        intro hdesc
        exact hxy (R'.isDescendant_reachable (G := G) hdesc).symm
      unfold occupationCovariance
      have horth := R'.expectation_centeredOccupation_mul_eta_eq_zero_of_not_isDescendant
        (G := G) C hout
      have hmeanY : occupationMean C y = R'.occupationProbability (G := G) C y := by
        unfold occupationMean ActualMartingaleProjection.lawExpectation
        rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
        have ha : R'.parentAbsentProbability (G := G) C y = 1 := by
          rw [hyroot]
          exact R'.parentAbsentProbability_rootOf (G := G) C y
        rw [ha]
        ring
      unfold ActualMartingaleProjection.eta at horth
      have hparent (I : IndepFinset G) :
          ActualMartingaleProjection.parentOccupationIndicator R' I y = 0 :=
        ActualMartingaleProjection.parentOccupationIndicator_root R' I hyroot
      simp_rw [hparent] at horth
      simpa [hmeanY] using horth
    rw [hzero, abs_zero]
    positivity

/-- Every retained vertex has a retained rooted-leaf descendant. -/
theorem exists_rootedLeaf_descendant
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    {u : V} (huS : u ∈ S) :
    ∃ ell ∈ R.rootedLeaves (G := G) S,
      R.IsDescendant (G := G) u ell := by
  classical
  generalize hn : R.subtreeOrder (G := G) u = n
  induction n using Nat.strong_induction_on generalizing u with
  | h n ih =>
      by_cases hleaf : ∀ v, v ∈ S → R.IsDescendant (G := G) u v → u = v
      · exact ⟨u, (R.mem_rootedLeaves (G := G) S u).mpr
          ⟨huS, fun v hvS huv => (hleaf v hvS huv).symm⟩,
          Relation.ReflTransGen.refl⟩
      · push_neg at hleaf
        obtain ⟨v, hvS, huv, huvne⟩ := hleaf
        rcases (R.isDescendant_iff_eq_or_child_descendant (G := G) u v).mp huv with
          huvEq | ⟨w, huw, hwv⟩
        · exact (huvne huvEq).elim
        · have hwS : w ∈ S := hS hvS hwv
          have hwlt : R.subtreeOrder (G := G) w < n := by
            rw [← hn]
            exact R.subtreeOrder_child_lt (G := G) huw
          obtain ⟨ell, hell, hwell⟩ := ih _ hwlt hwS rfl
          exact ⟨ell, hell, Relation.ReflTransGen.trans
            (Relation.ReflTransGen.single huw) hwell⟩

/-- Retained children of `x`. -/
noncomputable def retainedChildren (R : ComponentRooting G)
    (S : Finset V) (x : V) : Finset V := by
  classical
  exact (R.children (G := G) x).filter (fun u => u ∈ S)

@[simp] theorem mem_retainedChildren (R : ComponentRooting G)
    (S : Finset V) (x u : V) :
    u ∈ R.retainedChildren (G := G) S x ↔
      R.IsChild (G := G) x u ∧ u ∈ S := by
  classical
  simp [retainedChildren]

/-- D.60 child-frontier bound: the number of retained child branches at any
vertex is bounded by the number of retained rooted leaves. -/
theorem retainedChildren_card_le_rootedLeaves_card
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    (x : V) :
    (R.retainedChildren (G := G) S x).card ≤
      (R.rootedLeaves (G := G) S).card := by
  classical
  -- Use a total choice with a harmless default outside the retained child set.
  let f : V → V := fun u => if hu : u ∈ R.retainedChildren (G := G) S x then
      Classical.choose (R.exists_rootedLeaf_descendant (G := G) C hS
        ((R.mem_retainedChildren (G := G) S x u).mp hu).2) else u
  apply Finset.card_le_card_of_injOn f
  · intro u hu
    change u ∈ R.retainedChildren (G := G) S x at hu
    change f u ∈ R.rootedLeaves (G := G) S
    rw [show f u = Classical.choose
        (R.exists_rootedLeaf_descendant (G := G) C hS
          ((R.mem_retainedChildren (G := G) S x u).mp hu).2) by
      simp only [f, dif_pos hu]]
    exact (Classical.choose_spec
      (R.exists_rootedLeaf_descendant (G := G) C hS
        ((R.mem_retainedChildren (G := G) S x u).mp hu).2)).1
  · intro u hu v hv huv
    change u ∈ R.retainedChildren (G := G) S x at hu
    change v ∈ R.retainedChildren (G := G) S x at hv
    have hfu : R.IsDescendant (G := G) u (f u) := by
      rw [show f u = Classical.choose
          (R.exists_rootedLeaf_descendant (G := G) C hS
            ((R.mem_retainedChildren (G := G) S x u).mp hu).2) by
        simp only [f, dif_pos hu]]
      exact (Classical.choose_spec
        (R.exists_rootedLeaf_descendant (G := G) C hS
          ((R.mem_retainedChildren (G := G) S x u).mp hu).2)).2
    have hfv : R.IsDescendant (G := G) v (f v) := by
      rw [show f v = Classical.choose
          (R.exists_rootedLeaf_descendant (G := G) C hS
            ((R.mem_retainedChildren (G := G) S x v).mp hv).2) by
        simp only [f, dif_pos hv]]
      exact (Classical.choose_spec
        (R.exists_rootedLeaf_descendant (G := G) C hS
          ((R.mem_retainedChildren (G := G) S x v).mp hv).2)).2
    by_contra huvne
    have hdisj := R.children_pairwiseDisjoint_descendants (G := G) C.isForest x
      ((R.mem_children (G := G) x u).mpr
        ((R.mem_retainedChildren (G := G) S x u).mp hu).1)
      ((R.mem_children (G := G) x v).mpr
        ((R.mem_retainedChildren (G := G) S x v).mp hv).1) huvne
    have hmemu : f u ∈ R.descendants (G := G) u :=
      (R.mem_descendants (G := G) u (f u)).mpr hfu
    have hmemv : f u ∈ R.descendants (G := G) v := by
      rw [huv]
      exact (R.mem_descendants (G := G) v (f v)).mpr hfv
    exact Finset.disjoint_left.mp hdisj hmemu hmemv

/-- Descendant chains are geodesic relative to the selected component root. -/
theorem depth_eq_depth_add_dist_of_isDescendant
    (R : ComponentRooting G) {u v : V}
    (huv : R.IsDescendant (G := G) u v) :
    R.depth (G := G) v =
      R.depth (G := G) u + G.dist u v := by
  induction huv using Relation.ReflTransGen.trans_induction_on with
  | refl => simp
  | single hchild =>
      rw [R.depth_child (G := G) hchild,
        SimpleGraph.dist_eq_one_iff_adj.mpr hchild.1]
  | @trans u v w huv hvw ihuv ihvw =>
      have hreachUV : G.Reachable u v :=
        R.isDescendant_reachable (G := G) huv
      have hreachVW : G.Reachable v w :=
        R.isDescendant_reachable (G := G) hvw
      have hreachUW : G.Reachable u w := hreachUV.trans hreachVW
      have hroot : R.rootOf (G := G) u = R.rootOf (G := G) w :=
        R.rootOf_eq_of_reachable (G := G) hreachUW
      have hlower : R.depth (G := G) w ≤
          R.depth (G := G) u + G.dist u w := by
        unfold depth
        rw [← hroot]
        exact (R.rootOf_reachable (G := G) u).dist_triangle_left w
      have hupper : G.dist u w ≤ G.dist u v + G.dist v w :=
        hreachVW.dist_triangle_right u
      omega

/-- Comparable ancestors of `x` at the same distance from `x` coincide. -/
theorem eq_of_isDescendant_of_isDescendant_of_dist_eq
    (R : ComponentRooting G) {x y z : V}
    (hyz : R.IsDescendant (G := G) y z)
    (hzx : R.IsDescendant (G := G) z x)
    (hdist : G.dist x y = G.dist x z) :
    y = z := by
  have hyx : R.IsDescendant (G := G) y x :=
    Relation.ReflTransGen.trans hyz hzx
  have hyzDepth := R.depth_eq_depth_add_dist_of_isDescendant (G := G) hyz
  have hzxDepth := R.depth_eq_depth_add_dist_of_isDescendant (G := G) hzx
  have hyxDepth := R.depth_eq_depth_add_dist_of_isDescendant (G := G) hyx
  have hdist' : G.dist y x = G.dist z x := by
    calc
      G.dist y x = G.dist x y := SimpleGraph.dist_comm
      _ = G.dist x z := hdist
      _ = G.dist z x := SimpleGraph.dist_comm
  have hzero : G.dist y z = 0 := by omega
  exact ((R.isDescendant_reachable (G := G) hyz).dist_eq_zero_iff).mp hzero

/-- If `a → b` is an original child edge but `b` is one step closer than `a`
to `x`, then `b` is an ancestor of `x`. -/
theorem isDescendant_of_isChild_of_dist_eq_add_one
    (hG : G.IsAcyclic) (R : ComponentRooting G) {x a b : V}
    (hab : R.IsChild (G := G) a b)
    (hxa : G.dist x a = G.dist x b + 1)
    (hxb : G.Reachable x b) :
    R.IsDescendant (G := G) b x := by
  suffices h : ∀ n : ℕ, ∀ b : V,
      G.dist x b = n → G.Reachable x b → ∀ a : V,
      R.IsChild (G := G) a b →
      G.dist x a = G.dist x b + 1 →
      R.IsDescendant (G := G) b x by
    exact h (G.dist x b) b rfl hxb a hab hxa
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro b hbn hreach a hab hxa
      by_cases hbx : b = x
      · subst b
        exact Relation.ReflTransGen.refl
      · obtain ⟨p, hpPath, hpLength⟩ := hreach.exists_path_of_dist
        have hpnn : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne (Ne.symm hbx)
        have hprefix : p.dropLast.length = G.dist x p.penultimate :=
          SimpleGraph.length_eq_dist_of_subwalk hpLength
            ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
        have hstep : G.dist x b = G.dist x p.penultimate + 1 := by
          calc
            G.dist x b = p.length := hpLength.symm
            _ = p.dropLast.length + 1 :=
              (p.length_dropLast_add_one hpnn).symm
            _ = G.dist x p.penultimate + 1 := by rw [hprefix]
        have hpb : G.Adj p.penultimate b := p.adj_penultimate hpnn
        rcases (R.adj_iff_isChild_or_reverse (G := G) hG).mp hpb with
          hpbChild | hbpChild
        · have hpa : p.penultimate = a :=
            R.isChild_unique (G := G) hG hpbChild hab
          rw [hpa] at hstep
          omega
        · have hpdesc : R.IsDescendant (G := G) p.penultimate x :=
            ih (G.dist x p.penultimate) (by omega)
              p.penultimate rfl p.dropLast.reachable b hbpChild hstep
          exact R.child_descendant (G := G) hbpChild hpdesc

/-- An original child edge keeps its orientation after rerooting at `x`
provided its upper endpoint is not an ancestor of `x`. -/
theorem rerootAt_isChild_of_isChild_of_not_isDescendant
    (hG : G.IsAcyclic) (R : ComponentRooting G) {x a b : V}
    (hxa : G.Reachable x a)
    (hab : R.IsChild (G := G) a b)
    (hnax : ¬ R.IsDescendant (G := G) a x) :
    (R.rerootAt (G := G) x).IsChild (G := G) a b := by
  have hxb : G.Reachable x b := hxa.trans hab.1.reachable
  have hdist : G.dist x b = G.dist x a + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable x hab.1 hxa with
      hback | hforward
    · have hbdesc : R.IsDescendant (G := G) b x :=
        R.isDescendant_of_isChild_of_dist_eq_add_one
          (G := G) hG hab hback hxb
      exact (hnax (R.child_descendant (G := G) hab hbdesc)).elim
    · exact hforward
  refine ⟨hab.1, ?_⟩
  rw [R.rerootAt_rootOf_eq_of_reachable (G := G) hxb]
  exact hdist

/-- A descendant chain whose upper endpoint is not an ancestor of `x` keeps
its orientation after rerooting the component at `x`. -/
theorem rerootAt_isDescendant_of_isDescendant_of_not_isDescendant
    (hG : G.IsAcyclic) (R : ComponentRooting G) {x y z : V}
    (hxy : G.Reachable x y)
    (hyz : R.IsDescendant (G := G) y z)
    (hnyx : ¬ R.IsDescendant (G := G) y x) :
    (R.rerootAt (G := G) x).IsDescendant (G := G) y z := by
  revert hxy hnyx
  refine Relation.ReflTransGen.head_induction_on hyz ?_ ?_
  · intro _ _
    exact Relation.ReflTransGen.refl
  · intro a c hac hcz ih hxa hnax
    have hxc : G.Reachable x c := hxa.trans hac.1.reachable
    have hncx : ¬ R.IsDescendant (G := G) c x := by
      intro hcx
      exact hnax (R.child_descendant (G := G) hac hcx)
    have hac' : (R.rerootAt (G := G) x).IsChild (G := G) a c :=
      R.rerootAt_isChild_of_isChild_of_not_isDescendant
        (G := G) hG hxa hac hnax
    exact Relation.ReflTransGen.head hac' (ih hxc hncx)

/-- Correct equal-distance helper for comparable vertices outside the ancestor
chain of the sphere center. -/
theorem eq_of_isDescendant_of_not_isDescendant_of_dist_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G) {x y z : V}
    (hxy : G.Reachable x y)
    (hyz : R.IsDescendant (G := G) y z)
    (hnyx : ¬ R.IsDescendant (G := G) y x)
    (hdist : G.dist x y = G.dist x z) :
    y = z := by
  let R' := R.rerootAt (G := G) x
  have hxz : G.Reachable x z :=
    hxy.trans (R.isDescendant_reachable (G := G) hyz)
  have hyz' : R'.IsDescendant (G := G) y z :=
    R.rerootAt_isDescendant_of_isDescendant_of_not_isDescendant
      (G := G) hG hxy hyz hnyx
  have hrootY : R'.rootOf (G := G) y = x :=
    R.rerootAt_rootOf_eq_of_reachable (G := G) hxy
  have hrootZ : R'.rootOf (G := G) z = x :=
    R.rerootAt_rootOf_eq_of_reachable (G := G) hxz
  have hdepth : R'.depth (G := G) y = R'.depth (G := G) z := by
    simp only [depth, hrootY, hrootZ]
    exact hdist
  exact R'.eq_of_isDescendant_of_depth_eq (G := G) hyz' hdepth

/-- The part of `S` lying in the connected component of `x`. -/
noncomputable def reachablePart (R : ComponentRooting G)
    (S : Finset V) (x : V) : Finset V := by
  classical
  exact S.filter fun y => G.Reachable x y

@[simp] theorem mem_reachablePart (R : ComponentRooting G)
    (S : Finset V) (x y : V) :
    y ∈ R.reachablePart (G := G) S x ↔ y ∈ S ∧ G.Reachable x y := by
  classical
  simp [reachablePart]

/-- Vertices of `S` reachable from `x` at graph distance exactly `n`. -/
noncomputable def reachableDistanceShell
    (R : ComponentRooting G) (S : Finset V)
    (x : V) (n : ℕ) : Finset V := by
  classical
  exact S.filter fun y => G.Reachable x y ∧ G.dist x y = n

@[simp] theorem mem_reachableDistanceShell
    (R : ComponentRooting G) (S : Finset V)
    (x : V) (n : ℕ) (y : V) :
    y ∈ R.reachableDistanceShell (G := G) S x n ↔
      y ∈ S ∧ G.Reachable x y ∧ G.dist x y = n := by
  classical
  simp [reachableDistanceShell]

/-- D.60: every reachable distance shell in an ancestor-closed retained set
has at most one vertex more than the number of retained rooted leaves. -/
theorem reachableDistanceShell_card_le_rootedLeaves_card_add_one
    (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (x : V) (n : ℕ) :
    (R.reachableDistanceShell (G := G) S x n).card ≤
      (R.rootedLeaves (G := G) S).card + 1 := by
  classical
  let leaf : V → V := fun u =>
    if hu : u ∈ S then
      Classical.choose (R.exists_rootedLeaf_descendant (G := G) C hS hu)
    else u
  have hleaf_mem (u : V) (hu : u ∈ S) :
      leaf u ∈ R.rootedLeaves (G := G) S := by
    rw [show leaf u = Classical.choose
        (R.exists_rootedLeaf_descendant (G := G) C hS hu) by
      simp only [leaf, dif_pos hu]]
    exact (Classical.choose_spec
      (R.exists_rootedLeaf_descendant (G := G) C hS hu)).1
  have hleaf_desc (u : V) (hu : u ∈ S) :
      R.IsDescendant (G := G) u (leaf u) := by
    rw [show leaf u = Classical.choose
        (R.exists_rootedLeaf_descendant (G := G) C hS hu) by
      simp only [leaf, dif_pos hu]]
    exact (Classical.choose_spec
      (R.exists_rootedLeaf_descendant (G := G) C hS hu)).2
  let f : V → Option V := fun u =>
    if u ∈ R.reachableDistanceShell (G := G) S x n then
      if R.IsDescendant (G := G) u x then none else some (leaf u)
    else none
  calc
    (R.reachableDistanceShell (G := G) S x n).card ≤
        (insert (none : Option V)
          ((R.rootedLeaves (G := G) S).image (fun u : V => some u))).card := by
      apply Finset.card_le_card_of_injOn f
      · intro u hu
        change u ∈ R.reachableDistanceShell (G := G) S x n at hu
        change f u ∈ insert (none : Option V)
          ((R.rootedLeaves (G := G) S).image (fun w : V => some w))
        by_cases hux : R.IsDescendant (G := G) u x
        · rw [show f u = none by simp only [f, if_pos hu, if_pos hux]]
          exact Finset.mem_insert_self (none : Option V) _
        · have huData :=
            (R.mem_reachableDistanceShell (G := G) S x n u).mp hu
          rw [show f u = some (leaf u) by
            simp only [f, if_pos hu, if_neg hux]]
          exact Finset.mem_insert_of_mem
            (Finset.mem_image.mpr ⟨leaf u, hleaf_mem u huData.1, rfl⟩)
      · intro u hu v hv huv
        change u ∈ R.reachableDistanceShell (G := G) S x n at hu
        change v ∈ R.reachableDistanceShell (G := G) S x n at hv
        have huData :=
          (R.mem_reachableDistanceShell (G := G) S x n u).mp hu
        have hvData :=
          (R.mem_reachableDistanceShell (G := G) S x n v).mp hv
        have hdist : G.dist x u = G.dist x v :=
          huData.2.2.trans hvData.2.2.symm
        by_cases hux : R.IsDescendant (G := G) u x
        · by_cases hvx : R.IsDescendant (G := G) v x
          · have hcomp := R.isDescendant_comparable_of_common_descendant
              (G := G) C.isForest hux hvx
            rcases hcomp with huvDesc | hvuDesc
            · exact R.eq_of_isDescendant_of_isDescendant_of_dist_eq
                (G := G) huvDesc hvx hdist
            · exact (R.eq_of_isDescendant_of_isDescendant_of_dist_eq
                (G := G) hvuDesc hux hdist.symm).symm
          · have hbad : (none : Option V) = some (leaf v) := by
              simpa only [f, if_pos hu, if_pos hux,
                if_pos hv, if_neg hvx] using huv
            cases hbad
        · by_cases hvx : R.IsDescendant (G := G) v x
          · have hbad : some (leaf u) = (none : Option V) := by
              simpa only [f, if_pos hu, if_neg hux,
                if_pos hv, if_pos hvx] using huv
            cases hbad
          · have hleafEq : leaf u = leaf v := by
              apply Option.some_injective V
              simpa only [f, if_pos hu, if_neg hux,
                if_pos hv, if_neg hvx] using huv
            have huLeaf : R.IsDescendant (G := G) u (leaf u) :=
              hleaf_desc u huData.1
            have hvLeaf : R.IsDescendant (G := G) v (leaf v) :=
              hleaf_desc v hvData.1
            rw [hleafEq] at huLeaf
            have hcomp := R.isDescendant_comparable_of_common_descendant
              (G := G) C.isForest huLeaf hvLeaf
            rcases hcomp with huvDesc | hvuDesc
            · exact R.eq_of_isDescendant_of_not_isDescendant_of_dist_eq
                (G := G) C.isForest huData.2.1 huvDesc hux hdist
            · exact (R.eq_of_isDescendant_of_not_isDescendant_of_dist_eq
                (G := G) C.isForest hvData.2.1 hvuDesc hvx hdist.symm).symm
    _ = (R.rootedLeaves (G := G) S).card + 1 := by
      rw [Finset.card_insert_of_notMem (by simp),
        Finset.card_image_of_injective _ (Option.some_injective V)]

/-- D.60 in the convenient `2L` form used in the covariance sum. -/
theorem reachableDistanceShell_card_le_two_mul_rootedLeaves_card
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (hSne : S.Nonempty) (x : V) (n : ℕ) :
    (R.reachableDistanceShell (G := G) S x n).card ≤
      2 * (R.rootedLeaves (G := G) S).card := by
  have hbase := R.reachableDistanceShell_card_le_rootedLeaves_card_add_one
    (G := G) C hS x n
  obtain ⟨u, huS⟩ := hSne
  obtain ⟨ell, hell, _⟩ :=
    R.exists_rootedLeaf_descendant (G := G) C hS huS
  have hLpos : 0 < (R.rootedLeaves (G := G) S).card :=
    Finset.card_pos.mpr ⟨ell, hell⟩
  omega

/-- Finite geometric sums of `(27/28)^k` are at most `28`. -/
theorem sum_pow_twentySeven_div_twentyEight_le (K : Finset ℕ) :
    (∑ k ∈ K, ((27 : ℝ) / 28) ^ k) ≤ 28 := by
  have hnorm : ‖((27 : ℝ) / 28)‖ < 1 := by
    norm_num [Real.norm_eq_abs]
  have hsum : Summable (fun k : ℕ => ((27 : ℝ) / 28) ^ k) :=
    summable_geometric_of_norm_lt_one hnorm
  calc
    (∑ k ∈ K, ((27 : ℝ) / 28) ^ k) ≤
        ∑' k : ℕ, ((27 : ℝ) / 28) ^ k := by
      exact hsum.sum_le_tsum K (fun k hk => pow_nonneg (by norm_num) k)
    _ = (1 - ((27 : ℝ) / 28))⁻¹ := tsum_geometric_of_norm_lt_one hnorm
    _ = 28 := by norm_num

/-- Every predictable-variation coefficient is nonnegative. -/
theorem predictableQuadraticCoefficient_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    0 ≤ R.predictableQuadraticCoefficient (G := G) C u := by
  unfold predictableQuadraticCoefficient
  exact mul_nonneg
    (mul_nonneg (R.occupationProbability_nonneg (G := G) C u)
      (le_of_lt (R.vacancyProbability_pos (G := G) C u)))
    (sq_nonneg _)

/-- Roots of represented components which lie in the retained set. -/
noncomputable def retainedRoots (R : ComponentRooting G)
    (S : Finset V) : Finset V := by
  classical
  exact S.filter fun u => u = R.rootOf (G := G) u

@[simp] theorem mem_retainedRoots (R : ComponentRooting G)
    (S : Finset V) (u : V) :
    u ∈ R.retainedRoots (G := G) S ↔
      u ∈ S ∧ u = R.rootOf (G := G) u := by
  classical
  simp [retainedRoots]

/-- D.62 parent-regrouped weight. -/
noncomputable def parentRegroupedWeight
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (x : V) : ℝ :=
  ∑ u ∈ R.retainedChildren (G := G) S x,
    R.predictableQuadraticCoefficient (G := G) C u

theorem parentRegroupedWeight_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (x : V) :
    0 ≤ R.parentRegroupedWeight (G := G) C S x := by
  classical
  unfold parentRegroupedWeight
  exact Finset.sum_nonneg fun u hu =>
    R.predictableQuadraticCoefficient_nonneg (G := G) C u

/-- Retained-child fibers of distinct parents are disjoint. -/
theorem retainedChildren_pairwiseDisjoint
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    (↑S : Set V).PairwiseDisjoint
      (fun x => R.retainedChildren (G := G) S x) := by
  classical
  intro x hx y hy hxy
  change Disjoint (R.retainedChildren (G := G) S x)
    (R.retainedChildren (G := G) S y)
  rw [Finset.disjoint_left]
  intro u hux huy
  have hxu := (R.mem_retainedChildren (G := G) S x u).mp hux |>.1
  have hyu := (R.mem_retainedChildren (G := G) S y u).mp huy |>.1
  exact hxy (R.isChild_unique (G := G) C.isForest hxu hyu)

/-- Retained child fibers partition precisely the retained nonroots. -/
theorem biUnion_retainedChildren_eq_sdiff_retainedRoots
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S) :
    S.biUnion (fun x => R.retainedChildren (G := G) S x) =
      S \ R.retainedRoots (G := G) S := by
  classical
  ext u
  constructor
  · intro hu
    rcases Finset.mem_biUnion.mp hu with ⟨x, hxS, hxu⟩
    have hxu' := (R.mem_retainedChildren (G := G) S x u).mp hxu
    refine Finset.mem_sdiff.mpr ⟨hxu'.2, ?_⟩
    intro huRoot
    have hur : u = R.rootOf (G := G) u :=
      (R.mem_retainedRoots (G := G) S u).mp huRoot |>.2
    exact R.not_isChild_of_eq_root (G := G) hur hxu'.1
  · intro hu
    rcases Finset.mem_sdiff.mp hu with ⟨huS, huNotRoot⟩
    have hnr : u ≠ R.rootOf (G := G) u := by
      intro hur
      exact huNotRoot ((R.mem_retainedRoots (G := G) S u).mpr ⟨huS, hur⟩)
    let p := R.selectedParent (G := G) u hnr
    have hpu : R.IsChild (G := G) p u :=
      R.selectedParent_isChild (G := G) u hnr
    have hpS : p ∈ S :=
      ActualMartingaleProjection.AncestorClosed.parent_mem R hS huS hpu
    exact Finset.mem_biUnion.mpr ⟨p, hpS,
      (R.mem_retainedChildren (G := G) S p u).mpr ⟨hpu, huS⟩⟩

/-- Total parent-weight mass is the coefficient mass of retained nonroots. -/
theorem sum_parentRegroupedWeight_eq_sum_nonroots
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S) :
    (∑ x ∈ S, R.parentRegroupedWeight (G := G) C S x) =
      ∑ u ∈ S \ R.retainedRoots (G := G) S,
        R.predictableQuadraticCoefficient (G := G) C u := by
  classical
  unfold parentRegroupedWeight
  calc
    (∑ x ∈ S, ∑ u ∈ R.retainedChildren (G := G) S x,
        R.predictableQuadraticCoefficient (G := G) C u) =
        ∑ u ∈ S.biUnion (fun x => R.retainedChildren (G := G) S x),
          R.predictableQuadraticCoefficient (G := G) C u := by
      exact (Finset.sum_biUnion
        (R.retainedChildren_pairwiseDisjoint (G := G) C S)).symm
    _ = _ := by
      rw [R.biUnion_retainedChildren_eq_sdiff_retainedRoots (G := G) C hS]

/-- D.63 pointwise parent-weight bound with an arbitrary retained upper
bound `m` for vertex contributions. -/
theorem parentRegroupedWeight_le_twentyEight_mul_rootedLeaves_mul
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (m : ℝ)
    (hm : ∀ u ∈ S, R.vertexVarianceContribution (G := G) C u ≤ m)
    (hm0 : 0 ≤ m) (x : V) :
    R.parentRegroupedWeight (G := G) C S x ≤
      28 * ((R.rootedLeaves (G := G) S).card : ℝ) * m := by
  classical
  unfold parentRegroupedWeight
  calc
    (∑ u ∈ R.retainedChildren (G := G) S x,
        R.predictableQuadraticCoefficient (G := G) C u) ≤
        ∑ u ∈ R.retainedChildren (G := G) S x, 28 * m := by
      apply Finset.sum_le_sum
      intro u hu
      have huS := (R.mem_retainedChildren (G := G) S x u).mp hu |>.2
      calc
        R.predictableQuadraticCoefficient (G := G) C u ≤
            28 * R.vertexVarianceContribution (G := G) C u :=
          R.predictableQuadraticCoefficient_le_twentyEight_mul_contribution
            (G := G) C hz u
        _ ≤ 28 * m := mul_le_mul_of_nonneg_left (hm u huS) (by norm_num)
    _ = ((R.retainedChildren (G := G) S x).card : ℝ) * (28 * m) := by simp
    _ ≤ ((R.rootedLeaves (G := G) S).card : ℝ) * (28 * m) := by
      have hcard : ((R.retainedChildren (G := G) S x).card : ℝ) ≤
          ((R.rootedLeaves (G := G) S).card : ℝ) := by
        exact_mod_cast R.retainedChildren_card_le_rootedLeaves_card
          (G := G) C hS x
      exact mul_le_mul_of_nonneg_right hcard (mul_nonneg (by norm_num) hm0)
    _ = 28 * ((R.rootedLeaves (G := G) S).card : ℝ) * m := by ring

/-- D.63 total-mass bound `sum w_x ≤ 28 G_S`. -/
theorem sum_parentRegroupedWeight_le_twentyEight_mul_retainedContribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S) :
    (∑ x ∈ S, R.parentRegroupedWeight (G := G) C S x) ≤
      28 * ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
  classical
  rw [R.sum_parentRegroupedWeight_eq_sum_nonroots (G := G) C hS]
  calc
    (∑ u ∈ S \ R.retainedRoots (G := G) S,
        R.predictableQuadraticCoefficient (G := G) C u) ≤
        ∑ u ∈ S, R.predictableQuadraticCoefficient (G := G) C u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        (fun u huS huNot =>
          R.predictableQuadraticCoefficient_nonneg (G := G) C u)
    _ ≤ ∑ u ∈ S, 28 * R.vertexVarianceContribution (G := G) C u := by
      exact Finset.sum_le_sum fun u hu =>
        R.predictableQuadraticCoefficient_le_twentyEight_mul_contribution
          (G := G) C hz u
    _ = 28 * ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
      rw [Finset.mul_sum]

/-- D.62: predictable quadratic variation regrouped by retained parents,
with a deterministic retained-root term. -/
theorem predictableQuadraticVariation_eq_root_sum_add_parentRegrouped
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    R.predictableQuadraticVariation (G := G) C S I =
      (∑ r ∈ R.retainedRoots (G := G) S,
        R.predictableQuadraticCoefficient (G := G) C r) +
      ∑ x ∈ S, R.parentRegroupedWeight (G := G) C S x *
        (1 - ActualMartingaleProjection.occupationIndicator I x) := by
  classical
  let roots := R.retainedRoots (G := G) S
  let c : V → ℝ := fun u =>
    R.predictableQuadraticCoefficient (G := G) C u
  let f : V → ℝ := fun u => c u *
    (1 - ActualMartingaleProjection.parentOccupationIndicator R I u)
  have hroots : roots ⊆ S := by
    intro r hr
    exact (R.mem_retainedRoots (G := G) S r).mp hr |>.1
  have hdisj : (↑S : Set V).PairwiseDisjoint
      (fun x => R.retainedChildren (G := G) S x) :=
    R.retainedChildren_pairwiseDisjoint (G := G) C S
  have hunion : S.biUnion (fun x => R.retainedChildren (G := G) S x) =
      S \ roots := by
    exact R.biUnion_retainedChildren_eq_sdiff_retainedRoots (G := G) C hS
  unfold predictableQuadraticVariation
  change (∑ u ∈ S, f u) = _
  calc
    (∑ u ∈ S, f u) =
        (∑ r ∈ roots, f r) + ∑ u ∈ S \ roots, f u := by
      rw [add_comm]
      exact (Finset.sum_sdiff hroots).symm
    _ = (∑ r ∈ roots, c r) + ∑ u ∈ S \ roots, f u := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro r hr
        have hrr : r = R.rootOf (G := G) r :=
          (R.mem_retainedRoots (G := G) S r).mp hr |>.2
        unfold f
        rw [ActualMartingaleProjection.parentOccupationIndicator_root R I hrr]
        ring
      · rfl
    _ = (∑ r ∈ roots, c r) +
        ∑ x ∈ S, ∑ u ∈ R.retainedChildren (G := G) S x, f u := by
      apply congrArg (fun z => (∑ r ∈ roots, c r) + z)
      calc
        (∑ u ∈ S \ roots, f u) =
            ∑ u ∈ S.biUnion (fun x => R.retainedChildren (G := G) S x),
              f u := by rw [hunion]
        _ = ∑ x ∈ S, ∑ u ∈ R.retainedChildren (G := G) S x, f u :=
          Finset.sum_biUnion hdisj
    _ = (∑ r ∈ roots, c r) +
        ∑ x ∈ S, ∑ u ∈ R.retainedChildren (G := G) S x,
          c u * (1 - ActualMartingaleProjection.occupationIndicator I x) := by
      apply congrArg (fun z => (∑ r ∈ roots, c r) + z)
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro u hu
      have hxu : R.IsChild (G := G) x u :=
        (R.mem_retainedChildren (G := G) S x u).mp hu |>.1
      have hnr : u ≠ R.rootOf (G := G) u := by
        intro hur
        exact R.not_isChild_of_eq_root (G := G) hur hxu
      unfold f
      rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent
          C R I hnr,
        R.selectedParent_eq_of_isChild (G := G) C hxu hnr]
    _ = (∑ r ∈ R.retainedRoots (G := G) S,
          R.predictableQuadraticCoefficient (G := G) C r) +
        ∑ x ∈ S, R.parentRegroupedWeight (G := G) C S x *
          (1 - ActualMartingaleProjection.occupationIndicator I x) := by
      dsimp [roots, c]
      apply congrArg (fun z =>
        (∑ r ∈ R.retainedRoots (G := G) S,
          R.predictableQuadraticCoefficient (G := G) C r) + z)
      apply Finset.sum_congr rfl
      intro x hx
      unfold parentRegroupedWeight
      rw [Finset.sum_mul]

/-- Occupation covariances across distinct connected components vanish. -/
theorem occupationCovariance_eq_zero_of_not_reachable
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {x y : V} (hxy : ¬ G.Reachable x y) :
    occupationCovariance C x y = 0 := by
  let R' := R.rerootAt (G := G) y
  have hyroot : y = R'.rootOf (G := G) y :=
    (R.rerootAt_rootOf_eq_of_reachable (G := G)
      (SimpleGraph.Reachable.refl y)).symm
  have hout : ¬ R'.IsDescendant (G := G) y x := by
    intro hdesc
    exact hxy (R'.isDescendant_reachable (G := G) hdesc).symm
  unfold occupationCovariance
  have horth := R'.expectation_centeredOccupation_mul_eta_eq_zero_of_not_isDescendant
    (G := G) C hout
  have hmeanY : occupationMean C y = R'.occupationProbability (G := G) C y := by
    unfold occupationMean ActualMartingaleProjection.lawExpectation
    rw [ActualMartingaleProjection.expectation_occupationIndicator_eq_parentAbsent_mul_probability]
    have ha : R'.parentAbsentProbability (G := G) C y = 1 := by
      rw [hyroot]
      exact R'.parentAbsentProbability_rootOf (G := G) C y
    rw [ha]
    ring
  unfold ActualMartingaleProjection.eta at horth
  have hparent (I : IndepFinset G) :
      ActualMartingaleProjection.parentOccupationIndicator R' I y = 0 :=
    ActualMartingaleProjection.parentOccupationIndicator_root R' I hyroot
  simp_rw [hparent] at horth
  simpa [hmeanY] using horth

/-- Shell regrouping estimate with an arbitrary nonnegative weight bound. -/
theorem sum_weight_mul_geometricDistance_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    (hSne : S.Nonempty) (w : V → ℝ) (W : ℝ)
    (hw0 : ∀ y, 0 ≤ w y)
    (hw : ∀ y ∈ S, w y ≤ W) (hW0 : 0 ≤ W) (x : V) :
    (∑ y ∈ R.reachablePart (G := G) S x,
      w y * ((27 : ℝ) / 28) ^ G.dist x y) ≤
      (2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) * 28 := by
  classical
  let T := R.reachablePart (G := G) S x
  let K := T.image fun y => G.dist x y
  have hmaps : ∀ y ∈ T, G.dist x y ∈ K := by
    intro y hy
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  have hfiber (k : ℕ) :
      T.filter (fun y => G.dist x y = k) =
        R.reachableDistanceShell (G := G) S x k := by
    ext y
    simp only [Finset.mem_filter, T, R.mem_reachablePart,
      R.mem_reachableDistanceShell]
    tauto
  change (∑ y ∈ T, w y * ((27 : ℝ) / 28) ^ G.dist x y) ≤ _
  calc
    (∑ y ∈ T, w y * ((27 : ℝ) / 28) ^ G.dist x y) =
        ∑ k ∈ K, ∑ y ∈ T.filter (fun y => G.dist x y = k),
          w y * ((27 : ℝ) / 28) ^ G.dist x y := by
      exact (Finset.sum_fiberwise_of_maps_to hmaps
        (fun y => w y * ((27 : ℝ) / 28) ^ G.dist x y)).symm
    _ = ∑ k ∈ K, ∑ y ∈ R.reachableDistanceShell (G := G) S x k,
          w y * ((27 : ℝ) / 28) ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hfiber k]
      apply Finset.sum_congr rfl
      intro y hy
      have hyDist :=
        (R.mem_reachableDistanceShell (G := G) S x k y).mp hy |>.2.2
      rw [hyDist]
    _ ≤ ∑ k ∈ K,
          (2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) *
            ((27 : ℝ) / 28) ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      let shell := R.reachableDistanceShell (G := G) S x k
      have hcardNat : shell.card ≤ 2 * (R.rootedLeaves (G := G) S).card :=
        R.reachableDistanceShell_card_le_two_mul_rootedLeaves_card
          (G := G) C hS hSne x k
      have hcardReal : (shell.card : ℝ) ≤
          2 * ((R.rootedLeaves (G := G) S).card : ℝ) := by
        exact_mod_cast hcardNat
      calc
        (∑ y ∈ shell, w y * ((27 : ℝ) / 28) ^ k) ≤
            ∑ y ∈ shell, W * ((27 : ℝ) / 28) ^ k := by
          apply Finset.sum_le_sum
          intro y hy
          have hyS := (R.mem_reachableDistanceShell
            (G := G) S x k y).mp hy |>.1
          exact mul_le_mul_of_nonneg_right (hw y hyS)
            (pow_nonneg (by norm_num) k)
        _ = (shell.card : ℝ) * (W * ((27 : ℝ) / 28) ^ k) := by simp
        _ ≤ (2 * ((R.rootedLeaves (G := G) S).card : ℝ)) *
              (W * ((27 : ℝ) / 28) ^ k) :=
          mul_le_mul_of_nonneg_right hcardReal
            (mul_nonneg hW0 (pow_nonneg (by norm_num) k))
        _ = (2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) *
              ((27 : ℝ) / 28) ^ k := by ring
    _ = (2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) *
          ∑ k ∈ K, ((27 : ℝ) / 28) ^ k := by
      rw [Finset.mul_sum]
    _ ≤ (2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) * 28 := by
      exact mul_le_mul_of_nonneg_left
        (sum_pow_twentySeven_div_twentyEight_le K)
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) hW0)

/-- One weighted covariance row is bounded by the shell estimate. -/
theorem sum_weight_mul_abs_occupationCovariance_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (hSne : S.Nonempty) (w : V → ℝ) (W : ℝ)
    (hw0 : ∀ y, 0 ≤ w y)
    (hw : ∀ y ∈ S, w y ≤ W) (hW0 : 0 ≤ W) (x : V) :
    (∑ y ∈ S, w y * |occupationCovariance C x y|) ≤
      (1 / 4 : ℝ) *
        ((2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) * 28) := by
  classical
  calc
    (∑ y ∈ S, w y * |occupationCovariance C x y|) =
        ∑ y ∈ R.reachablePart (G := G) S x,
          w y * |occupationCovariance C x y| := by
      rw [reachablePart, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro y hyS
      by_cases hxy : G.Reachable x y
      · simp [hxy]
      · rw [if_neg hxy,
          R.occupationCovariance_eq_zero_of_not_reachable (G := G) C hxy]
        simp
    _ ≤ ∑ y ∈ R.reachablePart (G := G) S x,
          w y * ((1 / 4 : ℝ) * ((27 : ℝ) / 28) ^ G.dist x y) := by
      apply Finset.sum_le_sum
      intro y hy
      exact mul_le_mul_of_nonneg_left
        (R.abs_occupationCovariance_le_dist (G := G) C hz x y) (hw0 y)
    _ = (1 / 4 : ℝ) *
          ∑ y ∈ R.reachablePart (G := G) S x,
            w y * ((27 : ℝ) / 28) ^ G.dist x y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    _ ≤ (1 / 4 : ℝ) *
        ((2 * ((R.rootedLeaves (G := G) S).card : ℝ) * W) * 28) := by
      exact mul_le_mul_of_nonneg_left
        (R.sum_weight_mul_geometricDistance_le
          (G := G) C hS hSne w W hw0 hw hW0 x) (by norm_num)

/-- Expectation of a weighted vacancy-indicator sum. -/
theorem lawExpectation_sum_weight_mul_one_sub_occupationIndicator
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (w : V → ℝ) :
    ActualMartingaleProjection.lawExpectation C
      (fun I => ∑ x ∈ S, w x *
        (1 - ActualMartingaleProjection.occupationIndicator I x)) =
      ∑ x ∈ S, w x * (1 - occupationMean C x) := by
  classical
  unfold ActualMartingaleProjection.lawExpectation
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        (∑ x ∈ S, w x *
          (1 - ActualMartingaleProjection.occupationIndicator I x))) =
        ∑ I : IndepFinset G, ∑ x ∈ S,
          C.law.probability I *
            (w x * (1 - ActualMartingaleProjection.occupationIndicator I x)) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.mul_sum]
    _ = ∑ x ∈ S, ∑ I : IndepFinset G,
          C.law.probability I *
            (w x * (1 - ActualMartingaleProjection.occupationIndicator I x)) := by
      rw [Finset.sum_comm]
    _ = ∑ x ∈ S, w x *
          (∑ I : IndepFinset G, C.law.probability I *
            (1 - ActualMartingaleProjection.occupationIndicator I x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ = ∑ x ∈ S, w x * (1 - occupationMean C x) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      unfold occupationMean ActualMartingaleProjection.lawExpectation
      calc
        (∑ I : IndepFinset G, C.law.probability I *
            (1 - ActualMartingaleProjection.occupationIndicator I x)) =
            (∑ I : IndepFinset G, C.law.probability I) -
              ∑ I : IndepFinset G, C.law.probability I *
                ActualMartingaleProjection.occupationIndicator I x := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro I hI
          ring
        _ = 1 - ∑ I : IndepFinset G, C.law.probability I *
                ActualMartingaleProjection.occupationIndicator I x := by
          rw [C.law.probability_sum]

/-- Exact covariance expansion for a weighted vacancy-indicator sum. -/
theorem lawVariance_sum_weight_mul_one_sub_occupationIndicator_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (w : V → ℝ) :
    ActualMartingaleProjection.lawVariance C
      (fun I => ∑ x ∈ S, w x *
        (1 - ActualMartingaleProjection.occupationIndicator I x)) =
      ∑ x ∈ S, ∑ y ∈ S, w x * w y * occupationCovariance C x y := by
  classical
  have hmean := R.lawExpectation_sum_weight_mul_one_sub_occupationIndicator
    (G := G) C S w
  have hcenter (I : IndepFinset G) :
      (∑ x ∈ S, w x *
          (1 - ActualMartingaleProjection.occupationIndicator I x)) -
        (∑ x ∈ S, w x * (1 - occupationMean C x)) =
      - ∑ x ∈ S, w x *
          (ActualMartingaleProjection.occupationIndicator I x -
            occupationMean C x) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  unfold ActualMartingaleProjection.lawVariance
  rw [hmean]
  calc
    (ActualMartingaleProjection.lawExpectation C fun I =>
        ((∑ x ∈ S, w x *
          (1 - ActualMartingaleProjection.occupationIndicator I x)) -
          ∑ x ∈ S, w x * (1 - occupationMean C x)) ^ 2) =
        ActualMartingaleProjection.lawExpectation C (fun I =>
          (∑ x ∈ S, w x *
            (ActualMartingaleProjection.occupationIndicator I x -
              occupationMean C x)) ^ 2) := by
      unfold ActualMartingaleProjection.lawExpectation
      apply Finset.sum_congr rfl
      intro I hI
      dsimp only
      rw [hcenter I]
      ring
    _ = ∑ x ∈ S, ∑ y ∈ S, w x * w y * occupationCovariance C x y := by
      unfold ActualMartingaleProjection.lawExpectation occupationCovariance
      calc
        (∑ I : IndepFinset G, C.law.probability I *
            (∑ x ∈ S, w x *
              (ActualMartingaleProjection.occupationIndicator I x -
                occupationMean C x)) ^ 2) =
            ∑ I : IndepFinset G, ∑ x ∈ S, ∑ y ∈ S,
              C.law.probability I *
                ((w x * (ActualMartingaleProjection.occupationIndicator I x -
                    occupationMean C x)) *
                 (w y * (ActualMartingaleProjection.occupationIndicator I y -
                    occupationMean C y))) := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [pow_two, Finset.sum_mul_sum]
          simp_rw [Finset.mul_sum]
        _ = ∑ x ∈ S, ∑ y ∈ S, ∑ I : IndepFinset G,
              C.law.probability I *
                ((w x * (ActualMartingaleProjection.occupationIndicator I x -
                    occupationMean C x)) *
                 (w y * (ActualMartingaleProjection.occupationIndicator I y -
                    occupationMean C y))) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_comm]
        _ = ∑ x ∈ S, ∑ y ∈ S, w x * w y *
              (∑ I : IndepFinset G, C.law.probability I *
                ((ActualMartingaleProjection.occupationIndicator I x -
                    occupationMean C x) *
                 (ActualMartingaleProjection.occupationIndicator I y -
                    occupationMean C y))) := by
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro I hI
          ring
        _ = _ := rfl

/-- Variance is invariant under adding a deterministic constant. -/
theorem lawVariance_const_add
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (a : ℝ) (f : IndepFinset G → ℝ) :
    ActualMartingaleProjection.lawVariance C (fun I => a + f I) =
      ActualMartingaleProjection.lawVariance C f := by
  classical
  have hmean : ActualMartingaleProjection.lawExpectation C
      (fun I => a + f I) =
      a + ActualMartingaleProjection.lawExpectation C f := by
    unfold ActualMartingaleProjection.lawExpectation
    calc
      (∑ I : IndepFinset G, C.law.probability I * (a + f I)) =
          (∑ I : IndepFinset G, a * C.law.probability I) +
            ∑ I : IndepFinset G, C.law.probability I * f I := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro I hI
        ring
      _ = a * (∑ I : IndepFinset G, C.law.probability I) +
            ∑ I : IndepFinset G, C.law.probability I * f I := by
        rw [Finset.mul_sum]
      _ = a + ∑ I : IndepFinset G, C.law.probability I * f I := by
        rw [C.law.probability_sum]
        ring
  unfold ActualMartingaleProjection.lawVariance
  rw [hmean]
  unfold ActualMartingaleProjection.lawExpectation
  apply Finset.sum_congr rfl
  intro I hI
  ring

/-- Exact weighted-covariance expansion of the variance of the actual D.57
predictable quadratic variation. -/
theorem lawVariance_predictableQuadraticVariation_eq_weightedCovariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S) :
    ActualMartingaleProjection.lawVariance C
      (R.predictableQuadraticVariation (G := G) C S) =
      ∑ x ∈ S, ∑ y ∈ S,
        R.parentRegroupedWeight (G := G) C S x *
        R.parentRegroupedWeight (G := G) C S y *
        occupationCovariance C x y := by
  classical
  let A : ℝ := ∑ r ∈ R.retainedRoots (G := G) S,
    R.predictableQuadraticCoefficient (G := G) C r
  let w : V → ℝ := fun x => R.parentRegroupedWeight (G := G) C S x
  have hfun : R.predictableQuadraticVariation (G := G) C S =
      fun I => A + ∑ x ∈ S, w x *
        (1 - ActualMartingaleProjection.occupationIndicator I x) := by
    funext I
    exact R.predictableQuadraticVariation_eq_root_sum_add_parentRegrouped
      (G := G) C hS I
  rw [hfun, R.lawVariance_const_add (G := G) C A]
  exact R.lawVariance_sum_weight_mul_one_sub_occupationIndicator_eq
    (G := G) C S w

/-- D.64: variance bound for the actual D.57 predictable quadratic
variation, with constant exactly `10976`. -/
theorem lawVariance_predictableQuadraticVariation_le_retainedContribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (m : ℝ)
    (hm : ∀ u ∈ S, R.vertexVarianceContribution (G := G) C u ≤ m)
    (hm0 : 0 ≤ m) :
    ActualMartingaleProjection.lawVariance C
      (R.predictableQuadraticVariation (G := G) C S) ≤
      10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m *
        (∑ u ∈ S, R.vertexVarianceContribution (G := G) C u) := by
  classical
  by_cases hSne : S.Nonempty
  · let L : ℝ := ((R.rootedLeaves (G := G) S).card : ℝ)
    let GS : ℝ := ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u
    let w : V → ℝ := fun x => R.parentRegroupedWeight (G := G) C S x
    let W : ℝ := 28 * L * m
    let H : ℝ := (1 / 4 : ℝ) * ((2 * L * W) * 28)
    have hW0 : 0 ≤ W := by dsimp [W, L]; positivity
    have hH0 : 0 ≤ H := by dsimp [H]; positivity
    have hw0 : ∀ x, 0 ≤ w x := by
      intro x
      exact R.parentRegroupedWeight_nonneg (G := G) C S x
    have hw : ∀ x ∈ S, w x ≤ W := by
      intro x hx
      exact R.parentRegroupedWeight_le_twentyEight_mul_rootedLeaves_mul
        (G := G) C hz hS m hm hm0 x
    have hwsum : (∑ x ∈ S, w x) ≤ 28 * GS := by
      exact R.sum_parentRegroupedWeight_le_twentyEight_mul_retainedContribution
        (G := G) C hz hS
    have hrow : ∀ x, (∑ y ∈ S, w y * |occupationCovariance C x y|) ≤ H := by
      intro x
      exact R.sum_weight_mul_abs_occupationCovariance_le
        (G := G) C hz hS hSne w W hw0 hw hW0 x
    rw [R.lawVariance_predictableQuadraticVariation_eq_weightedCovariance
      (G := G) C hS]
    change (∑ x ∈ S, ∑ y ∈ S,
        w x * w y * occupationCovariance C x y) ≤
      10976 * L ^ 2 * m * GS
    calc
      (∑ x ∈ S, ∑ y ∈ S,
          w x * w y * occupationCovariance C x y) ≤
          ∑ x ∈ S, w x *
            (∑ y ∈ S, w y * |occupationCovariance C x y|) := by
        apply Finset.sum_le_sum
        intro x hx
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro y hy
        calc
          w x * w y * occupationCovariance C x y ≤
              (w x * w y) * |occupationCovariance C x y| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg (hw0 x) (hw0 y))
          _ = w x * (w y * |occupationCovariance C x y|) := by ring
      _ ≤ ∑ x ∈ S, w x * H := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_left (hrow x) (hw0 x)
      _ = (∑ x ∈ S, w x) * H := by rw [Finset.sum_mul]
      _ ≤ (28 * GS) * H := mul_le_mul_of_nonneg_right hwsum hH0
      _ = 10976 * L ^ 2 * m * GS := by
        dsimp [H, W]
        ring
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hSne
    subst S
    simp [ActualMartingaleProjection.lawVariance,
      ActualMartingaleProjection.lawExpectation, predictableQuadraticVariation,
      rootedLeaves]

/-- The retained contribution mass is at most the global variance. -/
theorem sum_retained_vertexVarianceContribution_le_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    (∑ u ∈ S, R.vertexVarianceContribution (G := G) C u) ≤ C.variance := by
  calc
    (∑ u ∈ S, R.vertexVarianceContribution (G := G) C u) ≤
        ∑ u : V, R.vertexVarianceContribution (G := G) C u := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun u huUniv huNot =>
          R.vertexVarianceContribution_nonneg (G := G) C u)
    _ = C.variance := R.sum_vertexVarianceContribution_eq_variance (G := G) C

/-- D.7 variance conclusion under the original global canonical law. -/
theorem lawVariance_predictableQuadraticVariation_le_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (m : ℝ)
    (hm : ∀ u ∈ S, R.vertexVarianceContribution (G := G) C u ≤ m)
    (hm0 : 0 ≤ m) :
    ActualMartingaleProjection.lawVariance C
      (R.predictableQuadraticVariation (G := G) C S) ≤
      10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m * C.variance := by
  have hD64 :=
    R.lawVariance_predictableQuadraticVariation_le_retainedContribution
      (G := G) C hz hS m hm hm0
  have hGS := R.sum_retained_vertexVarianceContribution_le_variance
    (G := G) C S
  exact hD64.trans (mul_le_mul_of_nonneg_left hGS
    (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hm0))

/-- Principal D.7 package: exact mean and the `10976` global-variance bound
for the genuine predictable quadratic variation. -/
theorem predictableQuadraticVariation_D7
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (m : ℝ)
    (hm : ∀ u ∈ S, R.vertexVarianceContribution (G := G) C u ≤ m)
    (hm0 : 0 ≤ m) :
    ActualMartingaleProjection.lawExpectation C
        (R.predictableQuadraticVariation (G := G) C S) =
      ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u ∧
    ActualMartingaleProjection.lawVariance C
        (R.predictableQuadraticVariation (G := G) C S) ≤
      10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m * C.variance := by
  exact ⟨R.lawExpectation_predictableQuadraticVariation_eq (G := G) C S,
    R.lawVariance_predictableQuadraticVariation_le_variance
      (G := G) C hz hS m hm hm0⟩

end ComponentRooting
end
end ActualRootedVariance
end Erdos993
