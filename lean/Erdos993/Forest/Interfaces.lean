import Erdos993.Forest.Specification

/-!
# Named interfaces for the eventual-unimodality closure

The structures in this file are assumptions, not proofs of the manuscript's
analytic theorems.  They state the exact finite inequalities consumed by the
vertical closure while keeping those inputs visibly parameterized.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

/-! ## Rooted numeric data used by the closure -/

/-- The numeric observables supplied by a componentwise rooting of a canonical
forest state.  A later exact rooted-law module is responsible for constructing
this data and proving the variance decomposition. -/
structure RootedForestObservables {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) where
  occupationProbability : V → ℝ
  parentAbsentProbability : V → ℝ
  conditionalMeanDifference : V → ℝ
  subtreeOrder : V → ℕ
  occupationProbability_nonneg : ∀ v, 0 ≤ occupationProbability v
  occupationProbability_le_one : ∀ v, occupationProbability v ≤ 1
  parentAbsentProbability_nonneg : ∀ v, 0 ≤ parentAbsentProbability v
  parentAbsentProbability_le_one : ∀ v, parentAbsentProbability v ≤ 1
  subtreeOrder_pos : ∀ v, 0 < subtreeOrder v
  subtreeOrder_le_order : ∀ v, subtreeOrder v ≤ C.order
  variance_decomposition :
    (∑ v, parentAbsentProbability v * occupationProbability v *
      (1 - occupationProbability v) * conditionalMeanDifference v ^ 2) = C.variance

namespace RootedForestObservables

variable {V : Type u} [Fintype V] {G : SimpleGraph V}
  {C : CanonicalFirstRecoveryState G}

/-- The vertex variance contribution `g(v)=a_v p_v q_v Delta_v^2`. -/
def contribution (R : RootedForestObservables C) (v : V) : ℝ :=
  R.parentAbsentProbability v * R.occupationProbability v *
    (1 - R.occupationProbability v) * R.conditionalMeanDifference v ^ 2

theorem contribution_nonneg (R : RootedForestObservables C) (v : V) :
    0 ≤ R.contribution v := by
  have hq : 0 ≤ 1 - R.occupationProbability v :=
    sub_nonneg.mpr (R.occupationProbability_le_one v)
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (R.parentAbsentProbability_nonneg v)
        (R.occupationProbability_nonneg v)) hq)
    (sq_nonneg _)

theorem sum_contribution (R : RootedForestObservables C) :
    ∑ v, R.contribution v = C.variance :=
  R.variance_decomposition

end RootedForestObservables

/-- An adapter from a later exact notion of componentwise rooting to the
numeric observables consumed here.  This keeps all analytic interfaces tied to
the same class of genuine rooted realizations without fixing that construction
prematurely in Phase 0. -/
structure RootedForestFamily where
  Realization :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V},
      CanonicalFirstRecoveryState G → Type u
  observables :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G),
      Realization C → RootedForestObservables C

/-! ## Pointwise forms of the named manuscript conclusions -/

/-- Proposition 2.1 at a specified activity ceiling `Z`. -/
def IndexVarianceSizeLocalized {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (Z : ℝ) : Prop :=
  Real.sqrt (C.order : ℝ) / 2 < (C.index : ℝ) ∧
    Real.sqrt (C.order : ℝ) / (8 * (1 + Z) ^ 4) ≤ C.variance

/-- Theorem 4.1 at constants `kappa` and `threshold`. -/
def HasMacroscopicVarianceContribution {V : Type u} [Fintype V]
    {G : SimpleGraph V} {C : CanonicalFirstRecoveryState G}
    (R : RootedForestObservables C) (kappa : ℝ) : Prop :=
  ∃ v, kappa * C.variance ≤ R.contribution v

/-- The occupation and displacement bounds in Theorem 4.2. -/
def OccupationBalancedAt {V : Type u} [Fintype V] {G : SimpleGraph V}
    {C : CanonicalFirstRecoveryState G} (R : RootedForestObservables C)
    (v : V) (c rho : ℝ) : Prop :=
  rho ≤ R.occupationProbability v ∧
    4 * c * C.variance ≤ R.conditionalMeanDifference v ^ 2 ∧
    R.conditionalMeanDifference v ^ 2 ≤ (784 / rho) * C.variance

/-- The global size and variance comparison in Theorem 4.3. -/
def FirstRecoveryScaleAt {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (cV CV cN CN : ℝ) : Prop :=
  cV * (C.index : ℝ) ^ 2 ≤ C.variance ∧
    C.variance ≤ CV * (C.index : ℝ) ^ 2 ∧
    cN * (C.index : ℝ) ≤ (C.order : ℝ) ∧
    (C.order : ℝ) ≤ CN * (C.index : ℝ)

/-- The finite epsilon-plus-constant conclusion of Lemma 5.1. -/
def SublinearConditionalMeanAt {V : Type u} [Fintype V]
    {G : SimpleGraph V} {C : CanonicalFirstRecoveryState G}
    (R : RootedForestObservables C) (v : V) (eta K : ℝ) : Prop :=
  |R.conditionalMeanDifference v| ≤ eta * (R.subtreeOrder v : ℝ) + K

/-! ## Uniform interfaces retained as explicit assumptions -/

/-- Propositions 2.1 and 2.2, in precisely the forms needed to localize a
canonical counterexample. -/
structure LocalizationInterface where
  activity_lt_27 :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V},
      (C : CanonicalFirstRecoveryState G) → C.activity < 27
  index_variance_size :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V},
      (C : CanonicalFirstRecoveryState G) → ∀ Z : ℝ,
        C.activity ≤ Z → IndexVarianceSizeLocalized C Z

/-- Theorem 4.1 / Theorem D.1.  Quantification over `R` expresses the
manuscript's "under every componentwise rooting" clause. -/
structure MacroscopicContributionInterface (F : RootedForestFamily.{u}) where
  kappa27 : ℝ
  varianceThreshold27 : ℝ
  kappa27_pos : 0 < kappa27
  varianceThreshold27_nonneg : 0 ≤ varianceThreshold27
  conclusion :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G) (r : F.Realization C),
      C.activity < 27 → varianceThreshold27 ≤ C.variance →
        HasMacroscopicVarianceContribution (F.observables C r) kappa27

/-- Theorem 4.2, including both displacement inequalities displayed in (4.2). -/
structure OccupationBalanceInterface (F : RootedForestFamily.{u}) where
  rho : ℝ → ℝ
  varianceThreshold : ℝ → ℝ
  rho_pos : ∀ {c}, 0 < c → 0 < rho c
  varianceThreshold_nonneg : ∀ {c}, 0 < c → 0 ≤ varianceThreshold c
  conclusion :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V) (c : ℝ),
      0 < c → C.activity < 27 → varianceThreshold c ≤ C.variance →
      c * C.variance ≤ (F.observables C r).contribution v →
      OccupationBalancedAt (F.observables C r) v c (rho c)

/-- Theorem 4.3 / Theorem C.7. -/
structure FirstRecoveryScaleInterface where
  cV : ℝ
  CV : ℝ
  cN : ℝ
  CN : ℝ
  varianceThreshold : ℝ
  cV_pos : 0 < cV
  CV_pos : 0 < CV
  cN_pos : 0 < cN
  CN_pos : 0 < CN
  varianceThreshold_nonneg : 0 ≤ varianceThreshold
  conclusion :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G),
      C.activity < 27 → varianceThreshold ≤ C.variance →
        FirstRecoveryScaleAt C cV CV cN CN

/-- Lemma 5.1 in the form consumed by the closure.  The bound is uniform in
the finite forest, its rooting, and the selected descendant subtree. -/
structure SublinearConditionalMeanInterface (F : RootedForestFamily.{u}) where
  conclusion :
    ∀ (Z rho eta : ℝ), 0 < Z → 0 < rho → 0 < eta →
      ∃ K : ℝ, 0 ≤ K ∧
        ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
          (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
          C.activity ≤ Z → rho ≤ (F.observables C r).occupationProbability v →
            SublinearConditionalMeanAt (F.observables C r) v eta K

/-- The complete list of unformalized named inputs expected by the Phase 1
vertical closure.  Possessing a value of this structure is an assumption. -/
structure VerticalClosureAssumptions where
  rootedFamily : RootedForestFamily.{u}
  localization : LocalizationInterface.{u}
  macroscopicContribution : MacroscopicContributionInterface rootedFamily
  occupationBalance : OccupationBalanceInterface rootedFamily
  firstRecoveryScale : FirstRecoveryScaleInterface.{u}
  sublinearConditionalMean : SublinearConditionalMeanInterface rootedFamily

end
end Forest
end Erdos993
