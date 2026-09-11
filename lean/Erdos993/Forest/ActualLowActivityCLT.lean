import Erdos993.Forest.UniformFourthMoment
import Erdos993.Forest.ActualMartingaleProjection
import Erdos993.Forest.LowActivityScalar
import Erdos993.Forest.LargeDisplacementContribution
import Erdos993.Forest.MartingaleArrayCLT
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos993.Forest

noncomputable section

namespace FiniteLatticeLaw

variable {α : Type*} [Fintype α]

/-- A finite lattice law, regarded as a probability mass function on its actual
finite state space. -/
noncomputable def toPMF (L : FiniteLatticeLaw α) : PMF α := by
  refine PMF.ofFintype (fun a => ENNReal.ofReal (L.probability a)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · rw [L.probability_sum]
    norm_num
  · intro a ha
    exact L.probability_nonneg a

@[simp] theorem toPMF_apply_toReal (L : FiniteLatticeLaw α) (a : α) :
    (L.toPMF a).toReal = L.probability a := by
  simp [toPMF, L.probability_nonneg a]

/-- The actual occupation-count PMF carried by a finite lattice law. -/
noncomputable def statPMF (L : FiniteLatticeLaw α) : PMF ℕ :=
  L.toPMF.map L.stat

/-- The actual probability measure on the finite state space. -/
noncomputable def toMeasure [MeasurableSpace α] (L : FiniteLatticeLaw α) : Measure α :=
  L.toPMF.toMeasure

instance [MeasurableSpace α] (L : FiniteLatticeLaw α) :
    IsProbabilityMeasure L.toMeasure := PMF.toMeasure.isProbabilityMeasure L.toPMF

/-- Integrals against the actual finite law are its defining weighted sums. -/
theorem integral_toMeasure_eq_sum [MeasurableSpace α] [MeasurableSingletonClass α]
    (L : FiniteLatticeLaw α) (f : α → ℝ) :
    ∫ a, f a ∂L.toMeasure = ∑ a, L.probability a * f a := by
  rw [toMeasure, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp [smul_eq_mul]

/-- The statistic under the actual state-space measure has precisely the
count-pushforward law `statPMF`. -/
theorem hasLaw_stat [MeasurableSpace α] [MeasurableSingletonClass α]
    (L : FiniteLatticeLaw α) :
    HasLaw L.stat L.statPMF.toMeasure L.toMeasure := by
  refine ⟨(measurable_of_finite L.stat).aemeasurable, ?_⟩
  rw [toMeasure, statPMF, PMF.toMeasure_map]
  exact measurable_of_finite L.stat

/-- Point masses of the statistic PMF are the native `rankMass` values. -/
@[simp] theorem statPMF_apply_toReal (L : FiniteLatticeLaw α) (k : ℕ) :
    (L.statPMF k).toReal = L.rankMass k := by
  rw [statPMF, PMF.map_apply, tsum_fintype]
  rw [ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal, L.toPMF_apply_toReal]
    rw [rankMass, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    simp [eq_comm]
  · intro a ha
    split_ifs <;> simp [PMF.apply_ne_top]

/-- Equality of all native lattice rank masses gives equality of the actual
statistic PMFs, even when the finite state spaces differ. -/
theorem statPMF_eq_of_rankMass_eq
    {β : Type*} [Fintype β] (L : FiniteLatticeLaw α)
    (K : FiniteLatticeLaw β) (h : ∀ k, L.rankMass k = K.rankMass k) :
    L.statPMF = K.statPMF := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [L.statPMF_apply_toReal, K.statPMF_apply_toReal, h]

end FiniteLatticeLaw

universe u

/-- The standardized occupation count associated with an actual hard-core law. -/
noncomputable def standardizedHardCoreCount
    {V : Type u} [Fintype V] (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (k : ℕ) : ℝ :=
  ((k : ℝ) - (hardCoreLaw G z hz).mean) /
    Real.sqrt (hardCoreLaw G z hz).variance

/-- The exact conclusion of Appendix B, Theorem B.2, expressed using the
occupation-count pushforward of the actual finite hard-core law. -/
def LowActivityCLTStatement
    (V : ℕ → Type u) [∀ n, Fintype (V n)]
    (G : (n : ℕ) → SimpleGraph (V n))
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z n) : Prop :=
  TendstoInDistribution
    (fun n => standardizedHardCoreCount (G n) (z n) (hz n))
    atTop (id : ℝ → ℝ)
    (fun n => (hardCoreLaw (G n) (z n) (hz n)).statPMF.toMeasure)
    (gaussianReal 0 1)

/-- Convergence in distribution is invariant under replacing every row by an
identically distributed random variable, even when the row sample spaces vary. -/
theorem TendstoInDistribution.congr_identDistrib
    {ι E Ω' : Type*} {Ω₁ Ω₂ : ι → Type*}
    {m₁ : ∀ i, MeasurableSpace (Ω₁ i)}
    {m₂ : ∀ i, MeasurableSpace (Ω₂ i)}
    {μ₁ : (i : ι) → Measure (Ω₁ i)}
    {μ₂ : (i : ι) → Measure (Ω₂ i)}
    [∀ i, IsProbabilityMeasure (μ₁ i)]
    [∀ i, IsProbabilityMeasure (μ₂ i)]
    {m' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] [TopologicalSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : (i : ι) → Ω₁ i → E} {Y : (i : ι) → Ω₂ i → E}
    {Z : Ω' → E} {l : Filter ι}
    (hX : TendstoInDistribution X l Z μ₁ μ')
    (hXY : ∀ i, IdentDistrib (X i) (Y i) (μ₁ i) (μ₂ i)) :
    TendstoInDistribution Y l Z μ₂ μ' := by
  refine TendstoInDistribution.mk
    (fun i => (hXY i).aemeasurable_snd) hX.aemeasurable_limit ?_
  exact Filter.Tendsto.congr'
    (Filter.Eventually.of_forall fun i => Subtype.ext (hXY i).map_eq)
    hX.tendsto

namespace ActualLowActivityCLT

open Erdos993.ActualRootedVariance
open Erdos993.ActualMartingaleProjection
open Erdos993.UniformFourthMoment

universe v
variable {V : Type v} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- B.25, in the arbitrary-activity rooted partition-function API. -/
theorem partitionRecursion_B25 (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (u : V) :
    rootedPAt R z u = rootedQAt R z u + rootedAAt R z u ∧
    rootedQAt R z u = ∏ c ∈ R.children (G := G) u, rootedPAt R z c ∧
    rootedAAt R z u = z * ∏ c ∈ R.children (G := G) u, rootedQAt R z c := by
  exact ⟨rootedPAt_eq_rootedQAt_add_rootedAAt R z u,
    rootedQAt_eq_prod_rootedPAt hG R z u,
    rootedAAt_eq_z_mul_prod_rootedQAt hG R z u⟩

/-- B.26, the exact occupation-odds recursion at arbitrary activity. -/
theorem occupationOddsRecursion_B26 (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u / rootedVacancyProbabilityAt R z u =
      z * ∏ c ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z c := by
  classical
  unfold rootedOccupationProbabilityAt rootedVacancyProbabilityAt
  rw [div_div_div_cancel_right₀]
  · rw [rootedAAt_eq_z_mul_prod_rootedQAt hG R z u,
      rootedQAt_eq_prod_rootedPAt hG R z u]
    rw [mul_div_assoc, Finset.prod_div_distrib]
  · unfold rootedPAt
    exact (independenceEval_pos _ hz).ne'

/-- The local odds are bounded by the common activity, as used in B.39. -/
theorem occupationOdds_le_activity_B26
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u / rootedVacancyProbabilityAt R z u ≤ z := by
  rw [occupationOddsRecursion_B26 hG R z hz u]
  apply mul_le_of_le_one_right hz.le
  apply Finset.prod_le_one
  · intro c hc
    unfold rootedVacancyProbabilityAt
    exact (div_pos (rootedQAt_pos R z hz c) (by
      rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
      exact add_pos (rootedQAt_pos R z hz c) (rootedAAt_pos R z hz c))).le
  · intro c hc
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz c,
      rootedOccupationProbabilityAt_pos R z hz c]

/-- B.28/B.45, the exact conditional-mean displacement recursion. -/
theorem displacementRecursion_B28 (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedDisplacementAt R z hz u =
      1 - ∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c * rootedDisplacementAt R z hz c :=
  rootedDisplacementAt_eq_one_sub_sum hG R z hz u

/-- Actual arbitrary-activity innovation from B.31, on the literal hard-core
configuration space. -/
def etaAt (R : ComponentRooting G) (z : ℝ) (I : IndepFinset G) (u : V) : ℝ :=
  occupationIndicator I u - rootedOccupationProbabilityAt R z u *
    (1 - parentOccupationIndicator R I u)

/-- Probability that the parent is absent, realized by the exact independent-seed
coupling of the actual hard-core law. -/
def parentAbsentProbabilityAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  ∑ ω, (hardCoreBernoulliSeedLaw R z hz).probability ω *
    generatedAvailabilityReal R ω u

/-- B.30: availability propagates exactly from a parent to each child. -/
theorem parentAbsentProbabilityAt_child_B30
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) {u c : V} (huc : R.IsChild (G := G) u c) :
    parentAbsentProbabilityAt R z hz c =
      1 - parentAbsentProbabilityAt R z hz u *
        rootedOccupationProbabilityAt R z u := by
  have hocc := generatedOccupation_expectation_eq_probability_mul_availability
    hG R z hz u
  unfold parentAbsentProbabilityAt
  rw [mul_comm (∑ ω, (hardCoreBernoulliSeedLaw R z hz).probability ω *
    generatedAvailabilityReal R ω u) (rootedOccupationProbabilityAt R z u)]
  rw [← hocc]
  rw [← (hardCoreBernoulliSeedLaw R z hz).probability_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ω hω
  unfold generatedAvailabilityReal
  rw [generatedAvailable_eq_not_occupation_of_isChild hG R huc]
  rw [(hardCoreBernoulliSeedLaw R z hz).probability_sum]
  cases generatedOccupation R ω u <;> norm_num

/-- The manuscript weight `w_u = a_u p_u q_u` at arbitrary activity. -/
def varianceWeightAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  parentAbsentProbabilityAt R z hz u * rootedOccupationProbabilityAt R z u *
    rootedVacancyProbabilityAt R z u

/-- The availability denominator in B.35 is strictly positive. -/
theorem parentAbsentProbabilityAt_pos
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    0 < parentAbsentProbabilityAt R z hz u := by
  have h := generatedAvailability_expectation_lower_bound hG R z z hz le_rfl u
  have hz1 : 0 < 1 + z := by linarith
  exact lt_of_lt_of_le (div_pos zero_lt_one hz1) h

/-- The weight/availability ratio estimate in B.35. -/
theorem varianceWeight_div_parentAbsent_le_B35
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    varianceWeightAt R z hz u / parentAbsentProbabilityAt R z hz u ≤
      rootedOccupationProbabilityAt R z u := by
  have ha := parentAbsentProbabilityAt_pos hG R z hz u
  have hq : rootedVacancyProbabilityAt R z u ≤ 1 := by
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
      rootedOccupationProbabilityAt_pos R z hz u]
  unfold varianceWeightAt
  calc
    parentAbsentProbabilityAt R z hz u * rootedOccupationProbabilityAt R z u *
        rootedVacancyProbabilityAt R z u / parentAbsentProbabilityAt R z hz u =
        rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u := by
          field_simp
    _ ≤ rootedOccupationProbabilityAt R z u :=
      mul_le_of_le_one_right (rootedOccupationProbabilityAt_pos R z hz u).le hq

/-- B.34 upward child-transfer operator. -/
def transferAt (R : ComponentRooting G) (z : ℝ) (x : V → ℝ) (u : V) : ℝ :=
  ∑ c ∈ R.children (G := G) u, rootedOccupationProbabilityAt R z c * x c

/-- B.36 at arbitrary activity, in the rooted partition-function API. -/
theorem weightedChildCauchyAt_B36
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) (x : V → ℝ) :
    (transferAt R z x u) ^ 2 ≤
      (∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c / rootedVacancyProbabilityAt R z c) *
      ∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c * x c ^ 2 := by
  unfold transferAt
  apply ComponentRooting.weightedCauchySchwarz
  · intro c hc
    exact (rootedOccupationProbabilityAt_pos R z hz c).le
  · intro c hc
    unfold rootedVacancyProbabilityAt
    exact div_pos (rootedQAt_pos R z hz c) (by
      rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
      exact add_pos (rootedQAt_pos R z hz c) (rootedAAt_pos R z hz c))

/-- B.36, the exact weighted child Cauchy--Schwarz estimate on the actual
rooted hard-core law. -/
theorem weightedChildCauchy_B36
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (u : V) (x : V → ℝ) :
    (∑ c ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C c * x c) ^ 2 ≤
      (∑ c ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C c /
          R.vacancyProbability (G := G) C c) *
      ∑ c ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C c *
          R.vacancyProbability (G := G) C c * x c ^ 2 :=
  R.weightedChildCauchy C u x

/-- The powered weighted moment underlying the manuscript's weighted norms. -/
def weightedMomentAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (r : ℕ) (x : V → ℝ) : ℝ :=
  ∑ u, varianceWeightAt R z hz u * |x u| ^ r

/-- B.33, the arbitrary-activity variance identity in the exact parent-first
seed realization of the actual hard-core law. -/
theorem occupationVarianceAt_B33 (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    (∑ u : V, varianceWeightAt R z hz u *
      rootedDisplacementAt R z hz u ^ 2) =
      (hardCoreLaw G z hz).variance := by
  rw [← availability_energy_sum_eq_hardCoreVariance hG R z hz]
  rw [show (∑ u : V, varianceWeightAt R z hz u *
      rootedDisplacementAt R z hz u ^ 2) =
      ∑ k : Fin (Fintype.card V),
        varianceWeightAt R z hz (parentFirstEquiv R k) *
          rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 2 by
    exact (Equiv.sum_comp (parentFirstEquiv R)
      (fun u => varianceWeightAt R z hz u *
        rootedDisplacementAt R z hz u ^ 2)).symm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [varianceWeightAt, parentAbsentProbabilityAt, rootedEnergyAt]
  ring

/-- B.33, the literal centered occupation-count representation on the actual
hard-core configuration space. -/
theorem centeredOccupationCountRepresentation_B33
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) :
    centeredOccupationCount C I =
      ∑ u : V, R.conditionalMeanDifference (G := G) C u * eta C R I u :=
  centeredOccupationCount_eq_sum_eta C R I

/-- B.32, the unconditional innovation variance is the manuscript weight. -/
theorem innovationSecondMoment_B32
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I * eta C R I u ^ 2) =
      R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u *
        R.vacancyProbability (G := G) C u :=
  expectation_eta_sq_eq C R u

/-- B.33, the exact rooted variance telescope for the actual hard-core law. -/
theorem occupationVarianceRepresentation_B33
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    (∑ u : V, R.parentAbsentProbability (G := G) C u *
      R.occupationProbability (G := G) C u *
      R.vacancyProbability (G := G) C u *
      R.conditionalMeanDifference (G := G) C u ^ 2) = C.variance := by
  simpa [ComponentRooting.vertexVarianceContribution] using
    R.sum_vertexVarianceContribution_eq_variance (G := G) C

/-- The B.38 local aggregate of logarithmic child odds. -/
noncomputable def childLogOddsSumAt (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  ∑ c ∈ R.children (G := G) u,
    Real.log (1 + rootedOccupationProbabilityAt R z c /
      rootedVacancyProbabilityAt R z c)

lemma rootedVacancyProbabilityAt_pos_local
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedVacancyProbabilityAt R z u := by
  unfold rootedVacancyProbabilityAt
  exact div_pos (rootedQAt_pos R z hz u) (by
    rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
    exact add_pos (rootedQAt_pos R z hz u) (rootedAAt_pos R z hz u))

lemma one_add_occupationOdds_eq_inv_vacancyAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    1 + rootedOccupationProbabilityAt R z u /
      rootedVacancyProbabilityAt R z u =
      (rootedVacancyProbabilityAt R z u)⁻¹ := by
  have hq := rootedVacancyProbabilityAt_pos_local R z hz u
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  field_simp
  linarith

lemma exp_childLogOddsSumAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    Real.exp (childLogOddsSumAt R z u) =
      (∏ c ∈ R.children (G := G) u,
        rootedVacancyProbabilityAt R z c)⁻¹ := by
  rw [childLogOddsSumAt, Real.exp_sum, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro c hc
  rw [Real.exp_log]
  · exact one_add_occupationOdds_eq_inv_vacancyAt R z hz c
  · have hp := rootedOccupationProbabilityAt_pos R z hz c
    have hq := rootedVacancyProbabilityAt_pos_local R z hz c
    positivity

/-- B.38: exact occupation probability in terms of the child log-odds sum. -/
theorem occupationProbability_eq_activity_div_add_exp_B38
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u =
      z / (z + Real.exp (childLogOddsSumAt R z u)) := by
  have hp := rootedOccupationProbabilityAt_pos R z hz u
  have hq := rootedVacancyProbabilityAt_pos_local R z hz u
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hprod : 0 < ∏ c ∈ R.children (G := G) u,
      rootedVacancyProbabilityAt R z c := by
    apply Finset.prod_pos
    intro c hc
    exact rootedVacancyProbabilityAt_pos_local R z hz c
  have hrec := occupationOddsRecursion_B26 hG R z hz u
  have hexp := exp_childLogOddsSumAt R z hz u
  rw [hexp]
  field_simp
  field_simp at hrec
  nlinarith

/-- Concavity comparison for odds bounded by the common activity. -/
theorem odds_le_scaled_log (r z : ℝ) (hz : 0 < z) (hr : 0 ≤ r) (hrz : r ≤ z) :
    r ≤ (z / Real.log (1 + z)) * Real.log (1 + r) := by
  have ht0 : 0 ≤ r / z := div_nonneg hr hz.le
  have ht1 : r / z ≤ 1 := (div_le_one₀ hz).2 hrz
  have harg : r / z * (1 + z) + (1 - r / z) = 1 + r := by
    field_simp
    ring
  have hc := strictConcaveOn_log_Ioi.concaveOn.2
    (show 1 + z ∈ Set.Ioi (0 : ℝ) by change 0 < 1 + z; linarith)
    (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    ht0 (sub_nonneg.2 ht1) (by ring : r / z + (1 - r / z) = 1)
  have hlog : (r / z) * Real.log (1 + z) ≤ Real.log (1 + r) := by
    simpa [smul_eq_mul, harg] using hc
  have hzlog : 0 < z / Real.log (1 + z) :=
    div_pos hz (Real.log_pos (by linarith))
  have h := mul_le_mul_of_nonneg_left hlog hzlog.le
  calc
    r = (z / Real.log (1 + z)) * ((r / z) * Real.log (1 + z)) := by
      field_simp [Real.log_pos (by linarith : 1 < 1 + z) |>.ne']
    _ ≤ (z / Real.log (1 + z)) * Real.log (1 + r) := h

/-- Child odds are controlled by the local B.38 log aggregate. -/
theorem sum_childOdds_le_scaled_childLogOddsSumAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    (∑ c ∈ R.children (G := G) u,
      rootedOccupationProbabilityAt R z c / rootedVacancyProbabilityAt R z c) ≤
      (z / Real.log (1 + z)) * childLogOddsSumAt R z u := by
  rw [childLogOddsSumAt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  apply odds_le_scaled_log _ z hz
  · exact (div_pos (rootedOccupationProbabilityAt_pos R z hz c)
      (rootedVacancyProbabilityAt_pos_local R z hz c)).le
  · exact occupationOdds_le_activity_B26 hG R z hz c

lemma childLogOddsSumAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 ≤ childLogOddsSumAt R z u := by
  unfold childLogOddsSumAt
  apply Finset.sum_nonneg
  intro c hc
  apply Real.log_nonneg
  have := div_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
    (rootedVacancyProbabilityAt_pos_local R z hz c).le
  linarith

/-- B.39 local coefficient bound. -/
theorem quadraticCoefficientAt_le_B39
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (u : V) :
    rootedOccupationProbabilityAt R z u *
      (∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c / rootedVacancyProbabilityAt R z c) ≤
      (15 / 16 : ℝ) := by
  have hp := rootedOccupationProbabilityAt_pos R z hz u
  have hsum := sum_childOdds_le_scaled_childLogOddsSumAt hG R z hz u
  calc
    rootedOccupationProbabilityAt R z u *
        (∑ c ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z c / rootedVacancyProbabilityAt R z c) ≤
        rootedOccupationProbabilityAt R z u *
          ((z / Real.log (1 + z)) * childLogOddsSumAt R z u) :=
      mul_le_mul_of_nonneg_left hsum hp.le
    _ = (z / (z + Real.exp (childLogOddsSumAt R z u))) *
          ((z / Real.log (1 + z)) * childLogOddsSumAt R z u) := by
      rw [occupationProbability_eq_activity_div_add_exp_B38 hG R z hz u]
    _ ≤ (15 / 16 : ℝ) := lowActivity_quadratic_scalar z _ hz hz15
      (childLogOddsSumAt_nonneg R z hz u)

theorem parentAbsentProbabilityAt_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    parentAbsentProbabilityAt R z hz u ≤ 1 := by
  classical
  unfold parentAbsentProbabilityAt
  calc
    (∑ ω, (hardCoreBernoulliSeedLaw R z hz).probability ω *
      generatedAvailabilityReal R ω u) ≤
        ∑ ω, (hardCoreBernoulliSeedLaw R z hz).probability ω := by
      apply Finset.sum_le_sum
      intro ω hω
      have hp := (hardCoreBernoulliSeedLaw R z hz).probability_nonneg ω
      apply mul_le_of_le_one_right hp
      unfold generatedAvailabilityReal
      cases generatedAvailable R ω u <;> norm_num
    _ = 1 := (hardCoreBernoulliSeedLaw R z hz).probability_sum

lemma varianceWeightAt_nonneg
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 ≤ varianceWeightAt R z hz u := by
  unfold varianceWeightAt
  exact mul_nonneg (mul_nonneg (parentAbsentProbabilityAt_pos hG R z hz u).le
    (rootedOccupationProbabilityAt_pos R z hz u).le)
    (rootedVacancyProbabilityAt_pos_local R z hz u).le

/-- B.35 in the child-availability form needed for B.37. -/
theorem varianceWeightAt_le_occupation_mul_childAvailability_B35
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    varianceWeightAt R z hz u ≤ rootedOccupationProbabilityAt R z u *
      (1 - parentAbsentProbabilityAt R z hz u *
        rootedOccupationProbabilityAt R z u) := by
  have ha := parentAbsentProbabilityAt_le_one R z hz u
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hp := rootedOccupationProbabilityAt_pos R z hz u
  unfold varianceWeightAt
  nlinarith [mul_nonneg hp.le (sub_nonneg.2 ha)]

/-- B.37--B.39, the complete estimate at one parent. -/
theorem weightedTransferAt_parent_le_B39
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (u : V) (x : V → ℝ) :
    varianceWeightAt R z hz u * (transferAt R z x u) ^ 2 ≤
      (15 / 16 : ℝ) * ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * x c ^ 2 := by
  let L := ∑ c ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z c / rootedVacancyProbabilityAt R z c
  let S := ∑ c ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c * x c ^ 2
  let A := 1 - parentAbsentProbabilityAt R z hz u *
    rootedOccupationProbabilityAt R z u
  have hL : 0 ≤ L := by
    dsimp [L]
    apply Finset.sum_nonneg
    intro c hc
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le
  have hS : 0 ≤ S := by
    dsimp [S]
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (mul_nonneg
      (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le) (sq_nonneg (x c))
  have hA : 0 ≤ A := by
    dsimp [A]
    have ha := parentAbsentProbabilityAt_le_one R z hz u
    have hp := rootedOccupationProbabilityAt_le_one R z hz u
    have ha0 := (parentAbsentProbabilityAt_pos hG R z hz u).le
    have hp0 := (rootedOccupationProbabilityAt_pos R z hz u).le
    have hmul := mul_le_mul ha hp hp0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hcauchy : (transferAt R z x u) ^ 2 ≤ L * S := by
    exact weightedChildCauchyAt_B36 R z hz u x
  have hw : varianceWeightAt R z hz u ≤
      rootedOccupationProbabilityAt R z u * A := by
    exact varianceWeightAt_le_occupation_mul_childAvailability_B35 R z hz u
  have hcoeff : rootedOccupationProbabilityAt R z u * L ≤ (15 / 16 : ℝ) := by
    exact quadraticCoefficientAt_le_B39 hG R z hz hz15 u
  have hchildren : A * S = ∑ c ∈ R.children (G := G) u,
      varianceWeightAt R z hz c * x c ^ 2 := by
    dsimp [A, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have huc : R.IsChild (G := G) u c := by
      simpa [ComponentRooting.children] using hc
    unfold varianceWeightAt
    rw [parentAbsentProbabilityAt_child_B30 hG R z hz huc]
    ring
  calc
    varianceWeightAt R z hz u * (transferAt R z x u) ^ 2 ≤
        varianceWeightAt R z hz u * (L * S) :=
      mul_le_mul_of_nonneg_left hcauchy (varianceWeightAt_nonneg hG R z hz u)
    _ ≤ (rootedOccupationProbabilityAt R z u * A) * (L * S) :=
      mul_le_mul_of_nonneg_right hw (mul_nonneg hL hS)
    _ = (rootedOccupationProbabilityAt R z u * L) * (A * S) := by ring
    _ ≤ (15 / 16 : ℝ) * (A * S) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hA hS)
    _ = (15 / 16 : ℝ) * ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * x c ^ 2 := by rw [hchildren]

/-- Exact root/nonroot accounting: each nonroot occurs in exactly one child set,
while component roots occur in none. -/
theorem sum_sum_children_eq_sum_nonroots
    (hG : G.IsAcyclic) (R : ComponentRooting G) (f : V → ℝ) :
    (∑ u : V, ∑ c ∈ R.children (G := G) u, f c) =
      ∑ c ∈ Finset.univ.filter (fun c => c ≠ R.rootOf (G := G) c), f c := by
  classical
  calc
    (∑ u : V, ∑ c ∈ R.children (G := G) u, f c) =
        ∑ c : V, ∑ u ∈ Finset.univ.filter (fun u => R.IsChild (G := G) u c), f c := by
      simp only [ComponentRooting.children, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ c : V, if c ≠ R.rootOf (G := G) c then f c else 0 := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hcr : c = R.rootOf (G := G) c
      · have hnone (u : V) : ¬ R.IsChild (G := G) u c := by
          intro huc
          exact R.not_isChild_of_eq_root (G := G) hcr huc
        have hP : Finset.univ.filter (fun u => R.IsChild (G := G) u c) = ∅ := by
          ext u
          simp [hnone u]
        rw [hP]
        simp only [Finset.sum_empty]
        rw [if_neg]
        exact not_not_intro hcr
      · let p := R.selectedParent (G := G) c hcr
        have hpc : R.IsChild (G := G) p c :=
          R.selectedParent_isChild (G := G) c hcr
        have hiff (u : V) : R.IsChild (G := G) u c ↔ u = p := by
          constructor
          · intro huc
            exact R.isChild_unique (G := G) hG huc hpc
          · intro hup
            simpa [hup] using hpc
        have hP : Finset.univ.filter (fun u => R.IsChild (G := G) u c) = {p} := by
          ext u
          simp [hiff u]
        rw [hP]
        simp only [Finset.sum_singleton, if_pos hcr]
    _ = ∑ c ∈ Finset.univ.filter (fun c => c ≠ R.rootOf (G := G) c), f c := by
      simp only [Finset.sum_filter]

/-- Dropping the nonnegative root terms from the exact child accounting. -/
theorem sum_sum_children_le_sum
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ u : V, ∑ c ∈ R.children (G := G) u, f c) ≤ ∑ c : V, f c := by
  rw [sum_sum_children_eq_sum_nonroots hG R f]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro c hc hcn
  exact hf c

/-- B.40: actual rooted weighted L2 contraction with the exact constant. -/
theorem weightedMomentAt_transfer_two_le_B40
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (x : V → ℝ) :
    weightedMomentAt R z hz 2 (transferAt R z x) ≤
      (15 / 16 : ℝ) * weightedMomentAt R z hz 2 x := by
  have hchild :
      (∑ u : V, ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * x c ^ 2) ≤
        ∑ c : V, varianceWeightAt R z hz c * x c ^ 2 := by
    apply sum_sum_children_le_sum hG R
    intro c
    exact mul_nonneg (varianceWeightAt_nonneg hG R z hz c) (sq_nonneg (x c))
  unfold weightedMomentAt
  calc
    (∑ u : V, varianceWeightAt R z hz u * |transferAt R z x u| ^ 2) =
        ∑ u : V, varianceWeightAt R z hz u * (transferAt R z x u) ^ 2 := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [sq_abs]
    _ ≤ ∑ u : V, (15 / 16 : ℝ) * ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * x c ^ 2 := by
      apply Finset.sum_le_sum
      intro u hu
      exact weightedTransferAt_parent_le_B39 hG R z hz hz15 u x
    _ = (15 / 16 : ℝ) * (∑ u : V, ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * x c ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (15 / 16 : ℝ) * ∑ c : V, varianceWeightAt R z hz c * x c ^ 2 :=
      mul_le_mul_of_nonneg_left hchild (by norm_num)
    _ = (15 / 16 : ℝ) *
        ∑ c : V, varianceWeightAt R z hz c * |x c| ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro c hc
      rw [sq_abs]

/-- Finite weighted Hölder in the exact cubic form B.41. -/
theorem finiteHolder_three
    {ι : Type*} (s : Finset ι) (p q x : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    (∑ i ∈ s, p i * |x i|)^3 ≤
      (∑ i ∈ s, p i * q i * |x i|^3) *
        (∑ i ∈ s, p i / Real.sqrt (q i))^2 := by
  let w : ι → ℝ := fun i => p i / Real.sqrt (q i)
  let f : ι → ℝ := fun i => Real.sqrt (q i) * |x i|
  have hw (i : ι) : 0 ≤ w i := div_nonneg (hp i) (Real.sqrt_nonneg _)
  have hf (i : ι) : 0 ≤ f i := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have H := Real.inner_le_weight_mul_Lp_of_nonneg s (p := (3:ℝ)) (by norm_num) w f hw hf
  norm_num at H
  have hleft : (∑ i ∈ s, w i * f i) = ∑ i ∈ s, p i * |x i| := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w, f]
    have hs : Real.sqrt (q i) ≠ 0 := (Real.sqrt_pos.2 (hq i)).ne'
    field_simp
  have hmoment : (∑ i ∈ s, w i * (f i)^(3:ℕ)) =
      ∑ i ∈ s, p i * q i * |x i|^3 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w, f]
    have hs : Real.sqrt (q i) ≠ 0 := (Real.sqrt_pos.2 (hq i)).ne'
    have hs2 := Real.sq_sqrt (hq i).le
    field_simp
    rw [hs2]
    ring
  rw [hleft, hmoment] at H
  let W := ∑ i ∈ s, p i / Real.sqrt (q i)
  let M := ∑ i ∈ s, p i * q i * |x i| ^ 3
  have hW : 0 ≤ W := by
    dsimp [W]
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (hp i) (Real.sqrt_nonneg _)
  have hM : 0 ≤ M := by
    dsimp [M]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (hp i) (hq i).le) (pow_nonneg (abs_nonneg _) _)
  have hS : 0 ≤ ∑ i ∈ s, p i * |x i| :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hp i) (abs_nonneg _)
  change (∑ i ∈ s, p i * |x i|) ≤ W^(2/3 : ℝ) * M^(1/3 : ℝ) at H
  have hcube := pow_le_pow_left₀ hS H 3
  have hWpow : (W ^ (2/3 : ℝ))^3 = W^2 := by
    rw [← Real.rpow_mul_natCast hW]
    norm_num [Real.rpow_natCast]
  have hMpow : (M ^ (1/3 : ℝ))^3 = M := by
    convert Real.rpow_inv_natCast_pow hM (by norm_num : (3:ℕ) ≠ 0) using 1 <;> norm_num
  change (∑ i ∈ s, p i * |x i|)^3 ≤ M * W^2
  calc
    (∑ i ∈ s, p i * |x i|)^3 ≤ (W^(2/3 : ℝ) * M^(1/3 : ℝ))^3 := hcube
    _ = M * W^2 := by rw [mul_pow, hWpow, hMpow]; ring

/-- B.41 specialized to the actual rooted transfer. -/
theorem weightedChildHolderAt_B41
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) (x : V → ℝ) :
    |transferAt R z x u| ^ 3 ≤
      (∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c * |x c|^3) *
      (∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c /
          Real.sqrt (rootedVacancyProbabilityAt R z c))^2 := by
  let s := R.children (G := G) u
  let p : V → ℝ := fun c => rootedOccupationProbabilityAt R z c
  let q : V → ℝ := fun c => rootedVacancyProbabilityAt R z c
  have hp (c : V) : 0 ≤ p c := (rootedOccupationProbabilityAt_pos R z hz c).le
  have hq (c : V) : 0 < q c := rootedVacancyProbabilityAt_pos_local R z hz c
  have habs : |transferAt R z x u| ≤ ∑ c ∈ s, p c * |x c| := by
    unfold transferAt
    calc
      |∑ c ∈ s, p c * x c| ≤ ∑ c ∈ s, |p c * x c| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c ∈ s, p c * |x c| := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [abs_mul, abs_of_nonneg (hp c)]
  have hcub := pow_le_pow_left₀ (abs_nonneg _) habs 3
  calc
    |transferAt R z x u|^3 ≤ (∑ c ∈ s, p c * |x c|)^3 := hcub
    _ ≤ (∑ c ∈ s, p c * q c * |x c|^3) *
        (∑ c ∈ s, p c / Real.sqrt (q c))^2 := finiteHolder_three s p q x hp hq
    _ = _ := by rfl

lemma prob_div_sqrt_eq_ratio_div_sqrt_one_add
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hpq : p + q = 1)
    (hr : r = p / q) :
    p / Real.sqrt q = r / Real.sqrt (1 + r) := by
  have h1r : 0 < 1 + r := by rw [hr]; positivity
  have hsQ : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsR : 0 < Real.sqrt (1 + r) := Real.sqrt_pos.2 h1r
  have hsQ2 : (Real.sqrt q)^2 = q := Real.sq_sqrt hq.le
  have hsR2 : (Real.sqrt (1+r))^2 = 1+r := Real.sq_sqrt h1r.le
  have hcross : p * Real.sqrt (1+r) = r * Real.sqrt q := by
    have hsq : (p * Real.sqrt (1+r))^2 = (r * Real.sqrt q)^2 := by
      rw [mul_pow, mul_pow, hsQ2, hsR2, hr]
      field_simp
      nlinarith
    have hl : 0 ≤ p * Real.sqrt (1+r) := mul_nonneg hp hsR.le
    have hr0 : 0 ≤ r * Real.sqrt q := by rw [hr]; positivity
    nlinarith
  field_simp
  nlinarith

/-- The one-child square-root/log-odds comparison used in B.43. -/
theorem childOccupation_div_sqrtVacancy_le_log
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (c : V) :
    rootedOccupationProbabilityAt R z c /
        Real.sqrt (rootedVacancyProbabilityAt R z c) ≤
      (9 / 8 : ℝ) * Real.log (1 +
        rootedOccupationProbabilityAt R z c /
          rootedVacancyProbabilityAt R z c) := by
  let p := rootedOccupationProbabilityAt R z c
  let q := rootedVacancyProbabilityAt R z c
  let r := p / q
  have hp : 0 ≤ p := (rootedOccupationProbabilityAt_pos R z hz c).le
  have hq : 0 < q := rootedVacancyProbabilityAt_pos_local R z hz c
  have hpq : p + q = 1 := rootedOccupationProbabilityAt_add_vacancy R z hz c
  have hr0 : 0 ≤ r := div_nonneg hp hq.le
  have hrz : r ≤ z := occupationOdds_le_activity_B26 hG R z hz c
  have hr15 : r ≤ 3 / 2 := hrz.trans hz15
  have hid : p / Real.sqrt q = r / Real.sqrt (1+r) :=
    prob_div_sqrt_eq_ratio_div_sqrt_one_add p q r hp hq hpq rfl
  rw [show rootedOccupationProbabilityAt R z c = p from rfl,
      show rootedVacancyProbabilityAt R z c = q from rfl, hid]
  exact odds_div_sqrt_le_nine_eighths_log r hr0 hr15

/-- Summed child log-odds comparison entering scalar B.43. -/
theorem sum_childOccupation_div_sqrtVacancy_le_B43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (u : V) :
    (∑ c ∈ R.children (G := G) u,
      rootedOccupationProbabilityAt R z c /
        Real.sqrt (rootedVacancyProbabilityAt R z c)) ≤
      (9 / 8 : ℝ) * childLogOddsSumAt R z u := by
  rw [childLogOddsSumAt, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  exact childOccupation_div_sqrtVacancy_le_log hG R z hz hz15 c

/-- B.43: actual local cubic coefficient bound. -/
theorem cubicCoefficientAt_le_B43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (u : V) :
    rootedOccupationProbabilityAt R z u *
      (∑ c ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z c /
          Real.sqrt (rootedVacancyProbabilityAt R z c))^2 ≤
      (15 / 16 : ℝ) := by
  let P := ∑ c ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z c /
      Real.sqrt (rootedVacancyProbabilityAt R z c)
  let Y := childLogOddsSumAt R z u
  have hp := rootedOccupationProbabilityAt_pos R z hz u
  have hP : 0 ≤ P := by
    dsimp [P]
    apply Finset.sum_nonneg
    intro c hc
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
      (Real.sqrt_nonneg _)
  have hY : 0 ≤ Y := childLogOddsSumAt_nonneg R z hz u
  have hPY : P ≤ (9/8 : ℝ) * Y :=
    sum_childOccupation_div_sqrtVacancy_le_B43 hG R z hz hz15 u
  have hsq : P^2 ≤ ((9/8 : ℝ) * Y)^2 := by nlinarith
  calc
    rootedOccupationProbabilityAt R z u * P^2 ≤
        rootedOccupationProbabilityAt R z u * ((9/8 : ℝ) * Y)^2 :=
      mul_le_mul_of_nonneg_left hsq hp.le
    _ = (z / (z + Real.exp Y)) * ((9/8 : ℝ) * Y)^2 := by
      rw [occupationProbability_eq_activity_div_add_exp_B38 hG R z hz u]
    _ ≤ (15/16 : ℝ) := lowActivity_cubic_scalar z Y hz hz15 hY

/-- B.42: one-parent variance-weight/availability bridge after finite Hölder. -/
theorem weightedTransferAt_parent_bridge_B42
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) (x : V → ℝ) :
    varianceWeightAt R z hz u * |transferAt R z x u|^3 ≤
      (rootedOccupationProbabilityAt R z u *
        (∑ c ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z c /
            Real.sqrt (rootedVacancyProbabilityAt R z c))^2) *
      (∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * |x c|^3) := by
  let P := ∑ c ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z c /
      Real.sqrt (rootedVacancyProbabilityAt R z c)
  let C := ∑ c ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c * |x c|^3
  let A := 1 - parentAbsentProbabilityAt R z hz u *
    rootedOccupationProbabilityAt R z u
  have hP : 0 ≤ P := by
    dsimp [P]
    apply Finset.sum_nonneg
    intro c hc
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
      (Real.sqrt_nonneg _)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (mul_nonneg
      (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le)
      (pow_nonneg (abs_nonneg _) _)
  have hA : 0 ≤ A := by
    dsimp [A]
    have ha := parentAbsentProbabilityAt_le_one R z hz u
    have hp := rootedOccupationProbabilityAt_le_one R z hz u
    have ha0 := (parentAbsentProbabilityAt_pos hG R z hz u).le
    have hp0 := (rootedOccupationProbabilityAt_pos R z hz u).le
    have hmul := mul_le_mul ha hp hp0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hholder : |transferAt R z x u|^3 ≤ C * P^2 :=
    weightedChildHolderAt_B41 R z hz u x
  have hw : varianceWeightAt R z hz u ≤
      rootedOccupationProbabilityAt R z u * A :=
    varianceWeightAt_le_occupation_mul_childAvailability_B35 R z hz u
  have hchildren : A * C = ∑ c ∈ R.children (G := G) u,
      varianceWeightAt R z hz c * |x c|^3 := by
    dsimp [A, C]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    have huc : R.IsChild (G := G) u c := by
      simpa [ComponentRooting.children] using hc
    unfold varianceWeightAt
    rw [parentAbsentProbabilityAt_child_B30 hG R z hz huc]
    ring
  calc
    varianceWeightAt R z hz u * |transferAt R z x u|^3 ≤
        varianceWeightAt R z hz u * (C * P^2) :=
      mul_le_mul_of_nonneg_left hholder (varianceWeightAt_nonneg hG R z hz u)
    _ ≤ (rootedOccupationProbabilityAt R z u * A) * (C * P^2) :=
      mul_le_mul_of_nonneg_right hw (mul_nonneg hC (sq_nonneg P))
    _ = (rootedOccupationProbabilityAt R z u * P^2) * (A * C) := by ring
    _ = (rootedOccupationProbabilityAt R z u * P^2) *
        (∑ c ∈ R.children (G := G) u,
          varianceWeightAt R z hz c * |x c|^3) := by rw [hchildren]

/-- B.43 combined with B.42: complete cubic estimate at one parent. -/
theorem weightedTransferAt_parent_three_le_B43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (u : V) (x : V → ℝ) :
    varianceWeightAt R z hz u * |transferAt R z x u|^3 ≤
      (15 / 16 : ℝ) * ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * |x c|^3 := by
  have hbridge := weightedTransferAt_parent_bridge_B42 hG R z hz u x
  have hcoeff := cubicCoefficientAt_le_B43 hG R z hz hz15 u
  have hchild : 0 ≤ ∑ c ∈ R.children (G := G) u,
      varianceWeightAt R z hz c * |x c|^3 := by
    apply Finset.sum_nonneg
    intro c hc
    exact mul_nonneg (varianceWeightAt_nonneg hG R z hz c)
      (pow_nonneg (abs_nonneg _) _)
  exact hbridge.trans (mul_le_mul_of_nonneg_right hcoeff hchild)

/-- B.44: actual rooted weighted cubic contraction with exact constant `15/16`. -/
theorem weightedMomentAt_transfer_three_le_B44
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (x : V → ℝ) :
    weightedMomentAt R z hz 3 (transferAt R z x) ≤
      (15 / 16 : ℝ) * weightedMomentAt R z hz 3 x := by
  have hchild :
      (∑ u : V, ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * |x c|^3) ≤
        ∑ c : V, varianceWeightAt R z hz c * |x c|^3 := by
    apply sum_sum_children_le_sum hG R
    intro c
    exact mul_nonneg (varianceWeightAt_nonneg hG R z hz c)
      (pow_nonneg (abs_nonneg _) _)
  unfold weightedMomentAt
  calc
    (∑ u : V, varianceWeightAt R z hz u * |transferAt R z x u|^3) ≤
        ∑ u : V, (15 / 16 : ℝ) * ∑ c ∈ R.children (G := G) u,
          varianceWeightAt R z hz c * |x c|^3 := by
      apply Finset.sum_le_sum
      intro u hu
      exact weightedTransferAt_parent_three_le_B43 hG R z hz hz15 u x
    _ = (15 / 16 : ℝ) * (∑ u : V, ∑ c ∈ R.children (G := G) u,
        varianceWeightAt R z hz c * |x c|^3) := by rw [Finset.mul_sum]
    _ ≤ (15 / 16 : ℝ) * ∑ c : V,
        varianceWeightAt R z hz c * |x c|^3 :=
      mul_le_mul_of_nonneg_left hchild (by norm_num)

lemma abs_weightRoot_mul_rpow_nat
    (w x : ℝ) (n : ℕ) (hw : 0 ≤ w) (hn : n ≠ 0) :
    |w ^ ((n : ℝ)⁻¹) * x| ^ (n : ℝ) = w * |x|^n := by
  have hroot : 0 ≤ w ^ ((n : ℝ)⁻¹) := Real.rpow_nonneg hw _
  rw [abs_mul, abs_of_nonneg hroot,
    Real.mul_rpow hroot (abs_nonneg _)]
  rw [Real.rpow_natCast, Real.rpow_inv_natCast_pow hw hn,
    Real.rpow_natCast]

lemma weightedMinkowski_nat
    {ι : Type*} (s : Finset ι) (w x y : ι → ℝ)
    (n : ℕ) (hn1 : 1 ≤ n) (hw : ∀ i, 0 ≤ w i) :
    Real.rpow (∑ i ∈ s, w i * |x i + y i|^n) ((n : ℝ)⁻¹) ≤
      Real.rpow (∑ i ∈ s, w i * |x i|^n) ((n : ℝ)⁻¹) +
      Real.rpow (∑ i ∈ s, w i * |y i|^n) ((n : ℝ)⁻¹) := by
  let rootw : ι → ℝ := fun i => w i ^ ((n : ℝ)⁻¹)
  have H := Real.Lp_add_le s (fun i => rootw i * x i) (fun i => rootw i * y i)
    (p := (n : ℝ)) (by exact_mod_cast hn1)
  have hn : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hadd : (∑ i ∈ s, |rootw i * x i + rootw i * y i| ^ (n : ℝ)) =
      ∑ i ∈ s, w i * |x i + y i|^n := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [show rootw i * x i + rootw i * y i = rootw i * (x i + y i) by ring]
    exact abs_weightRoot_mul_rpow_nat (w i) (x i + y i) n (hw i) hn
  have hx : (∑ i ∈ s, |rootw i * x i| ^ (n : ℝ)) =
      ∑ i ∈ s, w i * |x i|^n := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_weightRoot_mul_rpow_nat (w i) (x i) n (hw i) hn
  have hy : (∑ i ∈ s, |rootw i * y i| ^ (n : ℝ)) =
      ∑ i ∈ s, w i * |y i|^n := by
    apply Finset.sum_congr rfl
    intro i hi
    exact abs_weightRoot_mul_rpow_nat (w i) (y i) n (hw i) hn
  norm_num only [one_div] at H
  rw [hadd, hx, hy] at H
  exact H

/-- Manuscript constant `C_W` from (B.47). -/
noncomputable def lowActivityCW : ℝ :=
  (1 + Real.sqrt 15 / 4)^2

/-- Manuscript constant `C_3` from (B.47), with the real cube root as `rpow (1/3)`. -/
noncomputable def lowActivityC3 : ℝ :=
  lowActivityCW /
    (1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹))^3

/-- The manuscript total weight `W`. -/
def totalVarianceWeightAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) : ℝ :=
  weightedMomentAt R z hz 0 (fun _ => 1)

lemma totalVarianceWeightAt_eq_sum
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    totalVarianceWeightAt R z hz = ∑ u : V, varianceWeightAt R z hz u := by
  simp [totalVarianceWeightAt, weightedMomentAt]

lemma weightedMomentAt_nonneg
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (n : ℕ) (x : V → ℝ) :
    0 ≤ weightedMomentAt R z hz n x := by
  unfold weightedMomentAt
  exact Finset.sum_nonneg fun u hu =>
    mul_nonneg (varianceWeightAt_nonneg hG R z hz u) (pow_nonneg (abs_nonneg _) _)

lemma weightedMomentAt_const_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (n : ℕ) :
    weightedMomentAt R z hz n (fun _ : V => 1) = totalVarianceWeightAt R z hz := by
  simp [weightedMomentAt, totalVarianceWeightAt]

lemma weightedMomentAt_neg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (n : ℕ) (x : V → ℝ) :
    weightedMomentAt R z hz n (fun u => -x u) = weightedMomentAt R z hz n x := by
  unfold weightedMomentAt
  apply Finset.sum_congr rfl
  intro u hu
  rw [abs_neg]

/-- Finite weighted Minkowski, specialized to `weightedMomentAt`. -/
theorem weightedMomentAt_add_rpow_inv_le
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (n : ℕ) (hn : 1 ≤ n) (x y : V → ℝ) :
    (weightedMomentAt R z hz n (fun u => x u + y u)) ^ ((n : ℝ)⁻¹) ≤
      (weightedMomentAt R z hz n x) ^ ((n : ℝ)⁻¹) +
      (weightedMomentAt R z hz n y) ^ ((n : ℝ)⁻¹) := by
  unfold weightedMomentAt
  exact weightedMinkowski_nat Finset.univ (varianceWeightAt R z hz) x y n hn
    (varianceWeightAt_nonneg hG R z hz)

/-- B.45, pointwise on the actual rooted displacement and transfer. -/
theorem one_eq_displacement_add_transfer_B45
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    1 = rootedDisplacementAt R z hz u +
      transferAt R z (rootedDisplacementAt R z hz) u := by
  rw [displacementRecursion_B28 hG R z hz u]
  unfold transferAt
  ring

/-- Function form of B.45. -/
theorem one_fun_eq_displacement_add_transfer_B45
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    (fun _ : V => (1 : ℝ)) = fun u => rootedDisplacementAt R z hz u +
      transferAt R z (rootedDisplacementAt R z hz) u := by
  funext u
  exact one_eq_displacement_add_transfer_B45 hG R z hz u

lemma weightedMomentAt_displacement_two_eq_variance
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    weightedMomentAt R z hz 2 (rootedDisplacementAt R z hz) =
      (hardCoreLaw G z hz).variance := by
  unfold weightedMomentAt
  rw [show (∑ u : V, varianceWeightAt R z hz u *
      |rootedDisplacementAt R z hz u|^2) =
      ∑ u : V, varianceWeightAt R z hz u *
        rootedDisplacementAt R z hz u ^ 2 by
    apply Finset.sum_congr rfl
    intro u hu
    rw [sq_abs]]
  exact occupationVarianceAt_B33 hG R z hz

lemma contractionSquareRoot_eq :
    (15 / 16 : ℝ) ^ ((2 : ℝ)⁻¹) = Real.sqrt 15 / 4 := by
  calc
    (15 / 16 : ℝ) ^ ((2 : ℝ)⁻¹) = Real.sqrt (15 / 16) := by
      rw [Real.sqrt_eq_rpow]
      norm_num
    _ = Real.sqrt 15 / 4 := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 15)]
      norm_num

lemma contractionCubeRoot_lt_one :
    (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹) < 1 := by
  exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)

lemma lowActivityCW_nonneg : 0 ≤ lowActivityCW := by
  unfold lowActivityCW
  positivity

lemma lowActivityC3_nonneg : 0 ≤ lowActivityC3 := by
  unfold lowActivityC3
  have hg : 0 < 1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹) :=
    sub_pos.2 contractionCubeRoot_lt_one
  exact div_nonneg lowActivityCW_nonneg (pow_nonneg hg.le 3)

/-- First half of B.46: the total weight is bounded by `C_W` times variance. -/
theorem totalVarianceWeightAt_le_CW_mul_variance_B46
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    totalVarianceWeightAt R z hz ≤
      lowActivityCW * (hardCoreLaw G z hz).variance := by
  let d : V → ℝ := rootedDisplacementAt R z hz
  let W := totalVarianceWeightAt R z hz
  let Var := (hardCoreLaw G z hz).variance
  let q := (15 / 16 : ℝ) ^ ((2 : ℝ)⁻¹)
  have hW : 0 ≤ W := by
    dsimp [W]
    rw [totalVarianceWeightAt_eq_sum]
    exact Finset.sum_nonneg fun u hu => varianceWeightAt_nonneg hG R z hz u
  have hVarEq : weightedMomentAt R z hz 2 d = Var :=
    weightedMomentAt_displacement_two_eq_variance hG R z hz
  have hVar : 0 ≤ Var := by
    rw [← hVarEq]
    exact weightedMomentAt_nonneg hG R z hz 2 d
  have hT : weightedMomentAt R z hz 2 (transferAt R z d) ≤
      (15/16 : ℝ) * Var := by
    rw [← hVarEq]
    exact weightedMomentAt_transfer_two_le_B40 hG R z hz hz15 d
  have hT0 := weightedMomentAt_nonneg hG R z hz 2 (transferAt R z d)
  have hTroot := Real.rpow_le_rpow hT0 hT (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
  have hmulroot : ((15/16 : ℝ) * Var) ^ ((2 : ℝ)⁻¹) =
      q * Var ^ ((2 : ℝ)⁻¹) := by
    dsimp [q]
    exact Real.mul_rpow (by norm_num) hVar
  rw [hmulroot] at hTroot
  have htri := weightedMomentAt_add_rpow_inv_le hG R z hz 2 (by norm_num) d
    (transferAt R z d)
  have hfun := one_fun_eq_displacement_add_transfer_B45 hG R z hz
  rw [← hfun, weightedMomentAt_const_one] at htri
  change W ^ ((2 : ℝ)⁻¹) ≤
      (weightedMomentAt R z hz 2 d) ^ ((2 : ℝ)⁻¹) +
      (weightedMomentAt R z hz 2 (transferAt R z d)) ^ ((2 : ℝ)⁻¹) at htri
  rw [hVarEq] at htri
  have hroot : W ^ ((2 : ℝ)⁻¹) ≤
      (1 + q) * Var ^ ((2 : ℝ)⁻¹) := by nlinarith
  have hsquare := pow_le_pow_left₀ (Real.rpow_nonneg hW _) hroot 2
  have hWroot : (W ^ ((2 : ℝ)⁻¹))^2 = W := by
    exact Real.rpow_inv_natCast_pow hW (by norm_num)
  have hVarroot : (Var ^ ((2 : ℝ)⁻¹))^2 = Var := by
    exact Real.rpow_inv_natCast_pow hVar (by norm_num)
  rw [hWroot, mul_pow, hVarroot] at hsquare
  change W ≤ lowActivityCW * Var
  rw [show lowActivityCW = (1 + q)^2 by
    unfold lowActivityCW
    dsimp [q]
    rw [contractionSquareRoot_eq]]
  exact hsquare

/-- Intermediate exact cubic moment bound by total weight. -/
theorem weightedMomentAt_displacement_three_le_weight
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    weightedMomentAt R z hz 3 (rootedDisplacementAt R z hz) ≤
      totalVarianceWeightAt R z hz /
        (1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹))^3 := by
  let d : V → ℝ := rootedDisplacementAt R z hz
  let W := totalVarianceWeightAt R z hz
  let S := weightedMomentAt R z hz 3 d
  let q := (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹)
  let gap := 1 - q
  have hW : 0 ≤ W := by
    dsimp [W]
    rw [totalVarianceWeightAt_eq_sum]
    exact Finset.sum_nonneg fun u hu => varianceWeightAt_nonneg hG R z hz u
  have hS : 0 ≤ S := weightedMomentAt_nonneg hG R z hz 3 d
  have hq : q < 1 := contractionCubeRoot_lt_one
  have hgap : 0 < gap := sub_pos.2 hq
  have hT : weightedMomentAt R z hz 3 (transferAt R z d) ≤
      (15/16 : ℝ) * S := by
    dsimp [S]
    exact weightedMomentAt_transfer_three_le_B44 hG R z hz hz15 d
  have hT0 := weightedMomentAt_nonneg hG R z hz 3 (transferAt R z d)
  have hTroot := Real.rpow_le_rpow hT0 hT (by positivity : 0 ≤ ((3 : ℝ)⁻¹))
  have hmulroot : ((15/16 : ℝ) * S) ^ ((3 : ℝ)⁻¹) =
      q * S ^ ((3 : ℝ)⁻¹) := by
    dsimp [q]
    exact Real.mul_rpow (by norm_num) hS
  rw [hmulroot] at hTroot
  have htri := weightedMomentAt_add_rpow_inv_le hG R z hz 3 (by norm_num)
    (fun _ : V => 1) (fun u => -transferAt R z d u)
  have hrec : d = fun u => (1 : ℝ) + -transferAt R z d u := by
    funext u
    have h := one_eq_displacement_add_transfer_B45 hG R z hz u
    dsimp [d] at h ⊢
    linarith
  rw [← hrec, weightedMomentAt_const_one, weightedMomentAt_neg] at htri
  change S ^ ((3 : ℝ)⁻¹) ≤ W ^ ((3 : ℝ)⁻¹) +
      (weightedMomentAt R z hz 3 (transferAt R z d)) ^ ((3 : ℝ)⁻¹) at htri
  have hgaproot : gap * S ^ ((3 : ℝ)⁻¹) ≤ W ^ ((3 : ℝ)⁻¹) := by
    dsimp [gap]
    nlinarith
  have hroot : S ^ ((3 : ℝ)⁻¹) ≤
      W ^ ((3 : ℝ)⁻¹) / gap := (le_div_iff₀ hgap).2 (by
        nlinarith [hgaproot])
  have hcube := pow_le_pow_left₀ (Real.rpow_nonneg hS _) hroot 3
  have hSroot : (S ^ ((3 : ℝ)⁻¹))^3 = S := by
    exact Real.rpow_inv_natCast_pow hS (by norm_num)
  have hWroot : (W ^ ((3 : ℝ)⁻¹))^3 = W := by
    exact Real.rpow_inv_natCast_pow hW (by norm_num)
  rw [hSroot, div_pow, hWroot] at hcube
  change S ≤ W / gap^3 at hcube
  exact hcube

/-- Second half of B.46 with the exact manuscript constant `C_3`. -/
theorem weightedMomentAt_displacement_three_le_C3_mul_variance_B46
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    weightedMomentAt R z hz 3 (rootedDisplacementAt R z hz) ≤
      lowActivityC3 * (hardCoreLaw G z hz).variance := by
  have hS := weightedMomentAt_displacement_three_le_weight hG R z hz hz15
  have hW := totalVarianceWeightAt_le_CW_mul_variance_B46 hG R z hz hz15
  have hgap : 0 < 1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹) :=
    sub_pos.2 contractionCubeRoot_lt_one
  calc
    weightedMomentAt R z hz 3 (rootedDisplacementAt R z hz) ≤
        totalVarianceWeightAt R z hz /
          (1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹))^3 := hS
    _ ≤ (lowActivityCW * (hardCoreLaw G z hz).variance) /
          (1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹))^3 := by
      exact div_le_div_of_nonneg_right hW (pow_nonneg hgap.le 3)
    _ = lowActivityC3 * (hardCoreLaw G z hz).variance := by
      unfold lowActivityC3
      field_simp

/-- Exact third absolute moment of a centered Bernoulli variable. -/
theorem bernoulli_centered_abs_cube_average
    (p d : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * |-p * d|^3 + p * |(1 - p) * d|^3 =
      p * (1 - p) * (p^2 + (1 - p)^2) * |d|^3 := by
  have hq : 0 ≤ 1 - p := sub_nonneg.2 hp1
  rw [abs_mul, abs_neg, abs_of_nonneg hp, abs_mul, abs_of_nonneg hq]
  ring

/-- The exact centered Bernoulli cubic coefficient is at most its variance. -/
theorem bernoulli_centered_abs_cube_coefficient_le
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * (p^2 + (1 - p)^2) ≤ p * (1 - p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.2 hp1
  have hpq : 0 ≤ p * (1 - p) := mul_nonneg hp hq
  have hsquares : p^2 + (1-p)^2 ≤ 1 := by
    nlinarith
  exact mul_le_of_le_one_right hpq hsquares

/-- Exact conditional third absolute moment of the seed-law martingale summand. -/
theorem finiteDoobMean_increment_abs_cube_current_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η : BernoulliAssignment V => |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3)
      (parentFirstEquiv R) k.castSucc ω =
    generatedAvailabilityReal R ω (parentFirstEquiv R k) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        (rootedOccupationProbabilityAt R z (parentFirstEquiv R k)^2 +
          rootedVacancyProbabilityAt R z (parentFirstEquiv R k)^2) *
        |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3) := by
  let p : ℝ := rootedOccupationProbabilityAt R z (parentFirstEquiv R k)
  let q : ℝ := rootedVacancyProbabilityAt R z (parentFirstEquiv R k)
  let d : ℝ := rootedDisplacementAt R z hz (parentFirstEquiv R k)
  let A : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k)
  have hp0 : 0 ≤ p := by dsimp [p]; exact (rootedOccupationProbabilityAt_pos R z hz _).le
  have hq0 : 0 ≤ q := by dsimp [q]; exact (rootedVacancyProbabilityAt_pos_local R z hz _).le
  have hD (η : BernoulliAssignment V) :
      finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η =
      A η * (if η (parentFirstEquiv R k) then q * d else -p * d) := by
    have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)
    rw [show q = 1 - p by dsimp [q, p]; linarith [hpq]]
    simpa [A, p, d, generatedAvailabilityReal] using
      generatedCountDoobIncrement_eq_available_exact hG R z hz k η
  have hfun : (fun η : BernoulliAssignment V => |finiteDoobIncrement
        (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3) =
      (fun η : BernoulliAssignment V => ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η) *
          (q^3 * |d|^3) +
        A η * (p^3 * |d|^3) -
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η) *
          (p^3 * |d|^3)) := by
    funext η
    rw [hD]
    unfold A generatedAvailabilityReal
    cases hs : η (parentFirstEquiv R k) <;>
      cases ha : generatedAvailable R η (parentFirstEquiv R k) <;>
      simp [hs, ha, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq0,
        pow_succ] <;>
      rw [show d * d = |d| * |d| by nlinarith [sq_abs d]] <;> ring
  rw [hfun, finiteDoobMean_sub, finiteDoobMean_add]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * (q^3 * |d|^3)) =
      (fun η => (q^3 * |d|^3) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [show (fun η => A η * (p^3 * |d|^3)) =
      (fun η => (p^3 * |d|^3) * A η) by funext η; ring]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * (p^3 * |d|^3)) =
      (fun η => (p^3 * |d|^3) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [finiteDoobMean_const_mul, finiteDoobMean_const_mul,
    finiteDoobMean_const_mul]
  rw [finiteDoobMean_generatedAvailability_mul_seed R z hz k ω,
    finiteDoobMean_generatedAvailability R z hz k ω]
  have hqdef : q = 1 - p := by
    dsimp [q, p]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)]
  change _ = A ω * (p * q * (p^2 + q^2) * |d|^3)
  rw [hqdef]
  ring

/-- Conditional B.48 estimate, obtained from the exact centered Bernoulli calculation. -/
theorem finiteDoobMean_increment_abs_cube_current_le
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η : BernoulliAssignment V => |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3)
      (parentFirstEquiv R) k.castSucc ω ≤
    generatedAvailabilityReal R ω (parentFirstEquiv R k) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3) := by
  rw [finiteDoobMean_increment_abs_cube_current_eq hG R z hz k ω]
  let p := rootedOccupationProbabilityAt R z (parentFirstEquiv R k)
  let q := rootedVacancyProbabilityAt R z (parentFirstEquiv R k)
  let A := generatedAvailabilityReal R ω (parentFirstEquiv R k)
  let d := rootedDisplacementAt R z hz (parentFirstEquiv R k)
  have hp : 0 ≤ p := by dsimp [p]; exact (rootedOccupationProbabilityAt_pos R z hz _).le
  have hp1 : p ≤ 1 := by dsimp [p]; exact rootedOccupationProbabilityAt_le_one R z hz _
  have hqdef : q = 1-p := by
    dsimp [q, p]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)]
  have hc := bernoulli_centered_abs_cube_coefficient_le p hp hp1
  rw [← hqdef] at hc
  have hA : 0 ≤ A := by
    dsimp [A]
    unfold generatedAvailabilityReal
    split <;> norm_num
  have hd : 0 ≤ |d|^3 := pow_nonneg (abs_nonneg _) _
  dsimp [p, q, A, d] at hc ⊢
  nlinarith [mul_nonneg hA hd]

/-- Unconditional third absolute moment of one seed-law martingale summand. -/
theorem finiteDoobIncrement_abs_cube_expectation_le_varianceWeight
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) :
    ∑ η : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability η *
      |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3 ≤
    varianceWeightAt R z hz (parentFirstEquiv R k) *
      |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3 := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  let Y : BernoulliAssignment V → ℝ := fun η =>
    |finiteDoobIncrement μ (fun ξ => generatedCountReal hG R ξ)
      (parentFirstEquiv R) k η|^3
  let E : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3)
  let ω₀ : BernoulliAssignment V := fun _ => false
  have hμpos : ∀ η, 0 < μ η := by
    intro η
    dsimp [μ]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hcond : ∀ η, finiteDoobMean μ Y (parentFirstEquiv R) k.castSucc η ≤ E η := by
    intro η
    exact finiteDoobMean_increment_abs_cube_current_le hG R z hz k η
  have htowerY := finiteDoobMean_tower_zero μ hμpos
    (hardCoreBernoulliSeedLaw R z hz).probability_sum
    Y (parentFirstEquiv R) k.castSucc ω₀
  have hzero : finiteDoobMean μ Y (parentFirstEquiv R) 0 ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) 0 ω₀ := by
    change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀
    rw [← htowerY]
    rw [finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum,
      finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum]
    apply Finset.sum_le_sum
    intro η hη
    exact mul_le_mul_of_nonneg_left (hcond η)
      ((hardCoreBernoulliSeedLaw R z hz).probability_nonneg η)
  change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ at hzero
  rw [finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum,
    finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum] at hzero
  dsimp [μ, Y, E] at hzero
  rw [show (∑ η : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (generatedAvailabilityReal R η (parentFirstEquiv R k) *
        (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
          rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
          |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3))) =
      (∑ η : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability η *
        generatedAvailabilityReal R η (parentFirstEquiv R k)) *
        (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
          rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
          |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3) by
    calc
      _ = ∑ η : BernoulliAssignment V,
          ((hardCoreBernoulliSeedLaw R z hz).probability η *
            generatedAvailabilityReal R η (parentFirstEquiv R k)) *
          (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
            rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
            |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3) := by
        apply Finset.sum_congr rfl
        intro η hη
        ring
      _ = _ := by rw [Finset.sum_mul]] at hzero
  unfold varianceWeightAt parentAbsentProbabilityAt
  nlinarith

/-- B.48 on the exact seed realization and its actual martingale increments. -/
theorem sum_finiteDoobIncrement_abs_cube_le_C3_mul_variance_B48
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    ∑ k : Fin (Fintype.card V),
      ∑ η : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability η *
        |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3 ≤
      lowActivityC3 * (hardCoreLaw G z hz).variance := by
  calc
    _ ≤ ∑ k : Fin (Fintype.card V),
        varianceWeightAt R z hz (parentFirstEquiv R k) *
          |rootedDisplacementAt R z hz (parentFirstEquiv R k)|^3 := by
      exact Finset.sum_le_sum fun k hk =>
        finiteDoobIncrement_abs_cube_expectation_le_varianceWeight hG R z hz k
    _ = weightedMomentAt R z hz 3 (rootedDisplacementAt R z hz) := by
      unfold weightedMomentAt
      exact Equiv.sum_comp (parentFirstEquiv R)
        (fun u => varianceWeightAt R z hz u * |rootedDisplacementAt R z hz u|^3)
    _ ≤ lowActivityC3 * (hardCoreLaw G z hz).variance :=
      weightedMomentAt_displacement_three_le_C3_mul_variance_B46 hG R z hz hz15

/-- The literal centered Bernoulli innovation on the exact independent-seed realization. -/
noncomputable def generatedEtaAt (R : ComponentRooting G) (z : ℝ)
    (ω : BernoulliAssignment V) (u : V) : ℝ :=
  generatedAvailabilityReal R ω u *
    (if ω u then rootedVacancyProbabilityAt R z u
      else -rootedOccupationProbabilityAt R z u)

/-- Each exact Doob increment is `δ_u η_u` in parent-first order. -/
theorem finiteDoobIncrement_eq_displacement_mul_generatedEtaAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k ω =
      rootedDisplacementAt R z hz (parentFirstEquiv R k) *
        generatedEtaAt R z ω (parentFirstEquiv R k) := by
  rw [generatedCountDoobIncrement_eq_available_exact hG R z hz k ω]
  unfold generatedEtaAt generatedAvailabilityReal
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz
    (parentFirstEquiv R k)
  have hq : rootedVacancyProbabilityAt R z (parentFirstEquiv R k) =
      1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k) := by linarith [hpq]
  rw [hq]
  cases ω (parentFirstEquiv R k) <;>
    cases generatedAvailable R ω (parentFirstEquiv R k) <;> simp <;> ring

/-- An exact seed Doob increment is pointwise dominated by the rooted
branch displacement at its current vertex. -/
theorem finiteDoobIncrement_abs_le_rootedDisplacementAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k ω| ≤
      |rootedDisplacementAt R z hz (parentFirstEquiv R k)| := by
  rw [generatedCountDoobIncrement_eq_available_exact hG R z hz k ω]
  let p := rootedOccupationProbabilityAt R z (parentFirstEquiv R k)
  let d := rootedDisplacementAt R z hz (parentFirstEquiv R k)
  have hp0 : 0 ≤ p := (rootedOccupationProbabilityAt_pos R z hz _).le
  have hp1 : p ≤ 1 := rootedOccupationProbabilityAt_le_one R z hz _
  change |(if generatedAvailable R ω (parentFirstEquiv R k) then 1 else 0) *
    (if ω (parentFirstEquiv R k) then (1-p)*d else -p*d)| ≤ |d|
  cases ha : generatedAvailable R ω (parentFirstEquiv R k) <;>
    cases hs : ω (parentFirstEquiv R k) <;>
    simp [ha, hs, abs_mul, abs_of_nonneg hp0,
      abs_of_nonneg (sub_nonneg.mpr hp1)] <;>
    apply mul_le_of_le_one_left (abs_nonneg d) <;> linarith

/-- Literal `∑_u E|δ_u η_u|³` form of B.48 on the exact seed coupling. -/
theorem sum_displacement_mul_generatedEtaAt_abs_cube_le_C3_mul_variance_B48
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    ∑ u : V, ∑ ω : BernoulliAssignment V,
      (hardCoreBernoulliSeedLaw R z hz).probability ω *
        |rootedDisplacementAt R z hz u * generatedEtaAt R z ω u|^3 ≤
      lowActivityC3 * (hardCoreLaw G z hz).variance := by
  calc
    _ = ∑ k : Fin (Fintype.card V), ∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          |rootedDisplacementAt R z hz (parentFirstEquiv R k) *
            generatedEtaAt R z ω (parentFirstEquiv R k)|^3 := by
      exact (Equiv.sum_comp (parentFirstEquiv R)
        (fun u => ∑ ω : BernoulliAssignment V,
          (hardCoreBernoulliSeedLaw R z hz).probability ω *
            |rootedDisplacementAt R z hz u * generatedEtaAt R z ω u|^3)).symm
    _ = ∑ k : Fin (Fintype.card V),
        ∑ ω : BernoulliAssignment V,
          (hardCoreBernoulliSeedLaw R z hz).probability ω *
            |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k ω|^3 := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro ω hω
      rw [finiteDoobIncrement_eq_displacement_mul_generatedEtaAt hG R z hz k ω]
    _ ≤ lowActivityC3 * (hardCoreLaw G z hz).variance :=
      sum_finiteDoobIncrement_abs_cube_le_C3_mul_variance_B48 hG R z hz hz15

/-- Normalized Lyapunov form of B.48, directly suited to a triangular-array CLT. -/
theorem sum_normalized_finiteDoobIncrement_abs_cube_le_B48
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (hVar : 0 < (hardCoreLaw G z hz).variance) :
    ∑ k : Fin (Fintype.card V),
      ∑ η : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability η *
          |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
            (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η /
              Real.sqrt (hardCoreLaw G z hz).variance|^3 ≤
      lowActivityC3 / Real.sqrt (hardCoreLaw G z hz).variance := by
  let Var := (hardCoreLaw G z hz).variance
  have hsqrt : 0 < Real.sqrt Var := Real.sqrt_pos.2 hVar
  have hB := sum_finiteDoobIncrement_abs_cube_le_C3_mul_variance_B48
    hG R z hz hz15
  have hscale :
      (∑ k : Fin (Fintype.card V),
        ∑ η : BernoulliAssignment V,
          (hardCoreBernoulliSeedLaw R z hz).probability η *
            |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η /
                Real.sqrt Var|^3) =
      (∑ k : Fin (Fintype.card V),
        ∑ η : BernoulliAssignment V,
          (hardCoreBernoulliSeedLaw R z hz).probability η *
            |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3) /
        (Real.sqrt Var)^3 := by
    calc
      _ = ∑ k : Fin (Fintype.card V),
          (∑ η : BernoulliAssignment V,
            (hardCoreBernoulliSeedLaw R z hz).probability η *
              |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3) /
            (Real.sqrt Var)^3 := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          _ = ∑ η : BernoulliAssignment V,
              ((hardCoreBernoulliSeedLaw R z hz).probability η *
                |finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                  (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η|^3) /
                (Real.sqrt Var)^3 := by
            apply Finset.sum_congr rfl
            intro η hη
            rw [abs_div, abs_of_pos hsqrt, div_pow]
            ring
          _ = _ := by rw [Finset.sum_div]
      _ = _ := by rw [Finset.sum_div]
  change _ ≤ lowActivityC3 / Real.sqrt Var
  rw [hscale]
  calc
    _ ≤ (lowActivityC3 * Var) / (Real.sqrt Var)^3 :=
      div_le_div_of_nonneg_right hB (pow_nonneg hsqrt.le 3)
    _ = lowActivityC3 / Real.sqrt Var := by
      have hsq : (Real.sqrt Var)^2 = Var := Real.sq_sqrt hVar.le
      calc
        (lowActivityC3 * Var) / (Real.sqrt Var)^3 =
            (lowActivityC3 * (Real.sqrt Var)^2) / (Real.sqrt Var)^3 := by rw [hsq]
        _ = lowActivityC3 / Real.sqrt Var := by field_simp [hsqrt.ne']

/-- The actual finite predictable quadratic variation of the parent-first seed Doob martingale. -/
noncomputable def scriptV (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (ω : BernoulliAssignment V) : ℝ :=
  ∑ k : Fin (Fintype.card V),
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2)
      (parentFirstEquiv R) k.castSucc ω

lemma scriptV_eq_sum_generatedAvailability_mul_energy
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (ω : BernoulliAssignment V) :
    scriptV hG R z hz ω =
      ∑ u : V, generatedAvailabilityReal R ω u * rootedEnergyAt R z hz u := by
  unfold scriptV
  rw [show (∑ k : Fin (Fintype.card V),
      finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2)
        (parentFirstEquiv R) k.castSucc ω) =
      ∑ k : Fin (Fintype.card V),
        generatedAvailabilityReal R ω (parentFirstEquiv R k) *
          rootedEnergyAt R z hz (parentFirstEquiv R k) by
    apply Finset.sum_congr rfl
    intro k hk
    exact finiteDoobMean_increment_sq_current hG R z hz k ω]
  exact Equiv.sum_comp (parentFirstEquiv R)
    (fun u => generatedAvailabilityReal R ω u * rootedEnergyAt R z hz u)

lemma parentOccupationIndicator_eq_selectedParent_of_acyclic
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (I : IndepFinset G) {u : V} (hu : u ≠ R.rootOf (G := G) u) :
    parentOccupationIndicator R I u =
      occupationIndicator I (R.selectedParent (G := G) u hu) := by
  unfold parentOccupationIndicator
  let p : V := R.selectedParent (G := G) u hu
  have hp : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hu
  rw [Finset.sum_eq_single p]
  · simp [hp, p]
  · intro q hq hqp
    by_cases hqchild : R.IsChild (G := G) q u
    · exact (hqp (R.isChild_unique (G := G) hG hqchild hp)).elim
    · simp [hqchild]
  · simp

lemma generatedOccupationIndicator_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (u : V) :
    occupationIndicator (generatedIndependentSet hG R ω) u =
      if generatedOccupation R ω u then 1 else 0 := by
  simp [occupationIndicator, generatedIndependentSet_val, generatedFinset]

lemma generatedAvailabilityReal_eq_one_sub_parentOccupationIndicator
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (u : V) :
    generatedAvailabilityReal R ω u =
      1 - parentOccupationIndicator R (generatedIndependentSet hG R ω) u := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · have hav : generatedAvailable R ω u = true := by
      unfold generatedAvailable
      rw [decide_eq_true_eq]
      intro p hpu
      exact (R.not_isChild_of_eq_root (G := G) hu hpu).elim
    rw [parentOccupationIndicator_root R _ hu]
    simp [generatedAvailabilityReal, hav]
  · rw [parentOccupationIndicator_eq_selectedParent_of_acyclic hG R _ hu]
    rw [generatedOccupationIndicator_eq hG R ω]
    have hp := R.selectedParent_isChild (G := G) u hu
    unfold generatedAvailabilityReal
    rw [generatedAvailable_eq_not_occupation_of_isChild hG R hp ω]
    cases generatedOccupation R ω (R.selectedParent (G := G) u hu) <;> norm_num

/-- B.49, the exact pointwise predictable quadratic variation formula. -/
theorem scriptV_formula_B49
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (ω : BernoulliAssignment V) :
    scriptV hG R z hz ω =
      ∑ u : V, rootedOccupationProbabilityAt R z u *
        rootedVacancyProbabilityAt R z u *
        rootedDisplacementAt R z hz u ^ 2 *
        (1 - parentOccupationIndicator R (generatedIndependentSet hG R ω) u) := by
  rw [scriptV_eq_sum_generatedAvailability_mul_energy hG R z hz ω]
  apply Finset.sum_congr rfl
  intro u hu
  rw [generatedAvailabilityReal_eq_one_sub_parentOccupationIndicator hG R ω u]
  unfold rootedEnergyAt
  ring

/-- B.49, the predictable quadratic variation has expectation equal to actual variance. -/
theorem scriptV_expectation_eq_variance_B49
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz) (scriptV hG R z hz) =
      (hardCoreLaw G z hz).variance := by
  unfold UniformFourthMoment.lawExpectation
  simp_rw [scriptV_eq_sum_generatedAvailability_mul_energy]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hmain := availability_energy_sum_eq_hardCoreVariance hG R z hz
  calc
    (∑ u : V, ∑ ω : BernoulliAssignment V,
      (hardCoreBernoulliSeedLaw R z hz).probability ω *
        (generatedAvailabilityReal R ω u * rootedEnergyAt R z hz u)) =
      ∑ u : V, (∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          generatedAvailabilityReal R ω u) * rootedEnergyAt R z hz u := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        ring
    _ = ∑ k : Fin (Fintype.card V),
      (∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          generatedAvailabilityReal R ω (parentFirstEquiv R k)) *
          rootedEnergyAt R z hz (parentFirstEquiv R k) := by
        exact (Equiv.sum_comp (parentFirstEquiv R)
          (fun u => (∑ ω : BernoulliAssignment V,
            (hardCoreBernoulliSeedLaw R z hz).probability ω *
              generatedAvailabilityReal R ω u) * rootedEnergyAt R z hz u)).symm
    _ = (hardCoreLaw G z hz).variance := hmain

/-- The deterministic local energy coefficient `h_u`. -/
noncomputable def hAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) : ℝ :=
  rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u *
    rootedDisplacementAt R z hz u ^ 2

/-- The aggregate energy of the children of `x`. -/
noncomputable def childEnergyAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) : ℝ :=
  ∑ c ∈ R.children (G := G) x, hAt R z hz c

lemma sum_parentOccupationIndicator_of_acyclic
    (_hG : G.IsAcyclic) (R : ComponentRooting G)
    (I : IndepFinset G) (d p : V → ℝ) :
    (∑ u : V, d u * p u * parentOccupationIndicator R I u) =
      ∑ x : V, occupationIndicator I x *
        (∑ u ∈ R.children (G := G) x, p u * d u) := by
  unfold parentOccupationIndicator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ComponentRooting.children, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : R.IsChild (G := G) x u
  · simp [h]; ring
  · simp [h]

/-- B.50, including the component-root virtual-parent convention. -/
theorem scriptV_deterministic_sub_linear_score_B50
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (ω : BernoulliAssignment V) :
    scriptV hG R z hz ω =
      (∑ u : V, hAt R z hz u) -
        ∑ x : V, childEnergyAt R z hz x *
          occupationIndicator (generatedIndependentSet hG R ω) x := by
  rw [scriptV_formula_B49 hG R z hz ω]
  have hreindex : (∑ u : V, hAt R z hz u *
      parentOccupationIndicator R (generatedIndependentSet hG R ω) u) =
      ∑ x : V, occupationIndicator (generatedIndependentSet hG R ω) x *
        (∑ u ∈ R.children (G := G) x, hAt R z hz u) := by
    simpa only [mul_one, one_mul] using sum_parentOccupationIndicator_of_acyclic hG R
      (generatedIndependentSet hG R ω) (fun u => hAt R z hz u) (fun _ => (1 : ℝ))
  rw [show (∑ u : V,
      rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u *
        rootedDisplacementAt R z hz u ^ 2 *
          (1 - parentOccupationIndicator R (generatedIndependentSet hG R ω) u)) =
      (∑ u : V, hAt R z hz u) -
        ∑ u : V, hAt R z hz u *
          parentOccupationIndicator R (generatedIndependentSet hG R ω) u by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro u hu
    unfold hAt
    ring]
  rw [hreindex]
  unfold childEnergyAt
  apply congrArg (fun t => (∑ u : V, hAt R z hz u) - t)
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The parent-last recursive solution of `(I + T) θ = d`. -/
noncomputable def thetaAt (R : ComponentRooting G) (z : ℝ)
    (d : V → ℝ) : V → ℝ :=
  (measure (fun u : V => R.subtreeOrder (G := G) u)).wf.fix
    (fun u rec => d u -
      (R.children (G := G) u).attach.sum (fun c =>
        rootedOccupationProbabilityAt R z c.1 *
          rec c.1 (R.subtreeOrder_child_lt (G := G)
            ((R.mem_children (G := G) u c.1).mp c.2))))

lemma thetaAt_eq_sub_transferAt
    (R : ComponentRooting G) (z : ℝ) (d : V → ℝ) (u : V) :
    thetaAt R z d u = d u - transferAt R z (thetaAt R z d) u := by
  rw [thetaAt, WellFounded.fix_eq]
  unfold transferAt
  congr 1
  exact Finset.sum_attach (R.children (G := G) u)
    (fun c => rootedOccupationProbabilityAt R z c *
      (measure (fun u : V => R.subtreeOrder (G := G) u)).wf.fix
        (fun u rec => d u -
          (R.children (G := G) u).attach.sum (fun c =>
            rootedOccupationProbabilityAt R z c.1 *
              rec c.1 (R.subtreeOrder_child_lt (G := G)
                ((R.mem_children (G := G) u c.1).mp c.2)))) c)

/-- The recursive solution exactly solves `(I + T) θ = d`. -/
theorem thetaAt_add_transferAt_eq_B51
    (R : ComponentRooting G) (z : ℝ) (d : V → ℝ) (u : V) :
    thetaAt R z d u + transferAt R z (thetaAt R z d) u = d u := by
  rw [thetaAt_eq_sub_transferAt]
  ring

/-- A deterministic linear occupation score on the actual configuration space. -/
noncomputable def occupationScore (d : V → ℝ) (I : IndepFinset G) : ℝ :=
  ∑ u : V, d u * occupationIndicator I u

/-- The same score on the exact independent-seed realization. -/
noncomputable def generatedOccupationScore (R : ComponentRooting G)
    (d : V → ℝ) (ω : BernoulliAssignment V) : ℝ :=
  ∑ u : V, d u * (if generatedOccupation R ω u then 1 else 0)

lemma generatedOccupationScore_eq_occupationScore
    (hG : G.IsAcyclic) (R : ComponentRooting G) (d : V → ℝ)
    (ω : BernoulliAssignment V) :
    generatedOccupationScore R d ω = occupationScore d (generatedIndependentSet hG R ω) := by
  unfold generatedOccupationScore occupationScore
  apply Finset.sum_congr rfl
  intro u hu
  rw [generatedOccupationIndicator_eq hG R ω u]

lemma finiteDoobBranchValue_const_mul
    (μ : BernoulliAssignment V → ℝ) (a : ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) (b : Bool) :
    finiteDoobBranchValue μ (fun η => a * f η) e k ω b =
      a * finiteDoobBranchValue μ f e k ω b := by
  unfold finiteDoobBranchValue
  exact finiteDoobMean_const_mul μ a f e k.succ (Function.update ω (e k) b)

lemma generatedOccupationScore_branch_difference_eq_sum_responses
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedOccupationScore R d) (parentFirstEquiv R) k ω true -
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedOccupationScore R d) (parentFirstEquiv R) k ω false =
      ∑ x : V, d x * occupationBranchResponse R z hz k ω x := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  have hm (b : Bool) : prefixMass μ (parentFirstEquiv R) k.succ
      (Function.update ω (parentFirstEquiv R k) b) ≠ 0 := by
    apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    dsimp [μ]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  unfold generatedOccupationScore
  rw [finiteDoobBranchValue_sum μ (parentFirstEquiv R) k ω
      (fun x η => d x * (if generatedOccupation R η x then (1 : ℝ) else 0)) true (hm true),
    finiteDoobBranchValue_sum μ (parentFirstEquiv R) k ω
      (fun x η => d x * (if generatedOccupation R η x then (1 : ℝ) else 0)) false (hm false),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [finiteDoobBranchValue_const_mul, finiteDoobBranchValue_const_mul]
  unfold occupationBranchResponse
  ring

lemma weighted_response_eq_zero_of_not_descendant
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) (x : V)
    (hx : x ∉ R.descendants (G := G) (parentFirstEquiv R k)) :
    d x * occupationBranchResponse R z hz k ω x = 0 := by
  rw [occupationBranchResponse_eq_zero_of_not_descendant R z hz k ω x hx]
  ring

lemma weighted_response_sum_eq_descendants
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    (∑ x : V, d x * occupationBranchResponse R z hz k ω x) =
      ∑ x ∈ R.descendants (G := G) (parentFirstEquiv R k),
        d x * occupationBranchResponse R z hz k ω x := by
  calc
    _ = ∑ x ∈ Finset.univ,
        if x ∈ R.descendants (G := G) (parentFirstEquiv R k) then
          d x * occupationBranchResponse R z hz k ω x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxd : x ∈ R.descendants (G := G) (parentFirstEquiv R k)
      · simp [hxd]
      · rw [weighted_response_eq_zero_of_not_descendant R z hz d k ω x hxd]
        simp
    _ = _ := by rw [Finset.sum_ite_mem]; simp

lemma weighted_response_sum_descendants_eq_theta
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (u : V) (hu : u ∈ R.descendants (G := G) (parentFirstEquiv R k)) :
    (∑ x ∈ R.descendants (G := G) u,
      d x * occupationBranchResponse R z hz k ω x) =
      thetaAt R z d u * occupationBranchResponse R z hz k ω u := by
  induction hn : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [R.descendants_eq_insert_biUnion_children (G := G) u]
      rw [Finset.sum_insert]
      · rw [Finset.sum_biUnion (R.children_pairwiseDisjoint_descendants (G := G) hG u)]
        have hchildren :
            (∑ v ∈ R.children (G := G) u,
              ∑ x ∈ R.descendants (G := G) v,
                d x * occupationBranchResponse R z hz k ω x) =
            ∑ v ∈ R.children (G := G) u,
              thetaAt R z d v * occupationBranchResponse R z hz k ω v := by
          apply Finset.sum_congr rfl
          intro v hv
          apply ih (R.subtreeOrder (G := G) v)
          · rw [← hn]
            exact R.subtreeOrder_child_lt (G := G)
              ((R.mem_children (G := G) u v).mp hv)
          · exact (R.mem_descendants (G := G) _ _).mpr
              ((R.mem_descendants (G := G) _ _).mp hu |>.tail
                ((R.mem_children (G := G) u v).mp hv))
          · rfl
        rw [hchildren]
        have hresp : ∀ v ∈ R.children (G := G) u,
            occupationBranchResponse R z hz k ω v =
              -rootedOccupationProbabilityAt R z v *
                occupationBranchResponse R z hz k ω u := by
          intro v hv
          apply occupationBranchResponse_child hG R z hz k ω
            ((R.mem_children (G := G) u v).mp hv)
          · exact (R.mem_descendants (G := G) _ _).mpr
              ((R.mem_descendants (G := G) _ _).mp hu |>.tail
                ((R.mem_children (G := G) u v).mp hv))
          · intro hvu
            subst v
            exact R.not_mem_descendants_child (G := G)
              ((R.mem_children (G := G) u (parentFirstEquiv R k)).mp hv) hu
        rw [show (∑ v ∈ R.children (G := G) u,
            thetaAt R z d v * occupationBranchResponse R z hz k ω v) =
            -(transferAt R z (thetaAt R z d) u) *
              occupationBranchResponse R z hz k ω u by
          unfold transferAt
          calc
            _ = ∑ v ∈ R.children (G := G) u,
                thetaAt R z d v * (-rootedOccupationProbabilityAt R z v *
                  occupationBranchResponse R z hz k ω u) := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    rw [hresp v hv]
            _ = ∑ v ∈ R.children (G := G) u,
                (-(rootedOccupationProbabilityAt R z v * thetaAt R z d v)) *
                  occupationBranchResponse R z hz k ω u := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    ring
            _ = _ := by rw [← Finset.sum_neg_distrib, Finset.sum_mul]]
        rw [thetaAt_eq_sub_transferAt]
        ring
      · rw [Finset.mem_biUnion]
        push Not
        intro v hv
        exact R.not_mem_descendants_child (G := G)
          ((R.mem_children (G := G) u v).mp hv)

/-- The Doob increment of an arbitrary generated linear score is `θ_u η_u`. -/
theorem finiteDoobIncrement_generatedOccupationScore_eq_theta_mul_eta_B51
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
      (generatedOccupationScore R d) (parentFirstEquiv R) k ω =
      thetaAt R z d (parentFirstEquiv R k) *
        generatedEtaAt R z ω (parentFirstEquiv R k) := by
  have hbranch :
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (generatedOccupationScore R d) (parentFirstEquiv R) k ω true -
        finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (generatedOccupationScore R d) (parentFirstEquiv R) k ω false =
      generatedAvailabilityReal R ω (parentFirstEquiv R k) *
        thetaAt R z d (parentFirstEquiv R k) := by
    rw [generatedOccupationScore_branch_difference_eq_sum_responses R z hz d k ω,
      weighted_response_sum_eq_descendants R z hz d k ω,
      weighted_response_sum_descendants_eq_theta hG R z hz d k ω
        (parentFirstEquiv R k) (R.self_mem_descendants (G := G) _),
      occupationBranchResponse_current hG R z hz k ω]
    unfold generatedAvailabilityReal
    ring
  change finiteDoobIncrement
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
      (generatedOccupationScore R d) (parentFirstEquiv R) k ω = _
  rw [finiteDoobIncrement_eq_branch_displacement
    (fun v => rootedOccupationProbabilityAt R z v)
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz)
    (generatedOccupationScore R d) (parentFirstEquiv R) k ω
    (hardCoreSeed_branchProbability_exact R z hz k ω)]
  rw [show finiteDoobBranchValue
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
        (generatedOccupationScore R d) (parentFirstEquiv R) k ω true -
      finiteDoobBranchValue
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
        (generatedOccupationScore R d) (parentFirstEquiv R) k ω false =
      generatedAvailabilityReal R ω (parentFirstEquiv R k) *
        thetaAt R z d (parentFirstEquiv R k) by exact hbranch]
  have hq : rootedVacancyProbabilityAt R z (parentFirstEquiv R k) =
      1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k) := by
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)]
  unfold generatedEtaAt generatedAvailabilityReal
  rw [hq]
  cases ω (parentFirstEquiv R k) <;>
    cases generatedAvailable R ω (parentFirstEquiv R k) <;> simp <;> ring

/-- The seed-law mean of the arbitrary generated score. -/
noncomputable def generatedScoreMean (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) : ℝ :=
  UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
    (generatedOccupationScore R d)

/-- The actual finite seed-law variance of an arbitrary generated score. -/
noncomputable def generatedScoreVariance (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) : ℝ :=
  ∑ ω : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability ω *
    (generatedOccupationScore R d ω - generatedScoreMean R z hz d)^2

lemma hardCoreSeed_probability_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∀ ω : BernoulliAssignment V, 0 < (hardCoreBernoulliSeedLaw R z hz).probability ω := by
  intro ω
  unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
  apply Finset.prod_pos
  intro u hu
  cases ω u <;> simp [rootedOccupationProbabilityAt_pos R z hz u,
    rootedOccupationProbabilityAt_lt_one R z hz u]

lemma finiteCenteredSecond_eq_sum_increment_sq
    (μ : BernoulliAssignment V → ℝ) (hμ : ∀ ω, 0 < μ ω)
    (hnorm : ∑ ω, μ ω = 1) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) :
    (∑ ω, μ ω * (X ω - ∑ η, μ η * X η)^2) =
      ∑ k : Fin (Fintype.card V), ∑ ω, μ ω *
        (finiteDoobIncrement μ X e k ω)^2 := by
  let m : ℝ := ∑ η, μ η * X η
  have htotal := finiteDoob_sq_expectation_total μ hμ hnorm X e
  have hcenter :
      (∑ ω, μ ω * (X ω - m)^2) = (∑ ω, μ ω * X ω^2) - m^2 := by
    calc
      _ = ∑ ω, (μ ω * X ω^2 - 2 * m * (μ ω * X ω) + m^2 * μ ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        ring
      _ = (∑ ω, μ ω * X ω^2) - 2 * m * (∑ ω, μ ω * X ω) +
          m^2 * (∑ ω, μ ω) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = (∑ ω, μ ω * X ω^2) - m^2 := by
        rw [hnorm]
        dsimp [m]
        ring
  change (∑ ω, μ ω * (X ω - m)^2) = _
  rw [hcenter]
  dsimp [m] at htotal ⊢
  linarith

/-- B.51 centered-score representation on the exact seed/generated occupation law. -/
theorem generatedOccupationScore_centered_eq_sum_theta_eta_B51
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) (ω : BernoulliAssignment V) :
    generatedOccupationScore R d ω - generatedScoreMean R z hz d =
      ∑ u : V, thetaAt R z d u * generatedEtaAt R z ω u := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  have htel := finiteDoobIncrement_sum_eq_terminal_sub_zero μ
    (generatedOccupationScore R d) (parentFirstEquiv R) ω
  have hfull := finiteDoobMean_full_eq μ (generatedOccupationScore R d)
    (hardCoreSeed_probability_pos R z hz) (parentFirstEquiv R) ω
  have hzero := finiteDoobMean_zero_of_normalized μ (generatedOccupationScore R d)
    (parentFirstEquiv R) ω (hardCoreBernoulliSeedLaw R z hz).probability_sum
  have hsum :
      generatedOccupationScore R d ω - generatedScoreMean R z hz d =
        ∑ k : Fin (Fintype.card V),
          finiteDoobIncrement μ (generatedOccupationScore R d) (parentFirstEquiv R) k ω := by
    rw [htel, hfull, hzero]
    rfl
  rw [hsum]
  rw [show (∑ k : Fin (Fintype.card V),
      finiteDoobIncrement μ (generatedOccupationScore R d) (parentFirstEquiv R) k ω) =
      ∑ k : Fin (Fintype.card V), thetaAt R z d (parentFirstEquiv R k) *
        generatedEtaAt R z ω (parentFirstEquiv R k) by
    apply Finset.sum_congr rfl
    intro k hk
    exact finiteDoobIncrement_generatedOccupationScore_eq_theta_mul_eta_B51
      hG R z hz d k ω]
  exact Equiv.sum_comp (parentFirstEquiv R)
    (fun u => thetaAt R z d u * generatedEtaAt R z ω u)

lemma generatedEtaAt_sq_expectation_eq_varianceWeight
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    (∑ ω : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability ω *
      generatedEtaAt R z ω u ^ 2) = varianceWeightAt R z hz u := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  let A : BernoulliAssignment V → ℝ := fun ω => generatedAvailabilityReal R ω u
  let S : BernoulliAssignment V → ℝ := fun ω => if ω u then 1 else 0
  let p := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  have hocc := generatedOccupation_expectation_eq_probability_mul_availability hG R z hz u
  have hSA : (∑ ω, μ ω * (S ω * A ω)) = p * (∑ ω, μ ω * A ω) := by
    rw [← hocc]
    apply Finset.sum_congr rfl
    intro ω hω
    dsimp [μ, S, A]
    rw [generatedOccupation_eq_seed_and_available]
    unfold generatedAvailabilityReal
    cases ω u <;> cases generatedAvailable R ω u <;> norm_num
  have hexpand :
      (∑ ω, μ ω * generatedEtaAt R z ω u ^ 2) =
      (∑ ω, μ ω * (S ω * A ω)) * q^2 +
        (∑ ω, μ ω * A ω) * p^2 -
        (∑ ω, μ ω * (S ω * A ω)) * p^2 := by
    calc
      _ = ∑ ω, ((μ ω * (S ω * A ω)) * q^2 + (μ ω * A ω) * p^2 -
          (μ ω * (S ω * A ω)) * p^2) := by
        apply Finset.sum_congr rfl
        intro ω hω
        dsimp [S, A, p, q]
        unfold generatedEtaAt generatedAvailabilityReal
        cases ω u <;> cases generatedAvailable R ω u <;> norm_num
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  rw [hexpand, hSA]
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  change _ = parentAbsentProbabilityAt R z hz u * p * q
  unfold parentAbsentProbabilityAt
  change _ = (∑ ω, μ ω * A ω) * p * q
  have hq : q = 1 - p := by dsimp [q, p]; linarith [hpq]
  rw [hq]
  ring

/-- B.51 exact variance identity for arbitrary deterministic occupation-score coefficients. -/
theorem generatedScoreVariance_eq_weightedMoment_theta_B51
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (d : V → ℝ) :
    generatedScoreVariance R z hz d = weightedMomentAt R z hz 2 (thetaAt R z d) := by
  unfold generatedScoreVariance generatedScoreMean UniformFourthMoment.lawExpectation
  rw [finiteCenteredSecond_eq_sum_increment_sq
    (hardCoreBernoulliSeedLaw R z hz).probability
    (hardCoreSeed_probability_pos R z hz)
    (hardCoreBernoulliSeedLaw R z hz).probability_sum
    (generatedOccupationScore R d) (parentFirstEquiv R)]
  rw [show (∑ k : Fin (Fintype.card V),
      ∑ ω : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability ω *
        finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (generatedOccupationScore R d) (parentFirstEquiv R) k ω ^ 2) =
      ∑ k : Fin (Fintype.card V), varianceWeightAt R z hz (parentFirstEquiv R k) *
        thetaAt R z d (parentFirstEquiv R k)^2 by
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
            (generatedOccupationScore R d) (parentFirstEquiv R) k ω ^ 2) =
        thetaAt R z d (parentFirstEquiv R k)^2 *
          (∑ ω : BernoulliAssignment V,
            (hardCoreBernoulliSeedLaw R z hz).probability ω *
              generatedEtaAt R z ω (parentFirstEquiv R k)^2) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      rw [finiteDoobIncrement_generatedOccupationScore_eq_theta_mul_eta_B51
        hG R z hz d k ω]
      ring]
    rw [generatedEtaAt_sq_expectation_eq_varianceWeight hG R z hz]
    ring]
  unfold weightedMomentAt
  rw [show (∑ k : Fin (Fintype.card V), varianceWeightAt R z hz (parentFirstEquiv R k) *
      thetaAt R z d (parentFirstEquiv R k)^2) =
      ∑ u : V, varianceWeightAt R z hz u * thetaAt R z d u^2 by
    exact Equiv.sum_comp (parentFirstEquiv R)
      (fun u => varianceWeightAt R z hz u * thetaAt R z d u^2)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [sq_abs]

/-- B.52: the recursive coefficients have controlled weighted second moment. -/
theorem weightedMomentAt_theta_two_le_B52
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (d : V → ℝ) :
    weightedMomentAt R z hz 2 (thetaAt R z d) ≤
      (1 / (1 - Real.sqrt 15 / 4) ^ 2) *
        weightedMomentAt R z hz 2 d := by
  let θ : V → ℝ := thetaAt R z d
  let S : ℝ := weightedMomentAt R z hz 2 θ
  let D : ℝ := weightedMomentAt R z hz 2 d
  let q : ℝ := (15 / 16 : ℝ) ^ ((2 : ℝ)⁻¹)
  let gap : ℝ := 1 - q
  have hS : 0 ≤ S := by
    dsimp [S]
    exact weightedMomentAt_nonneg hG R z hz 2 θ
  have hD : 0 ≤ D := by
    dsimp [D]
    exact weightedMomentAt_nonneg hG R z hz 2 d
  have hq : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.2 hq
  have hT :
      weightedMomentAt R z hz 2 (transferAt R z θ) ≤
        (15 / 16 : ℝ) * S := by
    dsimp [S]
    exact weightedMomentAt_transfer_two_le_B40 hG R z hz hz15 θ
  have hT0 :
      0 ≤ weightedMomentAt R z hz 2 (transferAt R z θ) :=
    weightedMomentAt_nonneg hG R z hz 2 (transferAt R z θ)
  have hTroot :=
    Real.rpow_le_rpow hT0 hT
      (by positivity : 0 ≤ ((2 : ℝ)⁻¹))
  have hmulroot :
      ((15 / 16 : ℝ) * S) ^ ((2 : ℝ)⁻¹) =
        q * S ^ ((2 : ℝ)⁻¹) := by
    dsimp [q]
    exact Real.mul_rpow (by norm_num) hS
  rw [hmulroot] at hTroot
  have hrec :
      θ = fun u => d u + -transferAt R z θ u := by
    funext u
    have h := thetaAt_add_transferAt_eq_B51 R z d u
    dsimp [θ] at h ⊢
    linarith
  have htri :=
    weightedMomentAt_add_rpow_inv_le
      hG R z hz 2 (by norm_num) d
        (fun u => -transferAt R z θ u)
  rw [← hrec, weightedMomentAt_neg] at htri
  change
    S ^ ((2 : ℝ)⁻¹) ≤
      D ^ ((2 : ℝ)⁻¹) +
        (weightedMomentAt R z hz 2 (transferAt R z θ)) ^
          ((2 : ℝ)⁻¹) at htri
  have hgaproot :
      gap * S ^ ((2 : ℝ)⁻¹) ≤ D ^ ((2 : ℝ)⁻¹) := by
    dsimp [gap]
    nlinarith
  have hroot :
      S ^ ((2 : ℝ)⁻¹) ≤
        D ^ ((2 : ℝ)⁻¹) / gap := by
    apply (le_div_iff₀ hgap).2
    simpa [mul_comm] using hgaproot
  have hsquare :=
    pow_le_pow_left₀ (Real.rpow_nonneg hS _) hroot 2
  have hSroot :
      (S ^ ((2 : ℝ)⁻¹)) ^ 2 = S := by
    exact Real.rpow_inv_natCast_pow hS (by norm_num)
  have hDroot :
      (D ^ ((2 : ℝ)⁻¹)) ^ 2 = D := by
    exact Real.rpow_inv_natCast_pow hD (by norm_num)
  rw [hSroot, div_pow, hDroot] at hsquare
  change
    S ≤ (1 / (1 - Real.sqrt 15 / 4) ^ 2) * D
  dsimp [gap, q] at hsquare
  rw [contractionSquareRoot_eq] at hsquare
  simpa [div_eq_mul_inv, mul_comm] using hsquare

/-- B.52 in the variance form used for deterministic linear occupation scores. -/
theorem generatedScoreVariance_le_weightedMoment_B52
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (d : V → ℝ) :
    generatedScoreVariance R z hz d ≤
      (1 / (1 - Real.sqrt 15 / 4) ^ 2) *
        weightedMomentAt R z hz 2 d := by
  rw [generatedScoreVariance_eq_weightedMoment_theta_B51 hG R z hz d]
  exact weightedMomentAt_theta_two_le_B52 hG R z hz hz15 d

/-- Finite seed-law variance of the predictable quadratic variation. -/
noncomputable def scriptVVariance (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) : ℝ :=
  ∑ ω : BernoulliAssignment V, (hardCoreBernoulliSeedLaw R z hz).probability ω *
    (scriptV hG R z hz ω -
      UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
        (scriptV hG R z hz))^2

lemma scriptVVariance_eq_generatedScoreVariance_childEnergy
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    scriptVVariance hG R z hz =
      generatedScoreVariance R z hz (childEnergyAt R z hz) := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  let H := ∑ u : V, hAt R z hz u
  let Y := generatedOccupationScore R (childEnergyAt R z hz)
  have hQ (ω : BernoulliAssignment V) :
      scriptV hG R z hz ω = H - Y ω := by
    rw [scriptV_deterministic_sub_linear_score_B50 hG R z hz ω]
    dsimp [H, Y]
    unfold generatedOccupationScore
    apply congrArg (fun t => (∑ u : V, hAt R z hz u) - t)
    apply Finset.sum_congr rfl
    intro x hx
    rw [generatedOccupationIndicator_eq hG R ω x]
  have hEQ :
      UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
        (scriptV hG R z hz) = H - generatedScoreMean R z hz (childEnergyAt R z hz) := by
    unfold UniformFourthMoment.lawExpectation generatedScoreMean
    change (∑ ω, μ ω * scriptV hG R z hz ω) =
      H - ∑ ω, μ ω * Y ω
    calc
      _ = ∑ ω, (μ ω * H - μ ω * Y ω) := by
        apply Finset.sum_congr rfl
        intro ω hω
        rw [hQ]
        ring
      _ = (∑ ω, μ ω) * H - ∑ ω, μ ω * Y ω := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = _ := by
        rw [(hardCoreBernoulliSeedLaw R z hz).probability_sum]
        ring
  unfold scriptVVariance generatedScoreVariance
  apply Finset.sum_congr rfl
  intro ω hω
  rw [hQ, hEQ]
  dsimp [Y]
  ring

/-- B.53: apply the B.52 score estimate to the child-energy coefficients. -/
theorem scriptVVariance_le_weighted_childEnergy_B53
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    scriptVVariance hG R z hz ≤
      (1 / (1 - Real.sqrt 15 / 4) ^ 2) *
        weightedMomentAt R z hz 2 (childEnergyAt R z hz) := by
  rw [scriptVVariance_eq_generatedScoreVariance_childEnergy hG R z hz]
  exact generatedScoreVariance_le_weightedMoment_B52 hG R z hz hz15
    (childEnergyAt R z hz)

/-- The B.54 child Bernoulli-variance aggregate `R_x`. -/
noncomputable def childPQAt (R : ComponentRooting G) (z : ℝ) (x : V) : ℝ :=
  ∑ c ∈ R.children (G := G) x,
    rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c

/-- The B.54 child cubic aggregate `B_x`. -/
noncomputable def childCubicAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (x : V) : ℝ :=
  ∑ c ∈ R.children (G := G) x,
    rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c *
      |rootedDisplacementAt R z hz c|^3

lemma rpow_interpolation_term
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    a ^ ((3 : ℝ)⁻¹) * (a * t^3) ^ (2 / 3 : ℝ) = a * t^2 := by
  by_cases ha0 : a = 0
  · simp [ha0]
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [Real.mul_rpow ha (pow_nonneg ht 3)]
    rw [show a ^ ((3 : ℝ)⁻¹) *
        (a ^ (2 / 3 : ℝ) * (t^3) ^ (2 / 3 : ℝ)) =
        (a ^ ((3 : ℝ)⁻¹) * a ^ (2 / 3 : ℝ)) *
          (t^3) ^ (2 / 3 : ℝ) by ring]
    rw [← Real.rpow_add ha']
    have htpart : (t^3) ^ (2 / 3 : ℝ) = t^2 := by
      calc
        (t^3) ^ (2 / 3 : ℝ) = (t ^ (3 : ℝ)) ^ (2 / 3 : ℝ) :=
          congrArg (fun x : ℝ => x ^ (2 / 3 : ℝ)) (Real.rpow_natCast t 3).symm
        _ = t ^ ((3 : ℝ) * (2 / 3 : ℝ)) := (Real.rpow_mul ht _ _).symm
        _ = t^2 := by norm_num [Real.rpow_natCast]
    rw [htpart]
    norm_num [Real.rpow_one]

/-- Finite Hölder interpolation in the exact `2`-versus-`3` form of B.54. -/
theorem finiteHolder_interpolation_two_three
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a t : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ht : ∀ i ∈ s, 0 ≤ t i) :
    (∑ i ∈ s, a i * (t i)^2) ≤
      (∑ i ∈ s, a i) ^ ((3 : ℝ)⁻¹) *
        (∑ i ∈ s, a i * (t i)^3) ^ (2 / 3 : ℝ) := by
  have H := Real.inner_le_Lp_mul_Lq s
    (fun i => (a i) ^ ((3 : ℝ)⁻¹))
    (fun i => (a i * (t i)^3) ^ (2 / 3 : ℝ))
    (p := (3 : ℝ)) (q := (3 / 2 : ℝ))
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
  rw [show (∑ i ∈ s, |a i ^ (3 : ℝ)⁻¹| ^ (3 : ℝ)) =
      ∑ i ∈ s, a i by
    apply Finset.sum_congr rfl
    intro i hi
    rw [abs_of_nonneg (Real.rpow_nonneg (ha i hi) _), ← Real.rpow_mul]
    · norm_num
    · exact ha i hi,
    show (∑ i ∈ s, |(a i * (t i)^3) ^ (2 / 3 : ℝ)| ^ (3 / 2 : ℝ)) =
      ∑ i ∈ s, a i * (t i)^3 by
    apply Finset.sum_congr rfl
    intro i hi
    have hait : 0 ≤ a i * (t i)^3 :=
      mul_nonneg (ha i hi) (pow_nonneg (ht i hi) 3)
    rw [abs_of_nonneg (Real.rpow_nonneg hait _), ← Real.rpow_mul]
    · norm_num
    · exact hait] at H
  norm_num at H
  calc
    _ = ∑ i ∈ s,
        (a i) ^ ((3 : ℝ)⁻¹) *
          (a i * (t i)^3) ^ (2 / 3 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (rpow_interpolation_term (a i) (t i) (ha i hi) (ht i hi)).symm
    _ ≤ _ := by convert H using 1 <;> norm_num

lemma childPQAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    0 ≤ childPQAt R z x := by
  unfold childPQAt
  exact Finset.sum_nonneg fun c hc => mul_nonneg
    (rootedOccupationProbabilityAt_pos R z hz c).le
    (rootedVacancyProbabilityAt_pos_local R z hz c).le

lemma childCubicAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    0 ≤ childCubicAt R z hz x := by
  unfold childCubicAt
  exact Finset.sum_nonneg fun c hc => mul_nonneg
    (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le)
    (pow_nonneg (abs_nonneg _) 3)

/-- B.54: child-energy interpolation. -/
theorem childEnergyAt_le_rpow_childPQ_mul_childCubic_B54
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    childEnergyAt R z hz x ≤
      (childPQAt R z x) ^ ((3 : ℝ)⁻¹) *
        (childCubicAt R z hz x) ^ (2 / 3 : ℝ) := by
  unfold childEnergyAt childPQAt childCubicAt hAt
  rw [show (∑ c ∈ R.children (G := G) x,
      rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c *
        rootedDisplacementAt R z hz c ^ 2) =
      ∑ c ∈ R.children (G := G) x,
        (rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c) *
          |rootedDisplacementAt R z hz c|^2 by
    apply Finset.sum_congr rfl
    intro c hc
    rw [sq_abs]]
  exact finiteHolder_interpolation_two_three
    (R.children (G := G) x)
    (fun c => rootedOccupationProbabilityAt R z c * rootedVacancyProbabilityAt R z c)
    (fun c => |rootedDisplacementAt R z hz c|)
    (fun c hc => mul_nonneg
      (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le)
    (fun c hc => abs_nonneg _)

/-- Exact one-variable maximum used in B.55:
`e⁻ᵗ t^(2/3) ≤ (2/(3e))^(2/3)` for `t ≥ 0`. -/
theorem exp_neg_mul_rpow_two_thirds_le (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t) * t ^ (2 / 3 : ℝ) ≤
      (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ) := by
  let y : ℝ := 3 * t / 2
  have hy : 0 ≤ y := by
    dsimp [y]
    positivity
  have hmax : y * Real.exp (-y) ≤ Real.exp (-1) :=
    Real.mul_exp_neg_le_exp_neg_one y
  have hmax0 : 0 ≤ y * Real.exp (-y) :=
    mul_nonneg hy (Real.exp_pos _).le
  have hpow :
      (y * Real.exp (-y)) ^ (2 / 3 : ℝ) ≤
        (Real.exp (-1)) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hmax0 hmax (by norm_num)
  rw [Real.mul_rpow hy (Real.exp_pos _).le] at hpow
  rw [← Real.exp_mul] at hpow
  calc
    Real.exp (-t) * t ^ (2 / 3 : ℝ) =
        (2 / 3 : ℝ) ^ (2 / 3 : ℝ) *
          (y ^ (2 / 3 : ℝ) * Real.exp (-y * (2 / 3 : ℝ))) := by
      have htScale : t = (2 / 3 : ℝ) * y := by
        dsimp [y]
        ring
      have hnegScale : -t = -y * (2 / 3 : ℝ) := by
        rw [htScale]
        ring
      calc
        Real.exp (-t) * t ^ (2 / 3 : ℝ) =
            Real.exp (-t) * ((2 / 3 : ℝ) * y) ^ (2 / 3 : ℝ) := by
          rw [htScale]
        _ = Real.exp (-t) *
            ((2 / 3 : ℝ) ^ (2 / 3 : ℝ) * y ^ (2 / 3 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2 / 3) hy]
        _ = (2 / 3 : ℝ) ^ (2 / 3 : ℝ) *
            (y ^ (2 / 3 : ℝ) * Real.exp (-y * (2 / 3 : ℝ))) := by
          rw [hnegScale]
          ring
    _ ≤ (2 / 3 : ℝ) ^ (2 / 3 : ℝ) *
          (Real.exp (-1)) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2 / 3) _)
    _ = (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.mul_rpow
        (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (Real.exp_pos (-1)).le]
      congr 1
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero]

/-- The exact absolute constant `C₀` from B.55. -/
noncomputable def lowActivityC0 : ℝ :=
  (3 / 2 : ℝ) * (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ)

lemma lowActivityC0_pos : 0 < lowActivityC0 := by
  unfold lowActivityC0
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (div_pos (by norm_num) (mul_pos (by norm_num) (Real.exp_pos 1))) _)

lemma lowActivityC0_nonneg : 0 ≤ lowActivityC0 := lowActivityC0_pos.le

lemma childPQAt_le_sum_childOccupation
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    childPQAt R z x ≤
      ∑ c ∈ R.children (G := G) x, rootedOccupationProbabilityAt R z c := by
  unfold childPQAt
  apply Finset.sum_le_sum
  intro c hc
  have hp := (rootedOccupationProbabilityAt_pos R z hz c).le
  have hq := (rootedVacancyProbabilityAt_pos_local R z hz c).le
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz c
  have hq1 : rootedVacancyProbabilityAt R z c ≤ 1 := by linarith
  exact mul_le_of_le_one_right hp hq1

lemma childEnergyAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    0 ≤ childEnergyAt R z hz x := by
  unfold childEnergyAt hAt
  exact Finset.sum_nonneg fun c hc => mul_nonneg
    (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
      (rootedVacancyProbabilityAt_pos_local R z hz c).le)
    (sq_nonneg _)

lemma varianceWeightAt_le_occupation
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (x : V) :
    varianceWeightAt R z hz x ≤ rootedOccupationProbabilityAt R z x := by
  have ha0 := (parentAbsentProbabilityAt_pos hG R z hz x).le
  have ha1 := parentAbsentProbabilityAt_le_one R z hz x
  have hp := (rootedOccupationProbabilityAt_pos R z hz x).le
  have hq := (rootedVacancyProbabilityAt_pos_local R z hz x).le
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz x
  have hq1 : rootedVacancyProbabilityAt R z x ≤ 1 := by linarith
  unfold varianceWeightAt
  calc
    parentAbsentProbabilityAt R z hz x * rootedOccupationProbabilityAt R z x *
        rootedVacancyProbabilityAt R z x ≤
      rootedOccupationProbabilityAt R z x * rootedVacancyProbabilityAt R z x := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_of_le_one_left hp ha1) hq
    _ ≤ rootedOccupationProbabilityAt R z x := mul_le_of_le_one_right hp hq1

/-- B.55: the local Hölder prefactor is uniformly bounded at activity `z ≤ 3/2`. -/
theorem varianceWeightAt_mul_childPQAt_rpow_two_thirds_le_B55
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (x : V) :
    varianceWeightAt R z hz x * (childPQAt R z x) ^ (2 / 3 : ℝ) ≤
      (3 / 2 : ℝ) * (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ) := by
  let t : ℝ := ∑ c ∈ R.children (G := G) x,
    rootedOccupationProbabilityAt R z c
  have ht : 0 ≤ t := by
    dsimp [t]
    exact Finset.sum_nonneg fun c hc =>
      (rootedOccupationProbabilityAt_pos R z hz c).le
  have hPQ0 := childPQAt_nonneg R z hz x
  have hPQle : childPQAt R z x ≤ t :=
    childPQAt_le_sum_childOccupation R z hz x
  have hrpow : (childPQAt R z x) ^ (2 / 3 : ℝ) ≤ t ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hPQ0 hPQle (by norm_num)
  have hw0 := varianceWeightAt_nonneg hG R z hz x
  have hwle : varianceWeightAt R z hz x ≤ (3 / 2 : ℝ) * Real.exp (-t) :=
    (varianceWeightAt_le_occupation hG R z hz x).trans
      (rootedOccupationProbabilityAt_le_ceiling_mul_exp_neg_child_sum
        hG R z (3 / 2) hz hz15 x)
  have hfirst :
      varianceWeightAt R z hz x * (childPQAt R z x) ^ (2 / 3 : ℝ) ≤
        ((3 / 2 : ℝ) * Real.exp (-t)) * t ^ (2 / 3 : ℝ) :=
    mul_le_mul hwle hrpow
      (Real.rpow_nonneg hPQ0 _) (mul_nonneg (by norm_num) (Real.exp_pos _).le)
  calc
    varianceWeightAt R z hz x * (childPQAt R z x) ^ (2 / 3 : ℝ) ≤
        ((3 / 2 : ℝ) * Real.exp (-t)) * t ^ (2 / 3 : ℝ) := hfirst
    _ = (3 / 2 : ℝ) * (Real.exp (-t) * t ^ (2 / 3 : ℝ)) := by ring
    _ ≤ (3 / 2 : ℝ) * (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left (exp_neg_mul_rpow_two_thirds_le t ht) (by norm_num)

/-- Pointwise consequence of B.54 and B.55 with the manuscript constant. -/
theorem varianceWeightAt_mul_childEnergyAt_sq_le_B55
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (x : V) :
    varianceWeightAt R z hz x * (childEnergyAt R z hz x) ^ 2 ≤
      ((3 / 2 : ℝ) * (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ)) *
        (childCubicAt R z hz x) ^ (4 / 3 : ℝ) := by
  have hE0 := childEnergyAt_nonneg R z hz x
  have h54 := childEnergyAt_le_rpow_childPQ_mul_childCubic_B54
    R z hz x
  have hsquare := pow_le_pow_left₀ hE0 h54 2
  have h55 := varianceWeightAt_mul_childPQAt_rpow_two_thirds_le_B55
    hG R z hz hz15 x
  have hB0 := childCubicAt_nonneg R z hz x
  calc
    varianceWeightAt R z hz x * (childEnergyAt R z hz x) ^ 2 ≤
        varianceWeightAt R z hz x *
          ((childPQAt R z x) ^ ((3 : ℝ)⁻¹) *
            (childCubicAt R z hz x) ^ (2 / 3 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare
        (varianceWeightAt_nonneg hG R z hz x)
    _ = (varianceWeightAt R z hz x *
          (childPQAt R z x) ^ (2 / 3 : ℝ)) *
        (childCubicAt R z hz x) ^ (4 / 3 : ℝ) := by
      rw [mul_pow]
      have hP0 := childPQAt_nonneg R z hz x
      rw [← Real.rpow_natCast ((childPQAt R z x) ^ ((3 : ℝ)⁻¹)) 2,
        ← Real.rpow_mul hP0, ← Real.rpow_natCast
          ((childCubicAt R z hz x) ^ (2 / 3 : ℝ)) 2,
        ← Real.rpow_mul hB0]
      norm_num
      ring
    _ ≤ ((3 / 2 : ℝ) * (2 / (3 * Real.exp 1) : ℝ) ^ (2 / 3 : ℝ)) *
        (childCubicAt R z hz x) ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right h55 (Real.rpow_nonneg hB0 _)

/-- B.56 availability lower bound at activity at most `3/2`. -/
theorem two_fifths_le_parentAbsentProbabilityAt_B56
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (u : V) :
    (2 / 5 : ℝ) ≤ parentAbsentProbabilityAt R z hz u := by
  have h := generatedAvailability_expectation_lower_bound
    hG R z (3 / 2) hz hz15 u
  unfold parentAbsentProbabilityAt
  convert h using 1 <;> norm_num

lemma childCubicAt_le_two_five_mul_child_weighted_cubic
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (x : V) :
    childCubicAt R z hz x ≤
      (5 / 2 : ℝ) * ∑ c ∈ R.children (G := G) x,
        varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3 := by
  unfold childCubicAt
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c hc
  let b : ℝ := rootedOccupationProbabilityAt R z c *
    rootedVacancyProbabilityAt R z c * |rootedDisplacementAt R z hz c| ^ 3
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg
      (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz c).le
        (rootedVacancyProbabilityAt_pos_local R z hz c).le)
      (pow_nonneg (abs_nonneg _) 3)
  have ha := two_fifths_le_parentAbsentProbabilityAt_B56 hG R z hz hz15 c
  have hmul := mul_le_mul_of_nonneg_right ha hb
  have hident :
      parentAbsentProbabilityAt R z hz c * b =
        varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3 := by
    unfold varianceWeightAt
    dsimp [b]
    ring
  rw [hident] at hmul
  nlinarith

/-- B.56: the total child cubic aggregate is controlled by the B.46 third moment. -/
theorem sum_childCubicAt_le_B56
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    (∑ x : V, childCubicAt R z hz x) ≤
      ((5 / 2 : ℝ) * lowActivityC3) * (hardCoreLaw G z hz).variance := by
  have hchild :
      (∑ x : V, ∑ c ∈ R.children (G := G) x,
        varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3) ≤
        ∑ c : V,
          varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3 := by
    apply sum_sum_children_le_sum hG R
    intro c
    exact mul_nonneg (varianceWeightAt_nonneg hG R z hz c)
      (pow_nonneg (abs_nonneg _) 3)
  calc
    (∑ x : V, childCubicAt R z hz x) ≤
        ∑ x : V, (5 / 2 : ℝ) * ∑ c ∈ R.children (G := G) x,
          varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3 := by
      exact Finset.sum_le_sum fun x hx =>
        childCubicAt_le_two_five_mul_child_weighted_cubic hG R z hz hz15 x
    _ = (5 / 2 : ℝ) * (∑ x : V, ∑ c ∈ R.children (G := G) x,
          varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3) := by
      rw [Finset.mul_sum]
    _ ≤ (5 / 2 : ℝ) * (∑ c : V,
          varianceWeightAt R z hz c * |rootedDisplacementAt R z hz c| ^ 3) :=
      mul_le_mul_of_nonneg_left hchild (by norm_num)
    _ = (5 / 2 : ℝ) *
        weightedMomentAt R z hz 3 (rootedDisplacementAt R z hz) := by
      rfl
    _ ≤ (5 / 2 : ℝ) *
        (lowActivityC3 * (hardCoreLaw G z hz).variance) :=
      mul_le_mul_of_nonneg_left
        (weightedMomentAt_displacement_three_le_C3_mul_variance_B46
          hG R z hz hz15) (by norm_num)
    _ = ((5 / 2 : ℝ) * lowActivityC3) *
        (hardCoreLaw G z hz).variance := by ring

lemma finset_sum_rpow_le_rpow_sum
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (p : ℝ) (hp : 1 ≤ p) :
    (∑ i ∈ s, (f i) ^ p) ≤ (∑ i ∈ s, f i) ^ p := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using Real.rpow_nonneg (show (0 : ℝ) ≤ 0 from le_rfl) p
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg hfs
      exact (add_le_add_right (ih hfs) _).trans
        (Real.add_rpow_le_rpow_add hfa hsum hp)

/-- B.57: the weighted child-energy sum is `O(V^(4/3))`, with exact constants. -/
theorem weightedMomentAt_childEnergy_two_le_B57
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    weightedMomentAt R z hz 2 (childEnergyAt R z hz) ≤
      lowActivityC0 *
        (((5 / 2 : ℝ) * lowActivityC3) *
          (hardCoreLaw G z hz).variance) ^ (4 / 3 : ℝ) := by
  have hpoint :
      weightedMomentAt R z hz 2 (childEnergyAt R z hz) ≤
        ∑ x : V, lowActivityC0 * (childCubicAt R z hz x) ^ (4 / 3 : ℝ) := by
    unfold weightedMomentAt
    apply Finset.sum_le_sum
    intro x hx
    rw [sq_abs]
    simpa [lowActivityC0] using
      varianceWeightAt_mul_childEnergyAt_sq_le_B55 hG R z hz hz15 x
  have hB0 : ∀ x : V, 0 ≤ childCubicAt R z hz x :=
    fun x => childCubicAt_nonneg R z hz x
  have hpowsum :
      (∑ x : V, (childCubicAt R z hz x) ^ (4 / 3 : ℝ)) ≤
        (∑ x : V, childCubicAt R z hz x) ^ (4 / 3 : ℝ) :=
    finset_sum_rpow_le_rpow_sum Finset.univ (childCubicAt R z hz)
      (fun x hx => hB0 x) (4 / 3 : ℝ) (by norm_num)
  have hBsum := sum_childCubicAt_le_B56 hG R z hz hz15
  have hsum0 : 0 ≤ ∑ x : V, childCubicAt R z hz x :=
    Finset.sum_nonneg fun x hx => hB0 x
  have hrpow :
      (∑ x : V, childCubicAt R z hz x) ^ (4 / 3 : ℝ) ≤
        (((5 / 2 : ℝ) * lowActivityC3) *
          (hardCoreLaw G z hz).variance) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow hsum0 hBsum (by norm_num)
  calc
    weightedMomentAt R z hz 2 (childEnergyAt R z hz) ≤
        ∑ x : V, lowActivityC0 * (childCubicAt R z hz x) ^ (4 / 3 : ℝ) :=
      hpoint
    _ = lowActivityC0 *
        (∑ x : V, (childCubicAt R z hz x) ^ (4 / 3 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ lowActivityC0 *
        (∑ x : V, childCubicAt R z hz x) ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hpowsum lowActivityC0_nonneg
    _ ≤ lowActivityC0 *
        (((5 / 2 : ℝ) * lowActivityC3) *
          (hardCoreLaw G z hz).variance) ^ (4 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left hrpow lowActivityC0_nonneg

lemma lowActivityCW_pos : 0 < lowActivityCW := by
  unfold lowActivityCW
  have hs : 0 ≤ Real.sqrt 15 := Real.sqrt_nonneg 15
  positivity

lemma lowActivityC3_pos : 0 < lowActivityC3 := by
  unfold lowActivityC3
  have hg : 0 < 1 - (15 / 16 : ℝ) ^ ((3 : ℝ)⁻¹) :=
    sub_pos.2 contractionCubeRoot_lt_one
  exact div_pos lowActivityCW_pos (pow_pos hg 3)

/-- Explicit positive absolute constant in B.58. -/
noncomputable def lowActivityCQ : ℝ :=
  (1 / (1 - Real.sqrt 15 / 4) ^ 2) * lowActivityC0 *
    (((5 / 2 : ℝ) * lowActivityC3) ^ (4 / 3 : ℝ))

lemma lowActivityCQ_pos : 0 < lowActivityCQ := by
  have hsqrt : Real.sqrt 15 / 4 < 1 := by
    rw [← contractionSquareRoot_eq]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hgap : 0 < 1 - Real.sqrt 15 / 4 := sub_pos.2 hsqrt
  unfold lowActivityCQ
  exact mul_pos
    (mul_pos (div_pos zero_lt_one (pow_pos hgap 2)) lowActivityC0_pos)
    (Real.rpow_pos_of_pos (mul_pos (by norm_num) lowActivityC3_pos) _)

lemma lowActivityCQ_nonneg : 0 ≤ lowActivityCQ := lowActivityCQ_pos.le

/-- B.58: predictable quadratic-variation variance concentration. -/
theorem scriptVVariance_le_CQ_mul_variance_rpow_B58
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) :
    scriptVVariance hG R z hz ≤
      lowActivityCQ * (hardCoreLaw G z hz).variance ^ (4 / 3 : ℝ) := by
  let Var : ℝ := (hardCoreLaw G z hz).variance
  have hVar : 0 ≤ Var := (hardCoreLaw G z hz).variance_nonneg
  have hK : 0 ≤ (5 / 2 : ℝ) * lowActivityC3 :=
    mul_nonneg (by norm_num) lowActivityC3_nonneg
  have h53 := scriptVVariance_le_weighted_childEnergy_B53 hG R z hz hz15
  have h57 := weightedMomentAt_childEnergy_two_le_B57 hG R z hz hz15
  have hgapCoeff : 0 ≤ 1 / (1 - Real.sqrt 15 / 4) ^ 2 :=
    div_nonneg zero_le_one (sq_nonneg _)
  calc
    scriptVVariance hG R z hz ≤
        (1 / (1 - Real.sqrt 15 / 4) ^ 2) *
          weightedMomentAt R z hz 2 (childEnergyAt R z hz) := h53
    _ ≤ (1 / (1 - Real.sqrt 15 / 4) ^ 2) *
        (lowActivityC0 * (((5 / 2 : ℝ) * lowActivityC3) * Var) ^
          (4 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h57 hgapCoeff
    _ = lowActivityCQ * Var ^ (4 / 3 : ℝ) := by
      rw [Real.mul_rpow hK hVar]
      unfold lowActivityCQ
      ring

lemma scriptV_normalized_meanSquare_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z)
    (hVar : 0 < (hardCoreLaw G z hz).variance) :
    UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
        (fun ω => |scriptV hG R z hz ω / (hardCoreLaw G z hz).variance - 1| ^ 2) =
      scriptVVariance hG R z hz / (hardCoreLaw G z hz).variance ^ 2 := by
  unfold scriptVVariance
  rw [scriptV_expectation_eq_variance_B49 hG R z hz]
  unfold UniformFourthMoment.lawExpectation
  calc
    (∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          |scriptV hG R z hz ω / (hardCoreLaw G z hz).variance - 1| ^ 2) =
      ∑ ω : BernoulliAssignment V,
        ((hardCoreBernoulliSeedLaw R z hz).probability ω *
          (scriptV hG R z hz ω - (hardCoreLaw G z hz).variance) ^ 2) /
            (hardCoreLaw G z hz).variance ^ 2 := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [sq_abs]
      field_simp [hVar.ne']
    _ = (∑ ω : BernoulliAssignment V,
        (hardCoreBernoulliSeedLaw R z hz).probability ω *
          (scriptV hG R z hz ω - (hardCoreLaw G z hz).variance) ^ 2) /
            (hardCoreLaw G z hz).variance ^ 2 := by
      rw [Finset.sum_div]

/-- Normalized mean-square version of B.58, directly usable on rows with
positive variance tending to infinity. -/
theorem scriptV_normalized_meanSquare_le_B58
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2)
    (hVar : 0 < (hardCoreLaw G z hz).variance) :
    UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
        (fun ω => |scriptV hG R z hz ω / (hardCoreLaw G z hz).variance - 1| ^ 2) ≤
      lowActivityCQ * (hardCoreLaw G z hz).variance ^ (-2 / 3 : ℝ) := by
  let Var : ℝ := (hardCoreLaw G z hz).variance
  have h58 := scriptVVariance_le_CQ_mul_variance_rpow_B58 hG R z hz hz15
  have hnorm := scriptV_normalized_meanSquare_eq hG R z hz hVar
  have hdiv :
      scriptVVariance hG R z hz / Var ^ 2 ≤
        (lowActivityCQ * Var ^ (4 / 3 : ℝ)) / Var ^ 2 :=
    div_le_div_of_nonneg_right h58 (sq_nonneg Var)
  calc
    UniformFourthMoment.lawExpectation (hardCoreBernoulliSeedLaw R z hz)
        (fun ω => |scriptV hG R z hz ω / (hardCoreLaw G z hz).variance - 1| ^ 2) =
        scriptVVariance hG R z hz / Var ^ 2 := hnorm
    _ ≤ (lowActivityCQ * Var ^ (4 / 3 : ℝ)) / Var ^ 2 := hdiv
    _ = lowActivityCQ * Var ^ (-2 / 3 : ℝ) := by
      rw [mul_div_assoc]
      congr 1
      calc
        Var ^ (4 / 3 : ℝ) / Var ^ 2 =
            Var ^ (4 / 3 : ℝ) / Var ^ (2 : ℝ) := by
          congr 1
          exact (Real.rpow_natCast Var 2).symm
        _ = Var ^ ((4 / 3 : ℝ) - 2) := (Real.rpow_sub hVar _ _).symm
        _ = Var ^ (-2 / 3 : ℝ) := by norm_num


end ActualLowActivityCLT

end

end Erdos993.Forest
