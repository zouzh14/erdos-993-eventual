import Erdos993.Forest.AppendixDFellerFailure
import Erdos993.Forest.ActualLowActivityCLTArray

/-!
# Appendix D: retained martingale triangular array

This module starts the D.8 triangular-array construction.  It masks the exact
parent-first normalized hard-core seed Doob array by an arbitrary deterministic
retained vertex set.  The sample law is always the seed coupling of the original
global hard-core law; no retained subgraph is assigned a canonical law.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace Erdos993
namespace Forest

noncomputable section

open Erdos993.ActualRootedVariance
open Erdos993.ActualMartingaleProjection
open Erdos993.UniformFourthMoment
open Erdos993.Forest.MartingaleArrayCLT
open Erdos993.Forest.ActualLowActivityCLT

universe u

noncomputable local instance retainedArrayDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

lemma varyingSpace_slutsky_add
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : (n : ℕ) → Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (X E : (n : ℕ) → Ω n → ℝ) {Ω' : Type*} [MeasurableSpace Ω']
    (Z : Ω' → ℝ) (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (hXZ : TendstoInDistribution X atTop Z μ μ')
    (hE : TendstoInProbabilityVarying Ω μ E atTop 0)
    (hEmeas : ∀ n, AEMeasurable (E n) (μ n)) :
    TendstoInDistribution (fun n ω => X n ω + E n ω) atTop Z μ μ' := by
  let Y : (n : ℕ) → Ω n → ℝ := fun n ω => X n ω + E n ω
  have hY : ∀ n, AEMeasurable (Y n) (μ n) := fun n =>
    (hXZ.forall_aemeasurable n).add (hEmeas n)
  refine ⟨hY, hXZ.aemeasurable_limit, ?_⟩
  suffices ∀ (F : ℝ → ℝ) (hF_bounded : ∃ C, ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n => ∫ x, F x ∂((μ n).map (Y n))) atTop
        (𝓝 (∫ x, F x ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip 0
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have hprobMap n : IsProbabilityMeasure ((μ n).map (Y n)) :=
      Measure.isProbabilityMeasure_map (hY n)
    have hprobLim : IsProbabilityMeasure (μ'.map Z) :=
      Measure.isProbabilityMeasure_map hXZ.aemeasurable_limit
    simpa using tendsto_const_nhds
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop,
      |∫ x, F x ∂((μ n).map (Y n)) - ∫ x, F x ∂(μ'.map Z)| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ x, F x ∂((μ n).map (Y n)) - ∫ x, F x ∂(μ'.map Z)|
      ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ x, F x ∂((μ n).map (X n)) - ∫ x, F x ∂(μ'.map Z)| := by
    refine (abs_sub_le (∫ x, F x ∂((μ n).map (Y n)))
      (∫ x, F x ∂((μ n).map (X n))) (∫ x, F x ∂(μ'.map Z))).trans ?_
    gcongr
    have hdiff : AEMeasurable (fun x => Y n x - X n x) (μ n) :=
      (hY n).sub (hXZ.forall_aemeasurable n)
    have hnormdiff : AEMeasurable (fun x => ‖Y n x - X n x‖) (μ n) := hdiff.norm
    have h_int_Y : Integrable (fun x => F (Y n x)) (μ n) := by
      refine Integrable.of_bound
        (hF_cont.aestronglyMeasurable.comp_aemeasurable (hY n))
        (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (Y n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Y n a)) (F 0)).trans hF_bounded
    have h_int_X : Integrable (fun x => F (X n x)) (μ n) := by
      refine Integrable.of_bound
        (hF_cont.aestronglyMeasurable.comp_aemeasurable
          (hXZ.forall_aemeasurable n))
        (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
      specialize hF_bounded (X n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (X n a)) (F 0)).trans hF_bounded
    have h_int_sub : Integrable (fun a => ‖F (Y n a) - F (X n a)‖) (μ n) := by
      exact (h_int_Y.sub h_int_X).norm
    rw [integral_map (hY n) hF_cont.aestronglyMeasurable,
      integral_map (hXZ.forall_aemeasurable n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc
      ‖∫ a, F (Y n a) - F (X n a) ∂μ n‖ ≤
          ∫ a, ‖F (Y n a) - F (X n a)‖ ∂μ n := norm_integral_le_integral_norm _
      _ = ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, ‖F (Y n a) - F (X n a)‖ ∂μ n
          + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, ‖F (Y n a) - F (X n a)‖ ∂μ n := by
        symm
        simp_rw [← not_lt]
        refine integral_add_compl₀ ?_ h_int_sub
        exact nullMeasurableSet_lt hnormdiff aemeasurable_const
      _ ≤ ∫ a in {x | ‖Y n x - X n x‖ < ε / 2}, L * (ε / 2) ∂μ n
          + ∫ a in {x | ε / 2 ≤ ‖Y n x - X n x‖}, M ∂μ n := by
        gcongr ?_ + ?_
        · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
          · exact nullMeasurableSet_lt hnormdiff aemeasurable_const
          · exact fun x hx => hF_lip.norm_sub_le_of_le hx.le
        · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
          rw [← dist_eq_norm]
          convert hF_bounded _ _
      _ = L * (ε / 2) * (μ n).real {x | ‖Y n x - X n x‖ < ε / 2}
          + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
          Set.univ_inter, smul_eq_mul]
        ring
      _ ≤ L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖} := by
        rw [mul_assoc]
        gcongr
        grw [measureReal_le_one, mul_one]
  have hprobReal : Tendsto (fun n => (μ n).real
      {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}) atTop (𝓝 0) := by
    have hp := hE (ε / 2) (by positivity)
    have hp' : Tendsto (fun n => μ n {ω | ε / 2 ≤ |E n ω - 0|}) atTop (𝓝 0) := hp
    have hr := (show Tendsto ENNReal.toReal (𝓝 (0 : ENNReal)) (𝓝 (0 : ℝ)) from
      ENNReal.continuousAt_toReal ENNReal.zero_ne_top).comp hp'
    simpa [Y, Real.norm_eq_abs] using hr
  have h_tendsto : Tendsto (fun n =>
      L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
        + |∫ x, F x ∂((μ n).map (X n)) - ∫ x, F x ∂(μ'.map Z)|)
      atTop (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n =>
        L * (ε / 2) + M * (μ n).real {ω | ε / 2 ≤ ‖Y n ω - X n ω‖}
          + |∫ x, F x ∂((μ n).map (X n)) - ∫ x, F x ∂(μ'.map Z)|)
        atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ hprobReal)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · replace hXZ := hXZ.tendsto
      simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hXZ
      simpa [tendsto_iff_dist_tendsto_zero] using
        hXZ F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn
  exact (h_le n).trans_lt hn

variable (V : ℕ → Type u) [∀ n, Fintype (V n)]
variable (G : (n : ℕ) → SimpleGraph (V n))
variable (hG : ∀ n, (G n).IsAcyclic)
variable (z : ℕ → ℝ) (hz : ∀ n, 0 < z n)
variable (R : (n : ℕ) → ComponentRooting (G n))
variable (D : (n : ℕ) → Finset (V n))

/-- The normalized parent-first Doob array with entries outside `D n` set to
zero.  The row measure and filtration are inherited unchanged from the full
original-graph hard-core seed array. -/
noncomputable def retainedNormalizedHardCoreSeedArray :
    ArrayData (ActualSeedSpace V) :=
  { (normalizedHardCoreSeedArray V G hG z hz R) with
    increment := fun n k ω =>
      if parentFirstEquiv (R n) k ∈ D n then
        (normalizedHardCoreSeedArray V G hG z hz R).increment n k ω else 0 }

noncomputable instance retainedNormalizedHardCoreSeedArray_isProbabilityMeasure
    (n : ℕ) :
    IsProbabilityMeasure
      ((retainedNormalizedHardCoreSeedArray V G hG z hz R D).probability n) := by
  change IsProbabilityMeasure
    ((normalizedHardCoreSeedArray V G hG z hz R).probability n)
  infer_instance

/-- The conditional variance of a retained entry is the corresponding full
Doob conditional variance, while an omitted entry contributes zero. -/
theorem retainedNormalizedHardCoreSeedArray_conditionalVariance_ae_eq
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n)
    (k : Fin (Fintype.card (V n))) :
    (retainedNormalizedHardCoreSeedArray V G hG z hz R D).conditionalVariance n k
      =ᵐ[actualSeedMeasure V G z hz R n]
    fun ω => if parentFirstEquiv (R n) k ∈ D n then
      finiteDoobMean
        (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
        (fun η => (finiteDoobIncrement
          (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k η) ^ 2)
        (parentFirstEquiv (R n)) k.castSucc ω /
          hardCoreVariance V G z hz n else 0 := by
  by_cases hk : parentFirstEquiv (R n) k ∈ D n
  · have hEq :
        (retainedNormalizedHardCoreSeedArray V G hG z hz R D).conditionalVariance n k =
          (normalizedHardCoreSeedArray V G hG z hz R).conditionalVariance n k := by
      funext ω
      unfold ArrayData.conditionalVariance retainedNormalizedHardCoreSeedArray
      simp only [hk, if_true]
    rw [hEq]
    simpa [hk] using
      (normalizedHardCoreSeedArray_conditionalVariance_ae_eq
        V G hG z hz R n hVar k)
  · have hEq :
        (retainedNormalizedHardCoreSeedArray V G hG z hz R D).conditionalVariance n k =
          (0 : ActualSeedSpace V n → ℝ) := by
      funext ω
      unfold ArrayData.conditionalVariance retainedNormalizedHardCoreSeedArray
      simp only [hk, if_false]
      have hsquare : (fun _x : ActualSeedSpace V n => (0 : ℝ) ^ 2) = 0 := by
        funext x
        norm_num
      rw [hsquare, condExp_zero]
    rw [hEq]
    exact Filter.Eventually.of_forall (fun ω => by simp [hk])

/-- Deterministic masking preserves the martingale-difference-array
properties. -/
theorem retainedNormalizedHardCoreSeedArray_isMartingaleDifferenceArray :
    (retainedNormalizedHardCoreSeedArray V G hG z hz R D).IsMartingaleDifferenceArray := by
  let A := normalizedHardCoreSeedArray V G hG z hz R
  have hA := normalizedHardCoreSeedArray_isMartingaleDifferenceArray V G hG z hz R
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    unfold retainedNormalizedHardCoreSeedArray
    change StronglyMeasurable[
      (normalizedHardCoreSeedArray V G hG z hz R).filtration n (k.val + 1)]
      (fun ω => if parentFirstEquiv (R n) k ∈ D n then
        (normalizedHardCoreSeedArray V G hG z hz R).increment n k ω else 0)
    by_cases hk : parentFirstEquiv (R n) k ∈ D n
    · simpa [A, hk] using hA.stronglyMeasurable n k
    · simp only [hk, if_false]
      exact stronglyMeasurable_const
  · intro n k
    unfold retainedNormalizedHardCoreSeedArray
    change MemLp
      (fun ω => if parentFirstEquiv (R n) k ∈ D n then
        (normalizedHardCoreSeedArray V G hG z hz R).increment n k ω else 0)
      2 ((normalizedHardCoreSeedArray V G hG z hz R).probability n)
    by_cases hk : parentFirstEquiv (R n) k ∈ D n
    · simpa [A, hk] using hA.memLp_two n k
    · simp [hk]
  · intro n k
    unfold retainedNormalizedHardCoreSeedArray
    change ((normalizedHardCoreSeedArray V G hG z hz R).probability n)[
      (fun ω => if parentFirstEquiv (R n) k ∈ D n then
        (normalizedHardCoreSeedArray V G hG z hz R).increment n k ω else 0) |
        (normalizedHardCoreSeedArray V G hG z hz R).filtration n k.val] =ᵐ[
          (normalizedHardCoreSeedArray V G hG z hz R).probability n] 0
    by_cases hk : parentFirstEquiv (R n) k ∈ D n
    · simpa [A, hk] using hA.condExp_zero n k
    · simp only [hk, if_false]
      have hzero : (fun _ω : ActualSeedSpace V n => (0 : ℝ)) = 0 := rfl
      rw [hzero, condExp_zero]

/-- The retained array's generic predictable quadratic variation is the
retained sum of the exact availability-energy terms.  This is the termwise
bridge needed to identify the array quantity with D.57. -/
theorem retainedNormalizedHardCoreSeedArray_predictableQuadraticVariation_ae_eq
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n) :
    (retainedNormalizedHardCoreSeedArray V G hG z hz R D).predictableQuadraticVariation n
      =ᵐ[actualSeedMeasure V G z hz R n]
    fun ω => ∑ k : Fin (Fintype.card (V n)),
      if parentFirstEquiv (R n) k ∈ D n then
        generatedAvailabilityReal (R n) ω (parentFirstEquiv (R n) k) *
          rootedEnergyAt (R n) (z n) (hz n) (parentFirstEquiv (R n) k) /
            hardCoreVariance V G z hz n
      else 0 := by
  have hterm : ∀ k : Fin (Fintype.card (V n)),
      (retainedNormalizedHardCoreSeedArray V G hG z hz R D).conditionalVariance n k
        =ᵐ[actualSeedMeasure V G z hz R n]
      fun ω => if parentFirstEquiv (R n) k ∈ D n then
        finiteDoobMean
          (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
          (fun η => (finiteDoobIncrement
            (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
            (fun ξ => generatedCountReal (hG n) (R n) ξ)
            (parentFirstEquiv (R n)) k η) ^ 2)
          (parentFirstEquiv (R n)) k.castSucc ω /
            hardCoreVariance V G z hz n else 0 :=
    fun k => retainedNormalizedHardCoreSeedArray_conditionalVariance_ae_eq
      V G hG z hz R D n hVar k
  have hall : ∀ᵐ ω ∂actualSeedMeasure V G z hz R n,
      ∀ k : Fin (Fintype.card (V n)),
        (retainedNormalizedHardCoreSeedArray V G hG z hz R D).conditionalVariance n k ω =
          (if parentFirstEquiv (R n) k ∈ D n then
            finiteDoobMean
              (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
              (fun η => (finiteDoobIncrement
                (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
                (fun ξ => generatedCountReal (hG n) (R n) ξ)
                (parentFirstEquiv (R n)) k η) ^ 2)
              (parentFirstEquiv (R n)) k.castSucc ω /
                hardCoreVariance V G z hz n else 0) :=
    (ae_all_iff).2 hterm
  filter_upwards [hall] with ω hω
  unfold ArrayData.predictableQuadraticVariation
  apply Finset.sum_congr rfl
  intro k hk
  rw [hω k]
  by_cases hmem : parentFirstEquiv (R n) k ∈ D n
  · simp only [hmem, if_true]
    rw [finiteDoobMean_increment_sq_current (hG n) (R n) (z n) (hz n) k ω]
  · simp [hmem]

/-- The unconditional second moment of one exact seed Doob increment is
the corresponding original-law vertex variance contribution. -/
theorem finiteDoobIncrement_sq_expectation_eq_vertexVarianceContribution
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (k : Fin (Fintype.card W)) :
    (∑ η, (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability η *
      (finiteDoobIncrement
        (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability
        (fun ξ => generatedCountReal C.isForest Q ξ)
        (parentFirstEquiv Q) k η)^2) =
      Q.vertexVarianceContribution (G := H) C (parentFirstEquiv Q k) := by
  rw [finiteDoobIncrement_sq_expectation_eq_availability_energy
    C.isForest Q C.activity C.activity_pos k]
  rw [generatedAvailability_expectation_eq_parentAbsentProbability C Q]
  simp only [rootedEnergyAt, rootedOccupationProbabilityAt,
    rootedVacancyProbabilityAt, rootedDisplacementAt,
    ComponentRooting.vertexVarianceContribution,
    ComponentRooting.occupationProbability, ComponentRooting.vacancyProbability,
    ComponentRooting.conditionalMeanDifference,
    rootedAAt, rootedPAt, rootedQAt,
    ComponentRooting.rootedA, ComponentRooting.rootedP, ComponentRooting.rootedQ,
    ComponentRooting.conditionalMeanDifferenceAt,
    ComponentRooting.occupiedMeanAt, ComponentRooting.vacantMeanAt,
    ComponentRooting.occupiedMean, ComponentRooting.vacantMean]
  ring

/-- A normalized exact increment exceeding `epsilon` can only occur at a
vertex whose deterministic rooted displacement exceeds `epsilon * sqrt V`.
The truncated square is then bounded by the unnormalized square divided by
`V`. -/
theorem normalized_finiteDoobIncrement_truncation_le_displacement_selector
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (epsilon : ℝ) (k : Fin (Fintype.card W)) (ω : BernoulliAssignment W) :
    let Delta := finiteDoobIncrement
      (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability
      (fun ξ => generatedCountReal C.isForest Q ξ)
      (parentFirstEquiv Q) k ω
    let d := rootedDisplacementAt Q C.activity C.activity_pos (parentFirstEquiv Q k)
    (if epsilon < |Delta / Real.sqrt C.variance| then
        (Delta / Real.sqrt C.variance)^2 else 0) ≤
      if epsilon * Real.sqrt C.variance < |d| then
        Delta^2 / C.variance else 0 := by
  dsimp only
  let Delta := finiteDoobIncrement
      (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability
      (fun ξ => generatedCountReal C.isForest Q ξ)
      (parentFirstEquiv Q) k ω
  let d := rootedDisplacementAt Q C.activity C.activity_pos (parentFirstEquiv Q k)
  have hV := ComponentRooting.canonicalFirstRecovery_variance_pos C
  have hsqrt : 0 < Real.sqrt C.variance := Real.sqrt_pos.2 hV
  have hsqrt_sq : (Real.sqrt C.variance)^2 = C.variance := Real.sq_sqrt hV.le
  have habs : |Delta| ≤ |d| := by
    exact finiteDoobIncrement_abs_le_rootedDisplacementAt
      C.isForest Q C.activity C.activity_pos k ω
  by_cases htr : epsilon < |Delta / Real.sqrt C.variance|
  · rw [if_pos htr]
    have hlarge : epsilon * Real.sqrt C.variance < |d| := by
      calc
        epsilon * Real.sqrt C.variance <
            |Delta / Real.sqrt C.variance| * Real.sqrt C.variance :=
          mul_lt_mul_of_pos_right htr hsqrt
        _ = |Delta| := by
          rw [abs_div, abs_of_pos hsqrt]
          field_simp [hsqrt.ne']
        _ ≤ |d| := habs
    rw [if_pos hlarge]
    rw [div_pow, hsqrt_sq]
  · rw [if_neg htr]
    split
    · positivity
    · rfl

/-- Summed unconditional truncation estimate: the normalized retained-row
Lindeberg mass is bounded by the D.6 large-displacement contribution. -/
theorem sum_normalized_retained_increment_truncation_le_largeDisplacement
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (D : Finset W) (epsilon : ℝ) :
    (∑ k : Fin (Fintype.card W),
      ∑ ω : BernoulliAssignment W,
        (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability ω *
          (if parentFirstEquiv Q k ∈ D then
            let Delta := finiteDoobIncrement
              (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability
              (fun ξ => generatedCountReal C.isForest Q ξ)
              (parentFirstEquiv Q) k ω
            if epsilon < |Delta / Real.sqrt C.variance| then
              (Delta / Real.sqrt C.variance)^2 else 0
          else 0)) ≤
      Q.largeDisplacementContributionOn (G := H) C D
        (epsilon * Real.sqrt C.variance) / C.variance := by
  let mu := (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability
  let Delta : Fin (Fintype.card W) → BernoulliAssignment W → ℝ := fun k ω =>
    finiteDoobIncrement mu (fun ξ => generatedCountReal C.isForest Q ξ)
      (parentFirstEquiv Q) k ω
  let d : Fin (Fintype.card W) → ℝ := fun k =>
    rootedDisplacementAt Q C.activity C.activity_pos (parentFirstEquiv Q k)
  calc
    _ ≤ ∑ k : Fin (Fintype.card W),
        ∑ ω : BernoulliAssignment W, mu ω *
          (if parentFirstEquiv Q k ∈ D then
            if epsilon * Real.sqrt C.variance < |d k| then
              (Delta k ω)^2 / C.variance else 0
          else 0) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ω hω
      dsimp only [mu, Delta]
      apply mul_le_mul_of_nonneg_left
      · by_cases hkD : parentFirstEquiv Q k ∈ D
        · simp only [hkD, if_true]
          exact normalized_finiteDoobIncrement_truncation_le_displacement_selector
            C Q epsilon k ω
        · simp [hkD]
      · exact (hardCoreBernoulliSeedLaw Q C.activity C.activity_pos).probability_nonneg ω
    _ = ∑ k : Fin (Fintype.card W),
        if parentFirstEquiv Q k ∈ D then
          if epsilon * Real.sqrt C.variance < |d k| then
            Q.vertexVarianceContribution (G := H) C (parentFirstEquiv Q k) /
              C.variance else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkD : parentFirstEquiv Q k ∈ D
      · simp only [hkD, if_true]
        by_cases hd : epsilon * Real.sqrt C.variance < |d k|
        · simp only [hd, if_true]
          rw [show (∑ ω : BernoulliAssignment W,
              mu ω * ((Delta k ω)^2 / C.variance)) =
              (∑ ω : BernoulliAssignment W, mu ω * (Delta k ω)^2) /
                C.variance by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro ω hω
            ring]
          exact congrArg (fun x => x / C.variance)
            (finiteDoobIncrement_sq_expectation_eq_vertexVarianceContribution C Q k)
        · simp [hd]
      · simp [hkD]
    _ = Q.largeDisplacementContributionOn (G := H) C D
        (epsilon * Real.sqrt C.variance) / C.variance := by
      rw [show (∑ k : Fin (Fintype.card W),
          if parentFirstEquiv Q k ∈ D then
            if epsilon * Real.sqrt C.variance < |d k| then
              Q.vertexVarianceContribution (G := H) C (parentFirstEquiv Q k) /
                C.variance else 0
          else 0) =
          ∑ u : W, if u ∈ D then
            if epsilon * Real.sqrt C.variance <
                |Q.conditionalMeanDifference (G := H) C u| then
              Q.vertexVarianceContribution (G := H) C u / C.variance else 0
            else 0 by
        simpa only [d, rootedDisplacementAt,
          ComponentRooting.conditionalMeanDifference,
          rootedAAt, rootedPAt, rootedQAt,
          ComponentRooting.rootedA, ComponentRooting.rootedP, ComponentRooting.rootedQ,
          ComponentRooting.conditionalMeanDifferenceAt,
          ComponentRooting.occupiedMeanAt, ComponentRooting.vacantMeanAt,
          ComponentRooting.occupiedMean, ComponentRooting.vacantMean] using
            (Equiv.sum_comp (parentFirstEquiv Q)
              (fun u => if u ∈ D then
                if epsilon * Real.sqrt C.variance <
                    |Q.conditionalMeanDifference (G := H) C u| then
                  Q.vertexVarianceContribution (G := H) C u / C.variance else 0
                else 0))]
      unfold ComponentRooting.largeDisplacementContributionOn
      rw [Finset.sum_ite_mem]
      simp only [Finset.univ_inter]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases huD : u ∈ D <;>
        by_cases hdu : epsilon * Real.sqrt C.variance <
          |Q.conditionalMeanDifference (G := H) C u| <;> simp [huD, hdu]

/-- Seed availability is pointwise the original-configuration parent-vacancy
indicator after applying the exact global hard-core coupling. -/
theorem generatedAvailabilityReal_eq_parentAbsentIndicator
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (ω : BernoulliAssignment W) (v : W) :
    generatedAvailabilityReal Q ω v =
      1 - parentOccupationIndicator Q (generatedIndependentSet C.isForest Q ω) v := by
  classical
  by_cases hv : v = Q.rootOf (G := H) v
  · rw [parentOccupationIndicator_root Q _ hv]
    have hA : generatedAvailabilityReal Q ω v = 1 := by
      unfold generatedAvailabilityReal generatedAvailable
      rw [if_pos]
      exact decide_eq_true (by
        intro p hp
        exact (Q.not_isChild_of_eq_root (G := H) hv hp).elim)
    rw [hA]
    norm_num
  · let p := Q.selectedParent (G := H) v hv
    have hpv : Q.IsChild (G := H) p v := Q.selectedParent_isChild (G := H) v hv
    rw [parentOccupationIndicator_eq_selectedParent C Q _ hv]
    unfold occupationIndicator generatedAvailabilityReal
    rw [generatedAvailable_eq_not_occupation_of_isChild C.isForest Q hpv]
    simp only [generatedIndependentSet_val, generatedFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    cases hocc : generatedOccupation Q ω p <;> simp [hocc]

/-- The seed innovation agrees pointwise with the original-configuration innovation under the exact global coupling. -/
theorem generatedEtaAt_eq_eta_generatedIndependentSet
    {W : Type*} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (ω : BernoulliAssignment W) (v : W) :
    generatedEtaAt Q C.activity ω v =
      eta C Q (generatedIndependentSet C.isForest Q ω) v := by
  classical
  rw [eta]
  have hA := generatedAvailabilityReal_eq_parentAbsentIndicator C Q ω v
  have hpq := rootedOccupationProbabilityAt_add_vacancy Q C.activity C.activity_pos v
  unfold generatedEtaAt
  rw [hA]
  unfold occupationIndicator
  simp only [generatedIndependentSet_val, generatedFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [generatedOccupation_eq_seed_and_available]
  unfold generatedAvailabilityReal at hA
  cases hs : ω v <;> cases ha : generatedAvailable Q ω v <;>
    simp [ha] at hA <;>
    rw [← hA] <;>
    simp [hs, ha, ComponentRooting.occupationProbability,
      ComponentRooting.rootedA, ComponentRooting.rootedP,
      rootedOccupationProbabilityAt, rootedAAt, rootedPAt] at hpq ⊢ <;> linarith

/-- The exact seed coupling pushes forward to the full original hard-core
configuration PMF.  This packages the already-proved fiber-mass identity at
configuration level. -/
theorem generatedIndependentSet_toPMF_map_of_fiberMass
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (hH : H.IsAcyclic) (Q : ComponentRooting H)
    (a : ℝ) (ha : 0 < a) :
    (generatedCountLaw hH Q a ha).toPMF.map (generatedIndependentSet hH Q) =
      (hardCoreLaw H a ha).toPMF := by
  apply PMF.ext
  intro I
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal,
      FiniteLatticeLaw.toPMF_apply_toReal]
    simpa [eq_comm] using
      (exactHardCoreConfigurationCoupling_of_fiberMass hH Q a ha I)
  · intro ω hω
    split_ifs <;> simp [PMF.apply_ne_top]

/-- Consequently the globally generated independent set has exactly the
original hard-core configuration law. -/
theorem generatedIndependentSet_hasLaw_hardCore_of_fiberMass
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (hH : H.IsAcyclic) (Q : ComponentRooting H)
    (a : ℝ) (ha : 0 < a) :
    HasLaw (generatedIndependentSet hH Q)
      (hardCoreLaw H a ha).toMeasure
      (generatedCountLaw hH Q a ha).toMeasure := by
  constructor
  · exact (measurable_of_finite _).aemeasurable
  · have hmeas : Measurable (generatedIndependentSet hH Q) :=
      measurable_of_finite _
    rw [FiniteLatticeLaw.toMeasure, PMF.toMeasure_map _ _ hmeas]
    rw [generatedIndependentSet_toPMF_map_of_fiberMass hH Q a ha]
    rfl

/-- The seed finite-law PMF and generated-count finite-law PMF agree on
their common Bernoulli sample space; their statistics differ, but their atom
weights do not. -/
theorem hardCoreBernoulliSeedLaw_toPMF_eq_generatedCountLaw_toPMF
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (hH : H.IsAcyclic) (Q : ComponentRooting H)
    (a : ℝ) (ha : 0 < a) :
    (hardCoreBernoulliSeedLaw Q a ha).toPMF =
      (generatedCountLaw hH Q a ha).toPMF := by
  apply PMF.ext
  intro ω
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  simp [FiniteLatticeLaw.toPMF_apply_toReal, generatedCountLaw]

/-- Configuration-level exact coupling stated on the actual Bernoulli seed
measure used by the triangular array. -/
theorem generatedIndependentSet_hasLaw_hardCoreSeed_of_fiberMass
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (hH : H.IsAcyclic) (Q : ComponentRooting H)
    (a : ℝ) (ha : 0 < a) :
    HasLaw (generatedIndependentSet hH Q)
      (hardCoreLaw H a ha).toMeasure
      (hardCoreBernoulliSeedLaw Q a ha).toMeasure := by
  have h0 := generatedIndependentSet_hasLaw_hardCore_of_fiberMass
    hH Q a ha
  constructor
  · exact (measurable_of_finite _).aemeasurable
  · rw [FiniteLatticeLaw.toMeasure,
      hardCoreBernoulliSeedLaw_toPMF_eq_generatedCountLaw_toPMF hH Q a ha]
    simpa [FiniteLatticeLaw.toMeasure] using h0.map_eq

/-- The retained availability-energy sum is literally D.57, evaluated on
the globally generated hard-core configuration. -/
theorem retainedSeedEnergySum_eq_predictableQuadraticVariation
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H)
    (E : Finset W) (ω : BernoulliAssignment W) :
    (∑ k : Fin (Fintype.card W),
      if parentFirstEquiv Q k ∈ E then
        generatedAvailabilityReal Q ω (parentFirstEquiv Q k) *
          rootedEnergyAt Q C.activity C.activity_pos (parentFirstEquiv Q k) /
            C.variance
      else 0) =
      Q.predictableQuadraticVariation (G := H) C E
        (generatedIndependentSet C.isForest Q ω) / C.variance := by
  let F : W → ℝ := fun v =>
    if v ∈ E then
      generatedAvailabilityReal Q ω v *
        rootedEnergyAt Q C.activity C.activity_pos v / C.variance
    else 0
  have hreindex : (∑ k : Fin (Fintype.card W), F (parentFirstEquiv Q k)) =
      ∑ v : W, F v := Equiv.sum_comp (parentFirstEquiv Q) F
  change (∑ k : Fin (Fintype.card W), F (parentFirstEquiv Q k)) = _
  rw [hreindex]
  dsimp only [F]
  rw [show (∑ v : W, if v ∈ E then
      generatedAvailabilityReal Q ω v *
        rootedEnergyAt Q C.activity C.activity_pos v / C.variance else 0) =
      (∑ v ∈ E, generatedAvailabilityReal Q ω v *
        rootedEnergyAt Q C.activity C.activity_pos v) / C.variance by
    rw [Finset.sum_div]
    simp]
  unfold ActualRootedVariance.ComponentRooting.predictableQuadraticVariation
  apply congrArg (fun x : ℝ => x / C.variance)
  apply Finset.sum_congr rfl
  intro v hv
  rw [generatedAvailabilityReal_eq_parentAbsentIndicator C Q ω v]
  change (1 - parentOccupationIndicator Q
      (generatedIndependentSet C.isForest Q ω) v) *
        Q.predictableQuadraticCoefficient (G := H) C v =
    Q.predictableQuadraticCoefficient (G := H) C v *
      (1 - parentOccupationIndicator Q
        (generatedIndependentSet C.isForest Q ω) v)
  ring

/-- At the original canonical activity, the arbitrary-activity local
occupation probability is definitionally the rooted original-law quantity. -/
theorem rootedOccupationProbabilityAt_eq_original
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H) (v : W) :
    rootedOccupationProbabilityAt Q C.activity v =
      Q.occupationProbability (G := H) C v := by
  rfl

/-- At the original canonical activity, the arbitrary-activity vacancy
probability is the rooted original-law quantity. -/
theorem rootedVacancyProbabilityAt_eq_original
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H) (v : W) :
    rootedVacancyProbabilityAt Q C.activity v =
      Q.vacancyProbability (G := H) C v := by
  rfl

/-- The seed-array displacement at the canonical activity is exactly the
original-law rooted displacement. -/
theorem rootedDisplacementAt_eq_original
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H) (v : W) :
    rootedDisplacementAt Q C.activity C.activity_pos v =
      Q.conditionalMeanDifference (G := H) C v := by
  rfl

/-- Hence the seed conditional energy is exactly the D.57 deterministic
quadratic coefficient, still at the original global canonical law. -/
theorem rootedEnergyAt_eq_predictableQuadraticCoefficient
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) (Q : ComponentRooting H) (v : W) :
    rootedEnergyAt Q C.activity C.activity_pos v =
      Q.predictableQuadraticCoefficient (G := H) C v := by
  rfl

/-! ## The concrete D.66--D.68 retained array -/

namespace CanonicalCompactnessWrapper.CanonicalSequence

open CanonicalCompactnessWrapper

/-- The exact retained set selected in row `j` of the D.66--D.67 diagonal. -/
noncomputable def RetainedFellerSubsequence.retainedSet
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ) :
    Finset (Fin (S.order (A.subseq j))) :=
  (rooting (A.subseq j)).retainedVarianceSet
    (G := S.graph (A.subseq j)) (S.state (A.subseq j)) (A.alpha j)

/-- The concrete retained triangular array attached to the D.66--D.67
diagonal.  Its row law is the exact seed coupling of the original global
canonical state at `A.subseq j`; only the increments are masked. -/
noncomputable def RetainedFellerSubsequence.seedArray
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) :
    ArrayData (fun j => BernoulliAssignment (Fin (S.order (A.subseq j)))) :=
  retainedNormalizedHardCoreSeedArray
    (fun j => Fin (S.order (A.subseq j)))
    (fun j => S.graph (A.subseq j))
    (fun j => (S.state (A.subseq j)).isForest)
    (fun j => (S.state (A.subseq j)).activity)
    (fun j => (S.state (A.subseq j)).activity_pos)
    (fun j => rooting (A.subseq j))
    A.retainedSet

noncomputable instance RetainedFellerSubsequence.seedArray_isProbabilityMeasure
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ) :
    IsProbabilityMeasure (A.seedArray.probability j) := by
  unfold RetainedFellerSubsequence.seedArray
  infer_instance

/-- The generic array PQV is almost everywhere the original-law D.57
quantity along the concrete retained diagonal. -/
theorem RetainedFellerSubsequence.seedArray_predictableQuadraticVariation_ae_eq
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ) :
    A.seedArray.predictableQuadraticVariation j
      =ᵐ[A.seedArray.probability j]
    fun ω =>
      (rooting (A.subseq j)).predictableQuadraticVariation
        (G := S.graph (A.subseq j)) (S.state (A.subseq j))
        (A.retainedSet j)
        (generatedIndependentSet (S.state (A.subseq j)).isForest
          (rooting (A.subseq j)) ω) /
        S.V (A.subseq j) := by
  let Vseq : ℕ → Type := fun i => Fin (S.order (A.subseq i))
  let Gseq : (i : ℕ) → SimpleGraph (Vseq i) := fun i => S.graph (A.subseq i)
  let C : (i : ℕ) → CanonicalFirstRecoveryState (Gseq i) :=
    fun i => S.state (A.subseq i)
  let Rseq : (i : ℕ) → ComponentRooting (Gseq i) :=
    fun i => rooting (A.subseq i)
  have hVar : 0 < hardCoreVariance Vseq Gseq (fun i => (C i).activity)
      (fun i => (C i).activity_pos) j := by
    exact S.variance_pos (A.subseq j)
  have hseed :=
    retainedNormalizedHardCoreSeedArray_predictableQuadraticVariation_ae_eq
      Vseq Gseq (fun i => (C i).isForest)
      (fun i => (C i).activity) (fun i => (C i).activity_pos)
      Rseq (fun i => A.retainedSet i) j hVar
  have hcomp := hseed.trans (Filter.Eventually.of_forall (fun ω =>
    retainedSeedEnergySum_eq_predictableQuadraticVariation
      (C j) (Rseq j) (A.retainedSet j) ω))
  simpa [RetainedFellerSubsequence.seedArray, Vseq, Gseq, C, Rseq,
    hardCoreVariance, CanonicalSequence.V] using hcomp

/-- D.68 transported through the exact global seed coupling: the concrete
retained array has predictable quadratic variation converging in probability
to one. -/
theorem RetainedFellerSubsequence.seedArray_predictableQuadraticVariationCondition
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) :
    A.seedArray.PredictableQuadraticVariationCondition := by
  intro epsilon hepsilon
  have hconfig := A.predictableQuadraticVariation_D68 epsilon hepsilon
  apply hconfig.congr'
  apply Filter.Eventually.of_forall
  intro j
  letI : DecidableEq (Fin (S.order (A.subseq j))) :=
    Erdos993.UniformFourthMoment.classicalDecidableEq _
  let g := generatedIndependentSet (S.state (A.subseq j)).isForest
    (rooting (A.subseq j))
  let Q : IndepFinset (S.graph (A.subseq j)) → ℝ := fun I =>
    (rooting (A.subseq j)).predictableQuadraticVariation
      (G := S.graph (A.subseq j)) (S.state (A.subseq j))
      (A.retainedSet j) I / S.V (A.subseq j)
  have hpqv := A.seedArray_predictableQuadraticVariation_ae_eq j
  have hset : MeasurableSet {I | epsilon ≤ |Q I - 1|} :=
    MeasurableSet.of_discrete
  have hpre : MeasurableSet {ω | epsilon ≤ |Q (g ω) - 1|} :=
    MeasurableSet.of_discrete
  symm
  calc
    A.seedArray.probability j
        {ω | epsilon ≤ |A.seedArray.predictableQuadraticVariation j ω - 1|} =
      A.seedArray.probability j {ω | epsilon ≤ |Q (g ω) - 1|} := by
        apply measure_congr
        filter_upwards [hpqv] with ω hω
        change (epsilon ≤ |A.seedArray.predictableQuadraticVariation j ω - 1|) =
          (epsilon ≤ |Q (g ω) - 1|)
        rw [hω]
    _ = (S.state (A.subseq j)).law.toMeasure
        {I | epsilon ≤ |Q I - 1|} := by
      change (hardCoreBernoulliSeedLaw (rooting (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos).toMeasure
          {ω | epsilon ≤ |Q (g ω) - 1|} =
        (hardCoreLaw (S.graph (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos).toMeasure
          {I | epsilon ≤ |Q I - 1|}
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change (hardCoreBernoulliSeedLaw (rooting (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos).toMeasure.real
          {ω | epsilon ≤ |Q (g ω) - 1|} =
        (hardCoreLaw (S.graph (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos).toMeasure.real
          {I | epsilon ≤ |Q I - 1|}
      rw [← integral_indicator_one hpre, ← integral_indicator_one hset,
        FiniteLatticeLaw.integral_toMeasure_eq_sum,
        FiniteLatticeLaw.integral_toMeasure_eq_sum]
      simpa [Set.indicator, g, generatedCountLaw] using
        (generatedExpectation_eq_hardCoreExpectation_of_fiberMass
          (S.state (A.subseq j)).isForest (rooting (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos
          ({I | epsilon ≤ |Q I - 1|}.indicator (fun _ => (1 : ℝ))))
    _ = (S.state (A.subseq j)).law.toMeasure
        {I | epsilon ≤ abs
          ((rooting (A.subseq j)).predictableQuadraticVariation
            (G := S.graph (A.subseq j)) (S.state (A.subseq j))
            (A.retainedSet j) I / S.V (A.subseq j) - 1)} := by
      rfl

/-- D.6 along the concrete retained subsequence, with cutoff
`epsilon * sqrt V`.  This is the large-increment estimate under the original
global canonical law; the retained set only masks summands. -/
theorem RetainedFellerSubsequence.largeDisplacementContribution_tendsto_zero_D6
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun j =>
      (rooting (A.subseq j)).largeDisplacementContributionOn
        (G := S.graph (A.subseq j)) (S.state (A.subseq j))
        (A.retainedSet j) (epsilon * Real.sqrt (S.V (A.subseq j))) /
        S.V (A.subseq j)) atTop (𝓝 0) := by
  let Γ : ∀ j, SimpleGraph (Fin (S.order (A.subseq j))) :=
    fun j => S.graph (A.subseq j)
  let C : ∀ j, CanonicalFirstRecoveryState (Γ j) :=
    fun j => S.state (A.subseq j)
  let R : ∀ j, ComponentRooting (Γ j) :=
    fun j => rooting (A.subseq j)
  let D : ∀ j, Finset (Fin (S.order (A.subseq j))) := fun j => A.retainedSet j
  let b : ℕ → ℝ := fun j => epsilon * Real.sqrt (S.V (A.subseq j))
  let m : ℕ → ℝ := fun j =>
    (R j).maxVertexVarianceContribution (G := Γ j) (C j)
  have hV : Tendsto (fun j => S.V (A.subseq j)) atTop atTop :=
    S.variance_tendsto.comp A.strictMono_subseq.tendsto_atTop
  have hb : Tendsto b atTop atTop := by
    dsimp [b]
    exact (Real.tendsto_sqrt_atTop.comp hV).const_mul_atTop hepsilon
  have hfsub : Tendsto (fun j => m j / S.V (A.subseq j)) atTop (𝓝 0) := by
    simpa [m, R, Γ, C] using hFeller.comp A.strictMono_subseq.tendsto_atTop
  have hscale : Tendsto (fun j => m j / (b j)^2) atTop (𝓝 0) := by
    have hc := hfsub.const_mul (epsilon ^ 2)⁻¹
    convert hc using 1
    · funext j
      have hVpos := S.variance_pos (A.subseq j)
      have hsqrt : (Real.sqrt (S.V (A.subseq j))) ^ 2 = S.V (A.subseq j) :=
        Real.sq_sqrt hVpos.le
      dsimp [b]
      rw [mul_pow, hsqrt]
      field_simp [hepsilon.ne', hVpos.ne']
    · simp
  have hmain := ComponentRooting.largeDisplacementContributionOn_tendsto_zero
    Γ C R D b m
    (fun j => S.activity_lt (A.subseq j))
    (fun j => (R j).maxVertexVarianceContribution_pos (G := Γ j) (C j))
    (fun j u => (R j).vertexVarianceContribution_le_max (G := Γ j) (C j) u)
    hb hscale
  simpa [Γ, C, R, D, b, m, CanonicalSequence.V] using hmain

/-- Integrating a conditional Lindeberg sum recovers the sum of the
unconditional truncated second moments.  This is the finite tower bridge used
to pass from D.6 to the array CLT's conditional formulation. -/
theorem ArrayData.integral_conditionalLindebergSum_eq
    {Omega : Nat → Type u} [∀ n, MeasurableSpace (Omega n)]
    (A : ArrayData Omega) [∀ n, IsProbabilityMeasure (A.probability n)]
    (hA : A.IsMartingaleDifferenceArray) (epsilon : ℝ) (n : ℕ) :
    (∫ omega, A.conditionalLindebergSum epsilon n omega ∂(A.probability n)) =
      ∑ k : Fin (A.rowLength n), ∫ omega,
        if epsilon < |A.increment n k omega| then
          (A.increment n k omega)^2 else 0 ∂(A.probability n) := by
  let f : Fin (A.rowLength n) → Omega n → ℝ := fun k omega =>
    if epsilon < |A.increment n k omega| then
      (A.increment n k omega)^2 else 0
  have hfint : ∀ k, Integrable (f k) (A.probability n) := by
    intro k
    have hs : MeasurableSet {omega | epsilon < |A.increment n k omega|} :=
      measurableSet_lt measurable_const
        ((hA.stronglyMeasurable n k).mono
          ((A.filtration n).le (k.val + 1))).measurable.abs
    have hsq := (hA.memLp_two n k).integrable_sq
    simpa only [f, Set.indicator, Set.mem_setOf_eq] using hsq.indicator hs
  unfold ArrayData.conditionalLindebergSum
  rw [MeasureTheory.integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro k hk
    exact MeasureTheory.integral_condExp ((A.filtration n).le k.val)
  · intro k hk
    exact integrable_condExp

/-- The concrete retained rows are martingale-difference rows. -/
theorem RetainedFellerSubsequence.seedArray_isMartingaleDifferenceArray
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) :
    A.seedArray.IsMartingaleDifferenceArray := by
  unfold RetainedFellerSubsequence.seedArray
  exact retainedNormalizedHardCoreSeedArray_isMartingaleDifferenceArray
    (fun j => Fin (S.order (A.subseq j)))
    (fun j => S.graph (A.subseq j))
    (fun j => (S.state (A.subseq j)).isForest)
    (fun j => (S.state (A.subseq j)).activity)
    (fun j => (S.state (A.subseq j)).activity_pos)
    (fun j => rooting (A.subseq j))
    A.retainedSet


/-- Rowwise D.6 domination of the retained normalized-array Lindeberg mass.
This is the finite seed-space bridge required by the martingale-array CLT. -/
theorem retainedFellerSubsequence_lindeberg_row_le_D6
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (epsilon : ℝ) (j : ℕ) :
    (∑ k : Fin (A.seedArray.rowLength j), ∫ ω,
      if epsilon < |A.seedArray.increment j k ω| then
        (A.seedArray.increment j k ω)^2 else 0 ∂(A.seedArray.probability j)) ≤
      (rooting (A.subseq j)).largeDisplacementContributionOn
        (G := S.graph (A.subseq j)) (S.state (A.subseq j))
        (A.retainedSet j) (epsilon * Real.sqrt (S.V (A.subseq j))) /
          S.V (A.subseq j) := by
  letI : DecidableEq (Fin (S.order (A.subseq j))) :=
    Erdos993.UniformFourthMoment.classicalDecidableEq _
  have hraw := sum_normalized_retained_increment_truncation_le_largeDisplacement
    (S.state (A.subseq j)) (rooting (A.subseq j)) (A.retainedSet j) epsilon
  let Vseq : ℕ → Type _ := fun _ => Fin (S.order (A.subseq j))
  let Gseq : ∀ _j, SimpleGraph (Vseq _j) := fun _ => S.graph (A.subseq j)
  let hGseq : ∀ _j, (Gseq _j).IsAcyclic := fun _ => (S.state (A.subseq j)).isForest
  let zseq : ℕ → ℝ := fun _ => (S.state (A.subseq j)).activity
  let hzseq : ∀ _j, 0 < zseq _j := fun _ => (S.state (A.subseq j)).activity_pos
  let Rseq : ∀ _j, ComponentRooting (Gseq _j) := fun _ => rooting (A.subseq j)
  let Dseq : ∀ _j, Finset (Vseq _j) := fun _ => A.retainedSet j
  change (∑ k : Fin (Fintype.card (Fin (S.order (A.subseq j)))), ∫ ω,
      if epsilon <
          |(retainedNormalizedHardCoreSeedArray Vseq Gseq hGseq zseq hzseq Rseq Dseq).increment
            0 k ω| then
        ((retainedNormalizedHardCoreSeedArray Vseq Gseq hGseq zseq hzseq Rseq Dseq).increment
          0 k ω)^2 else 0 ∂
        (retainedNormalizedHardCoreSeedArray Vseq Gseq hGseq zseq hzseq Rseq Dseq).probability 0) ≤ _
  calc
    _ = ∑ k : Fin (Fintype.card (Fin (S.order (A.subseq j)))),
        ∑ ω : BernoulliAssignment (Fin (S.order (A.subseq j))),
          (hardCoreBernoulliSeedLaw (rooting (A.subseq j))
            (S.state (A.subseq j)).activity
            (S.state (A.subseq j)).activity_pos).probability ω *
            (if parentFirstEquiv (rooting (A.subseq j)) k ∈ A.retainedSet j then
              let Delta := finiteDoobIncrement
                (hardCoreBernoulliSeedLaw (rooting (A.subseq j))
                  (S.state (A.subseq j)).activity
                  (S.state (A.subseq j)).activity_pos).probability
                (fun ξ => generatedCountReal (S.state (A.subseq j)).isForest
                  (rooting (A.subseq j)) ξ)
                (parentFirstEquiv (rooting (A.subseq j))) k ω
              if epsilon < |Delta / Real.sqrt (S.V (A.subseq j))| then
                (Delta / Real.sqrt (S.V (A.subseq j)))^2 else 0
            else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      change (∫ ω,
          if epsilon <
              |(retainedNormalizedHardCoreSeedArray Vseq Gseq hGseq zseq hzseq Rseq Dseq).increment
                0 k ω| then
            ((retainedNormalizedHardCoreSeedArray Vseq Gseq hGseq zseq hzseq Rseq Dseq).increment
              0 k ω)^2 else 0 ∂
            (hardCoreBernoulliSeedLaw (rooting (A.subseq j))
              (S.state (A.subseq j)).activity
              (S.state (A.subseq j)).activity_pos).toMeasure) = _
      rw [FiniteLatticeLaw.integral_toMeasure_eq_sum]
      apply Finset.sum_congr rfl
      intro ω hω
      unfold retainedNormalizedHardCoreSeedArray
      by_cases hkD : parentFirstEquiv (rooting (A.subseq j)) k ∈ A.retainedSet j
      · simp only [hkD, if_true]
        have hVpos : 0 < hardCoreVariance Vseq Gseq zseq hzseq 0 := by
          simpa [Vseq, Gseq, zseq, CanonicalSequence.V, hardCoreVariance] using
            S.variance_pos (A.subseq j)
        rw [normalizedHardCoreSeedArray_increment_eq_of_variance_pos
          Vseq Gseq hGseq zseq hzseq Rseq 0 hVpos]
        simp [Vseq, Gseq, zseq, Rseq, Dseq, hardCoreVariance,
          CanonicalSequence.V, Forest.CanonicalFirstRecoveryState.variance,
          Forest.CanonicalFirstRecoveryState.law, hkD]
      · simp [Vseq, Gseq, zseq, Rseq, Dseq, hkD]
    _ ≤ _ := by
      simpa [CanonicalSequence.V] using hraw

/-- The unconditional retained-row Lindeberg masses tend to zero by the
rowwise D.6 domination and the retained Feller estimate. -/
theorem retainedFellerSubsequence_unconditionalLindeberg_tendsto_zero
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    Tendsto (fun j =>
      ∑ k : Fin (A.seedArray.rowLength j), ∫ ω,
        if epsilon < |A.seedArray.increment j k ω| then
          (A.seedArray.increment j k ω)^2 else 0 ∂(A.seedArray.probability j))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (g := fun j =>
      (rooting (A.subseq j)).largeDisplacementContributionOn
        (G := S.graph (A.subseq j)) (S.state (A.subseq j))
        (A.retainedSet j) (epsilon * Real.sqrt (S.V (A.subseq j))) /
          S.V (A.subseq j))
  · filter_upwards with j
    apply Finset.sum_nonneg
    intro k hk
    apply integral_nonneg
    intro ω
    change 0 ≤ (if epsilon < |A.seedArray.increment j k ω| then
      (A.seedArray.increment j k ω)^2 else 0)
    split <;> positivity
  · filter_upwards with j
    exact retainedFellerSubsequence_lindeberg_row_le_D6 A epsilon j
  · exact A.largeDisplacementContribution_tendsto_zero_D6 hFeller epsilon hepsilon

/-- The retained normalized seed array satisfies the generic conditional
Lindeberg condition. Markov's inequality upgrades the D.6 unconditional
truncation convergence to varying-space convergence in probability. -/
theorem RetainedFellerSubsequence.seedArray_conditionalLindebergCondition
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0)) :
    A.seedArray.ConditionalLindebergCondition := by
  intro epsilon hepsilon delta hdelta
  let X : ℕ → ℝ := fun j =>
    ∑ k : Fin (A.seedArray.rowLength j), ∫ ω,
      if epsilon < |A.seedArray.increment j k ω| then
        (A.seedArray.increment j k ω)^2 else 0 ∂(A.seedArray.probability j)
  have hX : Tendsto X atTop (𝓝 0) := by
    simpa [X] using
      retainedFellerSubsequence_unconditionalLindeberg_tendsto_zero
        A hFeller epsilon hepsilon
  have hdiv : Tendsto (fun j => X j / delta) atTop (𝓝 0) := by
    simpa using hX.div_const delta
  have hbound : Tendsto (fun j => ENNReal.ofReal (X j / delta)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hdiv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _j : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    hbound
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · apply Filter.Eventually.of_forall
    intro j
    let μ := A.seedArray.probability j
    let f := A.seedArray.conditionalLindebergSum epsilon j
    letI : IsProbabilityMeasure μ := by
      dsimp [μ]
      infer_instance
    have hA := A.seedArray_isMartingaleDifferenceArray
    have hterm : ∀ k : Fin (A.seedArray.rowLength j),
        0 ≤ᵐ[μ] μ[fun η =>
          if epsilon < |A.seedArray.increment j k η| then
            (A.seedArray.increment j k η)^2 else 0 |
              A.seedArray.filtration j k.val] := by
      intro k
      exact condExp_nonneg (Filter.Eventually.of_forall (fun η => by
        change (0 : ℝ) ≤ if epsilon < |A.seedArray.increment j k η| then
          (A.seedArray.increment j k η)^2 else 0
        split <;> positivity))
    have hall : ∀ᵐ ω ∂μ, ∀ k : Fin (A.seedArray.rowLength j),
        0 ≤ μ[fun η =>
          if epsilon < |A.seedArray.increment j k η| then
            (A.seedArray.increment j k η)^2 else 0 |
              A.seedArray.filtration j k.val] ω :=
      (ae_all_iff).2 hterm
    have hnonneg : 0 ≤ᵐ[μ] f := by
      filter_upwards [hall] with ω hω
      unfold f ArrayData.conditionalLindebergSum
      exact Finset.sum_nonneg (fun k _ => hω k)
    have hIntegral : (∫ ω, f ω ∂μ) = X j := by
      dsimp [f, μ, X]
      exact ArrayData.integral_conditionalLindebergSum_eq
        A.seedArray hA epsilon j
    have hevent :
        μ {ω | delta ≤ |f ω - 0|} = μ {ω | delta ≤ f ω} := by
      apply measure_congr
      filter_upwards [hnonneg] with ω hω
      have hω' : 0 ≤ f ω := by simpa using hω
      change (delta ≤ |f ω - 0|) = (delta ≤ f ω)
      rw [sub_zero, abs_of_nonneg hω']
    have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := f) hnonneg Integrable.of_finite delta
    have hreal : μ.real {ω | delta ≤ f ω} ≤ X j / delta := by
      apply (le_div_iff₀' hdelta).2
      rw [← hIntegral]
      exact hmarkov
    change μ {ω | delta ≤ |f ω - 0|} ≤ ENNReal.ofReal (X j / delta)
    rw [hevent]
    calc
      μ {ω | delta ≤ f ω} = ENNReal.ofReal (μ.real {ω | delta ≤ f ω}) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top μ {ω | delta ≤ f ω})).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- The retained row is exactly the normalized original-law martingale projection evaluated on the globally generated configuration. -/
theorem RetainedFellerSubsequence.seedArray_rowSum_eq_martingaleProjection
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ)
    (ω : BernoulliAssignment (Fin (S.order (A.subseq j)))) :
    A.seedArray.rowSum j ω =
      martingaleProjection (S.state (A.subseq j)) (rooting (A.subseq j))
        (A.retainedSet j)
        (generatedIndependentSet (S.state (A.subseq j)).isForest
          (rooting (A.subseq j)) ω) /
        Real.sqrt (S.V (A.subseq j)) := by
  classical
  letI : DecidableEq (Fin (S.order (A.subseq j))) :=
    Erdos993.UniformFourthMoment.classicalDecidableEq _
  let C := S.state (A.subseq j)
  let R := rooting (A.subseq j)
  let D := A.retainedSet j
  have hV : 0 < hardCoreVariance
      (fun i => Fin (S.order (A.subseq i)))
      (fun i => S.graph (A.subseq i))
      (fun i => (S.state (A.subseq i)).activity)
      (fun i => (S.state (A.subseq i)).activity_pos) j := by
    simpa [hardCoreVariance, CanonicalSequence.V] using S.variance_pos (A.subseq j)
  have hinc : ∀ k : Fin (A.seedArray.rowLength j),
      A.seedArray.increment j k ω =
        if parentFirstEquiv R k ∈ D then
          finiteDoobIncrement
            (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability
            (fun ξ => generatedCountReal C.isForest R ξ)
            (parentFirstEquiv R) k ω / Real.sqrt (S.V (A.subseq j))
        else 0 := by
    intro k
    unfold RetainedFellerSubsequence.seedArray
    unfold retainedNormalizedHardCoreSeedArray
    change (if parentFirstEquiv R k ∈ D then
      (normalizedHardCoreSeedArray
        (fun i => Fin (S.order (A.subseq i)))
        (fun i => S.graph (A.subseq i))
        (fun i => (S.state (A.subseq i)).isForest)
        (fun i => (S.state (A.subseq i)).activity)
        (fun i => (S.state (A.subseq i)).activity_pos)
        (fun i => rooting (A.subseq i))).increment j k ω else 0) = _
    rw [normalizedHardCoreSeedArray_increment_eq_of_variance_pos _ _ _ _ _ _ j hV]
    simp [C, R, D, hardCoreVariance, CanonicalSequence.V,
      Forest.CanonicalFirstRecoveryState.variance,
      Forest.CanonicalFirstRecoveryState.law]
  unfold ArrayData.rowSum
  simp_rw [hinc]
  let g : Fin (S.order (A.subseq j)) → ℝ := fun u =>
    if u ∈ D then
      R.conditionalMeanDifference (G := S.graph (A.subseq j)) C u *
        eta C R (generatedIndependentSet C.isForest R ω) u
    else 0
  calc
    (∑ k : Fin (A.seedArray.rowLength j),
      if parentFirstEquiv R k ∈ D then
        finiteDoobIncrement
          (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability
          (fun ξ => generatedCountReal C.isForest R ξ)
          (parentFirstEquiv R) k ω / Real.sqrt (S.V (A.subseq j)) else 0) =
        (∑ k : Fin (A.seedArray.rowLength j),
          if parentFirstEquiv R k ∈ D then
            finiteDoobIncrement
              (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability
              (fun ξ => generatedCountReal C.isForest R ξ)
              (parentFirstEquiv R) k ω else 0) / Real.sqrt (S.V (A.subseq j)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkD : parentFirstEquiv R k ∈ D <;> simp [hkD]
    _ = martingaleProjection C R D
        (generatedIndependentSet C.isForest R ω) / Real.sqrt (S.V (A.subseq j)) := by
      congr 1
      calc
        (∑ k : Fin (A.seedArray.rowLength j),
          if parentFirstEquiv R k ∈ D then
            finiteDoobIncrement
              (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability
              (fun ξ => generatedCountReal C.isForest R ξ)
              (parentFirstEquiv R) k ω else 0) =
            ∑ k : Fin (A.seedArray.rowLength j), g (parentFirstEquiv R k) := by
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hkD : parentFirstEquiv R k ∈ D
          · simp [g, hkD, finiteDoobIncrement_eq_displacement_mul_generatedEtaAt,
              generatedEtaAt_eq_eta_generatedIndependentSet,
              rootedDisplacementAt_eq_original]
          · simp [g, hkD]
        _ = ∑ u : Fin (S.order (A.subseq j)), g u :=
          Equiv.sum_comp (parentFirstEquiv R) g
        _ = martingaleProjection C R D
            (generatedIndependentSet C.isForest R ω) := by
          unfold g martingaleProjection
          rw [Finset.sum_ite_mem]
          simp

noncomputable def RetainedFellerSubsequence.omittedNormalizedSeedSum
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ)
    (ω : BernoulliAssignment (Fin (S.order (A.subseq j)))) : ℝ :=
  let C := S.state (A.subseq j)
  let R := rooting (A.subseq j)
  let I := generatedIndependentSet C.isForest R ω
  (centeredOccupationCount C I - martingaleProjection C R (A.retainedSet j) I) /
    Real.sqrt (S.V (A.subseq j))

/-- Exact normalized second moment of the omitted original-law martingale projection. -/
theorem RetainedFellerSubsequence.integral_omittedNormalizedSeedSum_sq_eq
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ) :
    (∫ ω, (A.omittedNormalizedSeedSum j ω)^2 ∂(A.seedArray.probability j)) =
      (rooting (A.subseq j)).omittedVarianceContribution
        (G := S.graph (A.subseq j)) (S.state (A.subseq j)) (A.retainedSet j) /
        S.V (A.subseq j) := by
  letI : DecidableEq (Fin (S.order (A.subseq j))) :=
    Erdos993.UniformFourthMoment.classicalDecidableEq _
  let C := S.state (A.subseq j)
  let R := rooting (A.subseq j)
  let D := A.retainedSet j
  let f : IndepFinset (S.graph (A.subseq j)) → ℝ := fun I =>
    (centeredOccupationCount C I - martingaleProjection C R D I)^2
  have htransfer := generatedExpectation_eq_hardCoreExpectation_of_fiberMass
    C.isForest R C.activity C.activity_pos f
  have hres := expectation_sq_residual_eq C R D
  have hD66 := retained_sum_add_omitted_eq_variance_D66 C R D
  have hV0 : 0 ≤ S.V (A.subseq j) := (S.variance_pos (A.subseq j)).le
  change (∫ ω, (A.omittedNormalizedSeedSum j ω)^2 ∂
    (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).toMeasure) = _
  rw [FiniteLatticeLaw.integral_toMeasure_eq_sum]
  change (∑ ω, (generatedCountLaw C.isForest R C.activity C.activity_pos).probability ω *
    (A.omittedNormalizedSeedSum j ω)^2) = _
  have hsqrt : (Real.sqrt (S.V (A.subseq j))) ^ 2 = S.V (A.subseq j) :=
    Real.sq_sqrt hV0
  simp only [RetainedFellerSubsequence.omittedNormalizedSeedSum]
  simp_rw [div_pow]
  rw [hsqrt]
  calc
    (∑ ω, (generatedCountLaw C.isForest R C.activity C.activity_pos).probability ω *
        ((centeredOccupationCount (S.state (A.subseq j))
            (generatedIndependentSet (S.state (A.subseq j)).isForest
              (rooting (A.subseq j)) ω) -
          martingaleProjection (S.state (A.subseq j)) (rooting (A.subseq j))
            (A.retainedSet j)
            (generatedIndependentSet (S.state (A.subseq j)).isForest
              (rooting (A.subseq j)) ω)) ^ 2 / S.V (A.subseq j))) =
      (∑ ω, (generatedCountLaw C.isForest R C.activity C.activity_pos).probability ω *
        f (generatedIndependentSet C.isForest R ω)) / S.V (A.subseq j) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω hω
      dsimp [f, C, R, D]
      ring
    _ = _ := by
      rw [htransfer]
      have heq0 :
          (∑ I, C.law.probability I *
            (centeredOccupationCount C I - martingaleProjection C R D I) ^ 2) =
            R.omittedVarianceContribution (G := S.graph (A.subseq j)) C D := by
        linarith [hres, hD66]
      have heq : (∑ I, (hardCoreLaw (S.graph (A.subseq j)) C.activity C.activity_pos).probability I * f I) =
          R.omittedVarianceContribution (G := S.graph (A.subseq j)) C D := by
        simpa [f, Forest.CanonicalFirstRecoveryState.law] using heq0
      rw [heq]

/-- The omitted normalized original-law martingale contribution vanishes in probability along the retained diagonal. -/
theorem RetainedFellerSubsequence.omittedNormalizedSeedSum_tendstoInProbability
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) :
    TendstoInProbabilityVarying
      (fun j => BernoulliAssignment (Fin (S.order (A.subseq j))))
      A.seedArray.probability A.omittedNormalizedSeedSum atTop 0 := by
  intro epsilon hepsilon
  have heps2 : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hscale : Tendsto (fun j => fellerErrorScale j / epsilon ^ 2)
      atTop (𝓝 0) := by
    simpa using fellerErrorScale_tendsto_zero.div_const (epsilon ^ 2)
  have hbound : Tendsto (fun j => ENNReal.ofReal
      (fellerErrorScale j / epsilon ^ 2)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hscale
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _j : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    hbound
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · apply Filter.Eventually.of_forall
    intro j
    let μ := A.seedArray.probability j
    let X := A.omittedNormalizedSeedSum j
    let f : BernoulliAssignment (Fin (S.order (A.subseq j))) → ℝ := fun ω => (X ω)^2
    letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
    have hf0 : 0 ≤ᵐ[μ] f := Filter.Eventually.of_forall (fun ω => sq_nonneg (X ω))
    have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := f) hf0 Integrable.of_finite (epsilon ^ 2)
    have hratio :
        (rooting (A.subseq j)).omittedVarianceContribution
          (G := S.graph (A.subseq j)) (S.state (A.subseq j)) (A.retainedSet j) /
            S.V (A.subseq j) ≤ fellerErrorScale j := by
      apply (div_le_iff₀ (S.variance_pos (A.subseq j))).2
      simpa [CanonicalSequence.V] using A.omitted_le j
    have hint : (∫ ω, f ω ∂μ) =
        (rooting (A.subseq j)).omittedVarianceContribution
          (G := S.graph (A.subseq j)) (S.state (A.subseq j)) (A.retainedSet j) /
            S.V (A.subseq j) := by
      simpa [μ, f, X] using A.integral_omittedNormalizedSeedSum_sq_eq j
    have hreal : μ.real {ω | epsilon ^ 2 ≤ f ω} ≤
        fellerErrorScale j / epsilon ^ 2 := by
      apply (le_div_iff₀' heps2).2
      calc
        epsilon ^ 2 * μ.real {ω | epsilon ^ 2 ≤ f ω} ≤
            ∫ ω, f ω ∂μ := hmarkov
        _ ≤ fellerErrorScale j := by rw [hint]; exact hratio
    have hevent : {ω | epsilon ≤ |X ω - 0|} = {ω | epsilon ^ 2 ≤ f ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, sub_zero, f]
      simpa [sq_abs] using
        (sq_le_sq₀ hepsilon.le (abs_nonneg (X ω))).symm
    rw [hevent]
    calc
      μ {ω | epsilon ^ 2 ≤ f ω} =
          ENNReal.ofReal (μ.real {ω | epsilon ^ 2 ≤ f ω}) := by
        exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
      _ ≤ ENNReal.ofReal (fellerErrorScale j / epsilon ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal

/-- The full normalized generated count is retained row plus the omitted original-law contribution. -/
theorem RetainedFellerSubsequence.seedArray_rowSum_add_omitted_eq_normalizedGenerated
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ)
    (ω : BernoulliAssignment (Fin (S.order (A.subseq j)))) :
    A.seedArray.rowSum j ω + A.omittedNormalizedSeedSum j ω =
      centeredOccupationCount (S.state (A.subseq j))
        (generatedIndependentSet (S.state (A.subseq j)).isForest
          (rooting (A.subseq j)) ω) / Real.sqrt (S.V (A.subseq j)) := by
  rw [A.seedArray_rowSum_eq_martingaleProjection j ω]
  unfold RetainedFellerSubsequence.omittedNormalizedSeedSum
  dsimp only
  ring

/-- The generic martingale-array CLT applied to the retained normalized seed rows. -/
theorem RetainedFellerSubsequence.seedArray_rowSum_tendstoInDistribution
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0)) :
    TendstoInDistribution A.seedArray.rowSum atTop (id : ℝ → ℝ)
      A.seedArray.probability (gaussianReal 0 1) := by
  exact A.seedArray.varyingSpaceMartingaleArrayCLT
    A.seedArray_isMartingaleDifferenceArray
    A.seedArray_predictableQuadraticVariationCondition
    (A.seedArray_conditionalLindebergCondition hFeller)
    ℝ inferInstance (gaussianReal 0 1) inferInstance
    (id : ℝ → ℝ) ProbabilityTheory.HasLaw.id
section CanonicalGeneratedLawTransfer

noncomputable local instance (priority := 2000) exactGeneratedFinDecidableEq (n : ℕ) :
    DecidableEq (Fin n) := Erdos993.UniformFourthMoment.classicalDecidableEq _

/-- Exact identification of the normalized generated-seed count with the canonical standardized law. -/
theorem RetainedFellerSubsequence.normalizedGenerated_hasLaw_standardizedLaw
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) (j : ℕ) :
    HasLaw (fun ω : BernoulliAssignment (Fin (S.order (A.subseq j))) =>
      centeredOccupationCount (S.state (A.subseq j))
        (generatedIndependentSet (S.state (A.subseq j)).isForest
          (rooting (A.subseq j)) ω) / Real.sqrt (S.V (A.subseq j)))
      (S.standardizedLaw (A.subseq j) : Measure ℝ)
      (A.seedArray.probability j) := by
  let n := A.subseq j
  let C := S.state n
  let R := rooting n
  let std : ℕ → ℝ := standardizedHardCoreCount
    (S.graph n) C.activity C.activity_pos
  have hstat : HasLaw C.law.stat C.law.statPMF.toMeasure C.law.toMeasure :=
    C.law.hasLaw_stat
  have hstd : HasLaw std (S.standardizedLaw n : Measure ℝ)
      C.law.statPMF.toMeasure := by
    constructor
    · exact (measurable_of_countable std).aemeasurable
    · rw [CanonicalSequence.standardizedLaw_toMeasure_eq_actual]
  have hconfig : HasLaw (fun I => std (C.law.stat I))
      (S.standardizedLaw n : Measure ℝ) C.law.toMeasure :=
    hstd.fun_comp hstat
  have hgen : HasLaw (generatedIndependentSet C.isForest R)
      C.law.toMeasure (A.seedArray.probability j) := by
    constructor
    · exact (measurable_of_finite _).aemeasurable
    · change Measure.map (generatedIndependentSet C.isForest R)
          (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).toMeasure =
        C.law.toMeasure
      rw [FiniteLatticeLaw.toMeasure, PMF.toMeasure_map]
      · rw [hardCoreBernoulliSeedLaw_toPMF_eq_generatedCountLaw_toPMF
            C.isForest R C.activity C.activity_pos,
          generatedIndependentSet_toPMF_map_of_fiberMass
            C.isForest R C.activity C.activity_pos]
        rfl
      · exact measurable_of_finite _
  have hall := hconfig.fun_comp hgen
  convert hall using 1
  · funext ω
    dsimp [std, C, R, n]
    unfold centeredOccupationCount occupationCount standardizedHardCoreCount
    have hmean :
        (hardCoreLaw (S.graph (A.subseq j))
          (S.state (A.subseq j)).activity
          (S.state (A.subseq j)).activity_pos).mean =
          ((S.state (A.subseq j)).index : ℝ) := by
      simpa [CanonicalFirstRecoveryState.law] using
        (S.state (A.subseq j)).law_mean
    rw [hmean, CanonicalSequence.V]
    rfl

end CanonicalGeneratedLawTransfer

/-- Slutsky transfer from the retained martingale row to the full normalized generated count. -/
theorem RetainedFellerSubsequence.normalizedGenerated_tendstoInDistribution
    {S : CanonicalSequence}
    {rooting : ∀ n, ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting)
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0)) :
    TendstoInDistribution (fun j ω =>
      centeredOccupationCount (S.state (A.subseq j))
        (generatedIndependentSet (S.state (A.subseq j)).isForest
          (rooting (A.subseq j)) ω) / Real.sqrt (S.V (A.subseq j)))
      atTop (id : ℝ → ℝ) A.seedArray.probability (gaussianReal 0 1) := by
  have hsum := varyingSpace_slutsky_add A.seedArray.probability
    A.seedArray.rowSum A.omittedNormalizedSeedSum
    (id : ℝ → ℝ) (gaussianReal 0 1)
    (A.seedArray_rowSum_tendstoInDistribution hFeller)
    A.omittedNormalizedSeedSum_tendstoInProbability
    (fun _ => Measurable.aemeasurable (measurable_of_finite _))
  convert hsum using 1
  funext j ω
  exact (A.seedArray_rowSum_add_omitted_eq_normalizedGenerated j ω).symm
/-- D.8: the literal Feller condition is impossible for the canonical sequence.
The contradiction is taken on the genuine canonical subsequence selected in D.66--D.67. -/
theorem feller_failure_D8
    (S : CanonicalSequence)
    (rooting : ∀ n, ComponentRooting (S.graph n)) :
    ¬ Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0) := by
  intro hFeller
  let A : RetainedFellerSubsequence S rooting :=
    Classical.choice (exists_retainedFellerSubsequence_D66_D67 S rooting hFeller)
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hfull := A.normalizedGenerated_tendstoInDistribution hFeller
  have hmap := hfull.tendsto
  have hstd : Tendsto (fun j => S.standardizedLaw (A.subseq j))
      atTop (𝓝 γ) := by
    convert hmap using 1
    · funext j
      exact Subtype.ext (A.normalizedGenerated_hasLaw_standardizedLaw j).map_eq.symm
    · simp [γ]
  let T : CanonicalSequence := S.subsequence A.subseq A.strictMono_subseq
  have hT : Tendsto T.standardizedLaw atTop (𝓝 γ) := by
    simpa [T] using hstd
  exact (not_tendsto_standardGaussian_D73_D79 T γ rfl) hT

end CanonicalCompactnessWrapper.CanonicalSequence

end
end Forest
end Erdos993
