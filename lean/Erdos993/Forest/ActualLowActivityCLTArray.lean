import Erdos993.Forest.ActualLowActivityCLTCondExp

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos993.Forest.ActualLowActivityCLT

open Erdos993.ActualRootedVariance
open Erdos993.ActualMartingaleProjection
open Erdos993.UniformFourthMoment
open Erdos993.Forest.MartingaleArrayCLT

universe u

noncomputable section

noncomputable local instance actualArrayDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

section ActualArray

variable (V : ℕ → Type u) [∀ n, Fintype (V n)]
variable (G : (n : ℕ) → SimpleGraph (V n))
variable (hG : ∀ n, (G n).IsAcyclic)
variable (z : ℕ → ℝ) (hz : ∀ n, 0 < z n)
variable (R : (n : ℕ) → ComponentRooting (G n))

/-- The actual canonical hard-core occupation-count variance in row `n`. -/
noncomputable def hardCoreVariance (n : ℕ) : ℝ :=
  (hardCoreLaw (G n) (z n) (hz n)).variance

private noncomputable def normalizedSeedDoobEntry
    (n : ℕ) (k : Fin (Fintype.card (V n)))
    (ω : BernoulliAssignment (V n)) : ℝ :=
  if 0 < hardCoreVariance V G z hz n then
    finiteDoobIncrement (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
      (fun ξ => generatedCountReal (hG n) (R n) ξ) (parentFirstEquiv (R n)) k ω /
        Real.sqrt (hardCoreVariance V G z hz n)
  else 0

noncomputable def normalizedHardCoreSeedArray :
    ArrayData (ActualSeedSpace V) where
  probability := actualSeedMeasure V G z hz R
  rowLength n := Fintype.card (V n)
  filtration := actualPrefixFiltration V G R
  increment := normalizedSeedDoobEntry V G hG z hz R

/-- Public pointwise form of a normalized seed-array increment on a positive-
variance row.  This exposes the private implementation only through the exact
mathematical formula needed by retained-array truncation estimates. -/
theorem normalizedHardCoreSeedArray_increment_eq_of_variance_pos
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n)
    (k : Fin (Fintype.card (V n))) (ω : BernoulliAssignment (V n)) :
    (normalizedHardCoreSeedArray V G hG z hz R).increment n k ω =
      finiteDoobIncrement
        (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
        (fun ξ => generatedCountReal (hG n) (R n) ξ)
        (parentFirstEquiv (R n)) k ω /
          Real.sqrt (hardCoreVariance V G z hz n) := by
  change normalizedSeedDoobEntry V G hG z hz R n k ω = _
  unfold normalizedSeedDoobEntry
  rw [if_pos hVar]

noncomputable instance actualSeedMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (actualSeedMeasure V G z hz R n) := by
  dsimp [actualSeedMeasure]
  infer_instance

noncomputable instance normalizedHardCoreSeedArray_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure
      ((normalizedHardCoreSeedArray V G hG z hz R).probability n) := by
  change IsProbabilityMeasure (actualSeedMeasure V G z hz R n)
  infer_instance

lemma actualPrefixMeasurableSpace_eq_oneRowPrefixSpace
    (n : ℕ) (k : Fin (Fintype.card (V n) + 1)) :
    actualPrefixMeasurableSpace V G R n k.val =
      oneRowPrefixSpace (parentFirstEquiv (R n)) k := by
  rfl

private theorem hardCoreSeedAtom_pos
    (n : ℕ) (ω : BernoulliAssignment (V n)) :
    0 < (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability ω := by
  rw [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability]
  unfold bernoulliWeight
  apply Finset.prod_pos
  intro v hv
  cases hseed : ω v
  · simp only [Bool.false_eq_true, if_false]
    have hvac : 0 < rootedVacancyProbabilityAt (R n) (z n) v := by
      unfold rootedVacancyProbabilityAt
      exact div_pos (rootedQAt_pos (R n) (z n) (hz n) v)
        (independenceEval_pos _ (hz n))
    linarith [rootedOccupationProbabilityAt_add_vacancy (R n) (z n) (hz n) v]
  · simp only [if_true]
    exact rootedOccupationProbabilityAt_pos (R n) (z n) (hz n) v

private theorem normalizedSeedDoobEntry_memLp_two
    (n : ℕ) (k : Fin (Fintype.card (V n))) :
    MemLp (normalizedSeedDoobEntry V G hG z hz R n k) 2
      (actualSeedMeasure V G z hz R n) := by
  letI : IsProbabilityMeasure (actualSeedMeasure V G z hz R n) :=
    (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).instIsProbabilityMeasureToMeasure
  let f := normalizedSeedDoobEntry V G hG z hz R n k
  obtain ⟨C, hC⟩ := Finite.exists_le (fun ω : BernoulliAssignment (V n) => ‖f ω‖)
  exact MemLp.of_bound (measurable_of_finite f).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The normalized seed-law Doob rows are martingale-difference rows.  Rows of
nonpositive variance are set identically to zero; this fallback disappears
eventually under the sole asymptotic hypothesis `variance → ∞`. -/
theorem normalizedHardCoreSeedArray_isMartingaleDifferenceArray :
    (normalizedHardCoreSeedArray V G hG z hz R).IsMartingaleDifferenceArray := by
  refine ⟨?_, ?_, ?_⟩
  · intro n k
    have hfil :
        (normalizedHardCoreSeedArray V G hG z hz R).filtration n (k.val + 1) =
          oneRowPrefixSpace (parentFirstEquiv (R n)) k.succ := by
      change actualPrefixMeasurableSpace V G R n (k.val + 1) = _
      exact actualPrefixMeasurableSpace_eq_oneRowPrefixSpace V G R n k.succ
    rw [hfil]
    change StronglyMeasurable[
      oneRowPrefixSpace (parentFirstEquiv (R n)) k.succ]
        (normalizedSeedDoobEntry V G hG z hz R n k)
    unfold normalizedSeedDoobEntry
    split_ifs with hVar
    · have hsm := (finiteDoobMean_stronglyMeasurable_prefix
          (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k.succ).sub
        ((finiteDoobMean_stronglyMeasurable_prefix
            (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
            (fun ξ => generatedCountReal (hG n) (R n) ξ)
            (parentFirstEquiv (R n)) k.castSucc).mono
          (oneRowPrefixSpace_mono _ (Fin.castSucc_le_succ k)))
      simpa [finiteDoobIncrement_eq_difference, div_eq_inv_mul] using
        hsm.const_mul (Real.sqrt (hardCoreVariance V G z hz n))⁻¹
    · exact stronglyMeasurable_const
  · exact normalizedSeedDoobEntry_memLp_two V G hG z hz R
  · intro n k
    have hfil :
        (normalizedHardCoreSeedArray V G hG z hz R).filtration n k.val =
          oneRowPrefixSpace (parentFirstEquiv (R n)) k.castSucc := by
      change actualPrefixMeasurableSpace V G R n k.val = _
      exact actualPrefixMeasurableSpace_eq_oneRowPrefixSpace V G R n k.castSucc
    rw [hfil]
    change (actualSeedMeasure V G z hz R n)[
        normalizedSeedDoobEntry V G hG z hz R n k |
          oneRowPrefixSpace (parentFirstEquiv (R n)) k.castSucc] =ᵐ[
        actualSeedMeasure V G z hz R n] 0
    unfold normalizedSeedDoobEntry
    split_ifs with hVar
    · let L := hardCoreBernoulliSeedLaw (R n) (z n) (hz n)
      let D : BernoulliAssignment (V n) → ℝ := fun η =>
        finiteDoobIncrement L.probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k η
      change L.toMeasure[(fun η => D η /
          Real.sqrt (hardCoreVariance V G z hz n)) |
          oneRowPrefixSpace (parentFirstEquiv (R n)) k.castSucc] =ᵐ[L.toMeasure] 0
      have hce := finiteDoobMean_eq_condExp L
        (hardCoreSeedAtom_pos V G z hz R n) (fun η => D η /
          Real.sqrt (hardCoreVariance V G z hz n))
        (parentFirstEquiv (R n)) k.castSucc
      filter_upwards [hce] with ω hω
      rw [hω]
      have hfun : (fun η => D η / Real.sqrt (hardCoreVariance V G z hz n)) =
          (fun η => (Real.sqrt (hardCoreVariance V G z hz n))⁻¹ * D η) := by
        funext η
        rw [div_eq_inv_mul]
      rw [hfun, finiteDoobMean_const_mul]
      have hcenter :
          finiteDoobMean L.probability D (parentFirstEquiv (R n)) k.castSucc ω = 0 := by
        dsimp [D, L]
        exact finiteDoobIncrement_centered_current
          (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
          (hardCoreSeedAtom_pos V G z hz R n)
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k ω
      rw [hcenter]
      simp
    · have hzfun : (fun _ω : BernoulliAssignment (V n) => (0 : ℝ)) = 0 := rfl
      rw [hzfun, condExp_zero]

private lemma hardCoreVariance_eventually_pos
    (hvariance : Tendsto (hardCoreVariance V G z hz) atTop atTop) :
    ∀ᶠ n in atTop, 0 < hardCoreVariance V G z hz n := by
  have hge : ∀ᶠ n in atTop, (1 : ℝ) ≤ hardCoreVariance V G z hz n :=
    (tendsto_atTop.1 hvariance) 1
  filter_upwards [hge] with n hn
  exact zero_lt_one.trans_le hn

/-- The total unconditional second moment of a positive-variance normalized
Doob row is exactly one. -/
theorem normalizedHardCoreSeedArray_rowVariance_eq_one
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n) :
    ∑ k : Fin (Fintype.card (V n)), ∫ ω,
      ((normalizedHardCoreSeedArray V G hG z hz R).increment n k ω) ^ 2
        ∂(normalizedHardCoreSeedArray V G hG z hz R).probability n = 1 := by
  let L := hardCoreBernoulliSeedLaw (R n) (z n) (hz n)
  change ∑ k : Fin (Fintype.card (V n)), ∫ ω,
      (normalizedSeedDoobEntry V G hG z hz R n k ω) ^ 2 ∂L.toMeasure = 1
  calc
    (∑ k : Fin (Fintype.card (V n)), ∫ ω,
        (normalizedSeedDoobEntry V G hG z hz R n k ω) ^ 2 ∂L.toMeasure) =
        ∑ k : Fin (Fintype.card (V n)),
          ∑ η : BernoulliAssignment (V n), L.probability η *
            (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [FiniteLatticeLaw.integral_toMeasure_eq_sum]
    _ = (∑ k : Fin (Fintype.card (V n)),
          ∑ η : BernoulliAssignment (V n), L.probability η *
            (finiteDoobIncrement L.probability
              (fun ξ => generatedCountReal (hG n) (R n) ξ)
              (parentFirstEquiv (R n)) k η) ^ 2) /
          hardCoreVariance V G z hz n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro η hη
      rw [normalizedSeedDoobEntry, if_pos hVar, div_pow,
        Real.sq_sqrt hVar.le]
      dsimp [L]
      ring
    _ = hardCoreVariance V G z hz n / hardCoreVariance V G z hz n := by
      congr 1
      simpa [L, hardCoreVariance] using
        (sum_increment_sq_expectation_eq_hardCoreVariance
          (hG n) (R n) (z n) (hz n))
    _ = 1 := div_self hVar.ne'

/-- Under the sole assumption that the actual hard-core variances diverge, the
normalized rows have unconditional variance one eventually. -/
theorem normalizedHardCoreSeedArray_eventually_rowVariance_eq_one
    (hvariance : Tendsto (hardCoreVariance V G z hz) atTop atTop) :
    ∀ᶠ n in atTop,
      ∑ k : Fin (Fintype.card (V n)), ∫ ω,
        ((normalizedHardCoreSeedArray V G hG z hz R).increment n k ω) ^ 2
          ∂(normalizedHardCoreSeedArray V G hG z hz R).probability n = 1 := by
  filter_upwards [hardCoreVariance_eventually_pos V G z hz hvariance] with n hn
  exact normalizedHardCoreSeedArray_rowVariance_eq_one V G hG z hz R n hn

/-- Termwise conditional-variance formula for the normalized seed Doob array.
This public wrapper is the retained-array bridge: deterministic masking can now
sum only those vertices selected by an Appendix D retained set. -/
theorem normalizedHardCoreSeedArray_conditionalVariance_ae_eq
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n)
    (k : Fin (Fintype.card (V n))) :
    (normalizedHardCoreSeedArray V G hG z hz R).conditionalVariance n k
      =ᵐ[actualSeedMeasure V G z hz R n]
    fun ω =>
      finiteDoobMean
        (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
        (fun η => (finiteDoobIncrement
          (hardCoreBernoulliSeedLaw (R n) (z n) (hz n)).probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k η) ^ 2)
        (parentFirstEquiv (R n)) k.castSucc ω /
          hardCoreVariance V G z hz n := by
  let L := hardCoreBernoulliSeedLaw (R n) (z n) (hz n)
  change L.toMeasure[
      (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2) |
        oneRowPrefixSpace (parentFirstEquiv (R n)) k.castSucc]
    =ᵐ[L.toMeasure] _
  have hce := finiteDoobMean_eq_condExp L
    (hardCoreSeedAtom_pos V G z hz R n)
    (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2)
    (parentFirstEquiv (R n)) k.castSucc
  filter_upwards [hce] with ω hω
  rw [hω]
  have hfun :
      (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2) =
        fun η => (hardCoreVariance V G z hz n)⁻¹ *
          (finiteDoobIncrement L.probability
            (fun ξ => generatedCountReal (hG n) (R n) ξ)
            (parentFirstEquiv (R n)) k η) ^ 2 := by
    funext η
    rw [normalizedSeedDoobEntry, if_pos hVar, div_pow,
      Real.sq_sqrt hVar.le]
    simp [L, div_eq_mul_inv, mul_comm]
  rw [hfun, finiteDoobMean_const_mul]
  change (hardCoreVariance V G z hz n)⁻¹ *
      finiteDoobMean L.probability
        (fun η => (finiteDoobIncrement L.probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k η) ^ 2)
        (parentFirstEquiv (R n)) k.castSucc ω =
    finiteDoobMean L.probability
        (fun η => (finiteDoobIncrement L.probability
          (fun ξ => generatedCountReal (hG n) (R n) ξ)
          (parentFirstEquiv (R n)) k η) ^ 2)
        (parentFirstEquiv (R n)) k.castSucc ω /
      hardCoreVariance V G z hz n
  rw [div_eq_mul_inv, mul_comm]

/-- On every positive-variance row, the array's predictable quadratic variation
is the actual finite Doob predictable variation `scriptV`, normalized by the
actual hard-core variance.  The equality is almost everywhere because
conditional expectation is defined only up to almost-everywhere equality. -/
private lemma normalizedHardCoreSeedArray_predictableQuadraticVariation_ae_eq
    (n : ℕ) (hVar : 0 < hardCoreVariance V G z hz n) :
    (normalizedHardCoreSeedArray V G hG z hz R).predictableQuadraticVariation n
      =ᵐ[actualSeedMeasure V G z hz R n]
    fun ω => scriptV (hG n) (R n) (z n) (hz n) ω /
      hardCoreVariance V G z hz n := by
  let L := hardCoreBernoulliSeedLaw (R n) (z n) (hz n)
  have hterm : ∀ k : Fin (Fintype.card (V n)),
      (normalizedHardCoreSeedArray V G hG z hz R).conditionalVariance n k
        =ᵐ[actualSeedMeasure V G z hz R n]
      fun ω =>
        finiteDoobMean L.probability
          (fun η => (finiteDoobIncrement L.probability
            (fun ξ => generatedCountReal (hG n) (R n) ξ)
            (parentFirstEquiv (R n)) k η) ^ 2)
          (parentFirstEquiv (R n)) k.castSucc ω /
            hardCoreVariance V G z hz n := by
    intro k
    change L.toMeasure[
        (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2) |
          oneRowPrefixSpace (parentFirstEquiv (R n)) k.castSucc]
      =ᵐ[L.toMeasure] _
    have hce := finiteDoobMean_eq_condExp L
      (hardCoreSeedAtom_pos V G z hz R n)
      (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2)
      (parentFirstEquiv (R n)) k.castSucc
    filter_upwards [hce] with ω hω
    rw [hω]
    have hfun :
        (fun η => (normalizedSeedDoobEntry V G hG z hz R n k η) ^ 2) =
          fun η => (hardCoreVariance V G z hz n)⁻¹ *
            (finiteDoobIncrement L.probability
              (fun ξ => generatedCountReal (hG n) (R n) ξ)
              (parentFirstEquiv (R n)) k η) ^ 2 := by
      funext η
      rw [normalizedSeedDoobEntry, if_pos hVar, div_pow,
        Real.sq_sqrt hVar.le]
      simp [L, div_eq_mul_inv, mul_comm]
    rw [hfun, finiteDoobMean_const_mul]
    simp [div_eq_mul_inv, mul_comm]
  have hall : ∀ᵐ ω ∂actualSeedMeasure V G z hz R n,
      ∀ k : Fin (Fintype.card (V n)),
        (normalizedHardCoreSeedArray V G hG z hz R).conditionalVariance n k ω =
          finiteDoobMean L.probability
            (fun η => (finiteDoobIncrement L.probability
              (fun ξ => generatedCountReal (hG n) (R n) ξ)
              (parentFirstEquiv (R n)) k η) ^ 2)
            (parentFirstEquiv (R n)) k.castSucc ω /
              hardCoreVariance V G z hz n :=
    (ae_all_iff).2 hterm
  filter_upwards [hall] with ω hω
  unfold ArrayData.predictableQuadraticVariation scriptV
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl (fun k _ => hω k)

/-- Quantitative B.59 tail estimate for one positive-variance row. -/
private lemma predictableQuadraticVariation_deviation_measure_le_B59
    (n : ℕ) (hz15 : z n ≤ 3 / 2)
    (hVar : 0 < hardCoreVariance V G z hz n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    actualSeedMeasure V G z hz R n
        {ω | epsilon ≤
          |ArrayData.predictableQuadraticVariation
              (normalizedHardCoreSeedArray V G hG z hz R) n ω - 1|} ≤
      ENNReal.ofReal (lowActivityCQ *
        (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ) / epsilon ^ 2) := by
  let μ := actualSeedMeasure V G z hz R n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, actualSeedMeasure]
    infer_instance
  let Q : BernoulliAssignment (V n) → ℝ := fun ω =>
    scriptV (hG n) (R n) (z n) (hz n) ω /
      hardCoreVariance V G z hz n
  have hpqv := normalizedHardCoreSeedArray_predictableQuadraticVariation_ae_eq
    V G hG z hz R n hVar
  have hevent :
      μ {ω | epsilon ≤
        |ArrayData.predictableQuadraticVariation
            (normalizedHardCoreSeedArray V G hG z hz R) n ω - 1|} =
      μ {ω | epsilon ≤ |Q ω - 1|} := by
    apply measure_congr
    filter_upwards [hpqv] with ω hω
    change (epsilon ≤
        |ArrayData.predictableQuadraticVariation
            (normalizedHardCoreSeedArray V G hG z hz R) n ω - 1|) =
      (epsilon ≤ |Q ω - 1|)
    rw [hω]
  have hIntegral :
      (∫ ω, |Q ω - 1| ^ 2 ∂μ) ≤
        lowActivityCQ * (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ) := by
    dsimp only [μ, Q, actualSeedMeasure]
    rw [FiniteLatticeLaw.integral_toMeasure_eq_sum]
    exact scriptV_normalized_meanSquare_le_B58
      (hG n) (R n) (z n) (hz n) hz15 hVar
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => |Q ω - 1| ^ 2)
    (Filter.Eventually.of_forall (fun ω => sq_nonneg |Q ω - 1|))
    (Integrable.of_finite) (epsilon ^ 2)
  have hsqEvent :
      {ω | epsilon ^ 2 ≤ |Q ω - 1| ^ 2} =
        {ω | epsilon ≤ |Q ω - 1|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact sq_le_sq₀ hepsilon.le (abs_nonneg (Q ω - 1))
  rw [hsqEvent] at hmarkov
  have hreal :
      μ.real {ω | epsilon ≤ |Q ω - 1|} ≤
        lowActivityCQ * (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ) /
          epsilon ^ 2 := by
    apply (le_div_iff₀' (sq_pos_of_pos hepsilon)).2
    exact hmarkov.trans hIntegral
  rw [hevent]
  calc
    μ {ω | epsilon ≤ |Q ω - 1|} =
        ENNReal.ofReal (μ.real {ω | epsilon ≤ |Q ω - 1|}) := by
      exact (ENNReal.ofReal_toReal
        (measure_ne_top μ {ω | epsilon ≤ |Q ω - 1|})).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- B.59: the normalized actual seed-law predictable quadratic variation
converges in probability to one.  Only divergence of the actual hard-core
variance is assumed; positivity is extracted eventually. -/
theorem normalizedHardCoreSeedArray_predictableQuadraticVariationCondition
    (hz15 : ∀ n, z n ≤ 3 / 2)
    (hvariance : Tendsto (hardCoreVariance V G z hz) atTop atTop) :
    ArrayData.PredictableQuadraticVariationCondition
      (normalizedHardCoreSeedArray V G hG z hz R) := by
  intro epsilon hepsilon
  have hVarPos := hardCoreVariance_eventually_pos V G z hz hvariance
  have hpow : Tendsto
      (fun n => (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ))
      atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 2 / 3)).comp hvariance
    simpa only [neg_div] using h
  have hboundReal : Tendsto
      (fun n => lowActivityCQ *
        (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ) / epsilon ^ 2)
      atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow).div_const (epsilon ^ 2)
  have hbound : Tendsto
      (fun n => ENNReal.ofReal (lowActivityCQ *
        (hardCoreVariance V G z hz n) ^ (-2 / 3 : ℝ) / epsilon ^ 2))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hboundReal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal)) atTop (nhds 0))
    hbound
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hVarPos] with n hn
    exact predictableQuadraticVariation_deviation_measure_le_B59
      V G hG z hz R n (hz15 n) hn epsilon hepsilon

/-- The integrated conditional Lindeberg sum of one positive-variance row is
bounded by the normalized cubic moment from B.48. -/
private lemma conditionalLindebergSum_integral_le_B60
    (n : ℕ) (hz15 : z n ≤ 3 / 2)
    (hVar : 0 < hardCoreVariance V G z hz n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    (∫ ω,
      ArrayData.conditionalLindebergSum
        (normalizedHardCoreSeedArray V G hG z hz R) epsilon n ω
      ∂actualSeedMeasure V G z hz R n) ≤
      (lowActivityC3 / Real.sqrt (hardCoreVariance V G z hz n)) / epsilon := by
  let A := normalizedHardCoreSeedArray V G hG z hz R
  let μ := actualSeedMeasure V G z hz R n
  let L := hardCoreBernoulliSeedLaw (R n) (z n) (hz n)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, actualSeedMeasure]
    infer_instance
  have hIntegral :
      (∫ ω, A.conditionalLindebergSum epsilon n ω ∂μ) =
        ∑ k : Fin (Fintype.card (V n)),
          ∑ η : BernoulliAssignment (V n), L.probability η *
            (if epsilon < |A.increment n k η| then
              (A.increment n k η) ^ 2 else 0) := by
    calc
      (∫ ω, A.conditionalLindebergSum epsilon n ω ∂μ) =
          ∑ k : Fin (Fintype.card (V n)), ∫ ω,
            μ[fun η => if epsilon < |A.increment n k η| then
              (A.increment n k η) ^ 2 else 0 |
                A.filtration n k.val] ω ∂μ := by
          change (∫ ω, ∑ k : Fin (Fintype.card (V n)),
            μ[fun η => if epsilon < |A.increment n k η| then
              (A.increment n k η) ^ 2 else 0 |
                A.filtration n k.val] ω ∂μ) = _
          rw [integral_finset_sum Finset.univ]
          intro k hk
          exact integrable_condExp
      _ = ∑ k : Fin (Fintype.card (V n)), ∫ η,
            (if epsilon < |A.increment n k η| then
              (A.increment n k η) ^ 2 else 0) ∂μ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_condExp ((A.filtration n).le k.val)]
      _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          dsimp only [μ, L, actualSeedMeasure]
          rw [FiniteLatticeLaw.integral_toMeasure_eq_sum]
  have htail : ∀ (k : Fin (Fintype.card (V n)))
      (η : BernoulliAssignment (V n)),
      (if epsilon < |A.increment n k η| then
        (A.increment n k η) ^ 2 else 0) ≤
          |A.increment n k η| ^ 3 / epsilon := by
    intro k η
    by_cases hlarge : epsilon < |A.increment n k η|
    · rw [if_pos hlarge]
      apply (le_div_iff₀ hepsilon).2
      calc
        (A.increment n k η) ^ 2 * epsilon =
            epsilon * |A.increment n k η| ^ 2 := by
          rw [sq_abs]
          ring
        _ ≤ |A.increment n k η| * |A.increment n k η| ^ 2 :=
          mul_le_mul_of_nonneg_right hlarge.le (sq_nonneg _)
        _ = |A.increment n k η| ^ 3 := by ring
    · rw [if_neg hlarge]
      exact div_nonneg (pow_nonneg (abs_nonneg _) 3) hepsilon.le
  have hVar' : 0 < (hardCoreLaw (G n) (z n) (hz n)).variance := hVar
  have hcubic :
      (∑ k : Fin (Fintype.card (V n)),
        ∑ η : BernoulliAssignment (V n), L.probability η *
          |A.increment n k η| ^ 3) ≤
        lowActivityC3 / Real.sqrt (hardCoreVariance V G z hz n) := by
    simpa [A, L, normalizedHardCoreSeedArray, normalizedSeedDoobEntry,
      hVar', hardCoreVariance] using
      (sum_normalized_finiteDoobIncrement_abs_cube_le_B48
        (hG n) (R n) (z n) (hz n) hz15 hVar)
  rw [show (∫ ω,
      ArrayData.conditionalLindebergSum
        (normalizedHardCoreSeedArray V G hG z hz R) epsilon n ω
      ∂actualSeedMeasure V G z hz R n) =
      ∫ ω, A.conditionalLindebergSum epsilon n ω ∂μ by rfl]
  rw [hIntegral]
  calc
    (∑ k : Fin (Fintype.card (V n)),
        ∑ η : BernoulliAssignment (V n), L.probability η *
          (if epsilon < |A.increment n k η| then
            (A.increment n k η) ^ 2 else 0)) ≤
        ∑ k : Fin (Fintype.card (V n)),
          ∑ η : BernoulliAssignment (V n), L.probability η *
            (|A.increment n k η| ^ 3 / epsilon) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro η hη
      exact mul_le_mul_of_nonneg_left (htail k η) (L.probability_nonneg η)
    _ = (∑ k : Fin (Fintype.card (V n)),
          ∑ η : BernoulliAssignment (V n), L.probability η *
            |A.increment n k η| ^ 3) / epsilon := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro η hη
      exact (mul_div_assoc (L.probability η)
        (|A.increment n k η| ^ 3) epsilon).symm
    _ ≤ (lowActivityC3 / Real.sqrt (hardCoreVariance V G z hz n)) /
          epsilon :=
      div_le_div_of_nonneg_right hcubic hepsilon.le

/-- Quantitative B.60 tail estimate for one positive-variance row. -/
private lemma conditionalLindebergSum_deviation_measure_le_B60
    (n : ℕ) (hz15 : z n ≤ 3 / 2)
    (hVar : 0 < hardCoreVariance V G z hz n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (delta : ℝ) (hdelta : 0 < delta) :
    actualSeedMeasure V G z hz R n
        {ω | delta ≤
          |ArrayData.conditionalLindebergSum
              (normalizedHardCoreSeedArray V G hG z hz R) epsilon n ω - 0|} ≤
      ENNReal.ofReal (((lowActivityC3 /
        Real.sqrt (hardCoreVariance V G z hz n)) / epsilon) / delta) := by
  let A := normalizedHardCoreSeedArray V G hG z hz R
  let μ := actualSeedMeasure V G z hz R n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, actualSeedMeasure]
    infer_instance
  have hterm : ∀ k : Fin (Fintype.card (V n)),
      0 ≤ᵐ[μ] μ[fun η =>
        if epsilon < |A.increment n k η| then
          (A.increment n k η) ^ 2 else 0 | A.filtration n k.val] := by
    intro k
    exact condExp_nonneg (Filter.Eventually.of_forall (fun η => by
      change (0 : ℝ) ≤ if epsilon < |A.increment n k η| then
        (A.increment n k η) ^ 2 else 0
      by_cases hlarge : epsilon < |A.increment n k η|
      · rw [if_pos hlarge]
        exact sq_nonneg _
      · rw [if_neg hlarge]))
  have hall : ∀ᵐ ω ∂μ, ∀ k : Fin (Fintype.card (V n)),
      0 ≤ μ[fun η =>
        if epsilon < |A.increment n k η| then
          (A.increment n k η) ^ 2 else 0 | A.filtration n k.val] ω :=
    (ae_all_iff).2 hterm
  have hnonneg : 0 ≤ᵐ[μ] A.conditionalLindebergSum epsilon n := by
    filter_upwards [hall] with ω hω
    unfold ArrayData.conditionalLindebergSum
    exact Finset.sum_nonneg (fun k _ => hω k)
  have hIntegral :
      (∫ ω, A.conditionalLindebergSum epsilon n ω ∂μ) ≤
        (lowActivityC3 / Real.sqrt (hardCoreVariance V G z hz n)) /
          epsilon := by
    exact conditionalLindebergSum_integral_le_B60
      V G hG z hz R n hz15 hVar epsilon hepsilon
  have hevent :
      μ {ω | delta ≤ |A.conditionalLindebergSum epsilon n ω - 0|} =
        μ {ω | delta ≤ A.conditionalLindebergSum epsilon n ω} := by
    apply measure_congr
    filter_upwards [hnonneg] with ω hω
    have hω' : 0 ≤ A.conditionalLindebergSum epsilon n ω := by
      simpa using hω
    change (delta ≤ |A.conditionalLindebergSum epsilon n ω - 0|) =
      (delta ≤ A.conditionalLindebergSum epsilon n ω)
    rw [sub_zero, abs_of_nonneg hω']
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := A.conditionalLindebergSum epsilon n)
    hnonneg Integrable.of_finite delta
  have hreal :
      μ.real {ω | delta ≤ A.conditionalLindebergSum epsilon n ω} ≤
        ((lowActivityC3 / Real.sqrt (hardCoreVariance V G z hz n)) /
          epsilon) / delta := by
    apply (le_div_iff₀' hdelta).2
    exact hmarkov.trans hIntegral
  change μ {ω | delta ≤ |A.conditionalLindebergSum epsilon n ω - 0|} ≤ _
  rw [hevent]
  calc
    μ {ω | delta ≤ A.conditionalLindebergSum epsilon n ω} =
        ENNReal.ofReal
          (μ.real {ω | delta ≤ A.conditionalLindebergSum epsilon n ω}) := by
      exact (ENNReal.ofReal_toReal
        (measure_ne_top μ
          {ω | delta ≤ A.conditionalLindebergSum epsilon n ω})).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- B.60: the normalized actual seed-law array satisfies the conditional
Lindeberg condition.  The normalized cubic bound B.48 gives an integrated
upper bound, and Markov's inequality gives the required varying-space
convergence in probability. -/
theorem normalizedHardCoreSeedArray_conditionalLindebergCondition
    (hz15 : ∀ n, z n ≤ 3 / 2)
    (hvariance : Tendsto (hardCoreVariance V G z hz) atTop atTop) :
    ArrayData.ConditionalLindebergCondition
      (normalizedHardCoreSeedArray V G hG z hz R) := by
  intro epsilon hepsilon delta hdelta
  have hVarPos := hardCoreVariance_eventually_pos V G z hz hvariance
  have hsqrt : Tendsto
      (fun n => Real.sqrt (hardCoreVariance V G z hz n)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hvariance
  have hbase : Tendsto
      (fun n => lowActivityC3 /
        Real.sqrt (hardCoreVariance V G z hz n)) atTop (nhds 0) :=
    hsqrt.const_div_atTop lowActivityC3
  have hboundReal : Tendsto
      (fun n => ((lowActivityC3 /
        Real.sqrt (hardCoreVariance V G z hz n)) / epsilon) / delta)
      atTop (nhds 0) := by
    simpa using (hbase.div_const epsilon).div_const delta
  have hbound : Tendsto
      (fun n => ENNReal.ofReal (((lowActivityC3 /
        Real.sqrt (hardCoreVariance V G z hz n)) / epsilon) / delta))
      atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hboundReal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal)) atTop (nhds 0))
    hbound
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hVarPos] with n hn
    exact conditionalLindebergSum_deviation_measure_le_B60
      V G hG z hz R n (hz15 n) hn epsilon hepsilon delta hdelta

/-- The normalized array row sum is exactly the standardized generated
occupation count.  The zero fallback also agrees when the variance vanishes,
since finite-law variance is nonnegative and division by zero is zero. -/
theorem normalizedHardCoreSeedArray_rowSum_eq_standardizedGeneratedCount
    (n : ℕ) (ω : ActualSeedSpace V n) :
    (normalizedHardCoreSeedArray V G hG z hz R).rowSum n ω =
      (generatedCountReal (hG n) (R n) ω -
        (hardCoreLaw (G n) (z n) (hz n)).mean) /
      Real.sqrt (hardCoreLaw (G n) (z n) (hz n)).variance := by
  by_cases hVar : 0 < hardCoreVariance V G z hz n
  · unfold ArrayData.rowSum
    simp_rw [normalizedHardCoreSeedArray, normalizedSeedDoobEntry, if_pos hVar]
    rw [← Finset.sum_div]
    congr 1
    simpa [generatedCountLaw] using
      (actualHardCore_centeredCount_eq_sum_finiteDoobIncrement
        (hG n) (R n) (z n) (hz n) (parentFirstEquiv (R n)) ω).symm
  · have hzero : hardCoreVariance V G z hz n = 0 := by
      apply le_antisymm (le_of_not_gt hVar)
      exact (hardCoreLaw (G n) (z n) (hz n)).variance_nonneg
    have hzero' : (hardCoreLaw (G n) (z n) (hz n)).variance = 0 := by
      simpa [hardCoreVariance] using hzero
    have hVar' : ¬0 < (hardCoreLaw (G n) (z n) (hz n)).variance := by
      simpa [hardCoreVariance] using hVar
    unfold ArrayData.rowSum
    simp [normalizedHardCoreSeedArray, normalizedSeedDoobEntry, hzero, hzero']

/-- The generic varying-space martingale-array CLT applied to the compiled
actual seed-law rows. -/
theorem normalizedHardCoreSeedArray_rowSum_tendstoInDistribution
    (hz15 : ∀ n, z n ≤ 3 / 2)
    (hvariance : Tendsto (hardCoreVariance V G z hz) atTop atTop) :
    TendstoInDistribution
      (normalizedHardCoreSeedArray V G hG z hz R).rowSum atTop
      (id : ℝ → ℝ)
      (normalizedHardCoreSeedArray V G hG z hz R).probability
      (gaussianReal 0 1) := by
  let A := normalizedHardCoreSeedArray V G hG z hz R
  change TendstoInDistribution A.rowSum atTop (id : ℝ → ℝ)
    A.probability (gaussianReal 0 1)
  exact A.varyingSpaceMartingaleArrayCLT
    (by simpa [A] using
      normalizedHardCoreSeedArray_isMartingaleDifferenceArray V G hG z hz R)
    (by simpa [A] using
      (normalizedHardCoreSeedArray_predictableQuadraticVariationCondition
        V G hG z hz R hz15 hvariance))
    (by simpa [A] using
      (normalizedHardCoreSeedArray_conditionalLindebergCondition
        V G hG z hz R hz15 hvariance))
    ℝ inferInstance (gaussianReal 0 1) inferInstance
    (id : ℝ → ℝ) ProbabilityTheory.HasLaw.id

/-- Appendix B.2 with an explicit (mathematically inessential) choice of one
root in every component of every forest. -/
theorem actualLowActivityCLT_of_rooting
    (hG : ∀ n, (G n).IsAcyclic)
    (R : (n : ℕ) → ComponentRooting (G n))
    (hz15 : ∀ n, z n ≤ 3 / 2)
    (hvariance : Tendsto
      (fun n => (hardCoreLaw (G n) (z n) (hz n)).variance) atTop atTop) :
    LowActivityCLTStatement V G z hz := by
  let A := normalizedHardCoreSeedArray V G hG z hz R
  have hvariance' : Tendsto (hardCoreVariance V G z hz) atTop atTop := by
    simpa [hardCoreVariance] using hvariance
  have hrow : TendstoInDistribution A.rowSum atTop (id : ℝ → ℝ)
      A.probability (gaussianReal 0 1) := by
    simpa [A] using normalizedHardCoreSeedArray_rowSum_tendstoInDistribution
      V G hG z hz R hz15 hvariance'
  let X : (n : ℕ) → ActualSeedSpace V n → ℝ := fun n ω =>
    (generatedCountReal (hG n) (R n) ω -
      (hardCoreLaw (G n) (z n) (hz n)).mean) /
      Real.sqrt (hardCoreLaw (G n) (z n) (hz n)).variance
  have hgenerated : TendstoInDistribution X atTop (id : ℝ → ℝ)
      A.probability (gaussianReal 0 1) := by
    exact TendstoInDistribution.congr
      (fun n => Filter.Eventually.of_forall (fun ω =>
        normalizedHardCoreSeedArray_rowSum_eq_standardizedGeneratedCount
          V G hG z hz R n ω))
      (Filter.Eventually.of_forall (fun x => rfl)) hrow
  have hident : ∀ n, IdentDistrib (X n)
      (standardizedHardCoreCount (G n) (z n) (hz n))
      (A.probability n)
      (hardCoreLaw (G n) (z n) (hz n)).statPMF.toMeasure := by
    intro n
    let Lg := generatedCountLaw (hG n) (R n) (z n) (hz n)
    let Lh := hardCoreLaw (G n) (z n) (hz n)
    have hrank : ∀ k, Lg.rankMass k = Lh.rankMass k := by
      simpa [Lg, Lh] using
        (exactHardCoreCountCoupling_of_fiberMass
          (hG n) (R n) (z n) (hz n))
    have hPMF : Lg.statPMF = Lh.statPMF :=
      FiniteLatticeLaw.statPMF_eq_of_rankMass_eq Lg Lh hrank
    have hcount0 := FiniteLatticeLaw.hasLaw_stat Lg
    rw [hPMF] at hcount0
    have hcount : HasLaw Lg.stat Lh.statPMF.toMeasure
        (actualSeedMeasure V G z hz R n) := by
      simpa [Lg, actualSeedMeasure, generatedCountLaw] using hcount0
    have hid : HasLaw (id : ℕ → ℕ) Lh.statPMF.toMeasure
        Lh.statPMF.toMeasure := ProbabilityTheory.HasLaw.id
    let u : ℕ → ℝ := fun k => standardizedHardCoreCount
      (G n) (z n) (hz n) k
    have hident' := (hcount.identDistrib hid).comp (measurable_of_countable u)
    simpa [A, X, u, Lg, Lh, Function.comp_def, standardizedHardCoreCount,
      generatedCountLaw, generatedCountReal] using hident'
  exact {
    forall_aemeasurable := fun n => (hident n).aemeasurable_snd
    aemeasurable_limit := hgenerated.aemeasurable_limit
    tendsto := by
      convert hgenerated.tendsto using 2 with n
      apply ProbabilityMeasure.toMeasure_injective
      exact (hident n).map_eq.symm
  }

end ActualArray

end

end Erdos993.Forest.ActualLowActivityCLT

namespace Erdos993.Forest

open Filter MeasureTheory ProbabilityTheory

universe u

noncomputable section

/-- **Theorem B.2 (low-activity hard-core CLT on finite forests).**

For any sequence of finite forests at activities at most `3 / 2`, divergence
of the actual hard-core occupation-count variance implies convergence of the
standardized canonical occupation count to the standard Gaussian.  Component
rootings are internal proof data, selected from the compiled existence theorem
and absent from the public statement. -/
theorem actualLowActivityCLT
    (V : ℕ → Type u) [∀ n, Fintype (V n)]
    (G : (n : ℕ) → SimpleGraph (V n))
    (hG : ∀ n, (G n).IsAcyclic)
    (z : ℕ → ℝ) (hz : ∀ n, 0 < z n)
    (hz15 : ∀ n, z n ≤ 3 / 2)
    (hvariance :
      Tendsto
        (fun n => (hardCoreLaw (G n) (z n) (hz n)).variance)
        atTop atTop) :
    LowActivityCLTStatement V G z hz := by
  let R : (n : ℕ) →
      Erdos993.ActualRootedVariance.ComponentRooting (G n) := fun n =>
    Classical.choice
      (Erdos993.ActualRootedVariance.nonempty_componentRooting (G n))
  exact ActualLowActivityCLT.actualLowActivityCLT_of_rooting
    V G z hz hG R hz15 hvariance

end

end Erdos993.Forest
