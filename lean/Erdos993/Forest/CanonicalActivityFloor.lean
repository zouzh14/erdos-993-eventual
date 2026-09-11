import Erdos993.Forest.ActualLowActivityCLTArray
import Erdos993.Forest.CanonicalFullDomainEnvelope

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos993.Forest.CanonicalCompactnessWrapper
noncomputable section
open Erdos993.MeasureFourierInversion
namespace CanonicalSequence

lemma rankPMF_map_val (S : CanonicalSequence) (n : ℕ) :
    (S.rankPMF n).map (fun k : Fin (S.order n + 1) => (k : ℕ)) =
      (S.state n).law.statPMF := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal, S.rankPMF_apply]
    rw [(S.state n).law.statPMF_apply_toReal]
    by_cases hk : k < S.order n + 1
    · have hmem : (⟨k, hk⟩ : Fin (S.order n + 1)) ∈ Finset.univ := Finset.mem_univ _
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · rw [if_pos rfl]
      · intro b hb hne
        have hvalne : (b : ℕ) ≠ k := by
          intro hval
          apply hne
          apply Fin.ext
          exact hval
        rw [if_neg (Ne.symm hvalne)]
        simp
      · exact fun hnot => (hnot hmem).elim
    · have hkorder : (S.state n).order < k := by
        simpa [CanonicalFirstRecoveryState.order] using (show S.order n < k by omega)
      have hzero := (S.state n).law_rankMass_eq_zero_of_order_lt k hkorder
      rw [hzero]
      apply Finset.sum_eq_zero
      intro b hb
      have hvalne : (b : ℕ) ≠ k := by
        intro hbk
        have := b.isLt
        omega
      rw [if_neg (Ne.symm hvalne)]
      simp
  · intro b hb
    split_ifs <;> simp [PMF.apply_ne_top]

lemma standardizedLaw_toMeasure_eq_actual
    (S : CanonicalSequence) (n : ℕ) :
    (S.standardizedLaw n : Measure ℝ) =
      ((S.state n).law.statPMF.toMeasure).map
        (standardizedHardCoreCount (S.graph n) (S.state n).activity
          (S.state n).activity_pos) := by
  change Measure.map (S.standardizedRank n) (S.rankPMF n).toMeasure = _
  rw [← S.rankPMF_map_val n]
  rw [← PMF.toMeasure_map]
  · rw [Measure.map_map]
    · apply Measure.map_congr
      filter_upwards with k
      unfold standardizedRank standardizedHardCoreCount V
      have hmean :
          (hardCoreLaw (S.graph n) (S.state n).activity
            (S.state n).activity_pos).mean = ((S.state n).index : ℝ) := by
        simpa [CanonicalFirstRecoveryState.law] using (S.state n).law_mean
      rw [hmean]
      rfl
    · fun_prop
    · exact measurable_of_finite _
  · exact measurable_of_finite _

lemma hasDerivAt_gaussianPDFReal_standard (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hinner : HasDerivAt
      (fun y : ℝ => -(y - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) (-x) x := by
    convert ((((hasDerivAt_id x).sub_const 0).pow 2).neg.div_const
      (2 * ((1 : ℝ≥0) : ℝ))) using 1 <;> norm_num <;> ring
  have hexp := hinner.exp
  have hmul := hexp.const_mul
    (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹
  convert hmul using 1 <;> simp [gaussianPDFReal] <;> ring

lemma standardGaussian_inverse_density_eq
    (γ : ProbabilityMeasure ℝ)
    (hγ : (γ : Measure ℝ) = gaussianReal 0 1)
    {ψ : ℕ → ℝ → ℂ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ (charFun γ) A) :
    gaussianPDFReal 0 1 = inverseCharFunDensity (γ : Measure ℝ) := by
  apply eq_inverseCharFunDensity_of_continuous
  · exact integrable_charFun_of_upToTwo
      (integrableCharFunUpToTwo_of_fullDomainEnvelope hA)
  · unfold gaussianPDFReal
    fun_prop
  · exact gaussianPDFReal_nonneg 0 1
  · rw [hγ, gaussianReal_of_var_ne_zero 0 (by norm_num)]
    rfl

lemma standardGaussian_inverse_curvature_pos
    (γ : ProbabilityMeasure ℝ)
    (hγ : (γ : Measure ℝ) = gaussianReal 0 1)
    {ψ : ℕ → ℝ → ℂ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ (charFun γ) A) :
    0 < ((inverseCharFunDerivOne (γ : Measure ℝ) 0).re) ^ 2 -
      inverseCharFunDensity (γ : Measure ℝ) 0 *
        (inverseCharFunDerivTwo (γ : Measure ℝ) 0).re := by
  have hpack := probabilityFourierInversionUpToTwo_of_fullDomainEnvelope hA
  have hdensity := standardGaussian_inverse_density_eq γ hγ hA
  have hfirst : ∀ x : ℝ,
      (inverseCharFunDerivOne (γ : Measure ℝ) x).re =
        -x * gaussianPDFReal 0 1 x := by
    intro x
    have hinv : HasDerivAt (gaussianPDFReal 0 1)
        (inverseCharFunDerivOne (γ : Measure ℝ) x).re x := by
      rw [hdensity]
      exact hpack.hasDeriv_density x
    exact hinv.unique (hasDerivAt_gaussianPDFReal_standard x)
  have hfirst0 := hfirst 0
  have hderiv_explicit : HasDerivAt
      (fun x : ℝ => -x * gaussianPDFReal 0 1 x)
      (- gaussianPDFReal 0 1 0) 0 := by
    convert ((hasDerivAt_id (𝕜 := ℝ) 0).neg.mul
      (hasDerivAt_gaussianPDFReal_standard 0)) using 1 <;> norm_num
  have hderiv_inverse : HasDerivAt
      (fun x : ℝ => -x * gaussianPDFReal 0 1 x)
      (inverseCharFunDerivTwo (γ : Measure ℝ) 0).re 0 := by
    have heq : (fun x : ℝ => (inverseCharFunDerivOne (γ : Measure ℝ) x).re) =
        (fun x : ℝ => -x * gaussianPDFReal 0 1 x) := funext hfirst
    rw [← heq]
    exact hpack.hasDeriv_derivOne 0
  have hsecond := hderiv_inverse.unique hderiv_explicit
  rw [hfirst0, ← hdensity, hsecond]
  norm_num
  exact (gaussianPDFReal_pos 0 1 0 (by norm_num)).ne'

/-- The actual lower-activity bridge needed in D.38: variance-divergent
canonical first-recovery forests cannot remain in the low-activity regime. -/
theorem eventually_activity_gt_three_halves (S : CanonicalSequence) :
    ∀ᶠ n in atTop, (3 : ℝ) / 2 < (S.state n).activity := by
  by_contra hfloor
  have hfreq : ∃ᶠ n in atTop,
      ¬ ((3 : ℝ) / 2 < (S.state n).activity) :=
    Filter.not_eventually.mp hfloor
  obtain ⟨subseq, hsubseq, hlow⟩ :=
    Filter.extraction_of_frequently_atTop hfreq
  have hz15 : ∀ m, (S.state (subseq m)).activity ≤ (3 : ℝ) / 2 :=
    fun m => le_of_not_gt (hlow m)
  have hvariance :
      Tendsto (fun m =>
        (hardCoreLaw (S.graph (subseq m))
          (S.state (subseq m)).activity
          (S.state (subseq m)).activity_pos).variance) atTop atTop := by
    simpa [V, CanonicalFirstRecoveryState.variance,
      CanonicalFirstRecoveryState.law] using
      S.variance_tendsto.comp hsubseq.tendsto_atTop
  have hCLT := Erdos993.Forest.actualLowActivityCLT
    (fun m => Fin (S.order (subseq m)))
    (fun m => S.graph (subseq m))
    (fun m => (S.state (subseq m)).isForest)
    (fun m => (S.state (subseq m)).activity)
    (fun m => (S.state (subseq m)).activity_pos)
    hz15 hvariance
  let γ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 1, inferInstance⟩
  have hweak : Tendsto (S.standardizedLaw ∘ subseq) atTop (𝓝 γ) := by
    unfold LowActivityCLTStatement at hCLT
    have ht := hCLT.tendsto
    simp only [Measure.map_id] at ht
    apply ht.congr'
    filter_upwards with m
    apply ProbabilityMeasure.toMeasure_injective
    exact (S.standardizedLaw_toMeasure_eq_actual (subseq m)).symm
  have hchar : ∀ u : ℝ,
      Tendsto (fun m => S.characteristic (subseq m) u) atTop
        (𝓝 (charFun γ u)) := by
    intro u
    have h := (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hweak u
    simpa [characteristic, Function.comp_def] using h
  have hA := Erdos993.Forest.AppendixA.CanonicalSequence.fullDomainEnvelope_of_appendixA4
    S γ subseq hsubseq hchar
  have hcurv := fourier_turan_curvature_limit_of_fullDomainEnvelope S γ subseq
    (Erdos993.Forest.AppendixA.appendixA4Envelope 27) hsubseq hweak hA
  have hpos := standardGaussian_inverse_curvature_pos γ rfl hA
  have hevent : ∀ᶠ m in atTop,
      0 < (S.V (subseq m)) ^ 2 *
        ((S.centeredMass (subseq m) 0) ^ 2 -
          S.centeredMass (subseq m) (-1) *
            S.centeredMass (subseq m) 1) :=
    hcurv.eventually (Ioi_mem_nhds hpos)
  obtain ⟨m, hm⟩ := hevent.exists
  have hreverse := S.centered_mass_strict_reverse_turan (subseq m)
  have hVpos := S.variance_pos (subseq m)
  nlinarith [sq_pos_of_pos hVpos]

end CanonicalSequence
end
end Erdos993.Forest.CanonicalCompactnessWrapper
