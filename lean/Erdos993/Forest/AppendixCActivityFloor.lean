import Erdos993.Forest.CanonicalFullDomainEnvelope
import Erdos993.Forest.ActualLowActivityCLTArray

open Filter MeasureTheory ProbabilityTheory Complex Real Set
open scoped BigOperators ENNReal NNReal Topology
open Erdos993.MeasureFourierInversion

namespace Erdos993.Forest.AppendixC

noncomputable section

lemma charFun_standardGaussian_real (t : ℝ) :
    charFun (gaussianReal 0 1) t =
      ((Real.exp (-((1 : ℝ) / 2) * t ^ 2) : ℝ) : ℂ) := by
  rw [charFun_gaussianReal]
  push_cast
  simp only [mul_zero, zero_mul, zero_sub]
  congr 1
  ring

lemma integrable_sq_mul_standardGaussianKernel :
    Integrable (fun t : ℝ => t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2)) := by
  simpa [Real.rpow_two, sq_abs] using
    (integrable_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
      (s := (2 : ℝ)) (by norm_num))

lemma integral_sq_mul_standardGaussianKernel_pos :
    0 < ∫ t : ℝ, t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2) := by
  let f : ℝ → ℝ := fun t => t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2)
  have hfnonneg : 0 ≤ f := by
    intro t
    exact mul_nonneg (sq_nonneg t) (Real.exp_pos _).le
  have hfint : Integrable f := by
    simpa [f] using integrable_sq_mul_standardGaussianKernel
  rw [integral_pos_iff_support_of_nonneg hfnonneg hfint]
  have hvol : 0 < volume (Set.Ioo (1 : ℝ) 2) := by
    rw [Real.volume_Ioo]
    norm_num
  exact lt_of_lt_of_le hvol (measure_mono (by
    intro x hx
    change f x ≠ 0
    dsimp [f]
    exact mul_ne_zero (pow_ne_zero 2 (by linarith [hx.1])) (Real.exp_ne_zero _)))

lemma inverseCharFunDensity_standardGaussian_zero_pos :
    0 < inverseCharFunDensity (gaussianReal 0 1) 0 := by
  have hi :
      (∫ t : ℝ, inversePhase t 0 * charFun (gaussianReal 0 1) t) =
        (((∫ t : ℝ, Real.exp (-((1 : ℝ) / 2) * t ^ 2)) : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ, inversePhase t 0 * charFun (gaussianReal 0 1) t) =
          ∫ t : ℝ, ((Real.exp (-((1 : ℝ) / 2) * t ^ 2) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [charFun_standardGaussian_real]
        simp [inversePhase]
      _ = (((∫ t : ℝ, Real.exp (-((1 : ℝ) / 2) * t ^ 2)) : ℝ) : ℂ) :=
        integral_ofReal
  rw [inverseCharFunDensity, inverseCharFun, hi, integral_gaussian]
  rw [← ofReal_inv, ← ofReal_mul]
  simp only [ofReal_re]
  positivity

lemma inverseCharFunDerivTwo_standardGaussian_zero_neg :
    (inverseCharFunDerivTwo (gaussianReal 0 1) 0).re < 0 := by
  have hi :
      (∫ t : ℝ, (-((t ^ 2 : ℝ) : ℂ)) * inversePhase t 0 *
          charFun (gaussianReal 0 1) t) =
        (((- ∫ t : ℝ, t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2)) : ℝ) : ℂ) := by
    calc
      (∫ t : ℝ, (-((t ^ 2 : ℝ) : ℂ)) * inversePhase t 0 *
          charFun (gaussianReal 0 1) t) =
          ∫ t : ℝ, (((-(t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2))) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [charFun_standardGaussian_real]
        simp [inversePhase]
      _ = (((∫ t : ℝ, -(t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2))) : ℝ) : ℂ) :=
        integral_ofReal
      _ = (((- ∫ t : ℝ, t ^ 2 * Real.exp (-((1 : ℝ) / 2) * t ^ 2)) : ℝ) : ℂ) := by
        rw [integral_neg]
  rw [inverseCharFunDerivTwo, hi]
  rw [← ofReal_inv, ← ofReal_mul]
  simp only [ofReal_re]
  exact mul_neg_of_pos_of_neg (by positivity)
    (neg_neg_of_pos integral_sq_mul_standardGaussianKernel_pos)

lemma standardGaussian_inverseCurvature_pos :
    0 < (inverseCharFunDerivOne (gaussianReal 0 1) 0).re ^ 2 -
      inverseCharFunDensity (gaussianReal 0 1) 0 *
        (inverseCharFunDerivTwo (gaussianReal 0 1) 0).re := by
  have h0 := inverseCharFunDensity_standardGaussian_zero_pos
  have h2 := inverseCharFunDerivTwo_standardGaussian_zero_neg
  nlinarith [sq_nonneg (inverseCharFunDerivOne (gaussianReal 0 1) 0).re]

open CanonicalCompactnessWrapper

/-- The bounded canonical rank PMF, embedded in `ℕ`, is the native hard-core count PMF. -/
theorem rankPMF_map_val_eq_statPMF
    (S : CanonicalSequence) (n : ℕ) :
    PMF.map (fun k : Fin (S.order n + 1) => (k : ℕ)) (S.rankPMF n) =
      (S.state n).law.statPMF := by
  apply PMF.ext
  intro k
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.map_apply, tsum_fintype]
  rw [FiniteLatticeLaw.statPMF_apply_toReal]
  by_cases hk : k < S.order n + 1
  · let k0 : Fin (S.order n + 1) := ⟨k, hk⟩
    rw [Finset.sum_eq_single k0]
    · simp [k0, CanonicalSequence.rankPMF_apply]
    · intro b hb hne
      have hval : k ≠ (b : ℕ) := by
        intro h
        apply hne
        apply Fin.ext
        exact h.symm
      simp [hval]
    · simp
  · have horder : S.order n < k := by omega
    rw [Finset.sum_eq_zero]
    · have hz :=
        (S.state n).law_rankMass_eq_zero_of_order_lt k (by
          simpa [CanonicalFirstRecoveryState.order] using horder)
      simpa using hz.symm
    · intro b hb
      have hval : k ≠ (b : ℕ) := by
        intro h
        have := b.isLt
        omega
      simp [hval]

/-- The compactness wrapper's standardized law is exactly the actual B.2 count law. -/
theorem standardizedLaw_eq_actualCountMap
    (S : CanonicalSequence) (n : ℕ) :
    S.standardizedLaw n =
      ProbabilityMeasure.map
        (⟨(S.state n).law.statPMF.toMeasure, inferInstance⟩ : ProbabilityMeasure ℕ)
        (measurable_of_countable
          (standardizedHardCoreCount (S.graph n) (S.state n).activity
            (S.state n).activity_pos)).aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (S.standardizedRank n) (S.rankPMF n).toMeasure = _
  let val : Fin (S.order n + 1) → ℕ := fun k => (k : ℕ)
  let std : ℕ → ℝ := standardizedHardCoreCount (S.graph n)
    (S.state n).activity (S.state n).activity_pos
  have hfun : S.standardizedRank n = std ∘ val := by
    funext k
    simp only [CanonicalSequence.standardizedRank, std, val,
      standardizedHardCoreCount, Function.comp_apply]
    rw [(S.state n).mean_eq_index]
    rfl
  rw [hfun]
  rw [PMF.toMeasure_map (std ∘ val) (S.rankPMF n) (by
    rw [← hfun]
    exact measurable_of_finite _)]
  change (PMF.map (std ∘ val) (S.rankPMF n)).toMeasure =
    Measure.map std (S.state n).law.statPMF.toMeasure
  rw [PMF.toMeasure_map std (S.state n).law.statPMF (measurable_of_countable std)]
  rw [← PMF.map_comp val (S.rankPMF n) std]
  rw [rankPMF_map_val_eq_statPMF S n]

/-- Actual B.2 therefore identifies the wrapper's low-activity weak limit. -/
theorem standardizedLaw_tendsto_standardGaussian
    (S : CanonicalSequence)
    (hz15 : ∀ n, (S.state n).activity ≤ (3 : ℝ) / 2) :
    Tendsto S.standardizedLaw atTop
      (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hclt := actualLowActivityCLT
    (fun n => Fin (S.order n)) S.graph (fun n => (S.state n).isForest)
    (fun n => (S.state n).activity) (fun n => (S.state n).activity_pos)
    hz15 (by simpa [CanonicalCompactnessWrapper.CanonicalSequence.V,
      CanonicalFirstRecoveryState.variance, CanonicalFirstRecoveryState.law] using
      S.variance_tendsto)
  have ht := hclt.tendsto
  have ht' :
      Tendsto (fun n =>
        ProbabilityMeasure.map
          (⟨(S.state n).law.statPMF.toMeasure, inferInstance⟩ : ProbabilityMeasure ℕ)
          (measurable_of_countable
            (standardizedHardCoreCount (S.graph n) (S.state n).activity
              (S.state n).activity_pos)).aemeasurable)
        atTop (𝓝 (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
    simpa only [Measure.map_id] using ht
  refine ht'.congr' ?_
  filter_upwards with n
  exact (standardizedLaw_eq_actualCountMap S n).symm

/-- There is no canonical first-recovery sequence whose activities all stay in
    the B.2 low-activity regime. -/
theorem CanonicalSequence.not_forall_activity_le_three_halves
    (S : CanonicalSequence)
    (hz15 : ∀ n, (S.state n).activity ≤ (3 : ℝ) / 2) : False := by
  let γ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hweak : Tendsto S.standardizedLaw atTop (𝓝 γ) := by
    simpa [γ] using standardizedLaw_tendsto_standardGaussian S hz15
  have hchar : ∀ u : ℝ,
      Tendsto (fun n => S.characteristic n u) atTop (𝓝 (charFun γ u)) := by
    intro u
    have hchars := (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hweak u
    simpa [CanonicalCompactnessWrapper.CanonicalSequence.characteristic,
      Function.comp_def] using hchars
  have hA := AppendixA.CanonicalSequence.fullDomainEnvelope_of_appendixA4
    S γ id strictMono_id hchar
  have hlim :=
    CanonicalCompactnessWrapper.CanonicalSequence.fourier_turan_curvature_limit_of_fullDomainEnvelope
      S γ id (AppendixA.appendixA4Envelope 27) strictMono_id hweak hA
  have hnonpos : ∀ n : ℕ,
      (S.V n) ^ 2 *
        ((S.centeredMass n 0) ^ 2 -
          S.centeredMass n (-1) * S.centeredMass n 1) ≤ 0 := by
    intro n
    have hrev := S.centered_mass_strict_reverse_turan n
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (S.V n)) (by linarith)
  have hlimit_nonpos :
      (Erdos993.MeasureFourierInversion.inverseCharFunDerivOne
          (gaussianReal 0 1) 0).re ^ 2 -
        Erdos993.MeasureFourierInversion.inverseCharFunDensity
            (gaussianReal 0 1) 0 *
          (Erdos993.MeasureFourierInversion.inverseCharFunDerivTwo
            (gaussianReal 0 1) 0).re ≤ 0 := by
    have hh := le_of_tendsto hlim (Filter.Eventually.of_forall hnonpos)
    simpa [γ, Function.comp_def] using hh
  exact (not_le_of_gt standardGaussian_inverseCurvature_pos) hlimit_nonpos

/-- Uniform finite activity floor for canonical states already presented on `Fin N`.
    This is the compactness/contradiction form of Appendix C.1. -/
theorem exists_uniform_activity_floor_fin :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N))
        (C : CanonicalFirstRecoveryState G),
        C.activity < 27 → T ≤ C.variance → (3 : ℝ) / 2 < C.activity := by
  by_contra h
  push Not at h
  have hbad : ∀ n : ℕ,
      ∃ (N : ℕ) (G : SimpleGraph (Fin N))
        (C : CanonicalFirstRecoveryState G),
        C.activity < 27 ∧ ((n : ℝ) + 1) ≤ C.variance ∧
          C.activity ≤ (3 : ℝ) / 2 := by
    intro n
    obtain ⟨N, G, C, hz27, hV, hz15⟩ := h ((n : ℝ) + 1) (by positivity)
    exact ⟨N, G, C, hz27, hV, hz15⟩
  choose N G C hz27 hV hz15 using hbad
  let S : CanonicalSequence := {
    order := N
    graph := G
    state := C
    activity_lt := hz27
    variance_pos := fun n => by linarith [hV n]
    variance_tendsto := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (Nat.ceil (max 0 b))] with n hn
      have hceil : b ≤ (Nat.ceil (max 0 b) : ℝ) :=
        le_trans (le_max_right 0 b) (Nat.le_ceil (max 0 b))
      have hnreal : (Nat.ceil (max 0 b) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      exact hceil.trans (hnreal.trans (by linarith [hV n])) }
  exact Erdos993.Forest.AppendixC.CanonicalSequence.not_forall_activity_le_three_halves
    S hz15

universe u v

/-- Independence coefficients are invariant under graph isomorphism. -/
theorem independenceCoefficients_eq_of_graphIso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    independenceCoefficients G = independenceCoefficients H := by
  funext k
  unfold independenceCoefficients
  norm_cast
  rw [← coeff_independencePolynomial G k,
    ← coeff_independencePolynomial H k,
    independencePolynomial_iso e]

/-- Independence evaluation is invariant under graph isomorphism. -/
theorem independenceEval_eq_of_graphIso'
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (z : ℝ) :
    independenceEval G z = independenceEval H z := by
  rw [independenceEval_eq_eval₂, independenceEval_eq_eval₂,
    independencePolynomial_iso e]

/-- Hard-core means are invariant under relabeling. -/
theorem hardCoreLaw_mean_eq_of_graphIso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean = (hardCoreLaw H z hz).mean := by
  rw [hardCoreLaw_mean_eq_sum_coefficients G z hz,
    hardCoreLaw_mean_eq_sum_coefficients H z hz,
    e.card_eq,
    independenceCoefficients_eq_of_graphIso e,
    independenceEval_eq_of_graphIso' e z]

/-- Hard-core variances are invariant under relabeling. -/
theorem hardCoreLaw_variance_eq_of_graphIso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).variance = (hardCoreLaw H z hz).variance := by
  rw [hardCoreLaw_variance_eq_sum_coefficients G z hz,
    hardCoreLaw_variance_eq_sum_coefficients H z hz,
    e.card_eq,
    independenceCoefficients_eq_of_graphIso e,
    independenceEval_eq_of_graphIso' e z,
    hardCoreLaw_mean_eq_of_graphIso e z hz]

/-- Relabel a global canonical first-recovery state along a graph isomorphism. -/
noncomputable def canonicalStateMapIso
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState G) (e : G ≃g H) :
    CanonicalFirstRecoveryState H where
  isForest := e.isAcyclic_iff.mp C.isForest
  index := C.index
  firstRecovery := by
    rw [← independenceCoefficients_eq_of_graphIso e]
    exact C.firstRecovery
  activity := C.activity
  activity_pos := C.activity_pos
  mean_eq_index := by
    rw [← hardCoreLaw_mean_eq_of_graphIso e C.activity C.activity_pos]
    exact C.mean_eq_index

@[simp] theorem canonicalStateMapIso_index
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState G) (e : G ≃g H) :
    (canonicalStateMapIso C e).index = C.index := rfl

@[simp] theorem canonicalStateMapIso_activity
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState G) (e : G ≃g H) :
    (canonicalStateMapIso C e).activity = C.activity := rfl

@[simp] theorem canonicalStateMapIso_variance
    {V : Type u} {W : Type v} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState G) (e : G ≃g H) :
    (canonicalStateMapIso C e).variance = C.variance := by
  unfold CanonicalFirstRecoveryState.variance CanonicalFirstRecoveryState.law
  exact (hardCoreLaw_variance_eq_of_graphIso e C.activity C.activity_pos).symm

/-- Appendix C.1 for arbitrary finite vertex types, obtained only by relabeling
    the original global graph and its original global canonical state. -/
theorem exists_uniform_activity_floor :
    ∃ T : ℝ, 0 ≤ T ∧
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V)
        (C : CanonicalFirstRecoveryState G),
        C.activity < 27 → T ≤ C.variance → (3 : ℝ) / 2 < C.activity := by
  obtain ⟨T, hT, hfin⟩ := exists_uniform_activity_floor_fin
  refine ⟨T, hT, ?_⟩
  intro V _ G C hz27 hvar
  let Gfin : SimpleGraph (Fin (Fintype.card V)) := G.overFin rfl
  let e : G ≃g Gfin := G.overFinIso rfl
  let Cfin : CanonicalFirstRecoveryState Gfin := canonicalStateMapIso C e
  have h := hfin (Fintype.card V) Gfin Cfin (by simpa [Cfin]) (by simpa [Cfin])
  simpa [Cfin] using h

end
end Erdos993.Forest.AppendixC
