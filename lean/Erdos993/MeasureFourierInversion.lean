import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.Real

open Filter MeasureTheory Complex Real Set ProbabilityTheory
open scoped ENNReal Topology RealInnerProductSpace FourierTransform NNReal

namespace Erdos993.MeasureFourierInversion

noncomputable section

/-- `e^{-itx}` in the characteristic-function convention used by `charFun`. -/
def inversePhase (t x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((t * x : ℝ) : ℂ))

/-- The inverse characteristic-function integral. -/
def inverseCharFun (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, inversePhase t x * charFun μ t

/-- Its `k`th formal inverse-integral derivative. -/
def inverseCharFunDeriv (μ : Measure ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, (-Complex.I * (t : ℂ)) ^ k *
      inversePhase t x * charFun μ t

@[simp] lemma inverseCharFunDeriv_zero (μ : Measure ℝ) :
    inverseCharFunDeriv μ 0 = inverseCharFun μ := by
  funext x
  simp [inverseCharFunDeriv, inverseCharFun]

/-- The inverse integral is a rescaled Mathlib Fourier transform. -/
lemma inverseCharFun_eq_fourier (μ : Measure ℝ) (x : ℝ) :
    inverseCharFun μ x =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * 𝓕 (charFun μ) (x / (2 * Real.pi)) := by
  rw [inverseCharFun, Real.fourier_real_eq_integral_exp_smul]
  congr 2 with t
  simp only [inversePhase, smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]
def IntegrableCharFunUpToTwo (μ : Measure ℝ) : Prop :=
  ∀ k : ℕ, k ≤ 2 →
    Integrable (fun t : ℝ => (t : ℂ) ^ k * charFun μ t) volume

lemma integrable_charFun_of_upToTwo {μ : Measure ℝ}
    (hφ : IntegrableCharFunUpToTwo μ) : Integrable (charFun μ) volume := by
  simpa using hφ 0 (by omega)

lemma integrable_mul_charFun_of_upToTwo {μ : Measure ℝ}
    (hφ : IntegrableCharFunUpToTwo μ) :
    Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume := by
  simpa using hφ 1 (by omega)

lemma integrable_sq_mul_charFun_of_upToTwo {μ : Measure ℝ}
    (hφ : IntegrableCharFunUpToTwo μ) :
    Integrable (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * charFun μ t) volume := by
  simpa using hφ 2 (by omega)

/-- The inverse integral is continuous. -/
lemma continuous_inverseCharFun {μ : Measure ℝ}
    (hφ : Integrable (charFun μ) volume) : Continuous (inverseCharFun μ) := by
  rw [show inverseCharFun μ = fun x =>
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ * 𝓕 (charFun μ) (x / (2 * Real.pi)) by
    funext x
    exact inverseCharFun_eq_fourier μ x]
  exact continuous_const.mul <|
    (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hφ).comp (by fun_prop)

/-- The uniform norm estimate for the inverse integral. -/
lemma norm_inverseCharFun_le {μ : Measure ℝ}
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    ‖inverseCharFun μ x‖ ≤ (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖charFun μ t‖ := by
  rw [inverseCharFun, norm_mul]
  have hnorm : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  rw [hnorm]
  gcongr
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards with t
  rw [norm_mul, show ‖inversePhase t x‖ = 1 by
    rw [inversePhase, norm_exp]
    norm_num]
  simp

/-- The Gaussian regularizer used in the measure-identification proof. Its integral is `2π`. -/
def gaussianRegularizer (c x : ℝ) : ℂ :=
  (((Real.pi * c) ^ (1 / 2 : ℝ) * Real.exp (-c * x ^ 2 / 4) : ℝ) : ℂ)

lemma gaussianRegularizer_nonneg {c x : ℝ} (hc : 0 ≤ c) :
    0 ≤ (gaussianRegularizer c x).re := by
  rw [gaussianRegularizer, Complex.ofReal_re]
  positivity

/-- The spatial Gaussian has the normalization inherited from the unscaled
characteristic-function convention. -/
lemma gaussianRegularizer_integral (c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, (gaussianRegularizer c x).re = 2 * Real.pi := by
  rw [show (fun x : ℝ => (gaussianRegularizer c x).re) =
      fun x : ℝ => (Real.pi * c) ^ (1 / 2 : ℝ) * Real.exp (-(c / 4) * x ^ 2) by
    funext x
    simp only [gaussianRegularizer, ofReal_re]
    congr 2
    ring]
  rw [integral_const_mul, integral_gaussian (c / 4)]
  have hpc : 0 < Real.pi * c := mul_pos Real.pi_pos hc
  rw [show (Real.pi * c) ^ (1 / 2 : ℝ) = Real.sqrt (Real.pi * c) by
    simpa [Real.sqrt_eq_rpow]]
  rw [← Real.sqrt_mul hpc.le]
  rw [show Real.pi * c * (Real.pi / (c / 4)) = (2 * Real.pi) ^ 2 by
    field_simp [hc.ne']
    norm_num]
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]

lemma gaussianRegularizer_integrable (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => gaussianRegularizer c x) volume := by
  have hbase : Integrable (fun x : ℝ =>
      Complex.exp (-(((c / 4 : ℝ) : ℂ)) * ‖x‖ ^ 2 + (0 : ℂ) * ⟪(0 : ℝ), x⟫)) volume :=
    GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (show 0 < (((c / 4 : ℝ) : ℂ)).re by
        simpa using div_pos hc (by norm_num : (0 : ℝ) < 4)) (0 : ℝ) (0 : ℝ)
  simp only [zero_mul, add_zero] at hbase
  have h := hbase.const_mul (((Real.pi * c) ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  apply h.congr
  filter_upwards with x
  change (((Real.pi * c) ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
      Complex.exp (-(((c / 4 : ℝ) : ℂ)) * (((‖x‖ : ℝ) : ℂ)) ^ 2) =
    (((Real.pi * c) ^ (1 / 2 : ℝ) * Real.exp (-c * x ^ 2 / 4) : ℝ) : ℂ)
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  norm_cast
  simp only [Real.norm_eq_abs]
  rw [sq_abs]
  ring

lemma integral_norm_gaussianRegularizer (c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, ‖gaussianRegularizer c x‖ = 2 * Real.pi := by
  rw [show (fun x : ℝ => ‖gaussianRegularizer c x‖) =
      fun x : ℝ => (gaussianRegularizer c x).re by
    funext x
    rw [gaussianRegularizer]
    simp only [norm_real, ofReal_re, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    exact mul_nonneg (Real.rpow_nonneg (mul_nonneg Real.pi_pos.le hc.le) _)
      (Real.exp_pos _).le]
  exact gaussianRegularizer_integral c hc

/-- The frequency-side Gaussian integral equals a nonnegative spatial Gaussian. -/
lemma integral_gaussian_frequency (c z : ℝ) (hc : 0 < c) :
    (∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w z) =
      gaussianRegularizer c z := by
  have h := fourier_gaussian_innerProductSpace'
    (b := ((c⁻¹ : ℝ) : ℂ)) (V := ℝ)
    (show 0 < (((c⁻¹ : ℝ) : ℂ)).re by simpa using inv_pos.mpr hc)
    (0 : ℝ) (z / (2 * Real.pi))
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simp only [smul_eq_mul, RCLike.inner_apply, map_zero, zero_mul, add_zero,
    Real.norm_eq_abs, sq_abs] at h
  norm_num at h
  calc
    _ = ∫ w : ℝ,
        Complex.exp (-(2 * (Real.pi : ℂ) * (w : ℂ) *
          ((z : ℂ) / (2 * Real.pi)) * Complex.I)) *
        Complex.exp (-((c : ℂ)⁻¹ * ((|w| : ℝ) : ℂ) ^ 2)) := by
      apply integral_congr_ae
      filter_upwards with w
      rw [inversePhase]
      have hphase : -Complex.I * ((w * z : ℝ) : ℂ) =
          -(2 * (Real.pi : ℂ) * (w : ℂ) *
            ((z : ℂ) / (2 * Real.pi)) * Complex.I) := by
        push_cast
        field_simp [Real.pi_ne_zero]
      have hgauss : -((c⁻¹ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2 =
          -((c : ℂ)⁻¹ * ((|w| : ℝ) : ℂ) ^ 2) := by
        simp only [Complex.ofReal_inv, Real.norm_eq_abs]
        ring
      rw [hphase, hgauss]
      ring
    _ = ((Real.pi : ℂ) * (c : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-((Real.pi : ℂ) ^ 2 *
          (((|z / (2 * Real.pi)| : ℝ) : ℂ) ^ 2) * (c : ℂ))) := h
    _ = gaussianRegularizer c z := by
      rw [gaussianRegularizer]
      have hcoef : ((Real.pi : ℂ) * (c : ℂ)) ^ (1 / 2 : ℂ) =
          (((Real.pi * c) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        simpa using
          (Complex.ofReal_cpow (mul_nonneg Real.pi_pos.le hc.le) (1 / 2 : ℝ)).symm
      have harg : -((Real.pi : ℂ) ^ 2 *
          (((|z / (2 * Real.pi)| : ℝ) : ℂ) ^ 2) * (c : ℂ)) =
          ((-c * z ^ 2 / 4 : ℝ) : ℂ) := by
        have habs : (((|z / (2 * Real.pi)| : ℝ) : ℂ) ^ 2) =
            (((z / (2 * Real.pi)) ^ 2 : ℝ) : ℂ) := by
          norm_cast
          exact sq_abs (z / (2 * Real.pi))
        rw [habs]
        push_cast
        field_simp [Real.pi_ne_zero]
        ring
      rw [hcoef, harg, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- The Gaussian-smoothed inverse integral, after the justified Fubini exchange. -/
lemma integral_gaussian_charFun_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) (x : ℝ) :
    (∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w x * charFun μ w) =
      ∫ y : ℝ, gaussianRegularizer c (x - y) ∂μ := by
  let g : ℝ → ℂ := fun w => Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w x
  have hg : Integrable g volume := by
    have hbase : Integrable (fun w : ℝ =>
        Complex.exp (-((c⁻¹ : ℝ) : ℂ) * ‖w‖ ^ 2 + (0 : ℂ) * ⟪(0 : ℝ), w⟫)) volume :=
      GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (show 0 < (((c⁻¹ : ℝ) : ℂ)).re by simpa using inv_pos.mpr hc) 0 0
    simp only [zero_mul, add_zero] at hbase
    have hphase : AEStronglyMeasurable (fun w : ℝ => inversePhase w x) volume := by
      apply Continuous.aestronglyMeasurable
      unfold inversePhase
      fun_prop
    have hbdd : ∀ᵐ w : ℝ ∂volume, ‖inversePhase w x‖ ≤ 1 := by
      filter_upwards with w
      rw [inversePhase, norm_exp]
      norm_num
    simpa [g, mul_comm] using hbase.bdd_mul hphase hbdd
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) μ := integrable_const 1
  let L : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ := -(innerₗ ℝ)
  have hswap := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (𝕜 := ℝ) (V := ℝ) (W := ℝ)
    (e := probChar) (μ := volume) (ν := μ) (L := L)
    Real.continuous_probChar (by dsimp [L]; fun_prop) hg hone
  calc
    _ = ∫ w : ℝ, g w •
          (VectorFourier.fourierIntegral probChar μ L.flip
            (fun _ : ℝ => (1 : ℂ)) w) := by
      apply integral_congr_ae
      filter_upwards with w
      have hfour : VectorFourier.fourierIntegral probChar μ L.flip
          (fun _ : ℝ => (1 : ℂ)) w = charFun μ w := by
        rw [VectorFourier.fourierIntegral, charFun_apply_real]
        apply integral_congr_ae
        filter_upwards with y
        dsimp [L]
        have hi : @inner ℝ ℝ _ w y = y * w := RCLike.inner_apply w y
        rw [hi]
        rw [Circle.smul_def, smul_eq_mul, probChar_apply, mul_one]
        congr 1
        push_cast
        ring
      rw [hfour]
      simp only [g, smul_eq_mul]
    _ = ∫ y : ℝ, (VectorFourier.fourierIntegral probChar volume L g y) • (1 : ℂ) ∂μ := hswap.symm
    _ = ∫ y : ℝ, gaussianRegularizer c (x - y) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [show VectorFourier.fourierIntegral probChar volume L g y =
        ∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w (x - y) by
        rw [VectorFourier.fourierIntegral]
        apply integral_congr_ae
        filter_upwards with w
        dsimp [L]
        have hi : @inner ℝ ℝ _ w y = y * w := RCLike.inner_apply w y
        rw [hi]
        rw [Circle.smul_def, probChar_apply]
        change Complex.exp (((-(- (y * w)) : ℝ) : ℂ) * Complex.I) *
            (Complex.exp (-((c⁻¹ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) *
              Complex.exp (-Complex.I * ((w * x : ℝ) : ℂ))) = _
        calc
          _ = Complex.exp (-((c⁻¹ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) *
              (Complex.exp (((y * w : ℝ) : ℂ) * Complex.I) *
                Complex.exp (-Complex.I * ((w * x : ℝ) : ℂ))) := by ring
          _ = Complex.exp (-((c⁻¹ : ℝ) : ℂ) * ((‖w‖ : ℝ) : ℂ) ^ 2) *
              Complex.exp ((((y * w : ℝ) : ℂ) * Complex.I) +
                (-Complex.I * ((w * x : ℝ) : ℂ))) := by rw [Complex.exp_add]
          _ = _ := by
            congr 2
            push_cast
            ring]
      simp only [smul_eq_mul, mul_one]
      exact integral_gaussian_frequency c (x - y) hc

/-- The inverse integral is the pointwise limit of nonnegative Gaussian convolutions. -/
lemma inverseCharFun_real_nonneg
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    (inverseCharFun μ x).im = 0 ∧ 0 ≤ (inverseCharFun μ x).re := by
  let F : ℝ → ℂ := fun c => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w x * charFun μ w
  have hphase : AEStronglyMeasurable (fun w : ℝ => inversePhase w x) volume := by
    apply Continuous.aestronglyMeasurable
    unfold inversePhase
    fun_prop
  have hphase_bdd : ∀ᵐ w : ℝ ∂volume, ‖inversePhase w x‖ ≤ 1 := by
    filter_upwards with w
    rw [inversePhase, norm_exp]
    norm_num
  have hphaseφ : Integrable (fun w : ℝ => inversePhase w x * charFun μ w) volume :=
    hφ.bdd_mul hphase hphase_bdd
  have hF : Tendsto F atTop (𝓝 (inverseCharFun μ x)) := by
    dsimp [F, inverseCharFun]
    apply tendsto_const_nhds.mul
    have hi := Real.tendsto_integral_cexp_sq_smul hphaseφ
    simpa only [smul_eq_mul, mul_assoc] using hi
  have hnon : ∀ᶠ c : ℝ in atTop, (F c).im = 0 ∧ 0 ≤ (F c).re := by
    filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
    rw [show F c = (((2 * Real.pi)⁻¹ *
        ∫ y : ℝ, (Real.pi * c) ^ (1 / 2 : ℝ) *
          Real.exp (-c * (x - y) ^ 2 / 4) ∂μ : ℝ) : ℂ) by
      dsimp [F]
      calc
        ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
            ∫ w : ℝ, Complex.exp (-c⁻¹ * |w| ^ 2) * inversePhase w x * charFun μ w =
            ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
              ∫ y : ℝ, gaussianRegularizer c (x - y) ∂μ :=
          congrArg (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ * z)
            (by simpa only [Real.norm_eq_abs] using integral_gaussian_charFun_eq μ c hc x)
        _ = _ := by
          rw [show (∫ y : ℝ, gaussianRegularizer c (x - y) ∂μ) =
              ((∫ y : ℝ, (Real.pi * c) ^ (1 / 2 : ℝ) *
                Real.exp (-c * (x - y) ^ 2 / 4) ∂μ : ℝ) : ℂ) by
            exact Complex.ofRealLI.integral_comp_comm _]
          rw [← Complex.ofReal_inv]
          norm_cast]
    simp only [ofReal_im, ofReal_re, true_and]
    apply mul_nonneg
    · positivity
    · exact integral_nonneg fun y =>
        mul_nonneg
          (Real.rpow_nonneg (mul_nonneg Real.pi_pos.le hc.le) _)
          (Real.exp_pos _).le
  have hFre := Complex.continuous_re.continuousAt.tendsto.comp hF
  have hFim := Complex.continuous_im.continuousAt.tendsto.comp hF
  constructor
  · apply tendsto_nhds_unique hFim
    exact tendsto_const_nhds.congr' (hnon.mono fun c hc => hc.1.symm)
  · exact IsClosed.mem_of_tendsto isClosed_Ici hFre (hnon.mono fun c hc => hc.2)

lemma gaussianRealProduct_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) :
    Integrable (fun z : ℝ × ℝ =>
      (gaussianRegularizer c (z.1 - z.2)).re) (volume.prod μ) := by
  let F : ℝ × ℝ → ℝ := fun z => (gaussianRegularizer c (z.1 - z.2)).re
  have hF : AEStronglyMeasurable F (volume.prod μ) := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    unfold gaussianRegularizer
    fun_prop
  apply (integrable_prod_iff' hF).2
  constructor
  · filter_upwards with y
    have hshift :=
      (gaussianRegularizer_integrable c hc).re.comp_sub_right y
    simpa [F] using hshift
  · have hconst : Integrable (fun _ : ℝ => (2 * Real.pi : ℝ)) μ := integrable_const _
    apply hconst.congr
    filter_upwards with y
    dsimp [F]
    simp_rw [abs_of_nonneg (gaussianRegularizer_nonneg hc.le)]
    calc
      2 * Real.pi = ∫ x : ℝ, (gaussianRegularizer c x).re ∂volume :=
        (gaussianRegularizer_integral c hc).symm
      _ = ∫ x : ℝ, (gaussianRegularizer c (x - y)).re ∂volume :=
        (integral_sub_right_eq_self
          (fun x : ℝ => (gaussianRegularizer c x).re) y).symm

lemma gaussianRealConvolution_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ =>
      ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ) volume := by
  exact (gaussianRealProduct_integrable μ c hc).integral_prod_left

lemma gaussianRealConvolution_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ =
      2 * Real.pi * (μ Set.univ).toReal := by
  rw [integral_integral_swap (gaussianRealProduct_integrable μ c hc)]
  rw [show (fun y : ℝ => ∫ x : ℝ,
      (gaussianRegularizer c (x - y)).re ∂volume) =
      fun _ : ℝ => (2 * Real.pi : ℝ) by
    funext y
    calc
      (∫ x : ℝ, (gaussianRegularizer c (x - y)).re ∂volume) =
          ∫ x : ℝ, (gaussianRegularizer c x).re ∂volume :=
        integral_sub_right_eq_self
          (fun x : ℝ => (gaussianRegularizer c x).re) y
      _ = 2 * Real.pi := gaussianRegularizer_integral c hc]
  rw [integral_const, Measure.real_def]
  simp only [smul_eq_mul]
  ring

lemma normalizedGaussianConvolution_nonneg
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) (x : ℝ) :
    0 ≤ (2 * Real.pi)⁻¹ *
      ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ := by
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro y
  exact gaussianRegularizer_nonneg hc.le

lemma normalizedGaussianConvolution_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : ℝ => (2 * Real.pi)⁻¹ *
      ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ) volume :=
  (gaussianRealConvolution_integrable μ c hc).const_mul _

lemma normalizedGaussianConvolution_integral
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, ((2 * Real.pi)⁻¹ *
      ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ) = (μ Set.univ).toReal := by
  rw [integral_const_mul, gaussianRealConvolution_integral μ c hc]
  field_simp [Real.pi_ne_zero]

lemma normalizedGaussianConvolution_eq_frequency
    (μ : Measure ℝ) [IsFiniteMeasure μ] (c : ℝ) (hc : 0 < c) (x : ℝ) :
    (((2 * Real.pi)⁻¹ *
      ∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) *
          inversePhase w x * charFun μ w := by
  rw [integral_gaussian_charFun_eq μ c hc x]
  have hInt : ((∫ y : ℝ, (gaussianRegularizer c (x - y)).re ∂μ : ℝ) : ℂ) =
      ∫ y : ℝ, gaussianRegularizer c (x - y) ∂μ := by
    show Complex.ofRealLI (∫ y : ℝ,
      (gaussianRegularizer c (x - y)).re ∂μ) = _
    rw [← Complex.ofRealLI.integral_comp_comm]
    apply integral_congr_ae
    filter_upwards with y
    rw [Complex.ofRealLI_apply]
    unfold gaussianRegularizer
    rw [Complex.ofReal_re]
  push_cast
  rw [hInt]

lemma integrable_inverseCharFun
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) : Integrable (inverseCharFun μ) volume := by
  let H : ℕ → ℝ → ℝ := fun n x => (2 * Real.pi)⁻¹ *
    ∫ y : ℝ, (gaussianRegularizer (n + 1 : ℝ) (x - y)).re ∂μ
  let F : ℕ → ℝ → ℂ := fun n x => (H n x : ℂ)
  have hHn : ∀ n, Integrable (H n) volume := by
    intro n
    exact normalizedGaussianConvolution_integrable μ (n + 1 : ℝ) (by positivity)
  have hFn : ∀ n, Integrable (F n) volume := by
    intro n
    exact (hHn n).ofReal
  have hFmeas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖F n x‖) volume := by
    intro n
    exact AEMeasurable.ennreal_ofReal (hFn n).norm.aemeasurable
  have hFlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (inverseCharFun μ x)) := by
    intro x
    let G : ℝ → ℂ := fun c => ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
      ∫ w : ℝ, Complex.exp (-c⁻¹ * ‖w‖ ^ 2) * inversePhase w x * charFun μ w
    have hphase : AEStronglyMeasurable (fun w : ℝ => inversePhase w x) volume := by
      apply Continuous.aestronglyMeasurable
      unfold inversePhase
      fun_prop
    have hphase_bdd : ∀ᵐ w : ℝ ∂volume, ‖inversePhase w x‖ ≤ 1 := by
      filter_upwards with w
      rw [inversePhase, norm_exp]
      norm_num
    have hphaseφ : Integrable (fun w : ℝ => inversePhase w x * charFun μ w) volume :=
      hφ.bdd_mul hphase hphase_bdd
    have hG : Tendsto G atTop (𝓝 (inverseCharFun μ x)) := by
      dsimp [G, inverseCharFun]
      apply tendsto_const_nhds.mul
      simpa only [smul_eq_mul, mul_assoc] using
        (Real.tendsto_integral_cexp_sq_smul hphaseφ)
    have hcomp : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
    apply (hG.comp hcomp).congr'
    filter_upwards with n
    dsimp [F, H, G]
    exact (normalizedGaussianConvolution_eq_frequency μ (n + 1 : ℝ)
      (by positivity) x).symm
  refine ⟨continuous_inverseCharFun hφ |>.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal ‖inverseCharFun μ x‖) =
        ∫⁻ x : ℝ, liminf (fun n => ENNReal.ofReal ‖F n x‖) atTop := by
      apply lintegral_congr
      intro x
      rw [show liminf (fun n => ENNReal.ofReal ‖F n x‖) atTop =
          ENNReal.ofReal ‖inverseCharFun μ x‖ by
        exact ((ENNReal.continuous_ofReal.comp continuous_norm).continuousAt.tendsto.comp
          (hFlim x)).liminf_eq]
    _ ≤ liminf (fun n => ∫⁻ x : ℝ, ENNReal.ofReal ‖F n x‖) atTop :=
      lintegral_liminf_le' hFmeas
    _ = ENNReal.ofReal ((μ Set.univ).toReal) := by
      have hlin : (fun n => ∫⁻ x : ℝ, ENNReal.ofReal ‖F n x‖) =
          fun _ => ENNReal.ofReal ((μ Set.univ).toReal) := by
        funext n
        rw [show (fun x : ℝ => ENNReal.ofReal ‖F n x‖) =
            fun x : ℝ => ENNReal.ofReal (H n x) by
          funext x
          rw [show ‖F n x‖ = H n x by
            dsimp [F]
            rw [Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (normalizedGaussianConvolution_nonneg μ
                (n + 1 : ℝ) (by positivity) x)]]]
        rw [← ofReal_integral_eq_lintegral_ofReal (hHn n)
          (Filter.Eventually.of_forall fun x =>
            normalizedGaussianConvolution_nonneg μ (n + 1 : ℝ)
              (by positivity) x)]
        rw [normalizedGaussianConvolution_integral μ (n + 1 : ℝ) (by positivity)]
      rw [hlin, liminf_const]
    _ < ∞ := by simp

/-- Function-side Fourier inversion in the characteristic-function normalization.
The change of variables `x = 2πs` is made explicitly, so the integral on the
left has the probability-theory phase `exp (itx)`. -/
lemma integral_exp_mul_inverseCharFun
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume)
    (hinv : Integrable (inverseCharFun μ) volume) (t : ℝ) :
    ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * inverseCharFun μ x =
      charFun μ t := by
  let a : ℝ := 2 * Real.pi
  let C : ℂ := ((a : ℝ) : ℂ)⁻¹
  let F : ℝ → ℂ := 𝓕 (charFun μ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hscaled : Integrable (fun x : ℝ => F (a⁻¹ * x)) volume := by
    have hmul := hinv.const_mul C⁻¹
    apply hmul.congr
    filter_upwards with x
    dsimp [C, F, a]
    rw [inverseCharFun_eq_fourier]
    push_cast
    field_simp [Real.pi_ne_zero]
  have hF : Integrable F volume :=
    (integrable_comp_mul_left_iff F (inv_ne_zero ha.ne')).1 hscaled
  have hFourierInv := MeasureTheory.Integrable.fourierInv_fourier_eq
    hφ hF (v := t) (continuous_charFun.continuousAt)
  let q : ℝ → ℂ := fun s =>
    Complex.exp (Complex.I * ((t * a * s : ℝ) : ℂ)) * F s
  have hqint : Integrable q volume := by
    have hphase : AEStronglyMeasurable (fun s : ℝ =>
        Complex.exp (Complex.I * ((t * a * s : ℝ) : ℂ))) volume := by
      fun_prop
    have hbdd : ∀ᵐ s : ℝ ∂volume, ‖Complex.exp
        (Complex.I * ((t * a * s : ℝ) : ℂ))‖ ≤ 1 := by
      filter_upwards with s
      rw [norm_exp]
      norm_num
    exact hF.bdd_mul hphase hbdd
  have hchange := MeasureTheory.Measure.integral_comp_mul_left q a⁻¹
  have hqcomp : (fun x : ℝ => q (a⁻¹ * x)) = fun x : ℝ =>
      Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * F (a⁻¹ * x) := by
    funext x
    dsimp [q]
    have harg : t * a * (a⁻¹ * x) = t * x := by
      field_simp [ha.ne']
    rw [harg]
  have hscaled_integral :
      ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * C * F (a⁻¹ * x) =
        ∫ s : ℝ, q s := by
    rw [show (fun x : ℝ => Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * C *
        F (a⁻¹ * x)) = fun x => C * q (a⁻¹ * x) by
      funext x
      dsimp [q]
      have harg : t * a * (a⁻¹ * x) = t * x := by
        field_simp [ha.ne']
      rw [harg]
      ring]
    have habs : |a⁻¹⁻¹| = a := by
      rw [inv_inv, abs_of_pos ha]
    calc
      (∫ x : ℝ, C * q (a⁻¹ * x)) =
          C * (∫ x : ℝ, q (a⁻¹ * x)) :=
        MeasureTheory.integral_const_mul C (fun x : ℝ => q (a⁻¹ * x))
      _ = C * (|a⁻¹⁻¹| • ∫ x : ℝ, q x) := by
        exact congrArg (fun z : ℂ => C * z) hchange
      _ = ∫ x : ℝ, q x := by
        rw [habs]
        change C * ((a : ℂ) * ∫ x : ℝ, q x) = ∫ x : ℝ, q x
        dsimp [C]
        field_simp [ha.ne']
  calc
    _ = ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * C * F (a⁻¹ * x) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp [C, a, F]
      rw [inverseCharFun_eq_fourier]
      push_cast
      field_simp [Real.pi_ne_zero]
    _ = ∫ s : ℝ, q s := hscaled_integral
    _ = 𝓕⁻ F t := by
      rw [Real.fourierInv_eq']
      apply integral_congr_ae
      filter_upwards with s
      dsimp [q, F, a]
      have hinner : @inner ℝ ℝ _ s t = t * s := RCLike.inner_apply s t
      rw [hinner]
      congr 2
      push_cast
      ring
    _ = charFun μ t := hFourierInv

/-- The measure induced by the real part of the inverse integral. -/
def inverseCharFunMeasure (μ : Measure ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (inverseCharFun μ x).re)

/-- The inverse-density measure is finite. -/
lemma inverseCharFunMeasure_isFinite
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    IsFiniteMeasure (inverseCharFunMeasure μ) := by
  apply isFiniteMeasure_withDensity_ofReal
  exact (integrable_inverseCharFun μ hφ).re.hasFiniteIntegral

/-- The density measure has the original characteristic function. -/
lemma charFun_inverseCharFunMeasure
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    charFun (inverseCharFunMeasure μ) = charFun μ := by
  have hinv := integrable_inverseCharFun μ hφ
  letI : IsFiniteMeasure (inverseCharFunMeasure μ) :=
    inverseCharFunMeasure_isFinite μ hφ
  funext t
  rw [charFun_apply_real]
  rw [show inverseCharFunMeasure μ =
      volume.withDensity (fun x => ENNReal.ofReal (inverseCharFun μ x).re) by rfl]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hpoint : ∀ x : ℝ,
        (ENNReal.ofReal (inverseCharFun μ x).re).toReal •
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
          Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) * inverseCharFun μ x := by
      intro x
      have hnon := inverseCharFun_real_nonneg μ hφ x
      rw [ENNReal.toReal_ofReal hnon.2]
      rw [show inverseCharFun μ x = ((inverseCharFun μ x).re : ℂ) by
        apply Complex.ext
        · simp
        · simpa using hnon.1]
      change ((inverseCharFun μ x).re : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
        Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) *
          ((inverseCharFun μ x).re : ℂ)
      have hphase : Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
          Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) := by
        congr 1
        push_cast
        ring
      rw [hphase]
      ring
    calc
      (∫ x : ℝ, (ENNReal.ofReal (inverseCharFun μ x).re).toReal •
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) =
          ∫ x : ℝ, Complex.exp (Complex.I * ((t * x : ℝ) : ℂ)) *
            inverseCharFun μ x :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = charFun μ t := integral_exp_mul_inverseCharFun μ hφ hinv t
  · have hdensMeas : Measurable (fun x : ℝ => (inverseCharFun μ x).re) :=
      (Complex.continuous_re.comp (continuous_inverseCharFun hφ)).measurable
    exact hdensMeas.ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- Fourier inversion at the measure level: the inverse density induces the
original finite measure. -/
theorem inverseCharFunMeasure_eq
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    inverseCharFunMeasure μ = μ := by
  letI : IsFiniteMeasure (inverseCharFunMeasure μ) :=
    inverseCharFunMeasure_isFinite μ hφ
  exact Measure.ext_of_charFun (charFun_inverseCharFunMeasure μ hφ)

/-- First inverse-integral derivative. -/
def inverseCharFunDerivOne (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, (-Complex.I * (t : ℂ)) * inversePhase t x * charFun μ t

/-- Second inverse-integral derivative. -/
def inverseCharFunDerivTwo (μ : Measure ℝ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t : ℝ, (-((t ^ 2 : ℝ) : ℂ)) * inversePhase t x * charFun μ t

/-- The real density represented by the inverse characteristic-function integral. -/
def inverseCharFunDensity (μ : Measure ℝ) (x : ℝ) : ℝ :=
  (inverseCharFun μ x).re

/-- A normalized inverse transform written through Mathlib's Fourier transform. -/
def normalizedInverseFourier (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ * 𝓕 g (x / (2 * Real.pi))

/-- The frequency multiplier induced by differentiating the inverse phase. -/
def inverseMultiplier (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (-Complex.I * (t : ℂ)) * g t

/-- Differentiation of the normalized inverse transform, with all `2π`
constants cancelled. -/
lemma hasDerivAt_normalizedInverseFourier {g : ℝ → ℂ}
    (hg : Integrable g volume)
    (htg : Integrable (fun t : ℝ => (t : ℂ) * g t) volume) (x : ℝ) :
    HasDerivAt (normalizedInverseFourier g)
      (normalizedInverseFourier (inverseMultiplier g) x) x := by
  let a : ℝ := 2 * Real.pi
  let C : ℂ := ((a : ℝ) : ℂ)⁻¹
  have ha : a ≠ 0 := by dsimp [a]; positivity
  have hreal : Integrable (fun t : ℝ => t • g t) volume := by
    apply htg.congr
    filter_upwards with t
    rfl
  have hd := Real.hasDerivAt_fourier hg hreal (x / a)
  have hcomp := hd.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id' x).div_const a)
  have hout := hcomp.const_mul C
  simp only [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] at hout
  change HasDerivAt (fun y : ℝ => C * 𝓕 g (y / a))
    (C * 𝓕 (fun t : ℝ => (-Complex.I * (t : ℂ)) * g t) (x / a)) x
  convert hout using 1
  congr 1
  change 𝓕 (fun t : ℝ => (-Complex.I * (t : ℂ)) * g t) (x / a) =
    (1 / a : ℝ) •
      𝓕 (fun t : ℝ => (-2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) • g t)
        (x / a)
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  change (∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * (x / a)) * I) *
      (-I * ↑t * g t)) =
    ((1 / a : ℝ) : ℂ) *
      ∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * (x / a)) * I) *
        ((-2 * (Real.pi : ℂ) * I * ↑t) * g t)
  let R : ℝ → ℂ := fun t =>
    Complex.exp (↑(-2 * Real.pi * t * (x / a)) * I) *
      ((-2 * (Real.pi : ℂ) * I * ↑t) * g t)
  calc
    (∫ t : ℝ, Complex.exp (↑(-2 * Real.pi * t * (x / a)) * I) *
        (-I * ↑t * g t)) =
        ∫ t : ℝ, ((1 / a : ℝ) : ℂ) * R t := by
      apply integral_congr_ae
      filter_upwards with t
      dsimp [R, a]
      have hcoef : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (-2 * (Real.pi : ℂ) * I * (t : ℂ))) = -I * (t : ℂ) := by
        push_cast
        field_simp [Real.pi_ne_zero]
      calc
        Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) *
            (-I * ↑t * g t) =
            Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) *
              ((-I * ↑t) * g t) := by ring
        _ = Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) *
              ((↑(1 / (2 * Real.pi)) * (-2 * (Real.pi : ℂ) * I * ↑t)) * g t) := by
              rw [hcoef]
        _ = ↑(1 / (2 * Real.pi)) *
              (Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) *
                (-2 * (Real.pi : ℂ) * I * ↑t * g t)) := by ring
    _ = ((1 / a : ℝ) : ℂ) * ∫ t : ℝ, R t :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := rfl

lemma normalizedInverseFourier_charFun (μ : Measure ℝ) :
    normalizedInverseFourier (charFun μ) = inverseCharFun μ := by
  funext x
  exact (inverseCharFun_eq_fourier μ x).symm

lemma normalizedInverseFourier_multiplier_charFun (μ : Measure ℝ) :
    normalizedInverseFourier (inverseMultiplier (charFun μ)) =
      inverseCharFunDerivOne μ := by
  funext x
  rw [normalizedInverseFourier, inverseCharFunDerivOne,
    Real.fourier_real_eq_integral_exp_smul]
  dsimp [inverseMultiplier]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [inversePhase]
  have hp : Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) =
      Complex.exp (-I * ↑(t * x)) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hp]
  ring

lemma normalizedInverseFourier_multiplier_two_charFun (μ : Measure ℝ) :
    normalizedInverseFourier (inverseMultiplier (inverseMultiplier (charFun μ))) =
      inverseCharFunDerivTwo μ := by
  funext x
  rw [normalizedInverseFourier, inverseCharFunDerivTwo,
    Real.fourier_real_eq_integral_exp_smul]
  dsimp [inverseMultiplier]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  rw [inversePhase]
  have hp : Complex.exp (↑(-2 * Real.pi * t * (x / (2 * Real.pi))) * I) =
      Complex.exp (-I * ↑(t * x)) := by
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hp]
  have hcoef : (-I * (t : ℂ)) * (-I * (t : ℂ)) =
      -(((t ^ 2 : ℝ) : ℂ)) := by
    calc
      (-I * (t : ℂ)) * (-I * (t : ℂ)) = I ^ 2 * (t : ℂ) ^ 2 := by ring
      _ = -(((t ^ 2 : ℝ) : ℂ)) := by rw [Complex.I_sq]; push_cast; ring
  calc
    Complex.exp (-I * ↑(t * x)) *
        (-I * ↑t * (-I * ↑t * charFun μ t)) =
        ((-I * (t : ℂ)) * (-I * (t : ℂ))) *
          Complex.exp (-I * ↑(t * x)) * charFun μ t := by ring
    _ = -(((t ^ 2 : ℝ) : ℂ)) *
          Complex.exp (-I * ↑(t * x)) * charFun μ t := by rw [hcoef]

/-- First derivative of the inverse characteristic-function integral. -/
lemma hasDerivAt_inverseCharFun {μ : Measure ℝ}
    (h0 : Integrable (charFun μ) volume)
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume) (x : ℝ) :
    HasDerivAt (inverseCharFun μ) (inverseCharFunDerivOne μ x) x := by
  rw [← normalizedInverseFourier_charFun μ,
    ← normalizedInverseFourier_multiplier_charFun μ]
  exact hasDerivAt_normalizedInverseFourier h0 h1 x

/-- Second derivative of the inverse characteristic-function integral. -/
lemma hasDerivAt_inverseCharFunDerivOne {μ : Measure ℝ}
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume)
    (h2 : Integrable (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * charFun μ t) volume)
    (x : ℝ) :
    HasDerivAt (inverseCharFunDerivOne μ) (inverseCharFunDerivTwo μ x) x := by
  have hg : Integrable (inverseMultiplier (charFun μ)) volume := by
    apply h1.const_mul (-Complex.I) |>.congr
    filter_upwards with t
    dsimp [inverseMultiplier]
    ring
  have htg : Integrable (fun t : ℝ => (t : ℂ) *
      inverseMultiplier (charFun μ) t) volume := by
    apply h2.const_mul (-Complex.I) |>.congr
    filter_upwards with t
    dsimp [inverseMultiplier]
    push_cast
    ring
  rw [← normalizedInverseFourier_multiplier_charFun μ,
    ← normalizedInverseFourier_multiplier_two_charFun μ]
  exact hasDerivAt_normalizedInverseFourier hg htg x

/-- A complex derivative of an everywhere real-valued function is real. -/
lemma derivative_im_eq_zero_of_im_eq_zero {F : ℝ → ℂ} {z : ℂ} {x : ℝ}
    (hreal : ∀ y, (F y).im = 0) (hD : HasDerivAt F z x) : z.im = 0 := by
  have hre : HasDerivAt (Complex.reCLM ∘ F) (Complex.reCLM z) x :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hD
  have hof : HasDerivAt (Complex.ofRealCLM ∘ (Complex.reCLM ∘ F))
      (Complex.ofRealCLM (Complex.reCLM z)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hre
  have hof' : HasDerivAt F (Complex.ofRealCLM (Complex.reCLM z)) x := by
    apply hof.congr_of_eventuallyEq
    filter_upwards with y
    dsimp
    apply Complex.ext
    · simp
    · simpa using hreal y
  have hz := hD.unique hof'
  have him := congrArg Complex.im hz
  simpa using him

lemma inverseCharFunDerivOne_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h0 : Integrable (charFun μ) volume)
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume) (x : ℝ) :
    (inverseCharFunDerivOne μ x).im = 0 := by
  apply derivative_im_eq_zero_of_im_eq_zero
    (fun y => (inverseCharFun_real_nonneg μ h0 y).1)
  exact hasDerivAt_inverseCharFun h0 h1 x

lemma inverseCharFunDerivTwo_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h0 : Integrable (charFun μ) volume)
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume)
    (h2 : Integrable (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * charFun μ t) volume)
    (x : ℝ) : (inverseCharFunDerivTwo μ x).im = 0 := by
  have hreal1 : ∀ y, (inverseCharFunDerivOne μ y).im = 0 :=
    fun y => inverseCharFunDerivOne_im μ h0 h1 y
  apply derivative_im_eq_zero_of_im_eq_zero hreal1
  exact hasDerivAt_inverseCharFunDerivOne h1 h2 x

lemma hasDerivAt_inverseCharFunDensity (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h0 : Integrable (charFun μ) volume)
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume) (x : ℝ) :
    HasDerivAt (inverseCharFunDensity μ) (inverseCharFunDerivOne μ x).re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_inverseCharFun h0 h1 x)

lemma hasDerivAt_inverseCharFunDensityDerivOne (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h1 : Integrable (fun t : ℝ => (t : ℂ) * charFun μ t) volume)
    (h2 : Integrable (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * charFun μ t) volume)
    (x : ℝ) : HasDerivAt (fun y => (inverseCharFunDerivOne μ y).re)
      (inverseCharFunDerivTwo μ x).re x := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_inverseCharFunDerivOne h1 h2 x)

/-- The inverse integral is the Fourier transform of the rescaled
characteristic function. -/
lemma inverseCharFun_eq_fourier_rescaled (μ : Measure ℝ) :
    inverseCharFun μ = 𝓕 (fun u : ℝ => charFun μ (2 * Real.pi * u)) := by
  funext x
  rw [inverseCharFun, Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun t => Complex.exp (-I * ((t : ℂ) * (x : ℂ))) * charFun μ t
  have hcv := MeasureTheory.Measure.integral_comp_mul_left g (2 * Real.pi)
  change (∫ u : ℝ, g (2 * Real.pi * u)) =
      |(2 * Real.pi)⁻¹| • ∫ t : ℝ, g t at hcv
  calc
    ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, inversePhase t x * charFun μ t =
        |(2 * Real.pi)⁻¹| • ∫ t : ℝ, g t := by
      change ((2 * Real.pi : ℝ) : ℂ)⁻¹ * _ =
        (((|(2 * Real.pi)⁻¹| : ℝ) : ℂ)) * _
      congr 1
      · norm_cast
        rw [abs_inv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos Real.pi_pos]
      · apply integral_congr_ae
        filter_upwards with t
        rw [inversePhase]
        dsimp [g]
        congr 2
        push_cast
        rfl
    _ = ∫ u : ℝ, g (2 * Real.pi * u) := hcv.symm
    _ = ∫ u : ℝ, Complex.exp (↑(-2 * Real.pi * u * x) * I) •
        charFun μ (2 * Real.pi * u) := by
      apply integral_congr_ae
      filter_upwards with u
      dsimp [g]
      change Complex.exp (-I *
          (((2 * Real.pi * u : ℝ) : ℂ) * (x : ℂ))) *
          charFun μ (2 * Real.pi * u) =
        Complex.exp (((-2 * Real.pi * u * x : ℝ) : ℂ) * I) *
          charFun μ (2 * Real.pi * u)
      congr 2
      push_cast
      ring

lemma integrable_rescaled_charFun {μ : Measure ℝ}
    (hφ : Integrable (charFun μ) volume) :
    Integrable (fun u : ℝ => charFun μ (2 * Real.pi * u)) volume := by
  exact hφ.comp_mul_left' (by positivity)

/-- Function-side Fourier inversion at the exact rescaling needed below. -/
lemma fourierInv_inverseCharFun_eq (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) (u : ℝ) :
    𝓕⁻ (inverseCharFun μ) u = charFun μ (2 * Real.pi * u) := by
  let q : ℝ → ℂ := fun u => charFun μ (2 * Real.pi * u)
  have hq : Integrable q volume := integrable_rescaled_charFun hφ
  have hFq : Integrable (𝓕 q) volume := by
    rw [← inverseCharFun_eq_fourier_rescaled μ]
    exact integrable_inverseCharFun μ hφ
  have hcont : ContinuousAt q u := by
    apply (continuous_charFun (μ := μ)).continuousAt.comp
    fun_prop
  have hinv := hq.fourierInv_fourier_eq hFq hcont
  rwa [← inverseCharFun_eq_fourier_rescaled μ] at hinv


/-- The real inverse density is continuous. -/
lemma continuous_inverseCharFunDensity {μ : Measure ℝ}
    (hφ : Integrable (charFun μ) volume) :
    Continuous (inverseCharFunDensity μ) :=
  Complex.continuous_re.comp (continuous_inverseCharFun hφ)

/-- The real inverse density is integrable. -/
lemma integrable_inverseCharFunDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    Integrable (inverseCharFunDensity μ) volume :=
  (integrable_inverseCharFun μ hφ).re

/-- The real inverse density is nonnegative pointwise. -/
lemma inverseCharFunDensity_nonneg
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    0 ≤ inverseCharFunDensity μ x :=
  (inverseCharFun_real_nonneg μ hφ x).2

/-- The real density, embedded in `ℂ`, is exactly the inverse integral. -/
lemma coe_inverseCharFunDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    ((inverseCharFunDensity μ x : ℝ) : ℂ) = inverseCharFun μ x := by
  apply Complex.ext
  · rfl
  · simp [inverseCharFunDensity, (inverseCharFun_real_nonneg μ hφ x).1]

/-- The original measure is represented by the real inverse density. -/
theorem measure_eq_withDensity_inverseCharFunDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    μ = volume.withDensity
      (fun x => ENNReal.ofReal (inverseCharFunDensity μ x)) := by
  exact (inverseCharFunMeasure_eq μ hφ).symm

/-- For a probability measure, the inverse density has total mass one. -/
theorem integral_inverseCharFunDensity_eq_one
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    ∫ x : ℝ, inverseCharFunDensity μ x = 1 := by
  letI : IsFiniteMeasure (inverseCharFunMeasure μ) :=
    inverseCharFunMeasure_isFinite μ hφ
  have heq := inverseCharFunMeasure_eq μ hφ
  have hconst := congrArg (fun ν : Measure ℝ => ∫ _ : ℝ, (1 : ℝ) ∂ν) heq
  change (∫ _ : ℝ, (1 : ℝ) ∂volume.withDensity
      (fun x => ENNReal.ofReal (inverseCharFun μ x).re)) =
    ∫ _ : ℝ, (1 : ℝ) ∂μ at hconst
  rw [integral_withDensity_eq_integral_toReal_smul] at hconst
  · simp only [smul_eq_mul, mul_one] at hconst
    have hpoint :
        (fun x : ℝ => (ENNReal.ofReal (inverseCharFun μ x).re).toReal) =
          inverseCharFunDensity μ := by
      funext x
      rw [ENNReal.toReal_ofReal (inverseCharFun_real_nonneg μ hφ x).2]
      rfl
    rw [hpoint] at hconst
    simpa using hconst
  · exact ((Complex.continuous_re.comp
      (continuous_inverseCharFun hφ)).measurable).ennreal_ofReal
  · filter_upwards with x
    exact ENNReal.ofReal_lt_top

/-- The pointwise uniform bound for the real inverse density. -/
lemma abs_inverseCharFunDensity_le
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    |inverseCharFunDensity μ x| ≤
      (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖charFun μ t‖ := by
  have hn := norm_inverseCharFun_le hφ x
  rw [← coe_inverseCharFunDensity μ hφ x] at hn
  simpa [abs_of_nonneg (inverseCharFunDensity_nonneg μ hφ x)] using hn

/-- The complete measure-level Fourier inversion package for a probability
measure with integrable characteristic function. -/
structure ProbabilityFourierInversion (μ : Measure ℝ) : Prop where
  density_continuous : Continuous (inverseCharFunDensity μ)
  density_integrable : Integrable (inverseCharFunDensity μ) volume
  density_nonneg : ∀ x, 0 ≤ inverseCharFunDensity μ x
  density_eq_inverse : ∀ x,
    ((inverseCharFunDensity μ x : ℝ) : ℂ) = inverseCharFun μ x
  measure_eq : μ = volume.withDensity
    (fun x => ENNReal.ofReal (inverseCharFunDensity μ x))
  density_integral : ∫ x : ℝ, inverseCharFunDensity μ x = 1
  density_bound : ∀ x, |inverseCharFunDensity μ x| ≤
    (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖charFun μ t‖

/-- Generic probability-measure Fourier inversion. -/
theorem probabilityFourierInversion
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : Integrable (charFun μ) volume) :
    ProbabilityFourierInversion μ := by
  refine ⟨continuous_inverseCharFunDensity hφ,
    integrable_inverseCharFunDensity μ hφ,
    inverseCharFunDensity_nonneg μ hφ,
    coe_inverseCharFunDensity μ hφ,
    measure_eq_withDensity_inverseCharFunDensity μ hφ,
    integral_inverseCharFunDensity_eq_one μ hφ,
    abs_inverseCharFunDensity_le μ hφ⟩

/-- Any other nonnegative measurable density of the same measure agrees with
the inverse density almost everywhere. -/
theorem ae_eq_inverseCharFunDensity
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume)
    {g : ℝ → ℝ} (hg : AEMeasurable g volume)
    (hg_nonneg : ∀ᵐ x ∂volume, 0 ≤ g x)
    (hmeasure : volume.withDensity (fun x => ENNReal.ofReal (g x)) = μ) :
    g =ᵐ[volume] inverseCharFunDensity μ := by
  have hmeasure' :
      volume.withDensity (fun x => ENNReal.ofReal (g x)) =
        volume.withDensity
          (fun x => ENNReal.ofReal (inverseCharFunDensity μ x)) :=
    hmeasure.trans (measure_eq_withDensity_inverseCharFunDensity μ hφ)
  have hofreal : (fun x => ENNReal.ofReal (g x)) =ᵐ[volume]
      (fun x => ENNReal.ofReal (inverseCharFunDensity μ x)) :=
    (withDensity_eq_iff_of_sigmaFinite hg.ennreal_ofReal
      (continuous_inverseCharFunDensity hφ).measurable.ennreal_ofReal.aemeasurable).1
      hmeasure'
  filter_upwards [hofreal, hg_nonneg] with x hx hgnon
  exact (ENNReal.ofReal_eq_ofReal_iff hgnon
    (inverseCharFunDensity_nonneg μ hφ x)).1 hx

/-- A continuous nonnegative density representative is uniquely the inverse
density at every point. -/
theorem eq_inverseCharFunDensity_of_continuous
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hφ : Integrable (charFun μ) volume)
    {g : ℝ → ℝ} (hg : Continuous g)
    (hg_nonneg : ∀ x, 0 ≤ g x)
    (hmeasure : volume.withDensity (fun x => ENNReal.ofReal (g x)) = μ) :
    g = inverseCharFunDensity μ := by
  apply MeasureTheory.Measure.eq_of_ae_eq (μ := volume)
  · exact ae_eq_inverseCharFunDensity μ hφ hg.aemeasurable
      (Filter.Eventually.of_forall hg_nonneg) hmeasure
  · exact hg
  · exact continuous_inverseCharFunDensity hφ

/-- The complete weighted inversion package through derivative order two.
The displayed complex formulas use the inherited `e^{-itx}` convention, hence
the first multiplier is `-I*t` and the second is `-t^2`. -/
structure ProbabilityFourierInversionUpToTwo (μ : Measure ℝ) : Prop extends
    ProbabilityFourierInversion μ where
  hasDeriv_density : ∀ x, HasDerivAt (inverseCharFunDensity μ)
    (inverseCharFunDerivOne μ x).re x
  hasDeriv_derivOne : ∀ x,
    HasDerivAt (fun y => (inverseCharFunDerivOne μ y).re)
      (inverseCharFunDerivTwo μ x).re x
  derivOne_formula : ∀ x,
    (((inverseCharFunDerivOne μ x).re : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-Complex.I * (t : ℂ)) * inversePhase t x * charFun μ t
  derivTwo_formula : ∀ x,
    (((inverseCharFunDerivTwo μ x).re : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t : ℝ, (-((t ^ 2 : ℝ) : ℂ)) * inversePhase t x * charFun μ t

/-- Generic weighted Fourier inversion and differentiation through order two. -/
theorem probabilityFourierInversionUpToTwo
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hφ : IntegrableCharFunUpToTwo μ) :
    ProbabilityFourierInversionUpToTwo μ := by
  have h0 := integrable_charFun_of_upToTwo hφ
  have h1 := integrable_mul_charFun_of_upToTwo hφ
  have h2 := integrable_sq_mul_charFun_of_upToTwo hφ
  refine ⟨probabilityFourierInversion μ h0,
    (fun x => hasDerivAt_inverseCharFunDensity μ h0 h1 x),
    (fun x => hasDerivAt_inverseCharFunDensityDerivOne μ h1 h2 x), ?_, ?_⟩
  · intro x
    change (((inverseCharFunDerivOne μ x).re : ℝ) : ℂ) =
      inverseCharFunDerivOne μ x
    apply Complex.ext
    · simp
    · exact (inverseCharFunDerivOne_im μ h0 h1 x).symm
  · intro x
    change (((inverseCharFunDerivTwo μ x).re : ℝ) : ℂ) =
      inverseCharFunDerivTwo μ x
    apply Complex.ext
    · simp
    · exact (inverseCharFunDerivTwo_im μ h0 h1 h2 x).symm

end
end Erdos993.MeasureFourierInversion
