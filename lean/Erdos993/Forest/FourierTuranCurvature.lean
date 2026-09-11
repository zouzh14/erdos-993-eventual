import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter MeasureTheory Complex Real

namespace Erdos993.Forest.FourierTuranCurvature

noncomputable section

/-- The second-order weight used in the weighted `L¹` hypothesis. -/
def weight (x : ℝ) : ℝ := 1 + x ^ 2

/-- The B.18 kernel.  The value at nonpositive `V` is harmless; all applications assume `0 < V`. -/
def kernel (V u v : ℝ) : ℝ := V * (1 - Real.cos ((u - v) / Real.sqrt V))

/-- The quadratic pointwise limit of `kernel`. -/
def quadraticKernel (u v : ℝ) : ℝ := (u - v) ^ 2 / 2

/-- The complex Fourier phase in B.15. -/
def phase (V : ℝ) (j : ℤ) (u : ℝ) : ℂ :=
  Complex.exp (-Complex.I * ((u * (j : ℝ) / Real.sqrt V : ℝ) : ℂ))

/-- Exact lattice Fourier inversion for the centered law (B.15), after the change of
variables `u = t * sqrt V`.  `ψ` is the zero-extended scaled characteristic function. -/
def LatticeFourierInversion (V : ℝ) (p : ℤ → ℝ) (ψ : ℝ → ℂ) : Prop :=
  ∀ j : ℤ,
    (p j : ℂ) = (1 / ((2 * Real.pi * Real.sqrt V : ℝ) : ℂ)) *
      ∫ u : ℝ, phase V j u * ψ u

/-- B.15, exposed as a named theorem rather than hidden in later plumbing. -/
theorem probability_eq_fourier_integral {V : ℝ} {p : ℤ → ℝ} {ψ : ℝ → ℂ}
    (hInv : LatticeFourierInversion V p ψ) (j : ℤ) :
    (p j : ℂ) = (1 / ((2 * Real.pi * Real.sqrt V : ℝ) : ℂ)) *
      ∫ u : ℝ, phase V j u * ψ u :=
  hInv j

lemma phase_zero (V u : ℝ) : phase V 0 u = 1 := by
  simp [phase]

lemma phase_neg_one (V u : ℝ) :
    phase V (-1) u = Complex.exp (Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) := by
  simp [phase]
  congr 1
  ring

lemma phase_one (V u : ℝ) :
    phase V 1 u = Complex.exp (-Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) := by
  simp [phase]

/-- B.16 at the analytic-algebraic level.  The integrand is the product
`ψ(u) * ψ(v)`; the two explicit integrability assumptions are only those needed
to use linearity of the Bochner integral on an infinite measure space. -/
theorem b16_double_integral {V : ℝ} (hV : 0 < V) (ψ : ℝ → ℂ)
    (h0 : Integrable (fun z : ℝ × ℝ => (V : ℂ) * (ψ z.1 * ψ z.2))
      (volume.prod volume))
    (hphase : Integrable (fun z : ℝ × ℝ =>
      (V : ℂ) *
        ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
         (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)))
      (volume.prod volume)) :
    (∫ z : ℝ × ℝ,
        (V : ℂ) *
          (1 - Complex.exp
            (Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ))) *
          (ψ z.1 * ψ z.2) ∂(volume.prod volume)) =
      (V : ℂ) *
        ((∫ u : ℝ, ψ u) ^ 2 -
          (∫ u : ℝ, Complex.exp (Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) * ψ u) *
          (∫ v : ℝ, Complex.exp (-Complex.I * ((v / Real.sqrt V : ℝ) : ℂ)) * ψ v)) := by
  have hs : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  calc
    _ = ∫ z : ℝ × ℝ,
        ((V : ℂ) * (ψ z.1 * ψ z.2) -
          (V : ℂ) *
            ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
             (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)))
          ∂(volume.prod volume) := by
        apply integral_congr_ae
        filter_upwards with z
        have hexp :
            Complex.exp
                (Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ)) =
              Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) *
                Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) := by
          rw [← Complex.exp_add]
          congr 1
          push_cast
          field_simp
          ring
        rw [hexp]
        ring
    _ = (∫ z : ℝ × ℝ, (V : ℂ) * (ψ z.1 * ψ z.2) ∂(volume.prod volume)) -
        ∫ z : ℝ × ℝ,
          (V : ℂ) *
            ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
             (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2))
          ∂(volume.prod volume) := integral_sub h0 hphase
    _ = (V : ℂ) * (∫ z : ℝ × ℝ, ψ z.1 * ψ z.2 ∂(volume.prod volume)) -
        (V : ℂ) *
          (∫ z : ℝ × ℝ,
            (Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
            (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)
            ∂(volume.prod volume)) := by
      congr 1
      · exact integral_const_mul (V : ℂ) (fun z : ℝ × ℝ => ψ z.1 * ψ z.2)
      · exact integral_const_mul (V : ℂ) (fun z : ℝ × ℝ =>
          (Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
          (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2))
    _ = _ := by
      rw [show (∫ z : ℝ × ℝ, ψ z.1 * ψ z.2 ∂(volume.prod volume)) =
          (∫ u : ℝ, ψ u) * ∫ v : ℝ, ψ v from integral_prod_mul ψ ψ,
        show (∫ z : ℝ × ℝ,
            (Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
            (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)
            ∂(volume.prod volume)) =
          (∫ u : ℝ, Complex.exp (Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) * ψ u) *
          ∫ v : ℝ, Complex.exp (-Complex.I * ((v / Real.sqrt V : ℝ) : ℂ)) * ψ v from
            integral_prod_mul
              (fun u : ℝ => Complex.exp (Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) * ψ u)
              (fun v : ℝ => Complex.exp (-Complex.I * ((v / Real.sqrt V : ℝ) : ℂ)) * ψ v)]
      ring

/-- Exact B.16, derived from B.15 and the product-integral algebra above. -/
theorem curvature_eq_b16_double_integral {V : ℝ} (hV : 0 < V)
    (p : ℤ → ℝ) (ψ : ℝ → ℂ)
    (hInv : LatticeFourierInversion V p ψ)
    (h0 : Integrable (fun z : ℝ × ℝ => (V : ℂ) * (ψ z.1 * ψ z.2))
      (volume.prod volume))
    (hphase : Integrable (fun z : ℝ × ℝ =>
      (V : ℂ) *
        ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
         (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)))
      (volume.prod volume)) :
    ((V : ℂ) ^ 2) *
        (((p 0 : ℝ) : ℂ) ^ 2 - (((p (-1) : ℝ) : ℂ) * ((p 1 : ℝ) : ℂ))) =
      (1 / (((2 * Real.pi : ℝ) : ℂ) ^ 2)) *
        ∫ z : ℝ × ℝ,
          (V : ℂ) *
            (1 - Complex.exp
              (Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ))) *
            (ψ z.1 * ψ z.2) ∂(volume.prod volume) := by
  have hs : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hzero : (∫ u : ℝ, phase V 0 u * ψ u) = ∫ u : ℝ, ψ u := by
    apply integral_congr_ae
    filter_upwards with u
    simp [phase_zero]
  have hneg : (∫ u : ℝ, phase V (-1) u * ψ u) =
      ∫ u : ℝ, Complex.exp (Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) * ψ u := by
    apply integral_congr_ae
    filter_upwards with u
    rw [phase_neg_one]
  have hone : (∫ u : ℝ, phase V 1 u * ψ u) =
      ∫ u : ℝ, Complex.exp (-Complex.I * ((u / Real.sqrt V : ℝ) : ℂ)) * ψ u := by
    apply integral_congr_ae
    filter_upwards with u
    rw [phase_one]
  rw [hInv 0, hInv (-1), hInv 1, hzero, hneg, hone,
    b16_double_integral hV ψ h0 hphase]
  push_cast [Real.sq_sqrt hV.le]
  have hsc : (((Real.sqrt V : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hs
  have hsqc : (((Real.sqrt V : ℝ) : ℂ)) ^ 2 = (V : ℂ) := by
    exact_mod_cast Real.sq_sqrt hV.le
  field_simp [hsc, hsqc]
  rw [hsqc]
  ring


theorem integral_antisymmetric_eq_zero (g : (ℝ × ℝ) → ℂ)
    (hanti : ∀ z, g z.swap = -g z) :
    ∫ z, g z ∂(volume.prod volume) = 0 := by
  have hswap := MeasureTheory.integral_prod_swap (μ := volume) (ν := volume) g
  have hneg : (∫ z, g z.swap ∂(volume.prod volume)) = -∫ z, g z ∂(volume.prod volume) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with z
    exact hanti z
  have hself : (∫ z, g z ∂(volume.prod volume)) =
      -∫ z, g z ∂(volume.prod volume) := hswap.symm.trans hneg
  have htwo : (2 : ℂ) * (∫ z, g z ∂(volume.prod volume)) = 0 := by
    linear_combination hself
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The imaginary sine part in B.16 vanishes by the swap `u ↔ v`. -/
theorem sine_part_integral_eq_zero (V : ℝ) (ψ : ℝ → ℂ) :
    (∫ z : ℝ × ℝ,
      ((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) *
        (ψ z.1 * ψ z.2) ∂(volume.prod volume)) = 0 := by
  apply integral_antisymmetric_eq_zero
  intro z
  change
    ((Real.sin ((z.2 - z.1) / Real.sqrt V) : ℝ) : ℂ) *
        (ψ z.2 * ψ z.1) =
      -(((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) *
        (ψ z.1 * ψ z.2))
  have harg : (z.2 - z.1) / Real.sqrt V =
      -((z.1 - z.2) / Real.sqrt V) := by ring
  rw [harg, Real.sin_neg]
  push_cast
  ring

/-- B.18: the kernel is nonnegative and globally bounded by `(u-v)²/2`. -/
theorem kernel_nonneg_and_le (V u v : ℝ) (hV : 0 ≤ V) :
    0 ≤ kernel V u v ∧ kernel V u v ≤ quadraticKernel u v := by
  constructor
  · exact mul_nonneg hV (sub_nonneg.mpr (Real.cos_le_one _))
  · by_cases hVz : V = 0
    · simp [kernel, quadraticKernel, hVz]
      positivity
    · have hVpos : 0 < V := lt_of_le_of_ne hV (Ne.symm hVz)
      have hs : 0 < Real.sqrt V := Real.sqrt_pos.2 hVpos
      have hc := Real.one_sub_sq_div_two_le_cos
        (x := (u - v) / Real.sqrt V)
      dsimp [kernel, quadraticKernel]
      have hmul := mul_le_mul_of_nonneg_left
        (show 1 - Real.cos ((u - v) / Real.sqrt V) ≤
            (((u - v) / Real.sqrt V) ^ 2) / 2 by linarith) hV
      rw [div_pow, Real.sq_sqrt hVpos.le] at hmul
      field_simp at hmul ⊢
      nlinarith

/-- A convenient product weight dominates the B.18 envelope. -/
theorem quadraticKernel_le_weight_mul_weight (u v : ℝ) :
    quadraticKernel u v ≤ weight u * weight v := by
  dsimp [quadraticKernel, weight]
  nlinarith [sq_nonneg (u + v), sq_nonneg (u * v)]

/-- Exact trigonometric factorization used for the B.18 pointwise limit. -/
lemma kernel_eq_sinc (V u v : ℝ) (hV : 0 < V) (huv : u ≠ v) :
    kernel V u v = quadraticKernel u v *
      (Real.sinc ((u - v) / (2 * Real.sqrt V))) ^ 2 := by
  have hs : Real.sqrt V ≠ 0 := (Real.sqrt_pos.2 hV).ne'
  have hd : u - v ≠ 0 := sub_ne_zero.mpr huv
  rw [Real.sinc_of_ne_zero (div_ne_zero hd (mul_ne_zero (by norm_num) hs))]
  dsimp [kernel, quadraticKernel]
  have htrig : 1 - Real.cos ((u - v) / Real.sqrt V) =
      2 * Real.sin ((u - v) / (2 * Real.sqrt V)) ^ 2 := by
    rw [show (u - v) / Real.sqrt V = 2 * ((u - v) / (2 * Real.sqrt V)) by field_simp]
    rw [Real.cos_two_mul, Real.sin_sq]
    ring
  rw [htrig]
  field_simp [Real.sq_sqrt hV.le]
  nlinarith [Real.sq_sqrt hV.le]

/-- B.18 pointwise convergence, stated for an arbitrary variance sequence. -/
theorem kernel_tendsto_quadratic {V : ℕ → ℝ}
    (hV : Tendsto V atTop atTop) (u v : ℝ) :
    Tendsto (fun n => kernel (V n) u v) atTop (nhds (quadraticKernel u v)) := by
  by_cases huv : u = v
  · subst v
    simp [kernel, quadraticKernel]
  · have hVpos : ∀ᶠ n in atTop, 0 < V n := (hV.eventually (eventually_gt_atTop 0))
    have hsqrt : Tendsto (fun n => Real.sqrt (V n)) atTop atTop := Real.tendsto_sqrt_atTop.comp hV
    have harg : Tendsto (fun n => (u - v) / (2 * Real.sqrt (V n))) atTop (nhds 0) := by
      have hinv : Tendsto (fun n => (Real.sqrt (V n))⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hsqrt
      have hc : Tendsto (fun n => ((u - v) / 2) * (Real.sqrt (V n))⁻¹)
          atTop (nhds 0) := by
        simpa using (tendsto_const_nhds.mul hinv)
      convert hc using 1 <;> simp [div_eq_mul_inv] <;> ring
    have hsinc : Tendsto (fun n => Real.sinc ((u - v) / (2 * Real.sqrt (V n))))
        atTop (nhds 1) := by
      simpa using (Real.continuous_sinc.continuousAt.tendsto.comp harg)
    have hfac : Tendsto
        (fun n => quadraticKernel u v *
          (Real.sinc ((u - v) / (2 * Real.sqrt (V n)))) ^ 2)
        atTop (nhds (quadraticKernel u v)) := by
      simpa using (tendsto_const_nhds.mul (hsinc.pow 2))
    apply hfac.congr'
    filter_upwards [hVpos] with n hn
    exact (kernel_eq_sinc (V n) u v hn huv).symm

/-- The B.16/B.20 product integrand after exact sine cancellation. -/
def curvatureIntegrand (V : ℝ) (ψ : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (kernel V z.1 z.2 : ℂ) * (ψ z.1 * ψ z.2)

/-- The limiting quadratic product integrand in B.20. -/
def limitingCurvatureIntegrand (φ : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (quadraticKernel z.1 z.2 : ℂ) * (φ z.1 * φ z.2)

/-- The imaginary sine summand in the expansion of the B.16 exponential. -/
def imaginarySineIntegrand (V : ℝ) (ψ : ℝ → ℂ) (z : ℝ × ℝ) : ℂ :=
  (Complex.I * (V : ℂ)) *
    (((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) *
      (ψ z.1 * ψ z.2))

/-- The scaled imaginary sine summand also integrates to zero exactly. -/
theorem imaginarySineIntegrand_integral_eq_zero (V : ℝ) (ψ : ℝ → ℂ) :
    (∫ z : ℝ × ℝ, imaginarySineIntegrand V ψ z ∂(volume.prod volume)) = 0 := by
  rw [show (∫ z : ℝ × ℝ, imaginarySineIntegrand V ψ z ∂(volume.prod volume)) =
      (Complex.I * (V : ℂ)) *
        ∫ z : ℝ × ℝ,
          ((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) *
            (ψ z.1 * ψ z.2) ∂(volume.prod volume) from
    integral_const_mul (Complex.I * (V : ℂ)) (fun z : ℝ × ℝ =>
      ((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) *
        (ψ z.1 * ψ z.2))]
  rw [sine_part_integral_eq_zero]
  simp

/-- B.16's complex exponential integral is exactly its real cosine-kernel
integral.  This is where the sine term is removed, rather than assumed away. -/
theorem b16_raw_integral_eq_kernel_integral (V : ℝ) (ψ : ℝ → ℂ)
    (hkernel : Integrable (curvatureIntegrand V ψ) (volume.prod volume))
    (hsine : Integrable (imaginarySineIntegrand V ψ) (volume.prod volume)) :
    (∫ z : ℝ × ℝ,
        (V : ℂ) *
          (1 - Complex.exp
            (Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ))) *
          (ψ z.1 * ψ z.2) ∂(volume.prod volume)) =
      ∫ z : ℝ × ℝ, curvatureIntegrand V ψ z ∂(volume.prod volume) := by
  calc
    _ = ∫ z : ℝ × ℝ,
        (curvatureIntegrand V ψ z - imaginarySineIntegrand V ψ z)
          ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with z
      have hexp :
          Complex.exp
              (Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ)) =
            ((Real.cos ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) +
              ((Real.sin ((z.1 - z.2) / Real.sqrt V) : ℝ) : ℂ) * Complex.I := by
        rw [show Complex.I * (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ) =
            (((z.1 - z.2) / Real.sqrt V : ℝ) : ℂ) * Complex.I by ring,
          Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
      rw [hexp]
      simp only [curvatureIntegrand, imaginarySineIntegrand, kernel]
      push_cast
      ring
    _ = (∫ z : ℝ × ℝ, curvatureIntegrand V ψ z ∂(volume.prod volume)) -
        ∫ z : ℝ × ℝ, imaginarySineIntegrand V ψ z ∂(volume.prod volume) :=
      integral_sub hkernel hsine
    _ = _ := by rw [imaginarySineIntegrand_integral_eq_zero]; simp

/-- The real form of B.16, obtained from B.15 and exact sine cancellation. -/
theorem curvature_eq_kernel_integral {V : ℝ} (hV : 0 < V)
    (p : ℤ → ℝ) (ψ : ℝ → ℂ)
    (hInv : LatticeFourierInversion V p ψ)
    (h0 : Integrable (fun z : ℝ × ℝ => (V : ℂ) * (ψ z.1 * ψ z.2))
      (volume.prod volume))
    (hphase : Integrable (fun z : ℝ × ℝ =>
      (V : ℂ) *
        ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * ψ z.1) *
         (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * ψ z.2)))
      (volume.prod volume))
    (hkernel : Integrable (curvatureIntegrand V ψ) (volume.prod volume))
    (hsine : Integrable (imaginarySineIntegrand V ψ) (volume.prod volume)) :
    V ^ 2 * (p 0 ^ 2 - p (-1) * p 1) =
      (1 / (2 * Real.pi) ^ 2) *
        (∫ z : ℝ × ℝ, curvatureIntegrand V ψ z ∂(volume.prod volume)).re := by
  have hc := curvature_eq_b16_double_integral hV p ψ hInv h0 hphase
  rw [b16_raw_integral_eq_kernel_integral V ψ hkernel hsine] at hc
  have hlhs :
      ((V : ℂ) ^ 2) *
          (((p 0 : ℝ) : ℂ) ^ 2 - (((p (-1) : ℝ) : ℂ) * ((p 1 : ℝ) : ℂ))) =
        ((V ^ 2 * (p 0 ^ 2 - p (-1) * p 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcoef :
      (1 / (((2 * Real.pi : ℝ) : ℂ) ^ 2)) =
        ((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  have hc' :
      ((V ^ 2 * (p 0 ^ 2 - p (-1) * p 1) : ℝ) : ℂ) =
        ((1 / (2 * Real.pi) ^ 2 : ℝ) : ℂ) *
          ∫ z : ℝ × ℝ, curvatureIntegrand V ψ z ∂(volume.prod volume) := by
    rw [← hlhs, ← hcoef]
    exact hc
  have hre := congrArg Complex.re hc'
  norm_num [Complex.mul_re, Complex.inv_re, Complex.normSq_apply, pow_two] at hre ⊢
  exact hre

def weightedNorm (g : ℝ → ℂ) (u : ℝ) : ℝ := weight u * ‖g u‖

def weightedDifference (g h : ℝ → ℂ) (u : ℝ) : ℝ :=
  weight u * ‖g u - h u‖

def weightedL1Distance (g h : ℝ → ℂ) : ℝ :=
  ∫ u : ℝ, weightedDifference g h u

/-- Genuine weighted `L¹` convergence through weight two, including the weighted
integrability data used in the quantitative product estimate. -/
structure WeightedL1Convergence (ψ : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) : Prop where
  phi_integrable : Integrable (weightedNorm φ)
  psi_integrable : ∀ n, Integrable (weightedNorm (ψ n))
  difference_integrable : ∀ n, Integrable (weightedDifference (ψ n) φ)
  tendsto_distance : Tendsto (fun n => weightedL1Distance (ψ n) φ) atTop (nhds 0)

lemma weight_nonneg (u : ℝ) : 0 ≤ weight u := by
  simp [weight]
  positivity

lemma norm_mul_sub_mul_le (a b c d : ℂ) :
    ‖a * b - c * d‖ ≤
      ‖a - c‖ * ‖b - d‖ + ‖a - c‖ * ‖d‖ + ‖c‖ * ‖b - d‖ := by
  have hid : a * b - c * d =
      (a - c) * (b - d) + (a - c) * d + c * (b - d) := by ring
  rw [hid]
  calc
    _ ≤ ‖(a - c) * (b - d) + (a - c) * d‖ + ‖c * (b - d)‖ := norm_add_le _ _
    _ ≤ (‖(a - c) * (b - d)‖ + ‖(a - c) * d‖) + ‖c * (b - d)‖ := by
      gcongr
      exact norm_add_le _ _
    _ = _ := by simp only [norm_mul]

lemma curvature_difference_norm_le
    (V : ℝ) (hV : 0 ≤ V) (g h : ℝ → ℂ) (z : ℝ × ℝ) :
    ‖curvatureIntegrand V g z - curvatureIntegrand V h z‖ ≤
      weightedDifference g h z.1 * weightedDifference g h z.2 +
      weightedDifference g h z.1 * weightedNorm h z.2 +
      weightedNorm h z.1 * weightedDifference g h z.2 := by
  have hk := kernel_nonneg_and_le V z.1 z.2 hV
  have hkw : kernel V z.1 z.2 ≤ weight z.1 * weight z.2 :=
    hk.2.trans (quadraticKernel_le_weight_mul_weight z.1 z.2)
  have hprod := norm_mul_sub_mul_le (g z.1) (g z.2) (h z.1) (h z.2)
  calc
    _ = ‖((kernel V z.1 z.2 : ℂ) *
          (g z.1 * g z.2 - h z.1 * h z.2))‖ := by
        congr 1
        simp only [curvatureIntegrand]
        ring
    _ = kernel V z.1 z.2 * ‖g z.1 * g z.2 - h z.1 * h z.2‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk.1]
    _ ≤ (weight z.1 * weight z.2) *
          ‖g z.1 * g z.2 - h z.1 * h z.2‖ :=
        mul_le_mul_of_nonneg_right hkw (norm_nonneg _)
    _ ≤ (weight z.1 * weight z.2) *
          (‖g z.1 - h z.1‖ * ‖g z.2 - h z.2‖ +
           ‖g z.1 - h z.1‖ * ‖h z.2‖ +
           ‖h z.1‖ * ‖g z.2 - h z.2‖) :=
        mul_le_mul_of_nonneg_left hprod
          (mul_nonneg (weight_nonneg z.1) (weight_nonneg z.2))
    _ = _ := by
      simp only [weightedDifference, weightedNorm]
      ring

def productErrorMajorant (g h : ℝ → ℂ) (z : ℝ × ℝ) : ℝ :=
  weightedDifference g h z.1 * weightedDifference g h z.2 +
  weightedDifference g h z.1 * weightedNorm h z.2 +
  weightedNorm h z.1 * weightedDifference g h z.2

def weightedL1Norm (g : ℝ → ℂ) : ℝ := ∫ u : ℝ, weightedNorm g u

lemma curvature_norm_le
    (V : ℝ) (hV : 0 ≤ V) (g : ℝ → ℂ) (z : ℝ × ℝ) :
    ‖curvatureIntegrand V g z‖ ≤ weightedNorm g z.1 * weightedNorm g z.2 := by
  have hk := kernel_nonneg_and_le V z.1 z.2 hV
  have hkw : kernel V z.1 z.2 ≤ weight z.1 * weight z.2 :=
    hk.2.trans (quadraticKernel_le_weight_mul_weight z.1 z.2)
  calc
    _ = kernel V z.1 z.2 * (‖g z.1‖ * ‖g z.2‖) := by
      simp [curvatureIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hk.1]
    _ ≤ (weight z.1 * weight z.2) * (‖g z.1‖ * ‖g z.2‖) :=
      mul_le_mul_of_nonneg_right hkw (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [weightedNorm]; ring

lemma curvatureIntegrand_integrable
    (V : ℝ) (hV : 0 ≤ V) (g : ℝ → ℂ)
    (hg : Integrable (weightedNorm g))
    (hmeas : AEStronglyMeasurable (curvatureIntegrand V g) (volume.prod volume)) :
    Integrable (curvatureIntegrand V g) (volume.prod volume) := by
  apply (hg.mul_prod hg).mono' hmeas
  filter_upwards with z
  exact curvature_norm_le V hV g z

lemma productErrorMajorant_integrable
    {ψ : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hweighted : WeightedL1Convergence ψ φ) (n : ℕ) :
    Integrable (productErrorMajorant (ψ n) φ) (volume.prod volume) := by
  have hd := hweighted.difference_integrable n
  have hp := hweighted.phi_integrable
  exact ((hd.mul_prod hd).add (hd.mul_prod hp)).add (hp.mul_prod hd)

lemma integral_productErrorMajorant
    {ψ : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hweighted : WeightedL1Convergence ψ φ) (n : ℕ) :
    (∫ z : ℝ × ℝ, productErrorMajorant (ψ n) φ z ∂(volume.prod volume)) =
      weightedL1Distance (ψ n) φ * weightedL1Distance (ψ n) φ +
      weightedL1Distance (ψ n) φ * weightedL1Norm φ +
      weightedL1Norm φ * weightedL1Distance (ψ n) φ := by
  have hd := hweighted.difference_integrable n
  have hp := hweighted.phi_integrable
  simp only [productErrorMajorant]
  calc
    _ = (∫ z : ℝ × ℝ,
          weightedDifference (ψ n) φ z.1 * weightedDifference (ψ n) φ z.2 +
          weightedDifference (ψ n) φ z.1 * weightedNorm φ z.2
          ∂(volume.prod volume)) +
        ∫ z : ℝ × ℝ,
          weightedNorm φ z.1 * weightedDifference (ψ n) φ z.2
          ∂(volume.prod volume) := by
      apply integral_add ((hd.mul_prod hd).add (hd.mul_prod hp)) (hp.mul_prod hd)
    _ = ((∫ z : ℝ × ℝ,
            weightedDifference (ψ n) φ z.1 * weightedDifference (ψ n) φ z.2
            ∂(volume.prod volume)) +
          ∫ z : ℝ × ℝ,
            weightedDifference (ψ n) φ z.1 * weightedNorm φ z.2
            ∂(volume.prod volume)) +
        ∫ z : ℝ × ℝ,
          weightedNorm φ z.1 * weightedDifference (ψ n) φ z.2
          ∂(volume.prod volume) := by
      rw [integral_add (hd.mul_prod hd) (hd.mul_prod hp)]
    _ = _ := by
      rw [integral_prod_mul, integral_prod_mul, integral_prod_mul]
      rfl

lemma integral_curvature_difference_norm_le
    {ψ : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hweighted : WeightedL1Convergence ψ φ)
    (V : ℝ) (hV : 0 ≤ V) (n : ℕ)
    (hmeasψ : AEStronglyMeasurable (curvatureIntegrand V (ψ n))
      (volume.prod volume))
    (hmeasφ : AEStronglyMeasurable (curvatureIntegrand V φ)
      (volume.prod volume)) :
    ‖(∫ z : ℝ × ℝ, curvatureIntegrand V (ψ n) z ∂(volume.prod volume)) -
      ∫ z : ℝ × ℝ, curvatureIntegrand V φ z ∂(volume.prod volume)‖ ≤
      weightedL1Distance (ψ n) φ * weightedL1Distance (ψ n) φ +
      weightedL1Distance (ψ n) φ * weightedL1Norm φ +
      weightedL1Norm φ * weightedL1Distance (ψ n) φ := by
  have hψint := curvatureIntegrand_integrable V hV (ψ n)
    (hweighted.psi_integrable n) hmeasψ
  have hφint := curvatureIntegrand_integrable V hV φ
    hweighted.phi_integrable hmeasφ
  rw [← integral_sub hψint hφint]
  calc
    _ ≤ ∫ z : ℝ × ℝ, productErrorMajorant (ψ n) φ z ∂(volume.prod volume) := by
      apply norm_integral_le_of_norm_le (productErrorMajorant_integrable hweighted n)
      filter_upwards with z
      exact curvature_difference_norm_le V hV (ψ n) φ z
    _ = _ := integral_productErrorMajorant hweighted n

lemma fixed_phi_kernel_integral_tendsto
    (V : ℕ → ℝ) (φ : ℝ → ℂ)
    (hV : Tendsto V atTop atTop) (hVpos : ∀ n, 0 < V n)
    (hφ : Integrable (weightedNorm φ))
    (hmeasφ : ∀ n, AEStronglyMeasurable (curvatureIntegrand (V n) φ)
      (volume.prod volume)) :
    Tendsto
      (fun n => ∫ z : ℝ × ℝ,
        curvatureIntegrand (V n) φ z ∂(volume.prod volume))
      atTop
      (nhds (∫ z : ℝ × ℝ,
        limitingCurvatureIntegrand φ z ∂(volume.prod volume))) := by
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun z : ℝ × ℝ => weightedNorm φ z.1 * weightedNorm φ z.2)
    hmeasφ (hφ.mul_prod hφ)
  · intro n
    filter_upwards with z
    exact curvature_norm_le (V n) (hVpos n).le φ z
  · filter_upwards with z
    have hk := kernel_tendsto_quadratic (V := V) hV z.1 z.2
    have hkc : Tendsto (fun n => (kernel (V n) z.1 z.2 : ℂ)) atTop
        (nhds (quadraticKernel z.1 z.2 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hk
    simpa only [curvatureIntegrand, limitingCurvatureIntegrand] using
      hkc.mul (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => φ z.1 * φ z.2) atTop (nhds (φ z.1 * φ z.2)))

/-- B.20 proved by an essential weighted-`L¹` product replacement, followed
by dominated convergence only for the fixed limiting product `φ ⊗ φ`. -/
theorem b20_integral_tendsto
    (V : ℕ → ℝ) (ψ : ℕ → ℝ → ℂ) (φ : ℝ → ℂ)
    (hV : Tendsto V atTop atTop) (hVpos : ∀ n, 0 < V n)
    (hweighted : WeightedL1Convergence ψ φ)
    (hmeasψ : ∀ n, AEStronglyMeasurable (curvatureIntegrand (V n) (ψ n))
      (volume.prod volume))
    (hmeasφ : ∀ n, AEStronglyMeasurable (curvatureIntegrand (V n) φ)
      (volume.prod volume)) :
    Tendsto
      (fun n => ∫ z : ℝ × ℝ,
        curvatureIntegrand (V n) (ψ n) z ∂(volume.prod volume))
      atTop
      (nhds (∫ z : ℝ × ℝ,
        limitingCurvatureIntegrand φ z ∂(volume.prod volume))) := by
  have hD := hweighted.tendsto_distance
  have hA : Tendsto (fun _ : ℕ => weightedL1Norm φ) atTop
      (nhds (weightedL1Norm φ)) := tendsto_const_nhds
  have herror : Tendsto (fun n =>
      weightedL1Distance (ψ n) φ * weightedL1Distance (ψ n) φ +
      weightedL1Distance (ψ n) φ * weightedL1Norm φ +
      weightedL1Norm φ * weightedL1Distance (ψ n) φ) atTop (nhds 0) := by
    simpa [add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (hD.mul hD).add ((hD.mul hA).add (hA.mul hD))
  have hreplace : Tendsto (fun n =>
      (∫ z : ℝ × ℝ, curvatureIntegrand (V n) (ψ n) z ∂(volume.prod volume)) -
      ∫ z : ℝ × ℝ, curvatureIntegrand (V n) φ z ∂(volume.prod volume))
      atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero
    · intro n
      exact norm_nonneg _
    · intro n
      exact integral_curvature_difference_norm_le hweighted (V n) (hVpos n).le n
        (hmeasψ n) (hmeasφ n)
    · exact herror
  have hfixed := fixed_phi_kernel_integral_tendsto V φ hV hVpos
    hweighted.phi_integrable hmeasφ
  simpa only [sub_add_cancel, zero_add] using hreplace.add hfixed


/-- Zeroth Fourier moment. -/
def moment0 (φ : ℝ → ℂ) : ℂ := ∫ u : ℝ, φ u

/-- First Fourier moment. -/
def moment1 (φ : ℝ → ℂ) : ℂ := ∫ u : ℝ, (u : ℂ) * φ u

/-- Second Fourier moment. -/
def moment2 (φ : ℝ → ℂ) : ℂ := ∫ u : ℝ, ((u ^ 2 : ℝ) : ℂ) * φ u

/-- B.21, together with the value formula from B.14, expressed using the
Fourier moments.  These are representation hypotheses, not curvature data. -/
def FourierDerivativeIdentities
    (f f' f'' : ℝ → ℝ) (φ : ℝ → ℂ) : Prop :=
  ((f 0 : ℝ) : ℂ) = (1 / ((2 * Real.pi : ℝ) : ℂ)) * moment0 φ ∧
  ((f' 0 : ℝ) : ℂ) =
    (1 / ((2 * Real.pi : ℝ) : ℂ)) * (-Complex.I * moment1 φ) ∧
  ((f'' 0 : ℝ) : ℂ) =
    (1 / ((2 * Real.pi : ℝ) : ℂ)) * (-moment2 φ)

/-- `f'` and `f''` really are the first two derivatives of `f`. -/
def TwiceDifferentiableWith (f f' f'' : ℝ → ℝ) : Prop :=
  (∀ x, HasDerivAt f (f' x) x) ∧ ∀ x, HasDerivAt f' (f'' x) x

/-- Expansion and symmetrization of the quadratic integral in B.20. -/
theorem limiting_integral_eq_moments (φ : ℝ → ℂ)
    (hleft : Integrable (fun z : ℝ × ℝ =>
      ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2) (volume.prod volume))
    (hright : Integrable (fun z : ℝ × ℝ =>
      φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)) (volume.prod volume))
    (hcross : Integrable (fun z : ℝ × ℝ =>
      (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2))
      (volume.prod volume)) :
    (∫ z : ℝ × ℝ, limitingCurvatureIntegrand φ z ∂(volume.prod volume)) =
      moment2 φ * moment0 φ - moment1 φ ^ 2 := by
  let left : (ℝ × ℝ) → ℂ := fun z =>
    ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2
  let right : (ℝ × ℝ) → ℂ := fun z =>
    φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)
  let cross : (ℝ × ℝ) → ℂ := fun z =>
    (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2)
  change Integrable left (volume.prod volume) at hleft
  change Integrable right (volume.prod volume) at hright
  change Integrable cross (volume.prod volume) at hcross
  have hpoint : ∀ z, limitingCurvatureIntegrand φ z =
      left z + right z - cross z := by
    intro z
    simp only [limitingCurvatureIntegrand, quadraticKernel, left, right, cross]
    push_cast
    ring
  calc
    _ = ∫ z : ℝ × ℝ, (left z + right z - cross z) ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hpoint z
    _ = (∫ z : ℝ × ℝ, left z ∂(volume.prod volume)) +
          (∫ z : ℝ × ℝ, right z ∂(volume.prod volume)) -
          ∫ z : ℝ × ℝ, cross z ∂(volume.prod volume) := by
      calc
        _ = (∫ z : ℝ × ℝ, (left z + right z) ∂(volume.prod volume)) -
              ∫ z : ℝ × ℝ, cross z ∂(volume.prod volume) :=
            integral_sub (hleft.add hright) hcross
        _ = _ := by rw [integral_add hleft hright]
    _ = ((∫ u : ℝ, ((((u ^ 2) / 2 : ℝ) : ℂ) * φ u)) * moment0 φ) +
          (moment0 φ * ∫ v : ℝ, ((((v ^ 2) / 2 : ℝ) : ℂ) * φ v)) -
          moment1 φ * moment1 φ := by
      simp only [left, right, cross, moment0, moment1]
      rw [show (∫ z : ℝ × ℝ,
            (((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2)
            ∂(volume.prod volume)) =
          (∫ u : ℝ, ((((u ^ 2) / 2 : ℝ) : ℂ) * φ u)) *
            ∫ v : ℝ, φ v from
          integral_prod_mul
            (fun u : ℝ => ((((u ^ 2) / 2 : ℝ) : ℂ) * φ u)) φ,
        show (∫ z : ℝ × ℝ,
            φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)
            ∂(volume.prod volume)) =
          (∫ u : ℝ, φ u) *
            ∫ v : ℝ, ((((v ^ 2) / 2 : ℝ) : ℂ) * φ v) from
          integral_prod_mul φ
            (fun v : ℝ => ((((v ^ 2) / 2 : ℝ) : ℂ) * φ v)),
        show (∫ z : ℝ × ℝ,
            (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2)
            ∂(volume.prod volume)) =
          (∫ u : ℝ, ((u : ℝ) : ℂ) * φ u) *
            ∫ v : ℝ, ((v : ℝ) : ℂ) * φ v from
          integral_prod_mul
            (fun u : ℝ => ((u : ℝ) : ℂ) * φ u)
            (fun v : ℝ => ((v : ℝ) : ℂ) * φ v)]
    _ = _ := by
      have hhalf : (∫ u : ℝ, ((((u ^ 2) / 2 : ℝ) : ℂ) * φ u)) =
          (1 / 2 : ℂ) * moment2 φ := by
        calc
          _ = ∫ u : ℝ, (1 / 2 : ℂ) * ((((u ^ 2 : ℝ) : ℂ) * φ u)) := by
            apply integral_congr_ae
            filter_upwards with u
            push_cast
            ring
          _ = (1 / 2 : ℂ) * ∫ u : ℝ, ((((u ^ 2 : ℝ) : ℂ) * φ u)) :=
            integral_const_mul (1 / 2 : ℂ)
              (fun u : ℝ => (((u ^ 2 : ℝ) : ℂ) * φ u))
          _ = _ := rfl
      rw [hhalf]
      ring

/-- B.21 identifies the limiting Fourier moment expression with the desired
Turan curvature. -/
theorem b21_moments_eq_derivative_curvature
    (f f' f'' : ℝ → ℝ) (φ : ℝ → ℂ)
    (hFourier : FourierDerivativeIdentities f f' f'' φ) :
    (1 / (((2 * Real.pi : ℝ) : ℂ) ^ 2)) *
        (moment2 φ * moment0 φ - moment1 φ ^ 2) =
      (((f' 0) ^ 2 - f 0 * f'' 0 : ℝ) : ℂ) := by
  rcases hFourier with ⟨hzero, hone, htwo⟩
  have hcast :
      (((f' 0) ^ 2 - f 0 * f'' 0 : ℝ) : ℂ) =
        (((f' 0 : ℝ) : ℂ) ^ 2 -
          (((f 0 : ℝ) : ℂ) * ((f'' 0 : ℝ) : ℂ))) := by
    push_cast
    rfl
  rw [hcast, hone, hzero, htwo]
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  field_simp [hpi]
  simp only [pow_two]
  rw [Complex.I_mul_I]
  ring

/-- A limiting density with actual first and second derivatives and the B.14/B.21
Fourier representations at zero. -/
def TwiceDifferentiableFourierDensity
    (f f' f'' : ℝ → ℝ) (φ : ℝ → ℂ) : Prop :=
  TwiceDifferentiableWith f f' f'' ∧ FourierDerivativeIdentities f f' f'' φ

/-- Wave 1 unit W1.3: lattice inversion, B.16, B.18, B.20, and the
B.21 Fourier identities combine to give the limiting Turan curvature.  The
actual derivative relationship is orthogonal to this algebraic endpoint and is
therefore not assumed here; the measure-level inversion adapter supplies both
it and these identities. -/
theorem fourier_turan_curvature_limit
    (V : ℕ → ℝ) (p : ℕ → ℤ → ℝ)
    (ψ : ℕ → ℝ → ℂ) (φ : ℝ → ℂ)
    (f f' f'' : ℝ → ℝ)
    (hV : Tendsto V atTop atTop)
    (hVpos : ∀ n, 0 < V n)
    (hInv : ∀ n, LatticeFourierInversion (V n) (p n) (ψ n))
    (hweighted : WeightedL1Convergence ψ φ)
    (hmeasψ : ∀ n, AEStronglyMeasurable (curvatureIntegrand (V n) (ψ n))
      (volume.prod volume))
    (hmeasφ : ∀ n, AEStronglyMeasurable (curvatureIntegrand (V n) φ)
      (volume.prod volume))
    (h0 : ∀ n, Integrable
      (fun z : ℝ × ℝ => (V n : ℂ) * (ψ n z.1 * ψ n z.2))
      (volume.prod volume))
    (hphase : ∀ n, Integrable (fun z : ℝ × ℝ =>
      (V n : ℂ) *
        ((Complex.exp
            (Complex.I * ((z.1 / Real.sqrt (V n) : ℝ) : ℂ)) * ψ n z.1) *
         (Complex.exp
            (-Complex.I * ((z.2 / Real.sqrt (V n) : ℝ) : ℂ)) * ψ n z.2)))
      (volume.prod volume))
    (hsine : ∀ n, Integrable (imaginarySineIntegrand (V n) (ψ n))
      (volume.prod volume))
    (hleft : Integrable (fun z : ℝ × ℝ =>
      ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2) (volume.prod volume))
    (hright : Integrable (fun z : ℝ × ℝ =>
      φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)) (volume.prod volume))
    (hcross : Integrable (fun z : ℝ × ℝ =>
      (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2))
      (volume.prod volume))
    (hdensity : FourierDerivativeIdentities f f' f'' φ) :
    Tendsto
      (fun n => V n ^ 2 * (p n 0 ^ 2 - p n (-1) * p n 1))
      atTop (nhds ((f' 0) ^ 2 - f 0 * f'' 0)) := by
  let J : ℕ → ℂ := fun n =>
    ∫ z : ℝ × ℝ, curvatureIntegrand (V n) (ψ n) z ∂(volume.prod volume)
  let Jlim : ℂ :=
    ∫ z : ℝ × ℝ, limitingCurvatureIntegrand φ z ∂(volume.prod volume)
  have hJ : Tendsto J atTop (nhds Jlim) := by
    exact b20_integral_tendsto V ψ φ hV hVpos hweighted hmeasψ hmeasφ
  have hJre : Tendsto (fun n => (J n).re) atTop (nhds Jlim.re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hJ
  let c : ℝ := 1 / (2 * Real.pi) ^ 2
  have hscaled : Tendsto (fun n => c * (J n).re) atTop (nhds (c * Jlim.re)) :=
    tendsto_const_nhds.mul hJre
  have hseq : Tendsto
      (fun n => V n ^ 2 * (p n 0 ^ 2 - p n (-1) * p n 1))
      atTop (nhds (c * Jlim.re)) := by
    apply hscaled.congr'
    filter_upwards with n
    simpa only [c, J] using
      (curvature_eq_kernel_integral (hVpos n) (p n) (ψ n)
        (hInv n) (h0 n) (hphase n)
        (curvatureIntegrand_integrable (V n) (hVpos n).le (ψ n)
          (hweighted.psi_integrable n) (hmeasψ n))
        (hsine n)).symm
  have hmoment : Jlim = moment2 φ * moment0 φ - moment1 φ ^ 2 := by
    exact limiting_integral_eq_moments φ hleft hright hcross
  have hlimComplex :
      ((c : ℝ) : ℂ) * Jlim = (((f' 0) ^ 2 - f 0 * f'' 0 : ℝ) : ℂ) := by
    have hcoef : ((c : ℝ) : ℂ) =
        1 / (((2 * Real.pi : ℝ) : ℂ) ^ 2) := by
      dsimp [c]
      push_cast
      rfl
    rw [hcoef, hmoment]
    exact b21_moments_eq_derivative_curvature f f' f'' φ hdensity
  have hlimReal : c * Jlim.re = (f' 0) ^ 2 - f 0 * f'' 0 := by
    have hre := congrArg Complex.re hlimComplex
    norm_num [Complex.mul_re, pow_two] at hre ⊢
    exact hre
  rw [hlimReal] at hseq
  exact hseq

end

end Erdos993.Forest.FourierTuranCurvature
