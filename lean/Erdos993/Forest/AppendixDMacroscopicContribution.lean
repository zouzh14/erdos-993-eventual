import Erdos993.Forest.ActualMartingaleProjection
import Erdos993.Forest.ComplexConditionalExpectation
import Erdos993.Forest.ConditionalOutsideLaw
import Erdos993.Forest.IndependentComponentFourier
import Erdos993.Forest.UniformFourthMoment
import Erdos993.Forest.MartingaleArrayCLT
import Erdos993.Forest.LargeDisplacementContribution
import Erdos993.Forest.CanonicalCompactnessWrapper
import Erdos993.Forest.CanonicalActivityFloor
import Erdos993.Forest.CanonicalCenterDecay
import Erdos993.Forest.FiniteSubprobabilityCompactness
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Appendix D: macroscopic variance contribution (actual rooted progress)

This module formalizes additional finite ingredients of Appendix D for the actual
component rooting.  Every quantity is evaluated in the one original
`CanonicalFirstRecoveryState`; no descendant subtree, exposed law, or retained
forest is assigned canonicity or first-recovery data.
-/

open scoped BigOperators Topology NNReal ENNReal
open Filter Set

namespace Erdos993
namespace ActualRootedVariance

noncomputable section

universe u

noncomputable local instance finiteSubtypeAppendixD
    {α : Type*} [Fintype α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

namespace ComponentRooting

open Forest

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Stable finite-product replacement: products of two families of contractions
differ by at most the sum of the one-factor errors.  This is the algebraic
product bridge used in (D.31)--(D.32). -/
theorem norm_prod_sub_prod_le_sum_norm_sub
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤
      ∑ i ∈ s, ‖a i - b i‖ := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hais : ‖a i‖ ≤ 1 := ha i (Finset.mem_insert_self i s)
      have hbis : ‖b i‖ ≤ 1 := hb i (Finset.mem_insert_self i s)
      have ha' : ∀ j ∈ s, ‖a j‖ ≤ 1 := fun j hj =>
        ha j (Finset.mem_insert_of_mem hj)
      have hb' : ∀ j ∈ s, ‖b j‖ ≤ 1 := fun j hj =>
        hb j (Finset.mem_insert_of_mem hj)
      have hprodB : ‖∏ j ∈ s, b j‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun j hj => norm_nonneg _) hb'
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      calc
        ‖a i * ∏ x ∈ s, a x - b i * ∏ x ∈ s, b x‖ =
            ‖a i * ((∏ x ∈ s, a x) - ∏ x ∈ s, b x) +
              (a i - b i) * ∏ x ∈ s, b x‖ := by
                congr 1
                ring
        _ ≤ ‖a i * ((∏ x ∈ s, a x) - ∏ x ∈ s, b x)‖ +
              ‖(a i - b i) * ∏ x ∈ s, b x‖ := norm_add_le _ _
        _ = ‖a i‖ * ‖(∏ x ∈ s, a x) - ∏ x ∈ s, b x‖ +
              ‖a i - b i‖ * ‖∏ x ∈ s, b x‖ := by
                rw [norm_mul, norm_mul]
        _ ≤ ‖(∏ x ∈ s, a x) - ∏ x ∈ s, b x‖ +
              ‖a i - b i‖ := by
                exact add_le_add
                  (mul_le_of_le_one_left (norm_nonneg _) hais)
                  (mul_le_of_le_one_right (norm_nonneg _) hprodB)
        _ ≤ ‖a i - b i‖ + ∑ x ∈ s, ‖a x - b x‖ := by
                have hih := ih ha' hb'
                linarith


/-- A global quadratic majorant for the same third-order Fourier remainder.
The small phase uses the production cubic Taylor bound; outside the unit ball
only the unit norm of a pure imaginary exponential is used. -/
theorem norm_thirdOrderRemainder_le_four_mul_sq (t x : ℝ) :
    ‖MartingaleArrayCLT.thirdOrderRemainder t x‖ ≤ 4 * |t * x| ^ 2 := by
  by_cases hsmall : |t * x| ≤ 1
  · calc
      ‖MartingaleArrayCLT.thirdOrderRemainder t x‖ ≤
          (2 / 9 : ℝ) * |t * x| ^ 3 :=
        MartingaleArrayCLT.norm_thirdOrderRemainder_le t x hsmall
      _ ≤ 4 * |t * x| ^ 2 := by
        have hnonneg : 0 ≤ |t * x| := abs_nonneg _
        nlinarith [mul_self_nonneg |t * x|]
  · have hlarge : 1 ≤ |t * x| := le_of_not_ge hsmall
    have hphase : ‖MartingaleArrayCLT.complexPhase t x‖ = 1 := by
      exact Complex.norm_exp_I_mul_ofReal (t * x)
    have hI : ‖Complex.I * ((t * x : ℝ) : ℂ)‖ = |t * x| := by
      simp [Real.norm_eq_abs]
    have hquad : ‖(((t * x) ^ 2 / 2 : ℝ) : ℂ)‖ = |t * x| ^ 2 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      · rw [sq_abs]
      · positivity
    calc
      ‖MartingaleArrayCLT.thirdOrderRemainder t x‖ =
          ‖MartingaleArrayCLT.complexPhase t x - 1 -
            Complex.I * ((t * x : ℝ) : ℂ) +
            (((t * x) ^ 2 / 2 : ℝ) : ℂ)‖ := rfl
      _ ≤ ‖MartingaleArrayCLT.complexPhase t x - 1 -
              Complex.I * ((t * x : ℝ) : ℂ)‖ +
            ‖(((t * x) ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖MartingaleArrayCLT.complexPhase t x - 1‖ +
            ‖Complex.I * ((t * x : ℝ) : ℂ)‖) +
            ‖(((t * x) ^ 2 / 2 : ℝ) : ℂ)‖ := by
              gcongr
              exact norm_sub_le _ _
      _ ≤ (‖MartingaleArrayCLT.complexPhase t x‖ + ‖(1 : ℂ)‖ +
            ‖Complex.I * ((t * x : ℝ) : ℂ)‖) +
            ‖(((t * x) ^ 2 / 2 : ℝ) : ℂ)‖ := by
              gcongr
              exact norm_sub_le _ _
      _ = 2 + |t * x| + |t * x| ^ 2 / 2 := by
            rw [hphase, hI, hquad]
            norm_num
      _ ≤ 4 * |t * x| ^ 2 := by
            have hnonneg : 0 ≤ |t * x| := abs_nonneg _
            nlinarith [mul_self_nonneg (|t * x| - 1)]

/-- Exact one-factor quadratic expansion, with error bounded by the expected
production third-order remainder. -/
theorem centeredCharacteristic_quadratic_error_le_remainder
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (θ : ℝ) :
    ‖L.centeredCharacteristic θ -
        (1 - (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ))‖ ≤
      ∑ a, L.probability a *
        ‖MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ := by
  have hm1 : (∑ a, L.probability a * L.centeredValue a) = 0 := by
    simpa [FiniteLatticeLaw.centeredMoment] using L.centeredMoment_one
  have hm2 : (∑ a, L.probability a * L.centeredValue a ^ 2) = L.variance := by
    simpa [FiniteLatticeLaw.centeredMoment] using L.centeredMoment_two
  have hprobC : (∑ a, (L.probability a : ℂ)) = 1 := by
    exact_mod_cast L.probability_sum
  have hm1C :
      (∑ a, (L.probability a : ℂ) * (L.centeredValue a : ℂ)) = 0 := by
    exact_mod_cast hm1
  have hm2C :
      (∑ a, (L.probability a : ℂ) * ((L.centeredValue a ^ 2 : ℝ) : ℂ)) =
        (L.variance : ℂ) := by
    exact_mod_cast hm2
  have hlinear :
      (∑ a, (L.probability a : ℂ) *
        (Complex.I * ((θ * L.centeredValue a : ℝ) : ℂ))) = 0 := by
    calc
      _ = Complex.I * (θ : ℂ) *
          ∑ a, (L.probability a : ℂ) * (L.centeredValue a : ℂ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a ha
            push_cast
            ring
      _ = 0 := by rw [hm1C]; ring
  have hquadratic :
      (∑ a, (L.probability a : ℂ) *
        (((θ * L.centeredValue a) ^ 2 / 2 : ℝ) : ℂ)) =
        (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ) := by
    calc
      _ = (((θ ^ 2 / 2 : ℝ) : ℂ)) *
          ∑ a, (L.probability a : ℂ) *
            ((L.centeredValue a ^ 2 : ℝ) : ℂ) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro a ha
              push_cast
              ring
      _ = (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ) := by
        rw [hm2C]
        push_cast
        ring
  have hsum :
      L.centeredCharacteristic θ -
          (1 - (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ)) =
        ∑ a, (L.probability a : ℂ) *
          MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a) := by
    symm
    calc
      (∑ a, (L.probability a : ℂ) *
          MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)) =
          ∑ a, ((L.probability a : ℂ) *
              FiniteLatticeLaw.phase θ (L.centeredValue a) -
            (L.probability a : ℂ) -
            (L.probability a : ℂ) *
              (Complex.I * ((θ * L.centeredValue a : ℝ) : ℂ)) +
            (L.probability a : ℂ) *
              (((θ * L.centeredValue a) ^ 2 / 2 : ℝ) : ℂ)) := by
                apply Finset.sum_congr rfl
                intro a ha
                unfold MartingaleArrayCLT.thirdOrderRemainder
                  MartingaleArrayCLT.complexPhase FiniteLatticeLaw.phase
                ring
      _ = (∑ a, (L.probability a : ℂ) *
              FiniteLatticeLaw.phase θ (L.centeredValue a)) -
            (∑ a, (L.probability a : ℂ)) -
            (∑ a, (L.probability a : ℂ) *
              (Complex.I * ((θ * L.centeredValue a : ℝ) : ℂ))) +
            (∑ a, (L.probability a : ℂ) *
              (((θ * L.centeredValue a) ^ 2 / 2 : ℝ) : ℂ)) := by
                rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  Finset.sum_sub_distrib]
      _ = L.centeredCharacteristic θ - 1 +
            (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ) := by
                rw [hprobC, hlinear, hquadratic]
                simp [FiniteLatticeLaw.centeredCharacteristic,
                  FiniteLatticeLaw.centeredValue]
      _ = L.centeredCharacteristic θ -
            (1 - (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ)) := by ring
  rw [hsum]
  calc
    ‖∑ a, (L.probability a : ℂ) *
        MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ ≤
      ∑ a, ‖(L.probability a : ℂ) *
        MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ :=
          norm_sum_le _ _
    _ = ∑ a, L.probability a *
        ‖MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (L.probability_nonneg a)]

/-- Fourth-moment/truncation form of the one-factor D.31 estimate.  The cutoff
`R` is external and no property of the law beyond its literal centered moments
is assumed. -/
theorem centeredCharacteristic_quadratic_error_le_fourth
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (θ Rcut : ℝ)
    (hR : 0 < Rcut) (hθR : |θ| * Rcut ≤ 1) :
    ‖L.centeredCharacteristic θ -
        (1 - (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ))‖ ≤
      (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * L.variance +
        (4 * θ ^ 2 / Rcut ^ 2) * L.centeredMoment 4 := by
  have hpoint : ∀ a,
      ‖MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ ≤
        (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * L.centeredValue a ^ 2 +
          (4 * θ ^ 2 / Rcut ^ 2) * L.centeredValue a ^ 4 := by
    intro a
    let z := L.centeredValue a
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    have hz4 : 0 ≤ z ^ 4 := by positivity
    have hA : 0 ≤ (2 / 9 : ℝ) * |θ| ^ 3 * Rcut := by positivity
    have hB : 0 ≤ 4 * θ ^ 2 / Rcut ^ 2 := by positivity
    by_cases hzR : |z| ≤ Rcut
    · have hphase : |θ * z| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hzR (abs_nonneg θ)).trans hθR
      have hcub : |z| ^ 3 ≤ Rcut * z ^ 2 := by
        calc
          |z| ^ 3 = |z| * |z| ^ 2 := by ring
          _ ≤ Rcut * |z| ^ 2 :=
            mul_le_mul_of_nonneg_right hzR (sq_nonneg |z|)
          _ = Rcut * z ^ 2 := by rw [sq_abs]
      calc
        ‖MartingaleArrayCLT.thirdOrderRemainder θ z‖ ≤
            (2 / 9 : ℝ) * |θ * z| ^ 3 :=
          MartingaleArrayCLT.norm_thirdOrderRemainder_le θ z hphase
        _ = (2 / 9 : ℝ) * |θ| ^ 3 * |z| ^ 3 := by
          rw [abs_mul, mul_pow]
          ring
        _ ≤ (2 / 9 : ℝ) * |θ| ^ 3 * (Rcut * z ^ 2) := by
          have hcoef : 0 ≤ (2 / 9 : ℝ) * |θ| ^ 3 := by positivity
          exact mul_le_mul_of_nonneg_left hcub hcoef
        _ = (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * z ^ 2 := by ring
        _ ≤ (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * z ^ 2 +
              (4 * θ ^ 2 / Rcut ^ 2) * z ^ 4 :=
          le_add_of_nonneg_right (mul_nonneg hB hz4)
    · have hRz : Rcut ≤ |z| := le_of_not_ge hzR
      have hsqabs : Rcut ^ 2 ≤ |z| ^ 2 := by
        simpa [pow_two] using mul_self_le_mul_self hR.le hRz
      have hsq : Rcut ^ 2 ≤ z ^ 2 := by simpa [sq_abs] using hsqabs
      have hR2 : 0 < Rcut ^ 2 := sq_pos_of_pos hR
      have hzdiv : z ^ 2 ≤ z ^ 4 / Rcut ^ 2 := by
        rw [le_div_iff₀ hR2]
        have hmul := mul_le_mul_of_nonneg_right hsq hz2
        nlinarith
      calc
        ‖MartingaleArrayCLT.thirdOrderRemainder θ z‖ ≤
            4 * |θ * z| ^ 2 :=
          norm_thirdOrderRemainder_le_four_mul_sq θ z
        _ = 4 * θ ^ 2 * z ^ 2 := by
          rw [abs_mul, mul_pow, sq_abs, sq_abs]
          ring
        _ ≤ (4 * θ ^ 2) * (z ^ 4 / Rcut ^ 2) := by
          exact mul_le_mul_of_nonneg_left hzdiv (by positivity)
        _ = (4 * θ ^ 2 / Rcut ^ 2) * z ^ 4 := by field_simp
        _ ≤ (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * z ^ 2 +
              (4 * θ ^ 2 / Rcut ^ 2) * z ^ 4 :=
          le_add_of_nonneg_left (mul_nonneg hA hz2)
  calc
    ‖L.centeredCharacteristic θ -
        (1 - (((θ ^ 2 / 2) * L.variance : ℝ) : ℂ))‖ ≤
      ∑ a, L.probability a *
        ‖MartingaleArrayCLT.thirdOrderRemainder θ (L.centeredValue a)‖ :=
          centeredCharacteristic_quadratic_error_le_remainder L θ
    _ ≤ ∑ a, L.probability a *
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut * L.centeredValue a ^ 2 +
          (4 * θ ^ 2 / Rcut ^ 2) * L.centeredValue a ^ 4) := by
            exact Finset.sum_le_sum fun a ha =>
              mul_le_mul_of_nonneg_left (hpoint a) (L.probability_nonneg a)
    _ = ∑ a,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
            (L.probability a * L.centeredValue a ^ 2) +
          (4 * θ ^ 2 / Rcut ^ 2) *
            (L.probability a * L.centeredValue a ^ 4)) := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = (2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
          (∑ a, L.probability a * L.centeredValue a ^ 2) +
        (4 * θ ^ 2 / Rcut ^ 2) *
          (∑ a, L.probability a * L.centeredValue a ^ 4) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * L.variance +
        (4 * θ ^ 2 / Rcut ^ 2) * L.centeredMoment 4 := by
          rw [show (∑ a, L.probability a * L.centeredValue a ^ 2) =
              L.variance by
            simpa [FiniteLatticeLaw.centeredMoment] using L.centeredMoment_two]
          rfl

/-- Uniform real-exponential remainder needed to replace the quadratic factors
by their Gaussian counterparts. -/
theorem norm_one_sub_sub_complex_exp_neg_le_sq (q : ℝ) (hq : 0 ≤ q) :
    ‖(((1 - q : ℝ) : ℂ) - Complex.exp (((-q : ℝ) : ℂ)))‖ ≤ q ^ 2 := by
  rw [← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  by_cases hq1 : q ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le (x := -q) (by
      rw [abs_neg, abs_of_nonneg hq]
      exact hq1)
    have heq : 1 - q - Real.exp (-q) =
        -(Real.exp (-q) - 1 - (-q)) := by ring
    rw [heq, abs_neg]
    simpa only [neg_sq] using h
  · have hLower := Real.one_sub_le_exp_neg q
    have hExpLe : Real.exp (-q) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [abs_of_nonpos (by linarith)]
    have hqOne : 1 ≤ q := le_of_not_ge hq1
    nlinarith [sq_nonneg (q - 1)]

/-- D.29--D.32 in finite-product form: a triangular array of independent
finite laws is compared directly with the Gaussian having the summed variance.
The error is explicit in the common truncation scale and the literal fourth
centered moments. -/
theorem centeredCharacteristic_product_gaussian_error_D29_D32
    {ι : Type*} [DecidableEq ι] {α : ι → Type*}
    [(i : ι) → Fintype (α i)]
    (s : Finset ι) (L : (i : ι) → FiniteLatticeLaw (α i))
    (θ Rcut : ℝ) (hR : 0 < Rcut) (hθR : |θ| * Rcut ≤ 1) :
    ‖(∏ i ∈ s, (L i).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ i ∈ s, (L i).variance) : ℝ) : ℂ))‖ ≤
      ∑ i ∈ s,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut * (L i).variance +
          (4 * θ ^ 2 / Rcut ^ 2) * (L i).centeredMoment 4 +
          (θ ^ 2 / 2 * (L i).variance) ^ 2) := by
  let q : ι → ℝ := fun i => θ ^ 2 / 2 * (L i).variance
  have hq : ∀ i, 0 ≤ q i := fun i =>
    mul_nonneg (by positivity) (L i).variance_nonneg
  have ha : ∀ i ∈ s, ‖(L i).centeredCharacteristic θ‖ ≤ 1 := by
    intro i hi
    simpa [FiniteLatticeLaw.characteristicModulus] using
      (L i).characteristicModulus_le_one θ
  have hb : ∀ i ∈ s, ‖Complex.exp (((-q i : ℝ) : ℂ))‖ ≤ 1 := by
    intro i hi
    rw [Complex.norm_exp]
    simp only [Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hq i))
  have hone : ∀ i,
      ‖(L i).centeredCharacteristic θ -
          Complex.exp (((-q i : ℝ) : ℂ))‖ ≤
        (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * (L i).variance +
          (4 * θ ^ 2 / Rcut ^ 2) * (L i).centeredMoment 4 +
          (q i) ^ 2 := by
    intro i
    calc
      ‖(L i).centeredCharacteristic θ -
          Complex.exp (((-q i : ℝ) : ℂ))‖ =
        ‖((L i).centeredCharacteristic θ - (((1 - q i : ℝ) : ℂ))) +
          ((((1 - q i : ℝ) : ℂ)) -
            Complex.exp (((-q i : ℝ) : ℂ)))‖ := by congr 1 <;> ring
      _ ≤ ‖(L i).centeredCharacteristic θ - (((1 - q i : ℝ) : ℂ))‖ +
          ‖(((1 - q i : ℝ) : ℂ)) -
            Complex.exp (((-q i : ℝ) : ℂ))‖ := norm_add_le _ _
      _ ≤ ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut * (L i).variance +
          (4 * θ ^ 2 / Rcut ^ 2) * (L i).centeredMoment 4) +
          (q i) ^ 2 := add_le_add
            (by
              simpa [q] using
                (centeredCharacteristic_quadratic_error_le_fourth
                  (L i) θ Rcut hR hθR))
            (norm_one_sub_sub_complex_exp_neg_le_sq (q i) (hq i))
      _ = (2 / 9 : ℝ) * |θ| ^ 3 * Rcut * (L i).variance +
          (4 * θ ^ 2 / Rcut ^ 2) * (L i).centeredMoment 4 +
          (q i) ^ 2 := by ring
  have hprod := norm_prod_sub_prod_le_sum_norm_sub s
    (fun i => (L i).centeredCharacteristic θ)
    (fun i => Complex.exp (((-q i : ℝ) : ℂ))) ha hb
  have hexp :
      (∏ i ∈ s, Complex.exp (((-q i : ℝ) : ℂ))) =
        Complex.exp (((-(θ ^ 2 / 2 * ∑ i ∈ s, (L i).variance) : ℝ) : ℂ)) := by
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [q]
    rw [Finset.sum_neg_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [hexp] at hprod
  simpa [q] using hprod.trans (Finset.sum_le_sum fun i hi => hone i)

/-- Two ancestors of one vertex in an actually rooted forest are comparable.
This is the rooted-forest combinatorial fact behind disjointness of antichain
subtrees in (D.14). -/
theorem isDescendant_comparable_of_common_descendant
    (hG : G.IsAcyclic) (R : ComponentRooting G) {u v x : V}
    (hux : R.IsDescendant (G := G) u x)
    (hvx : R.IsDescendant (G := G) v x) :
    R.IsDescendant (G := G) u v ∨ R.IsDescendant (G := G) v u := by
  let r : V → V → Prop := fun a b => R.IsChild (G := G) b a
  have hr : Relator.RightUnique r := by
    intro a b c hab hac
    exact R.isChild_unique (G := G) hG hab hac
  have hxu : Relation.ReflTransGen r x u := by
    simpa [r, Function.swap] using hux.swap
  have hxv : Relation.ReflTransGen r x v := by
    simpa [r, Function.swap] using hvx.swap
  rcases Relation.ReflTransGen.total_of_right_unique hr hxu hxv with huv | hvu
  · right
    simpa [r, Function.swap, IsDescendant] using huv.swap
  · left
    simpa [r, Function.swap, IsDescendant] using hvu.swap

/-- A rooted antichain is a finite set containing no two distinct vertices
that are comparable in the actual descendant order. -/
def IsRootedAntichain (R : ComponentRooting G) (A : Finset V) : Prop :=
  (↑A : Set V).Pairwise fun u v =>
    ¬ R.IsDescendant (G := G) u v ∧ ¬ R.IsDescendant (G := G) v u

/-- Descendant subtrees rooted at a rooted antichain are pairwise disjoint. -/
theorem rootedAntichain_pairwiseDisjoint_descendants
    (hG : G.IsAcyclic) (R : ComponentRooting G) {A : Finset V}
    (hA : R.IsRootedAntichain (G := G) A) :
    (↑A : Set V).PairwiseDisjoint (fun u => R.descendants (G := G) u) := by
  intro u hu v hv huv
  change Disjoint (R.descendants (G := G) u) (R.descendants (G := G) v)
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hc := R.isDescendant_comparable_of_common_descendant (G := G) hG
    ((R.mem_descendants (G := G) u x).mp hxu)
    ((R.mem_descendants (G := G) v x).mp hxv)
  have hnc := hA hu hv huv
  exact hc.elim hnc.1 hnc.2

/-- Appendix D equation (D.14): the actual subtree variance masses over any
rooted antichain sum to at most the variance of the original canonical state. -/
theorem sum_subtreeVarianceMass_le_variance_of_rootedAntichain
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (hA : R.IsRootedAntichain (G := G) A) :
    (∑ u ∈ A, R.subtreeVarianceMass (G := G) C u) ≤ C.variance := by
  classical
  have hdisj := R.rootedAntichain_pairwiseDisjoint_descendants
    (G := G) C.isForest hA
  calc
    (∑ u ∈ A, R.subtreeVarianceMass (G := G) C u) =
        ∑ u ∈ A, ∑ x ∈ R.descendants (G := G) u,
          R.vertexVarianceContribution (G := G) C x := by
      apply Finset.sum_congr rfl
      intro u hu
      exact R.subtreeVarianceMass_eq_sum_descendants (G := G) C u
    _ = ∑ x ∈ A.biUnion (fun u => R.descendants (G := G) u),
          R.vertexVarianceContribution (G := G) C x := by
      exact (Finset.sum_biUnion hdisj).symm
    _ ≤ ∑ x, R.vertexVarianceContribution (G := G) C x := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun x _ _ => R.vertexVarianceContribution_nonneg (G := G) C x)
    _ = C.variance := R.sum_vertexVarianceContribution_eq_variance (G := G) C

/-- The second inequality in (D.11): the actual forced-vacant subtree
variance is at most `784 E(u)`. -/
theorem vacantVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (u : V) :
    R.vacantVariance (G := G) C u ≤
      784 * R.subtreeVarianceMass (G := G) C u := by
  let p := R.occupationProbability (G := G) C u
  let q := R.vacancyProbability (G := G) C u
  let vP := R.subtreeVariance (G := G) C u
  let vQ := R.vacantVariance (G := G) C u
  let vR := R.occupiedVariance (G := G) C u
  let d := R.conditionalMeanDifference (G := G) C u
  have hq : (1 : ℝ) / 28 < q :=
    R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz u
  have hp0 : 0 ≤ p := R.occupationProbability_nonneg (G := G) C u
  have hvQ0 : 0 ≤ vQ := by
    dsimp [vQ, vacantVariance]
    exact FiniteLatticeLaw.variance_nonneg _
  have hvR0 : 0 ≤ vR := by
    dsimp [vR, occupiedVariance]
    exact FiniteLatticeLaw.variance_nonneg _
  have hd0 : 0 ≤ d ^ 2 := sq_nonneg _
  have hmix := R.subtreeVariance_law_total_variance (G := G) C u
  change vP = q * vQ + p * vR + p * q * d ^ 2 at hmix
  have hqv : q * vQ ≤ vP := by
    rw [hmix]
    nlinarith [mul_nonneg hp0 hvR0,
      mul_nonneg (mul_nonneg hp0 (le_trans (by norm_num) hq.le)) hd0]
  have hQle : vQ ≤ 28 * vP := by
    nlinarith
  have hPle := R.subtreeVariance_le_twentyEight_mul_subtreeVarianceMass
    (G := G) C hz u
  change vP ≤ 28 * R.subtreeVarianceMass (G := G) C u at hPle
  nlinarith [R.subtreeVarianceMass_nonneg (G := G) C u]

/-- Descendant sets are nested along the rooted descendant order. -/
theorem descendants_subset_of_isDescendant
    (R : ComponentRooting G) {u v : V}
    (huv : R.IsDescendant (G := G) u v) :
    R.descendants (G := G) v ⊆ R.descendants (G := G) u := by
  intro x hx
  rw [R.mem_descendants (G := G)] at hx ⊢
  exact Relation.ReflTransGen.trans huv hx

/-- The contextual subtree variance mass is nonincreasing down every actual
rooted descendant path. -/
theorem subtreeVarianceMass_le_of_isDescendant
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) {u v : V}
    (huv : R.IsDescendant (G := G) u v) :
    R.subtreeVarianceMass (G := G) C v ≤
      R.subtreeVarianceMass (G := G) C u := by
  rw [R.subtreeVarianceMass_eq_sum_descendants (G := G) C v,
    R.subtreeVarianceMass_eq_sum_descendants (G := G) C u]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (R.descendants_subset_of_isDescendant (G := G) huv)
    (fun x _ _ => R.vertexVarianceContribution_nonneg (G := G) C x)

/-- The retained high-subtree-mass set `S(α)` from (D.41). -/
noncomputable def retainedVarianceSet
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (alpha : ℝ) : Finset V :=
  Finset.univ.filter fun u =>
    alpha * C.variance ≤ R.subtreeVarianceMass (G := G) C u

@[simp] theorem mem_retainedVarianceSet
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (alpha : ℝ) (u : V) :
    u ∈ R.retainedVarianceSet (G := G) C alpha ↔
      alpha * C.variance ≤ R.subtreeVarianceMass (G := G) C u := by
  classical
  simp [retainedVarianceSet]

/-- The actual retained high-mass set is ancestor-closed, exactly as used in
D.5 and in the martingale projection. -/
theorem retainedVarianceSet_ancestorClosed
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (alpha : ℝ) :
    ActualMartingaleProjection.AncestorClosed R
      (R.retainedVarianceSet (G := G) C alpha) := by
  intro u v hv huv
  rw [R.mem_retainedVarianceSet (G := G)] at hv ⊢
  exact hv.trans (R.subtreeVarianceMass_le_of_isDescendant (G := G) C huv)

/-- Maximal vertices of a retained rooted subforest, i.e. its rooted leaves.
This order-theoretic definition avoids assigning any separate law to the
retained set. -/
noncomputable def rootedLeaves
    (R : ComponentRooting G) (D : Finset V) : Finset V := by
  classical
  exact D.filter fun u => ∀ v ∈ D,
    R.IsDescendant (G := G) u v → v = u

@[simp] theorem mem_rootedLeaves
    (R : ComponentRooting G) (D : Finset V) (u : V) :
    u ∈ R.rootedLeaves (G := G) D ↔
      u ∈ D ∧ ∀ v ∈ D, R.IsDescendant (G := G) u v → v = u := by
  classical
  simp [rootedLeaves]

/-- Rooted leaves are an antichain in the actual componentwise descendant
order. -/
theorem rootedLeaves_isRootedAntichain
    (R : ComponentRooting G) (D : Finset V) :
    R.IsRootedAntichain (G := G) (R.rootedLeaves (G := G) D) := by
  intro u hu v hv huv
  change u ∈ R.rootedLeaves (G := G) D at hu
  change v ∈ R.rootedLeaves (G := G) D at hv
  rw [R.mem_rootedLeaves (G := G)] at hu hv
  constructor
  · intro huvdesc
    exact huv (hu.2 v hv.1 huvdesc).symm
  · intro hvudesc
    exact huv (hv.2 u hu.1 hvudesc)

/-- Appendix D equation (D.45): `S(alpha)` has at most `1/alpha` rooted
leaves.  Cardinality is cast to `ℝ`, which is the form needed for the later
uniform leaf bound. -/
theorem rootedLeaves_card_le_one_div_alpha
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (alpha : ℝ) (halpha : 0 < alpha) :
    ((R.rootedLeaves (G := G)
      (R.retainedVarianceSet (G := G) C alpha)).card : ℝ) ≤ 1 / alpha := by
  let L := R.rootedLeaves (G := G)
      (R.retainedVarianceSet (G := G) C alpha)
  have hanti : R.IsRootedAntichain (G := G) L :=
    R.rootedLeaves_isRootedAntichain (G := G)
      (R.retainedVarianceSet (G := G) C alpha)
  have hsum := R.sum_subtreeVarianceMass_le_variance_of_rootedAntichain
    (G := G) C L hanti
  have hlower : (L.card : ℝ) * (alpha * C.variance) ≤
      ∑ u ∈ L, R.subtreeVarianceMass (G := G) C u := by
    calc
      (L.card : ℝ) * (alpha * C.variance) =
          ∑ u ∈ L, alpha * C.variance := by simp
      _ ≤ ∑ u ∈ L, R.subtreeVarianceMass (G := G) C u := by
        apply Finset.sum_le_sum
        intro u hu
        have huD := (R.mem_rootedLeaves (G := G)
          (R.retainedVarianceSet (G := G) C alpha) u).mp hu |>.1
        exact (R.mem_retainedVarianceSet (G := G) C alpha u).mp huD
  have hV := canonicalFirstRecovery_variance_pos C
  apply (le_div_iff₀ halpha).2
  have hprod : ((L.card : ℝ) * alpha) * C.variance ≤ 1 * C.variance := by
    rw [one_mul]
    calc
      ((L.card : ℝ) * alpha) * C.variance =
          (L.card : ℝ) * (alpha * C.variance) := by ring
      _ ≤ ∑ u ∈ L, R.subtreeVarianceMass (G := G) C u := hlower
      _ ≤ C.variance := hsum
  exact le_of_mul_le_mul_right hprod hV

/-- `m`, the maximum actual vertex variance contribution.  The empty-vertex
branch is included only to make the definition total; canonical first-recovery
states have positive variance and hence use the genuine nonempty maximum. -/
noncomputable def maxVertexVarianceContribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) : ℝ := by
  classical
  exact if h : (Finset.univ : Finset V).Nonempty then
    (Finset.univ.image fun u =>
      R.vertexVarianceContribution (G := G) C u).max' (h.image _)
  else 0

/-- Every actual contribution is bounded by its finite maximum. -/
theorem vertexVarianceContribution_le_max
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vertexVarianceContribution (G := G) C u ≤
      R.maxVertexVarianceContribution (G := G) C := by
  classical
  have hne : (Finset.univ : Finset V).Nonempty := ⟨u, Finset.mem_univ u⟩
  rw [maxVertexVarianceContribution, dif_pos hne]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨u, Finset.mem_univ u, rfl⟩)

/-- The genuine maximum contribution is strictly positive for every canonical
first-recovery state. -/
theorem maxVertexVarianceContribution_pos
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    0 < R.maxVertexVarianceContribution (G := G) C := by
  classical
  have hsum : 0 < ∑ u, R.vertexVarianceContribution (G := G) C u := by
    rw [R.sum_vertexVarianceContribution_eq_variance (G := G) C]
    exact canonicalFirstRecovery_variance_pos C
  obtain ⟨u, hu, hupos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := (Finset.univ : Finset V))
      (fun v _ => R.vertexVarianceContribution_nonneg (G := G) C v)).mp hsum
  exact hupos.trans_le (R.vertexVarianceContribution_le_max (G := G) C u)

/-- The exposed boundary `∂⁺D` from (D.20), including roots of original
components disjoint from `D`. -/
noncomputable def exposedBoundary
    (R : ComponentRooting G) (D : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun u =>
    u ∉ D ∧ (u = R.rootOf (G := G) u ∨
      ∃ p ∈ D, R.IsChild (G := G) p u)

@[simp] theorem mem_exposedBoundary
    (R : ComponentRooting G) (D : Finset V) (u : V) :
    u ∈ R.exposedBoundary (G := G) D ↔
      u ∉ D ∧ (u = R.rootOf (G := G) u ∨
        ∃ p ∈ D, R.IsChild (G := G) p u) := by
  classical
  simp [exposedBoundary]

/-- An ancestor outside an ancestor-closed set of one of its exposed boundary
vertices is that boundary vertex itself. -/
theorem eq_of_isDescendant_of_mem_exposedBoundary
    (hG : G.IsAcyclic) (R : ComponentRooting G) {D : Finset V}
    (hD : ActualMartingaleProjection.AncestorClosed R D)
    {u v : V} (hu : u ∉ D) (hv : v ∈ R.exposedBoundary (G := G) D)
    (huv : R.IsDescendant (G := G) u v) : u = v := by
  rcases (R.mem_exposedBoundary (G := G) D v).mp hv with ⟨hvD, hvroot | hvparent⟩
  · have hdv : R.depth (G := G) v = 0 := by
      rw [hvroot]
      exact R.depth_rootOf (G := G) v
    have hle := R.depth_le_of_isDescendant (G := G) huv
    have hdeq : R.depth (G := G) u = R.depth (G := G) v := by omega
    exact R.eq_of_isDescendant_of_depth_eq (G := G) huv hdeq
  · obtain ⟨p, hpD, hpv⟩ := hvparent
    by_contra huvne
    have hult := R.depth_lt_of_isDescendant_of_ne (G := G) huv huvne
    have hpdepth := R.depth_child (G := G) hpv
    have hule : R.depth (G := G) u ≤ R.depth (G := G) p := by omega
    have hcomp := R.isDescendant_comparable_of_common_descendant (G := G) hG
      huv (Relation.ReflTransGen.single hpv)
    rcases hcomp with hup | hpu
    · exact hu (hD hpD hup)
    · have hple := R.depth_le_of_isDescendant (G := G) hpu
      have heqDepth : R.depth (G := G) p = R.depth (G := G) u := by omega
      have hpuEq := R.eq_of_isDescendant_of_depth_eq (G := G) hpu heqDepth
      exact hu (hpuEq ▸ hpD)

/-- The exposed boundary of an ancestor-closed set is a rooted antichain. -/
theorem exposedBoundary_isRootedAntichain
    (hG : G.IsAcyclic) (R : ComponentRooting G) {D : Finset V}
    (hD : ActualMartingaleProjection.AncestorClosed R D) :
    R.IsRootedAntichain (G := G) (R.exposedBoundary (G := G) D) := by
  intro u hu v hv huv
  have huD := (R.mem_exposedBoundary (G := G) D u).mp hu |>.1
  have hvD := (R.mem_exposedBoundary (G := G) D v).mp hv |>.1
  constructor
  · intro hdesc
    exact huv (R.eq_of_isDescendant_of_mem_exposedBoundary
      (G := G) hG hD huD hv hdesc)
  · intro hdesc
    exact huv (R.eq_of_isDescendant_of_mem_exposedBoundary
      (G := G) hG hD hvD hu hdesc).symm

/-- Union of the genuine rooted descendant subtrees below a rooted antichain. -/
noncomputable def antichainDescendantUnion
    (R : ComponentRooting G) (A : Finset V) : Finset V := by
  classical
  exact A.biUnion (fun u => R.descendants (G := G) u)

/-- The vertices observed when all descendant subtrees below `A` are left
unrevealed. -/
noncomputable def antichainObservedSet
    (R : ComponentRooting G) (A : Finset V) : Finset V := by
  classical
  exact Finset.univ \ R.antichainDescendantUnion (G := G) A

@[simp] theorem mem_antichainDescendantUnion
    (R : ComponentRooting G) (A : Finset V) (x : V) :
    x ∈ R.antichainDescendantUnion (G := G) A ↔
      ∃ u ∈ A, R.IsDescendant (G := G) u x := by
  classical
  simp [antichainDescendantUnion, R.mem_descendants (G := G)]

@[simp] theorem mem_antichainObservedSet
    (R : ComponentRooting G) (A : Finset V) (x : V) :
    x ∈ R.antichainObservedSet (G := G) A ↔
      x ∉ R.antichainDescendantUnion (G := G) A := by
  classical
  simp [antichainObservedSet]

/-- The complement of a union of rooted descendant subtrees is
ancestor-closed. -/
theorem antichainObservedSet_ancestorClosed
    (R : ComponentRooting G) (A : Finset V) :
    ActualMartingaleProjection.AncestorClosed R
      (R.antichainObservedSet (G := G) A) := by
  intro u v hv huv
  rw [R.mem_antichainObservedSet (G := G)] at hv ⊢
  intro huUnion
  rw [R.mem_antichainDescendantUnion (G := G)] at huUnion
  obtain ⟨a, haA, hau⟩ := huUnion
  apply hv
  rw [R.mem_antichainDescendantUnion (G := G)]
  exact ⟨a, haA, Relation.ReflTransGen.trans hau huv⟩

/-- Revealing the complement of the descendant subtrees below a rooted
antichain exposes exactly that antichain. -/
theorem exposedBoundary_antichainObservedSet
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (hA : R.IsRootedAntichain (G := G) A) :
    R.exposedBoundary (G := G) (R.antichainObservedSet (G := G) A) = A := by
  classical
  let D := R.antichainObservedSet (G := G) A
  have hD : ActualMartingaleProjection.AncestorClosed R D :=
    R.antichainObservedSet_ancestorClosed (G := G) A
  ext u
  constructor
  · intro huB
    have huOut : u ∉ D := (R.mem_exposedBoundary (G := G) D u).mp huB |>.1
    have huUnion : u ∈ R.antichainDescendantUnion (G := G) A := by
      simpa [D] using huOut
    obtain ⟨a, haA, hau⟩ :=
      (R.mem_antichainDescendantUnion (G := G) A u).mp huUnion
    have haOut : a ∉ D := by
      intro haD
      have haNotUnion : a ∉ R.antichainDescendantUnion (G := G) A := by
        exact (R.mem_antichainObservedSet (G := G) A a).mp (by simpa [D] using haD)
      exact haNotUnion ((R.mem_antichainDescendantUnion (G := G) A a).mpr
        ⟨a, haA, Relation.ReflTransGen.refl⟩)
    have hauEq := R.eq_of_isDescendant_of_mem_exposedBoundary
      (G := G) C.isForest hD haOut huB hau
    exact hauEq ▸ haA
  · intro huA
    rw [R.mem_exposedBoundary (G := G) D]
    have huOut : u ∉ D := by
      intro huD
      have huNotUnion : u ∉ R.antichainDescendantUnion (G := G) A := by
        exact (R.mem_antichainObservedSet (G := G) A u).mp (by simpa [D] using huD)
      exact huNotUnion ((R.mem_antichainDescendantUnion (G := G) A u).mpr
        ⟨u, huA, Relation.ReflTransGen.refl⟩)
    refine ⟨huOut, ?_⟩
    by_cases hroot : u = R.rootOf (G := G) u
    · exact Or.inl hroot
    · right
      let p := R.selectedParent (G := G) u hroot
      have hpu : R.IsChild (G := G) p u :=
        R.selectedParent_isChild (G := G) u hroot
      refine ⟨p, ?_, hpu⟩
      rw [show D = R.antichainObservedSet (G := G) A from rfl,
        R.mem_antichainObservedSet (G := G)]
      intro hpUnion
      obtain ⟨a, haA, hap⟩ :=
        (R.mem_antichainDescendantUnion (G := G) A p).mp hpUnion
      have hau : R.IsDescendant (G := G) a u :=
        Relation.ReflTransGen.trans hap (Relation.ReflTransGen.single hpu)
      by_cases hauEq : a = u
      · subst a
        have hle := R.depth_le_of_isDescendant (G := G) hap
        have hdepth := R.depth_child (G := G) hpu
        omega
      · exact (hA haA huA hauEq).1 hau

/-- Every vertex outside an ancestor-closed set lies below a unique exposed
boundary root; this existence statement is proved by induction on actual root
depth. -/
theorem exists_exposedBoundary_ancestor
    (R : ComponentRooting G) {D : Finset V}
    (hD : ActualMartingaleProjection.AncestorClosed R D)
    {x : V} (hxD : x ∉ D) :
    ∃ u ∈ R.exposedBoundary (G := G) D,
      R.IsDescendant (G := G) u x := by
  classical
  generalize hn : R.depth (G := G) x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      by_cases hxroot : x = R.rootOf (G := G) x
      · exact ⟨x, (R.mem_exposedBoundary (G := G) D x).mpr
          ⟨hxD, Or.inl hxroot⟩, Relation.ReflTransGen.refl⟩
      · let p := R.selectedParent (G := G) x hxroot
        have hpx : R.IsChild (G := G) p x :=
          R.selectedParent_isChild (G := G) x hxroot
        by_cases hpD : p ∈ D
        · exact ⟨x, (R.mem_exposedBoundary (G := G) D x).mpr
            ⟨hxD, Or.inr ⟨p, hpD, hpx⟩⟩, Relation.ReflTransGen.refl⟩
        · have hpdepth := R.depth_child (G := G) hpx
          obtain ⟨u, huBoundary, hup⟩ :=
            ih (R.depth (G := G) p) (by omega) hpD rfl
          exact ⟨u, huBoundary,
            Relation.ReflTransGen.trans hup (Relation.ReflTransGen.single hpx)⟩

/-- The finite complement of a retained set, with its classical decidable
equality hidden behind a named definition. -/
noncomputable def outsideSet (D : Finset V) : Finset V := by
  classical
  exact Finset.univ \ D

@[simp] theorem mem_outsideSet (D : Finset V) (x : V) :
    x ∈ outsideSet D ↔ x ∉ D := by
  classical
  simp [outsideSet]

/-- Union of all actual descendant subtrees rooted on the exposed boundary. -/
noncomputable def exposedDescendantUnion
    (R : ComponentRooting G) (D : Finset V) : Finset V := by
  classical
  exact (R.exposedBoundary (G := G) D).biUnion
    (fun u => R.descendants (G := G) u)

/-- The descendant subtrees of the exposed boundary partition exactly the
complement of an ancestor-closed set. -/
theorem exposedBoundary_biUnion_descendants
    (R : ComponentRooting G) {D : Finset V}
    (hD : ActualMartingaleProjection.AncestorClosed R D) :
    R.exposedDescendantUnion (G := G) D = outsideSet D := by
  classical
  unfold exposedDescendantUnion
  ext x
  constructor
  · intro hx
    rw [mem_outsideSet]
    rw [Finset.mem_biUnion] at hx
    obtain ⟨u, huBoundary, hux⟩ := hx
    intro hxD
    have huD := hD hxD ((R.mem_descendants (G := G) u x).mp hux)
    exact (R.mem_exposedBoundary (G := G) D u).mp huBoundary |>.1 huD
  · intro hx
    rw [mem_outsideSet] at hx
    obtain ⟨u, huBoundary, hux⟩ := R.exists_exposedBoundary_ancestor hD hx
    rw [Finset.mem_biUnion]
    exact ⟨u, huBoundary, (R.mem_descendants (G := G) u x).mpr hux⟩

/-- The actual unobserved block below an exposed root: the full descendant
tree when its observed parent is vacant, and the root-deleted tree when that
parent is occupied.  This definition carries only the original configuration
and rooting; it assigns no canonicity to the block. -/
noncomputable def exposedAllowedPiece
    (R : ComponentRooting G) (I : IndepFinset G) (u : V) : Finset V := by
  classical
  exact if ActualMartingaleProjection.parentOccupationIndicator R I u = 0 then
    R.descendants (G := G) u else R.properDescendants (G := G) u

/-- Union of the configuration-dependent blocks below the exposed boundary. -/
noncomputable def exposedAllowedUnion
    (R : ComponentRooting G) (D : Finset V) (I : IndepFinset G) : Finset V := by
  classical
  exact (R.exposedBoundary (G := G) D).biUnion
    (fun u => R.exposedAllowedPiece (G := G) I u)

/-- Exact D.25 support decomposition of the conditional outside graph.  Every
block remains at the original global activity through `AllowedOutsideGraph`;
this statement does not transfer canonicity or first recovery to any block. -/
theorem allowedOutsideVertices_eq_exposedAllowedUnion_D25
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    ActualMartingaleProjection.allowedOutsideVertices D I =
      R.exposedAllowedUnion (G := G) D I := by
  classical
  ext x
  rw [ActualMartingaleProjection.mem_allowedOutsideVertices]
  constructor
  · intro hx
    obtain ⟨u, huBoundary, hux⟩ :=
      R.exists_exposedBoundary_ancestor (G := G) hD hx.1
    rw [exposedAllowedUnion, Finset.mem_biUnion]
    refine ⟨u, huBoundary, ?_⟩
    unfold exposedAllowedPiece
    split_ifs with hzero
    · exact (R.mem_descendants (G := G) u x).mpr hux
    · rw [properDescendants, Finset.mem_erase]
      refine ⟨?_, (R.mem_descendants (G := G) u x).mpr hux⟩
      intro hxu
      subst x
      rcases (R.mem_exposedBoundary (G := G) D u).mp huBoundary with
        ⟨huD, hroot | ⟨p, hpD, hpu⟩⟩
      · exact hzero (ActualMartingaleProjection.parentOccupationIndicator_root
          R I hroot)
      · have huroot : u ≠ R.rootOf (G := G) u := by
          intro hur
          exact (R.not_isChild_of_eq_root (G := G) hur hpu).elim
        by_cases hpI : p ∈ I.val
        · have hpRestriction : p ∈ ActualMartingaleProjection.restriction D I :=
            Finset.mem_inter.mpr ⟨hpI, hpD⟩
          exact (hx.2 p hpRestriction) hpu.1.symm
        · apply hzero
          rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent
              C R I huroot,
            R.selectedParent_eq_of_isChild (G := G) C hpu huroot]
          simp [ActualMartingaleProjection.occupationIndicator, hpI]
  · intro hx
    rw [exposedAllowedUnion, Finset.mem_biUnion] at hx
    obtain ⟨u, huBoundary, hux⟩ := hx
    have huD : u ∉ D :=
      (R.mem_exposedBoundary (G := G) D u).mp huBoundary |>.1
    have hdescDisjoint :=
      ActualMartingaleProjection.descendants_disjoint_of_ancestorClosed
        (G := G) R hD huD
    unfold exposedAllowedPiece at hux
    split_ifs at hux with hzero
    · have huxDesc : x ∈ R.descendants (G := G) u := hux
      refine ⟨?_, ?_⟩
      · intro hxD
        exact (Finset.disjoint_left.mp hdescDisjoint huxDesc hxD)
      · intro y hyRestriction
        have hyI : y ∈ I.val := (Finset.mem_inter.mp hyRestriction).1
        have hyD : y ∈ D := (Finset.mem_inter.mp hyRestriction).2
        have hyOutside : y ∉ R.descendants (G := G) u := by
          intro hyDesc
          exact Finset.disjoint_left.mp hdescDisjoint hyDesc hyD
        refine ActualMartingaleProjection.not_adj_descendant_of_restriction_eq_of_parent_absent
          C R D ?_ I I rfl hzero huxDesc hyI hyOutside
        intro p hpu
        rcases (R.mem_exposedBoundary (G := G) D u).mp huBoundary |>.2 with
          hroot | ⟨q, hqD, hqu⟩
        · exact (R.not_isChild_of_eq_root (G := G) hroot hpu).elim
        · have hpq := R.isChild_unique (G := G) C.isForest hpu hqu
          exact hpq.symm ▸ hqD
    · have hproper := Finset.mem_erase.mp hux
      have huxDesc : x ∈ R.descendants (G := G) u := hproper.2
      refine ⟨?_, ?_⟩
      · intro hxD
        exact Finset.disjoint_left.mp hdescDisjoint huxDesc hxD
      · intro y hyRestriction hxy
        have hyD : y ∈ D := (Finset.mem_inter.mp hyRestriction).2
        have hyOutside : y ∉ R.descendants (G := G) u := by
          intro hyDesc
          exact Finset.disjoint_left.mp hdescDisjoint hyDesc hyD
        obtain ⟨p, hpu, hyp⟩ :=
          ActualMartingaleProjection.adj_descendant_complement_eq_parent
            C R huxDesc hyOutside hxy
        subst y
        rcases (R.adj_iff_isChild_or_reverse (G := G) C.isForest).mp hxy with
          hxp | hpx
        · have huxDepth := R.depth_le_of_isDescendant (G := G)
            ((R.mem_descendants (G := G) u x).mp huxDesc)
          have hpuDepth := R.depth_child (G := G) hpu
          have hxpDepth := R.depth_child (G := G) hxp
          omega
        · have huxRel := (R.mem_descendants (G := G) u x).mp huxDesc
          have hEq := R.child_eq_of_common_descendant (G := G) C.isForest
            hpu hpx huxRel Relation.ReflTransGen.refl
          exact hproper.1 hEq.symm

/-- Each exposed conditional block is contained in its original descendant
subtree. -/
theorem exposedAllowedPiece_subset_descendants
    (R : ComponentRooting G) (I : IndepFinset G) (u : V) :
    R.exposedAllowedPiece (G := G) I u ⊆ R.descendants (G := G) u := by
  classical
  intro x hx
  unfold exposedAllowedPiece at hx
  split_ifs at hx
  · exact hx
  · exact (Finset.mem_erase.mp hx).2

/-- Distinct rooted-antichain descendant subtrees have no crossing graph edge. -/
theorem rootedAntichain_noCrossEdges_descendants
    (hG : G.IsAcyclic) (R : ComponentRooting G) {A : Finset V}
    (hA : R.IsRootedAntichain (G := G) A) :
    ∀ i ∈ A, ∀ j ∈ A, i ≠ j →
      ∀ ⦃x y : V⦄, x ∈ R.descendants (G := G) i →
        y ∈ R.descendants (G := G) j → ¬ G.Adj x y := by
  intro i hi j hj hij x y hix hjy hxy
  have hixRel := (R.mem_descendants (G := G) i x).mp hix
  have hjyRel := (R.mem_descendants (G := G) j y).mp hjy
  have hanti := hA hi hj hij
  rcases (R.adj_iff_isChild_or_reverse (G := G) hG).mp hxy with
    hxyChild | hyxChild
  · have hiyRel := Relation.ReflTransGen.trans hixRel
      (Relation.ReflTransGen.single hxyChild)
    exact (R.isDescendant_comparable_of_common_descendant (G := G) hG
      hiyRel hjyRel).elim hanti.1 hanti.2
  · have hjxRel := Relation.ReflTransGen.trans hjyRel
      (Relation.ReflTransGen.single hyxChild)
    exact (R.isDescendant_comparable_of_common_descendant (G := G) hG
      hixRel hjxRel).elim hanti.1 hanti.2

/-- The configuration-dependent exposed blocks are pairwise disjoint. -/
theorem exposedAllowedPiece_pairwiseDisjoint
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    (↑(R.exposedBoundary (G := G) D) : Set V).PairwiseDisjoint
      (fun u => R.exposedAllowedPiece (G := G) I u) := by
  intro u hu v hv huv
  change Disjoint (R.exposedAllowedPiece (G := G) I u)
    (R.exposedAllowedPiece (G := G) I v)
  rw [Finset.disjoint_left]
  intro x hxu hxv
  have hA := R.exposedBoundary_isRootedAntichain (G := G) C.isForest hD
  have hdisj := R.rootedAntichain_pairwiseDisjoint_descendants
    (G := G) C.isForest hA hu hv huv
  exact Finset.disjoint_left.mp hdisj
    (R.exposedAllowedPiece_subset_descendants (G := G) I u hxu)
    (R.exposedAllowedPiece_subset_descendants (G := G) I v hxv)

/-- Distinct configuration-dependent exposed blocks have no crossing edge. -/
theorem exposedAllowedPiece_noCrossEdges
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    ∀ u ∈ R.exposedBoundary (G := G) D,
      ∀ v ∈ R.exposedBoundary (G := G) D, u ≠ v →
        ∀ ⦃x y : V⦄, x ∈ R.exposedAllowedPiece (G := G) I u →
          y ∈ R.exposedAllowedPiece (G := G) I v → ¬ G.Adj x y := by
  have hA := R.exposedBoundary_isRootedAntichain (G := G) C.isForest hD
  intro u hu v hv huv x y hxu hxv
  exact R.rootedAntichain_noCrossEdges_descendants (G := G) C.isForest hA
    u hu v hv huv
    (R.exposedAllowedPiece_subset_descendants (G := G) I u hxu)
    (R.exposedAllowedPiece_subset_descendants (G := G) I v hxv)

/-- Exact D.25 characteristic-function product for the conditional outside
hard-core law.  All factors use `C.activity`; none is declared canonical. -/
theorem allowedOutside_characteristic_eq_prod_exposedAllowedPiece_D25
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) (theta : ℝ) :
    (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
      C.activity C.activity_pos).characteristic theta =
      ∏ u ∈ R.exposedBoundary (G := G) D,
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).characteristic theta := by
  classical
  change (hardCoreLaw
      (G.induce {x | x ∈ ActualMartingaleProjection.allowedOutsideVertices D I})
      C.activity C.activity_pos).characteristic theta = _
  rw [R.allowedOutsideVertices_eq_exposedAllowedUnion_D25 (G := G) C hD I]
  unfold exposedAllowedUnion
  exact Forest.AppendixA.hardCoreLaw_characteristic_induceFinset_biUnion
    G (R.exposedBoundary (G := G) D)
      (fun u => R.exposedAllowedPiece (G := G) I u)
    (R.exposedAllowedPiece_pairwiseDisjoint (G := G) C hD I)
    (R.exposedAllowedPiece_noCrossEdges (G := G) C hD I)
    C.activity theta C.activity_pos

/-- Conditional variance of one exposed block, expressed only through the
inherited global-activity `P`/`Q` laws. -/
noncomputable def exposedConditionalVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) : ℝ :=
  if ActualMartingaleProjection.parentOccupationIndicator R I u = 0 then
    R.subtreeVariance (G := G) C u else R.vacantVariance (G := G) C u

/-- The induced exposed-piece law has exactly its inherited conditional
variance at the unchanged global activity. -/
theorem exposedAllowedPiece_variance_eq_exposedConditionalVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    (hardCoreLaw (G.induce
      {x | x ∈ R.exposedAllowedPiece (G := G) I u})
      C.activity C.activity_pos).variance =
      R.exposedConditionalVariance (G := G) C I u := by
  classical
  by_cases hzero :
      ActualMartingaleProjection.parentOccupationIndicator R I u = 0
  · have hpiece : R.exposedAllowedPiece (G := G) I u =
        R.descendants (G := G) u := by
      unfold exposedAllowedPiece
      rw [if_pos hzero]
    rw [hpiece]
    rw [exposedConditionalVariance, if_pos hzero]
    rfl
  · have hpiece : R.exposedAllowedPiece (G := G) I u =
        R.properDescendants (G := G) u := by
      unfold exposedAllowedPiece
      rw [if_neg hzero]
    rw [hpiece]
    simp only [exposedConditionalVariance, hzero, if_false]
    unfold vacantVariance
    exact (hardCoreLaw_variance_iso
      (R.deleteSubtreeRootIsoProperDescendants (G := G) u)
      C.activity C.activity_pos).symm

/-- Exact D.25 conditional-variance sum.  This is an identity for the actual
allowed outside law, not a canonicity assertion about that law or its blocks. -/
theorem allowedOutside_variance_eq_sum_exposedConditionalVariance_D25
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
      C.activity C.activity_pos).variance =
      ∑ u ∈ R.exposedBoundary (G := G) D,
        R.exposedConditionalVariance (G := G) C I u := by
  classical
  change (hardCoreLaw
      (G.induce {x | x ∈ ActualMartingaleProjection.allowedOutsideVertices D I})
      C.activity C.activity_pos).variance = _
  rw [R.allowedOutsideVertices_eq_exposedAllowedUnion_D25 (G := G) C hD I]
  unfold exposedAllowedUnion
  rw [hardCoreLaw_variance_induceFinset_biUnion G
    (R.exposedBoundary (G := G) D)
    (fun u => R.exposedAllowedPiece (G := G) I u)
    (R.exposedAllowedPiece_pairwiseDisjoint (G := G) C hD I)
    (fun i hi j hj hij x hx y hy =>
      R.exposedAllowedPiece_noCrossEdges (G := G) C hD I
        i hi j hj hij hx hy)
    C.activity C.activity_pos]
  apply Finset.sum_congr rfl
  intro u hu
  exact R.exposedAllowedPiece_variance_eq_exposedConditionalVariance
    (G := G) C I u

/-- Every conditional D.25 block variance is controlled by `784` times its
original contextual subtree variance mass. -/
theorem exposedConditionalVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (I : IndepFinset G) (u : V) :
    R.exposedConditionalVariance (G := G) C I u ≤
      784 * R.subtreeVarianceMass (G := G) C u := by
  classical
  unfold exposedConditionalVariance
  split_ifs
  · have hP := R.subtreeVariance_le_twentyEight_mul_subtreeVarianceMass
      (G := G) C hz u
    have hE := R.subtreeVarianceMass_nonneg (G := G) C u
    nlinarith
  · exact R.vacantVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
      (G := G) C hz u

/-- D.24 for every configuration-dependent exposed `P`/`Q` block.  The
fourth-moment theorem is applied to the induced forest at `C.activity`; no
canonical structure is put on that induced forest. -/
theorem exposedAllowedPiece_fourthMoment_le_D24
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (I : IndepFinset G) (u : V) :
    (∑ s : IndepFinset
        (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u}),
      (hardCoreLaw
        (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
        C.activity C.activity_pos).probability s *
      ((s.val.card : ℝ) -
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).mean) ^ 4) ≤
      UniformFourthMoment.C4 27 *
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).variance *
        (1 + (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).variance) := by
  exact UniformFourthMoment.uniformFourthMoment_A3_card
    (C.isForest.induce
      {x | x ∈ R.exposedAllowedPiece (G := G) I u})
    C.activity 27 (by norm_num) C.activity_pos hz.le

/-- The finite-product Gaussian approximation specialized to the genuine
configuration-dependent exposed hard-core blocks.  Every factor remains at
`C.activity`; this theorem does not assign any canonical or first-recovery
structure to an exposed piece. -/
theorem exposedCenteredCharacteristic_product_gaussian_error_D30
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V) (I : IndepFinset G)
    (θ Rcut : ℝ) (hR : 0 < Rcut) (hθR : |θ| * Rcut ≤ 1) :
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ u ∈ A,
          R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ ≤
      ∑ u ∈ A,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
            R.exposedConditionalVariance (G := G) C I u +
          (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27 *
            R.exposedConditionalVariance (G := G) C I u *
            (1 + R.exposedConditionalVariance (G := G) C I u) +
          (θ ^ 2 / 2 *
            R.exposedConditionalVariance (G := G) C I u) ^ 2) := by
  classical
  let α : V → Type u := fun u => IndepFinset
    (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
  let L : (u : V) → FiniteLatticeLaw (α u) := fun u =>
    hardCoreLaw
      (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
      C.activity C.activity_pos
  have hv : ∀ u, (L u).variance =
      R.exposedConditionalVariance (G := G) C I u := by
    intro u
    exact R.exposedAllowedPiece_variance_eq_exposedConditionalVariance
      (G := G) C I u
  have hm4 : ∀ u, (L u).centeredMoment 4 ≤
      UniformFourthMoment.C4 27 *
        R.exposedConditionalVariance (G := G) C I u *
        (1 + R.exposedConditionalVariance (G := G) C I u) := by
    intro u
    rw [← hv u]
    simpa only [L, α, FiniteLatticeLaw.centeredMoment] using
      R.exposedAllowedPiece_fourthMoment_le_D24 (G := G) C hz I u
  have hbase := centeredCharacteristic_product_gaussian_error_D29_D32
    A L θ Rcut hR hθR
  calc
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ u ∈ A,
          R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ =
      ‖(∏ u ∈ A, (L u).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ u ∈ A, (L u).variance) : ℝ) : ℂ))‖ := by
          simp only [L, hv]
    _ ≤ ∑ u ∈ A,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut * (L u).variance +
          (4 * θ ^ 2 / Rcut ^ 2) * (L u).centeredMoment 4 +
          (θ ^ 2 / 2 * (L u).variance) ^ 2) := hbase
    _ ≤ ∑ u ∈ A,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
            R.exposedConditionalVariance (G := G) C I u +
          (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27 *
            R.exposedConditionalVariance (G := G) C I u *
            (1 + R.exposedConditionalVariance (G := G) C I u) +
          (θ ^ 2 / 2 *
            R.exposedConditionalVariance (G := G) C I u) ^ 2) := by
          apply Finset.sum_le_sum
          intro u hu
          rw [hv u]
          have hcoef : 0 ≤ 4 * θ ^ 2 / Rcut ^ 2 := by positivity
          have hmul := mul_le_mul_of_nonneg_left (hm4 u) hcoef
          nlinarith

/-- Aggregate D.31--D.32 bound when every exposed conditional block variance is
at most `M`.  The estimate is pointwise in the revealed original configuration,
so it can later be averaged without changing the hard-core activity. -/
theorem exposedCenteredCharacteristic_product_gaussian_error_le_of_blockVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V) (I : IndepFinset G)
    (θ Rcut M : ℝ) (hR : 0 < Rcut) (hθR : |θ| * Rcut ≤ 1)
    (hblock : ∀ u ∈ A,
      R.exposedConditionalVariance (G := G) C I u ≤ M) :
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ u ∈ A,
          R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ ≤
      (2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
          (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) +
        (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27 *
          ((∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) +
            M * (∑ u ∈ A,
              R.exposedConditionalVariance (G := G) C I u)) +
        (θ ^ 2 / 2) ^ 2 * M *
          (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) := by
  let v : V → ℝ := fun u =>
    R.exposedConditionalVariance (G := G) C I u
  let a : ℝ := (2 / 9 : ℝ) * |θ| ^ 3 * Rcut
  let b : ℝ := (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27
  let q : ℝ := (θ ^ 2 / 2) ^ 2
  have hb : 0 ≤ b := mul_nonneg (by positivity)
    (UniformFourthMoment.C4_nonneg_of_nonneg (by norm_num))
  have hq : 0 ≤ q := sq_nonneg _
  have hvnonneg : ∀ u, 0 ≤ v u := by
    intro u
    rw [show v u = (hardCoreLaw
      (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
      C.activity C.activity_pos).variance by
        symm
        exact R.exposedAllowedPiece_variance_eq_exposedConditionalVariance
          (G := G) C I u]
    exact FiniteLatticeLaw.variance_nonneg _
  have hvsq : ∀ u ∈ A, (v u) ^ 2 ≤ M * v u := by
    intro u hu
    have hmul := mul_le_mul_of_nonneg_right (hblock u hu) (hvnonneg u)
    simpa [v, pow_two] using hmul
  have hpoint : ∀ u ∈ A,
      a * v u + b * (v u * (1 + v u)) +
          q * v u ^ 2 ≤
        a * v u + b * (v u + M * v u) + q * (M * v u) := by
    intro u hu
    have hmid : v u * (1 + v u) ≤ v u + M * v u := by
      nlinarith [hvsq u hu]
    exact add_le_add
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hmid hb))
      (mul_le_mul_of_nonneg_left (hvsq u hu) hq)
  have hbase := R.exposedCenteredCharacteristic_product_gaussian_error_D30
    (G := G) C hz A I θ Rcut hR hθR
  calc
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic θ) -
        Complex.exp (((-(θ ^ 2 / 2 * ∑ u ∈ A,
          R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ ≤
      ∑ u ∈ A,
        ((2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
            R.exposedConditionalVariance (G := G) C I u +
          (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27 *
            R.exposedConditionalVariance (G := G) C I u *
            (1 + R.exposedConditionalVariance (G := G) C I u) +
          (θ ^ 2 / 2 *
            R.exposedConditionalVariance (G := G) C I u) ^ 2) := hbase
    _ = ∑ u ∈ A,
        (a * v u + b * (v u * (1 + v u)) + q * v u ^ 2) := by
          apply Finset.sum_congr rfl
          intro u hu
          simp only [a, b, q, v]
          ring
    _ ≤ ∑ u ∈ A,
        (a * v u + b * (v u + M * v u) + q * (M * v u)) := by
          exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = ∑ u ∈ A, (a + b * (1 + M) + q * M) * v u := by
          apply Finset.sum_congr rfl
          intro u hu
          ring
    _ = (a + b * (1 + M) + q * M) * (∑ u ∈ A, v u) := by
          rw [Finset.mul_sum]
    _ = a * (∑ u ∈ A, v u) +
        b * ((∑ u ∈ A, v u) + M * (∑ u ∈ A, v u)) +
        q * M * (∑ u ∈ A, v u) := by ring
    _ = (2 / 9 : ℝ) * |θ| ^ 3 * Rcut *
          (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) +
        (4 * θ ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27 *
          ((∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) +
            M * (∑ u ∈ A,
              R.exposedConditionalVariance (G := G) C I u)) +
        (θ ^ 2 / 2) ^ 2 * M *
          (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) := by
          rfl

/-- Uniform row form of D.30.  Under a rooted-antichain variance-mass bound
`E(u) ≤ beta * V`, the conditional product error is bounded by an explicit
quantity independent of the revealed configuration `I`. -/
theorem exposedCenteredCharacteristic_normalized_error_le_D30
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V)
    (hA : R.IsRootedAntichain (G := G) A) (I : IndepFinset G)
    (t epsilon beta : ℝ) (hVar : 0 < C.variance)
    (hepsilon : 0 < epsilon) (ht : |t| * epsilon ≤ 1)
    (hbeta : 0 ≤ beta)
    (hdiffuse : ∀ u ∈ A,
      R.subtreeVarianceMass (G := G) C u ≤ beta * C.variance) :
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic
              (t / Real.sqrt C.variance)) -
        Complex.exp (((-((t / Real.sqrt C.variance) ^ 2 / 2 *
          ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ ≤
      (2 / 9 : ℝ) * |t / Real.sqrt C.variance| ^ 3 *
          (epsilon * Real.sqrt C.variance) * (784 * C.variance) +
        (4 * (t / Real.sqrt C.variance) ^ 2 /
            (epsilon * Real.sqrt C.variance) ^ 2) *
          UniformFourthMoment.C4 27 *
          ((784 * C.variance) +
            (784 * beta * C.variance) * (784 * C.variance)) +
        ((t / Real.sqrt C.variance) ^ 2 / 2) ^ 2 *
          (784 * beta * C.variance) * (784 * C.variance) := by
  let theta := t / Real.sqrt C.variance
  let Rcut := epsilon * Real.sqrt C.variance
  let M := 784 * beta * C.variance
  let W := ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u
  have hsqrt : 0 < Real.sqrt C.variance := Real.sqrt_pos.2 hVar
  have hR : 0 < Rcut := mul_pos hepsilon hsqrt
  have hthetaR : |theta| * Rcut ≤ 1 := by
    rw [show theta = t / Real.sqrt C.variance by rfl,
      show Rcut = epsilon * Real.sqrt C.variance by rfl,
      abs_div, abs_of_pos hsqrt]
    field_simp
    simpa [mul_comm, mul_left_comm, mul_assoc] using ht
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hblock : ∀ u ∈ A,
      R.exposedConditionalVariance (G := G) C I u ≤ M := by
    intro u hu
    calc
      R.exposedConditionalVariance (G := G) C I u ≤
          784 * R.subtreeVarianceMass (G := G) C u :=
        R.exposedConditionalVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
          (G := G) C hz I u
      _ ≤ 784 * (beta * C.variance) := by
        exact mul_le_mul_of_nonneg_left (hdiffuse u hu) (by norm_num)
      _ = M := by simp [M]; ring
  have hWnonneg : 0 ≤ W := by
    apply Finset.sum_nonneg
    intro u hu
    rw [show R.exposedConditionalVariance (G := G) C I u =
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).variance by
      symm
      exact R.exposedAllowedPiece_variance_eq_exposedConditionalVariance
        (G := G) C I u]
    exact FiniteLatticeLaw.variance_nonneg _
  have hW : W ≤ 784 * C.variance := by
    calc
      W ≤ ∑ u ∈ A,
          784 * R.subtreeVarianceMass (G := G) C u := by
        apply Finset.sum_le_sum
        intro u hu
        exact R.exposedConditionalVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
          (G := G) C hz I u
      _ = 784 * ∑ u ∈ A,
          R.subtreeVarianceMass (G := G) C u := by
        rw [Finset.mul_sum]
      _ ≤ 784 * C.variance := by
        exact mul_le_mul_of_nonneg_left
          (R.sum_subtreeVarianceMass_le_variance_of_rootedAntichain
            (G := G) C A hA) (by norm_num)
  have hagg :=
    R.exposedCenteredCharacteristic_product_gaussian_error_le_of_blockVariance
      (G := G) C hz A I theta Rcut M hR hthetaR hblock
  let a : ℝ := (2 / 9 : ℝ) * |theta| ^ 3 * Rcut
  let b : ℝ := (4 * theta ^ 2 / Rcut ^ 2) * UniformFourthMoment.C4 27
  let q : ℝ := (theta ^ 2 / 2) ^ 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := mul_nonneg (by positivity)
    (UniformFourthMoment.C4_nonneg_of_nonneg (by norm_num))
  have hq : 0 ≤ q := sq_nonneg _
  calc
    ‖(∏ u ∈ A,
          (hardCoreLaw
            (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
            C.activity C.activity_pos).centeredCharacteristic
              (t / Real.sqrt C.variance)) -
        Complex.exp (((-((t / Real.sqrt C.variance) ^ 2 / 2 *
          ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖ ≤
      a * W + b * (W + M * W) + q * M * W := by
        simpa only [theta, Rcut, M, W, a, b, q] using hagg
    _ ≤ a * (784 * C.variance) +
        b * ((784 * C.variance) + M * (784 * C.variance)) +
        q * M * (784 * C.variance) := by
          have hMW : M * W ≤ M * (784 * C.variance) :=
            mul_le_mul_of_nonneg_left hW hM
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hW ha)
              (mul_le_mul_of_nonneg_left (add_le_add hW hMW) hb))
            (mul_le_mul_of_nonneg_left hW (mul_nonneg hq hM))
    _ = (2 / 9 : ℝ) * |t / Real.sqrt C.variance| ^ 3 *
          (epsilon * Real.sqrt C.variance) * (784 * C.variance) +
        (4 * (t / Real.sqrt C.variance) ^ 2 /
            (epsilon * Real.sqrt C.variance) ^ 2) *
          UniformFourthMoment.C4 27 *
          ((784 * C.variance) +
            (784 * beta * C.variance) * (784 * C.variance)) +
        ((t / Real.sqrt C.variance) ^ 2 / 2) ^ 2 *
          (784 * beta * C.variance) * (784 * C.variance) := by
            rfl

/-- The normalized row bound in `exposedCenteredCharacteristic_normalized_error_le_D30`
has the scale-free D.31--D.32 form used in sequential limits. -/
theorem normalized_exposed_product_error_bound_identity
    (Vscale t epsilon beta : ℝ) (hV : 0 < Vscale)
    (hepsilon : 0 < epsilon) :
    (2 / 9 : ℝ) * |t / Real.sqrt Vscale| ^ 3 *
          (epsilon * Real.sqrt Vscale) * (784 * Vscale) +
        (4 * (t / Real.sqrt Vscale) ^ 2 /
            (epsilon * Real.sqrt Vscale) ^ 2) *
          UniformFourthMoment.C4 27 *
          ((784 * Vscale) +
            (784 * beta * Vscale) * (784 * Vscale)) +
        ((t / Real.sqrt Vscale) ^ 2 / 2) ^ 2 *
          (784 * beta * Vscale) * (784 * Vscale) =
      (2 / 9 : ℝ) * 784 * |t| ^ 3 * epsilon +
        (4 * t ^ 2 / epsilon ^ 2) * UniformFourthMoment.C4 27 *
          (784 / Vscale + 784 ^ 2 * beta) +
        (t ^ 4 / 4) * 784 ^ 2 * beta := by
  have hs : 0 < Real.sqrt Vscale := Real.sqrt_pos.2 hV
  have hs0 : Real.sqrt Vscale ≠ 0 := ne_of_gt hs
  have he0 : epsilon ≠ 0 := ne_of_gt hepsilon
  rw [abs_div, abs_of_pos hs]
  have hs2 : (Real.sqrt Vscale) ^ 2 = Vscale := Real.sq_sqrt hV.le
  field_simp
  have hs4 : (Real.sqrt Vscale) ^ 4 = Vscale ^ 2 := by
    calc
      (Real.sqrt Vscale) ^ 4 = ((Real.sqrt Vscale) ^ 2) ^ 2 := by ring
      _ = Vscale ^ 2 := by rw [hs2]
  rw [hs2, hs4]
  ring

/-- The conditional product-versus-Gaussian error for one revealed global
configuration.  Every factor is an actual hard-core law at `C.activity`; no
canonical structure is put on the exposed allowed pieces. -/
noncomputable def exposedConditionalGaussianProductError
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (I : IndepFinset G) (t : ℝ) : ℝ :=
  ‖(∏ u ∈ A,
      (hardCoreLaw
        (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
        C.activity C.activity_pos).centeredCharacteristic
          (t / Real.sqrt C.variance)) -
    Complex.exp (((-((t / Real.sqrt C.variance) ^ 2 / 2 *
      ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) : ℝ) : ℂ))‖

/-- Sequential `L¹` conditional characteristic approximation D.30.  The
cutoff hypotheses are the exact asymptotic requirements used by D.31--D.32;
a diagonal cutoff can be chosen from variance divergence and diffuseness. -/
theorem exposedConditionalGaussianProductError_tendsto_zero_D30
    (Vertex : ℕ → Type u) [∀ n, Fintype (Vertex n)]
    (G : (n : ℕ) → SimpleGraph (Vertex n))
    (C : (n : ℕ) → CanonicalFirstRecoveryState (G n))
    (R : (n : ℕ) → ComponentRooting (G n))
    (A : (n : ℕ) → Finset (Vertex n))
    (hA : ∀ n, (R n).IsRootedAntichain (G := G n) (A n))
    (hz : ∀ n, (C n).activity < 27)
    (hVar : ∀ n, 0 < (C n).variance)
    (t : ℝ) (epsilon beta : ℕ → ℝ)
    (hepsilon_pos : ∀ n, 0 < epsilon n)
    (hepsilon : Tendsto epsilon atTop (𝓝 0))
    (ht : ∀ᶠ n in atTop, |t| * epsilon n ≤ 1)
    (hbeta_nonneg : ∀ n, 0 ≤ beta n)
    (hbeta : Tendsto beta atTop (𝓝 0))
    (hdiffuse : ∀ n, ∀ u ∈ A n,
      (R n).subtreeVarianceMass (G := G n) (C n) u ≤
        beta n * (C n).variance)
    (hscaled : Tendsto
      (fun n => (784 / (C n).variance + 784 ^ 2 * beta n) /
        (epsilon n) ^ 2) atTop (𝓝 0)) :
    Tendsto
      (fun n => ∑ I : IndepFinset (G n),
        (C n).law.probability I *
          exposedConditionalGaussianProductError
            (C n) (R n) (A n) I t)
      atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun n =>
    ((2 / 9 : ℝ) * 784 * |t| ^ 3) * epsilon n +
      ((4 * t ^ 2) * UniformFourthMoment.C4 27) *
        ((784 / (C n).variance + 784 ^ 2 * beta n) /
          (epsilon n) ^ 2) +
      ((t ^ 4 / 4) * 784 ^ 2) * beta n
  have hB : Tendsto B atTop (𝓝 0) := by
    have h1 : Tendsto
        (fun n => ((2 / 9 : ℝ) * 784 * |t| ^ 3) * epsilon n)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hepsilon)
    have h2 : Tendsto
        (fun n => ((4 * t ^ 2) * UniformFourthMoment.C4 27) *
          ((784 / (C n).variance + 784 ^ 2 * beta n) /
            (epsilon n) ^ 2)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hscaled)
    have h3 : Tendsto
        (fun n => ((t ^ 4 / 4) * 784 ^ 2) * beta n)
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hbeta)
    convert (h1.add h2).add h3 using 1 <;> norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0)) hB
  · exact Filter.Eventually.of_forall fun n => Finset.sum_nonneg fun I hI =>
      mul_nonneg ((C n).law.probability_nonneg I) (norm_nonneg _)
  · filter_upwards [ht] with n htn
    have hrow : ∀ I : IndepFinset (G n),
        exposedConditionalGaussianProductError
            (C n) (R n) (A n) I t ≤ B n := by
      intro I
      have hraw :=
        (R n).exposedCenteredCharacteristic_normalized_error_le_D30
          (G := G n) (C n) (hz n) (A n) (hA n) I t
            (epsilon n) (beta n) (hVar n) (hepsilon_pos n) htn
            (hbeta_nonneg n) (hdiffuse n)
      have hid := normalized_exposed_product_error_bound_identity
        (C n).variance t (epsilon n) (beta n) (hVar n) (hepsilon_pos n)
      calc
        exposedConditionalGaussianProductError
            (C n) (R n) (A n) I t ≤
          (2 / 9 : ℝ) * |t / Real.sqrt (C n).variance| ^ 3 *
              (epsilon n * Real.sqrt (C n).variance) *
                (784 * (C n).variance) +
            (4 * (t / Real.sqrt (C n).variance) ^ 2 /
                (epsilon n * Real.sqrt (C n).variance) ^ 2) *
              UniformFourthMoment.C4 27 *
              ((784 * (C n).variance) +
                (784 * beta n * (C n).variance) *
                  (784 * (C n).variance)) +
            ((t / Real.sqrt (C n).variance) ^ 2 / 2) ^ 2 *
              (784 * beta n * (C n).variance) *
                (784 * (C n).variance) := by
                  simpa only [exposedConditionalGaussianProductError] using hraw
        _ = (2 / 9 : ℝ) * 784 * |t| ^ 3 * epsilon n +
            (4 * t ^ 2 / (epsilon n) ^ 2) *
              UniformFourthMoment.C4 27 *
                (784 / (C n).variance + 784 ^ 2 * beta n) +
            (t ^ 4 / 4) * 784 ^ 2 * beta n := hid
        _ = B n := by
          dsimp [B]
          field_simp [ne_of_gt (hepsilon_pos n)]
    calc
      ∑ I : IndepFinset (G n),
          (C n).law.probability I *
            exposedConditionalGaussianProductError
              (C n) (R n) (A n) I t ≤
        ∑ I : IndepFinset (G n), (C n).law.probability I * B n := by
          apply Finset.sum_le_sum
          intro I hI
          exact mul_le_mul_of_nonneg_left (hrow I)
            ((C n).law.probability_nonneg I)
      _ = B n := by
        rw [← Finset.sum_mul, (C n).law.probability_sum, one_mul]

/-- A concrete diagonal cutoff for D.31.  The fourth-root scale makes both the
small-displacement cubic term and the normalized tail term tend to zero. -/
theorem exists_exposedGaussianProduct_cutoff_D30
    (Vscale beta : ℕ → ℝ)
    (hVpos : ∀ n, 0 < Vscale n)
    (hV : Tendsto Vscale atTop atTop)
    (hbeta_nonneg : ∀ n, 0 ≤ beta n)
    (hbeta : Tendsto beta atTop (𝓝 0)) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 < epsilon n) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      (∀ t : ℝ, ∀ᶠ n in atTop, |t| * epsilon n ≤ 1) ∧
      Tendsto
        (fun n => (784 / Vscale n + 784 ^ 2 * beta n) /
          epsilon n ^ 2) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n => 784 / Vscale n + 784 ^ 2 * beta n
  let epsilon : ℕ → ℝ := fun n => Real.sqrt (Real.sqrt (d n))
  have hinv : Tendsto (fun n => (Vscale n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hV
  have hfirst : Tendsto (fun n => 784 / Vscale n) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds.mul hinv :
      Tendsto (fun n => (784 : ℝ) * (Vscale n)⁻¹)
        atTop (𝓝 ((784 : ℝ) * 0)))
    simpa [div_eq_mul_inv] using h
  have hsecond : Tendsto (fun n => 784 ^ 2 * beta n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hbeta)
  have hd : Tendsto d atTop (𝓝 0) := by
    convert hfirst.add hsecond using 1 <;> norm_num
  have hdpos : ∀ n, 0 < d n := by
    intro n
    dsimp [d]
    have hfirstpos : 0 < 784 / Vscale n :=
      div_pos (by norm_num) (hVpos n)
    have hsecondnonneg : 0 ≤ (784 : ℝ) ^ 2 * beta n :=
      mul_nonneg (sq_nonneg _) (hbeta_nonneg n)
    exact add_pos_of_pos_of_nonneg hfirstpos hsecondnonneg
  have hepsilon_pos : ∀ n, 0 < epsilon n := by
    intro n
    exact Real.sqrt_pos.2 (Real.sqrt_pos.2 (hdpos n))
  have hepsilon : Tendsto epsilon atTop (𝓝 0) := by
    have h := hd.sqrt.sqrt
    simpa only [epsilon, Real.sqrt_zero] using h
  have ht : ∀ t : ℝ, ∀ᶠ n in atTop, |t| * epsilon n ≤ 1 := by
    intro t
    have hmul : Tendsto (fun n => |t| * epsilon n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hepsilon)
    have hevent : ∀ᶠ n in atTop, |t| * epsilon n < 1 :=
      (tendsto_order.1 hmul).2 1 zero_lt_one
    exact hevent.mono fun n hn => le_of_lt hn
  have hquot : ∀ n, d n / epsilon n ^ 2 = Real.sqrt (d n) := by
    intro n
    have hd0 : 0 ≤ d n := (hdpos n).le
    have hs0 : 0 < Real.sqrt (d n) := Real.sqrt_pos.2 (hdpos n)
    have hepssq : epsilon n ^ 2 = Real.sqrt (d n) := by
      exact Real.sq_sqrt (Real.sqrt_nonneg _)
    rw [hepssq]
    have hdsq : (Real.sqrt (d n)) ^ 2 = d n := Real.sq_sqrt hd0
    field_simp [ne_of_gt hs0]
    nlinarith
  have hscaled : Tendsto
      (fun n => (784 / Vscale n + 784 ^ 2 * beta n) / epsilon n ^ 2)
      atTop (𝓝 0) := by
    have hsqrt := hd.sqrt
    have heq : (fun n =>
        (784 / Vscale n + 784 ^ 2 * beta n) / epsilon n ^ 2) =
        fun n => Real.sqrt (d n) := by
      funext n
      simpa only [d] using hquot n
    rw [heq]
    simpa only [Real.sqrt_zero] using hsqrt
  exact ⟨epsilon, hepsilon_pos, hepsilon, ht, hscaled⟩

/-- D.30 with its cutoff discharged from variance divergence and a supplied
nonnegative diffuse rate `beta_n → 0`. -/
theorem exposedConditionalGaussianProductError_tendsto_zero_of_diffuseRate_D30
    (Vertex : ℕ → Type u) [∀ n, Fintype (Vertex n)]
    (G : (n : ℕ) → SimpleGraph (Vertex n))
    (C : (n : ℕ) → CanonicalFirstRecoveryState (G n))
    (R : (n : ℕ) → ComponentRooting (G n))
    (A : (n : ℕ) → Finset (Vertex n))
    (hA : ∀ n, (R n).IsRootedAntichain (G := G n) (A n))
    (hz : ∀ n, (C n).activity < 27)
    (hVar : ∀ n, 0 < (C n).variance)
    (hvariance : Tendsto (fun n => (C n).variance) atTop atTop)
    (beta : ℕ → ℝ) (hbeta_nonneg : ∀ n, 0 ≤ beta n)
    (hbeta : Tendsto beta atTop (𝓝 0))
    (hdiffuse : ∀ n, ∀ u ∈ A n,
      (R n).subtreeVarianceMass (G := G n) (C n) u ≤
        beta n * (C n).variance) :
    ∀ t : ℝ,
      Tendsto
        (fun n => ∑ I : IndepFinset (G n),
          (C n).law.probability I *
            exposedConditionalGaussianProductError
              (C n) (R n) (A n) I t)
        atTop (𝓝 0) := by
  obtain ⟨epsilon, hepsilon_pos, hepsilon, ht, hscaled⟩ :=
    exists_exposedGaussianProduct_cutoff_D30
      (fun n => (C n).variance) beta hVar hvariance hbeta_nonneg hbeta
  intro t
  exact exposedConditionalGaussianProductError_tendsto_zero_D30
    Vertex G C R A hA hz hVar t epsilon beta hepsilon_pos hepsilon
      (ht t) hbeta_nonneg hbeta hdiffuse hscaled

/-- The largest normalized subtree variance mass on a finite selected set,
with value zero on the empty set. -/
noncomputable def maximalSubtreeVarianceRatio
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) : ℝ :=
  if hA : A.Nonempty then
    A.sup' hA (fun u => R.subtreeVarianceMass (G := G) C u / C.variance)
  else 0

/-- The pointwise diffuse-antichain premise produces a nonnegative maximum
rate tending to zero, and this rate bounds every unnormalized subtree mass. -/
theorem maximalSubtreeVarianceRatio_data
    (Vertex : ℕ → Type u) [∀ n, Fintype (Vertex n)]
    (G : (n : ℕ) → SimpleGraph (Vertex n))
    (C : (n : ℕ) → CanonicalFirstRecoveryState (G n))
    (R : (n : ℕ) → ComponentRooting (G n))
    (A : (n : ℕ) → Finset (Vertex n))
    (hVar : ∀ n, 0 < (C n).variance)
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ A n,
        (R n).subtreeVarianceMass (G := G n) (C n) u /
          (C n).variance < epsilon) :
    let beta := fun n => maximalSubtreeVarianceRatio (C n) (R n) (A n)
    (∀ n, 0 ≤ beta n) ∧
      Tendsto beta atTop (𝓝 0) ∧
      (∀ n, ∀ u ∈ A n,
        (R n).subtreeVarianceMass (G := G n) (C n) u ≤
          beta n * (C n).variance) := by
  dsimp only
  have hnonneg : ∀ n,
      0 ≤ maximalSubtreeVarianceRatio (C n) (R n) (A n) := by
    intro n
    rw [maximalSubtreeVarianceRatio]
    split_ifs with hA
    · obtain ⟨u, hu, heq⟩ := Finset.exists_mem_eq_sup' hA
          (fun u => (R n).subtreeVarianceMass (G := G n) (C n) u /
            (C n).variance)
      rw [heq]
      exact div_nonneg
        ((R n).subtreeVarianceMass_nonneg (G := G n) (C n) u)
        (hVar n).le
    · exact le_rfl
  have hupper : ∀ n, ∀ u ∈ A n,
      (R n).subtreeVarianceMass (G := G n) (C n) u /
          (C n).variance ≤
        maximalSubtreeVarianceRatio (C n) (R n) (A n) := by
    intro n u hu
    rw [maximalSubtreeVarianceRatio]
    split_ifs with hA
    · exact Finset.le_sup' (fun u =>
        (R n).subtreeVarianceMass (G := G n) (C n) u /
          (C n).variance) hu
    · exact False.elim (hA ⟨u, hu⟩)
  have htendsto : Tendsto
      (fun n => maximalSubtreeVarianceRatio (C n) (R n) (A n))
      atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall fun n => lt_of_lt_of_le ha (hnonneg n)
    · intro a ha
      filter_upwards [hdiffuse a ha] with n hn
      rw [maximalSubtreeVarianceRatio]
      split_ifs with hA
      · exact (Finset.sup'_lt_iff hA).2 hn
      · simpa using ha
  refine ⟨hnonneg, htendsto, ?_⟩
  intro n u hu
  have h := hupper n u hu
  have hpos := hVar n
  calc
    (R n).subtreeVarianceMass (G := G n) (C n) u =
        ((R n).subtreeVarianceMass (G := G n) (C n) u /
          (C n).variance) * (C n).variance := by field_simp
    _ ≤ maximalSubtreeVarianceRatio (C n) (R n) (A n) *
        (C n).variance := mul_le_mul_of_nonneg_right h hpos.le

/-- D.30 directly from the diffuse maximum premise in D.22. -/
theorem exposedConditionalGaussianProductError_tendsto_zero_of_diffuse_D30
    (Vertex : ℕ → Type u) [∀ n, Fintype (Vertex n)]
    (G : (n : ℕ) → SimpleGraph (Vertex n))
    (C : (n : ℕ) → CanonicalFirstRecoveryState (G n))
    (R : (n : ℕ) → ComponentRooting (G n))
    (A : (n : ℕ) → Finset (Vertex n))
    (hA : ∀ n, (R n).IsRootedAntichain (G := G n) (A n))
    (hz : ∀ n, (C n).activity < 27)
    (hVar : ∀ n, 0 < (C n).variance)
    (hvariance : Tendsto (fun n => (C n).variance) atTop atTop)
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ A n,
        (R n).subtreeVarianceMass (G := G n) (C n) u /
          (C n).variance < epsilon) :
    ∀ t : ℝ,
      Tendsto
        (fun n => ∑ I : IndepFinset (G n),
          (C n).law.probability I *
            exposedConditionalGaussianProductError
              (C n) (R n) (A n) I t)
        atTop (𝓝 0) := by
  let beta : ℕ → ℝ := fun n =>
    maximalSubtreeVarianceRatio (C n) (R n) (A n)
  obtain ⟨hbeta_nonneg, hbeta, hmass⟩ :=
    maximalSubtreeVarianceRatio_data Vertex G C R A hVar hdiffuse
  exact exposedConditionalGaussianProductError_tendsto_zero_of_diffuseRate_D30
    Vertex G C R A hA hz hVar hvariance beta hbeta_nonneg hbeta hmass

/-- Finite probability-space form of the good-conditional-variance mass bound
D.33.  It is stated independently of measure-theory wrappers so it applies
directly to the canonical finite law on revealed global configurations. -/
theorem finite_goodVariance_mass_lower_bound_D33
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p X : Ω → ℝ) (Vscale c C0 omega : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hpsum : ∑ x, p x = 1)
    (hV : 0 < Vscale) (hC : omega < C0)
    (hmean : c * Vscale ≤ ∑ x, p x * X x)
    (hupper : ∀ x, X x ≤ C0 * Vscale) :
    (c - omega) / (C0 - omega) ≤
      ∑ x ∈ Finset.univ.filter (fun x => omega * Vscale ≤ X x), p x := by
  let good : Finset Ω := Finset.univ.filter (fun x => omega * Vscale ≤ X x)
  let bad : Finset Ω := Finset.univ \ good
  have hpartition : Finset.univ = good ∪ bad := by
    ext x
    simp [good, bad]
  have hdisj : Disjoint good bad := Finset.disjoint_sdiff
  have hsum_split (f : Ω → ℝ) :
      ∑ x, f x = ∑ x ∈ good, f x + ∑ x ∈ bad, f x := by
    rw [hpartition, Finset.sum_union hdisj]
  have hbad : ∀ x ∈ bad, X x ≤ omega * Vscale := by
    intro x hx
    have hxnot : x ∉ good := (Finset.mem_sdiff.mp hx).2
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and] at hxnot
    exact le_of_lt (lt_of_not_ge hxnot)
  have hexpect : (∑ x, p x * X x) ≤
      C0 * Vscale * (∑ x ∈ good, p x) +
        omega * Vscale * (∑ x ∈ bad, p x) := by
    rw [hsum_split (fun x => p x * X x)]
    apply add_le_add
    · calc
        ∑ x ∈ good, p x * X x ≤
            ∑ x ∈ good, p x * (C0 * Vscale) := by
          exact Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (hupper x) (hp x)
        _ = C0 * Vscale * (∑ x ∈ good, p x) := by
          rw [← Finset.sum_mul]
          ring
    · calc
        ∑ x ∈ bad, p x * X x ≤
            ∑ x ∈ bad, p x * (omega * Vscale) := by
          exact Finset.sum_le_sum fun x hx =>
            mul_le_mul_of_nonneg_left (hbad x hx) (hp x)
        _ = omega * Vscale * (∑ x ∈ bad, p x) := by
          rw [← Finset.sum_mul]
          ring
  have hmass : (∑ x ∈ good, p x) + (∑ x ∈ bad, p x) = 1 := by
    rw [← hsum_split p, hpsum]
  have hbadeq : (∑ x ∈ bad, p x) = 1 - (∑ x ∈ good, p x) := by
    linarith [hmass]
  have hchain := le_trans hmean hexpect
  rw [hbadeq] at hchain
  have hlin : (c - omega) * Vscale ≤
      (C0 - omega) * Vscale * (∑ x ∈ good, p x) := by
    calc
      (c - omega) * Vscale = c * Vscale - omega * Vscale := by ring
      _ ≤ (C0 * Vscale * (∑ x ∈ good, p x) +
          omega * Vscale * (1 - ∑ x ∈ good, p x)) -
            omega * Vscale := sub_le_sub_right hchain _
      _ = (C0 - omega) * Vscale * (∑ x ∈ good, p x) := by ring
  have hcancel : (c - omega) ≤
      (C0 - omega) * (∑ x ∈ good, p x) := by
    apply le_of_mul_le_mul_right _ hV
    convert hlin using 1 <;> ring
  have hdiv : (c - omega) / (C0 - omega) ≤
      ∑ x ∈ good, p x :=
    (div_le_iff₀ (sub_pos.mpr hC)).2 (by
      simpa [mul_comm] using hcancel)
  simpa [good] using hdiv

/-- A literal parent-occupation indicator always has one of its two genuine
indicator values. -/
theorem parentOccupationIndicator_eq_zero_or_one
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    ActualMartingaleProjection.parentOccupationIndicator R I u = 0 ∨
      ActualMartingaleProjection.parentOccupationIndicator R I u = 1 := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · left
    exact ActualMartingaleProjection.parentOccupationIndicator_root R I hroot
  · rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent
      C R I hroot]
    unfold ActualMartingaleProjection.occupationIndicator
    by_cases hmem : R.selectedParent (G := G) u hroot ∈ I.val
    · exact Or.inr (by simp [hmem])
    · exact Or.inl (by simp [hmem])

/-- Pointwise two-state expression for an exposed conditional variance. -/
theorem exposedConditionalVariance_eq_indicator_mixture
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    R.exposedConditionalVariance (G := G) C I u =
      (1 - ActualMartingaleProjection.parentOccupationIndicator R I u) *
          R.subtreeVariance (G := G) C u +
        ActualMartingaleProjection.parentOccupationIndicator R I u *
          R.vacantVariance (G := G) C u := by
  rcases R.parentOccupationIndicator_eq_zero_or_one (G := G) C I u with h | h
  · simp [exposedConditionalVariance, h]
  · simp [exposedConditionalVariance, h]

/-- Averaging the revealed parent state gives exactly the original contextual
subtree variance mass `E(u)`. -/
theorem expectation_exposedConditionalVariance_eq_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I *
      R.exposedConditionalVariance (G := G) C I u) =
      R.subtreeVarianceMass (G := G) C u := by
  classical
  let a := R.parentAbsentProbability (G := G) C u
  let vP := R.subtreeVariance (G := G) C u
  let vQ := R.vacantVariance (G := G) C u
  let xi : IndepFinset G → ℝ := fun I =>
    ActualMartingaleProjection.parentOccupationIndicator R I u
  have hA :
      (∑ I : IndepFinset G, C.law.probability I * (1 - xi I)) = a := by
    exact ActualMartingaleProjection.expectation_one_sub_parentOccupationIndicator
      C R u
  have hXi :
      (∑ I : IndepFinset G, C.law.probability I * xi I) = 1 - a := by
    calc
      (∑ I : IndepFinset G, C.law.probability I * xi I) =
          (∑ I : IndepFinset G, C.law.probability I) -
            ∑ I : IndepFinset G, C.law.probability I * (1 - xi I) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro I hI
              ring
      _ = 1 - a := by rw [C.law.probability_sum, hA]
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        R.exposedConditionalVariance (G := G) C I u) =
        ∑ I : IndepFinset G, C.law.probability I *
          ((1 - xi I) * vP + xi I * vQ) := by
            apply Finset.sum_congr rfl
            intro I hI
            rw [R.exposedConditionalVariance_eq_indicator_mixture
              (G := G) C I u]
    _ = (∑ I : IndepFinset G,
          C.law.probability I * (1 - xi I) * vP) +
        (∑ I : IndepFinset G,
          C.law.probability I * xi I * vQ) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro I hI
            ring
    _ = vP * (∑ I : IndepFinset G,
          C.law.probability I * (1 - xi I)) +
        vQ * (∑ I : IndepFinset G,
          C.law.probability I * xi I) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
            ring
    _ = a * vP + (1 - a) * vQ := by rw [hA, hXi]; ring
    _ = R.subtreeVarianceMass (G := G) C u := by
      rfl

/-- Exact averaged D.26 identity for any finite exposed boundary. -/
theorem expectation_sum_exposedConditionalVariance_eq_sum_subtreeVarianceMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) :
    (∑ I : IndepFinset G, C.law.probability I *
      (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u)) =
      ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  exact R.expectation_exposedConditionalVariance_eq_subtreeVarianceMass
    (G := G) C u

/-- The random conditional variance sum is nonnegative. -/
theorem sum_exposedConditionalVariance_nonneg
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (I : IndepFinset G) :
    0 ≤ ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u := by
  classical
  apply Finset.sum_nonneg
  intro u hu
  rw [← R.exposedAllowedPiece_variance_eq_exposedConditionalVariance
    (G := G) C I u]
  exact FiniteLatticeLaw.variance_nonneg _

/-- Finite D.27 upper bound for every revealed configuration. -/
theorem sum_exposedConditionalVariance_le_D27
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V) (I : IndepFinset G) :
    (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) ≤
      784 * ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u := by
  classical
  calc
    (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) ≤
        ∑ u ∈ A, 784 * R.subtreeVarianceMass (G := G) C u := by
          exact Finset.sum_le_sum fun u hu =>
            R.exposedConditionalVariance_le_sevenHundredEightyFour_mul_subtreeVarianceMass
              (G := G) C hz I u
    _ = 784 * ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u := by
      rw [Finset.mul_sum]

/-- In particular, a rooted antichain has conditional variance at most
`784 * V` in every revealed state. -/
theorem sum_exposedConditionalVariance_le_variance_D27
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V)
    (hA : R.IsRootedAntichain (G := G) A) (I : IndepFinset G) :
    (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) ≤
      784 * C.variance := by
  calc
    (∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u) ≤
        784 * ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u :=
      R.sum_exposedConditionalVariance_le_D27 (G := G) C hz A I
    _ ≤ 784 * C.variance := by
      gcongr
      exact R.sum_subtreeVarianceMass_le_variance_of_rootedAntichain
        (G := G) C A hA

/-- D.33 for the genuine exposed conditional variances of a rooted antichain.
The probability is taken under the original global canonical law. -/
theorem exposedConditionalVariance_goodMass_lower_bound_D33
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V)
    (hA : R.IsRootedAntichain (G := G) A)
    (c : ℝ) (hV : 0 < C.variance) (hc : c ≤ 1)
    (hlarge : c * C.variance ≤
      ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u) :
    (c / 2) / (784 - c / 2) ≤
      ∑ I ∈ Finset.univ.filter (fun I : IndepFinset G =>
        (c / 2) * C.variance ≤
          ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u),
        C.law.probability I := by
  classical
  have hgood := finite_goodVariance_mass_lower_bound_D33
    (fun I : IndepFinset G => C.law.probability I)
    (fun I => ∑ u ∈ A,
      R.exposedConditionalVariance (G := G) C I u)
    C.variance c 784 (c / 2)
    (fun I => C.law.probability_nonneg I)
    C.law.probability_sum hV (by linarith)
    (by
      rw [R.expectation_sum_exposedConditionalVariance_eq_sum_subtreeVarianceMass
        (G := G) C A]
      exact hlarge)
    (fun I => R.sum_exposedConditionalVariance_le_variance_D27
      (G := G) C hz A hA I)
  convert hgood using 1 <;> ring

/-- Generic finite weighted Chebyshev estimate. -/
theorem finite_weighted_chebyshev
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p X : Ω → ℝ) (Vscale B : ℝ)
    (hp : ∀ x, 0 ≤ p x) (hV : 0 < Vscale) (hB : 0 < B)
    (hsecond : (∑ x, p x * (X x) ^ 2) ≤ Vscale) :
    (∑ x ∈ Finset.univ.filter (fun x => B * Real.sqrt Vscale < |X x|), p x) ≤
      1 / B ^ 2 := by
  let bad := Finset.univ.filter (fun x => B * Real.sqrt Vscale < |X x|)
  have hpoint : ∀ x ∈ bad, B ^ 2 * Vscale * p x ≤ p x * (X x) ^ 2 := by
    intro x hx
    have htail : B * Real.sqrt Vscale < |X x| := by
      simpa [bad] using hx
    have hsqrt := Real.sq_sqrt hV.le
    have hsquare : B ^ 2 * Vscale ≤ (X x) ^ 2 := by
      have hsum : 0 < |X x| + B * Real.sqrt Vscale := by
        have hsqrtpos : 0 < Real.sqrt Vscale := Real.sqrt_pos.2 hV
        positivity
      have hprod : 0 <
          (|X x| - B * Real.sqrt Vscale) *
            (|X x| + B * Real.sqrt Vscale) :=
        mul_pos (sub_pos.mpr htail) hsum
      nlinarith [sq_abs (X x)]
    nlinarith [mul_nonneg (hp x) (sub_nonneg.mpr hsquare)]
  have hmul : B ^ 2 * Vscale * (∑ x ∈ bad, p x) ≤ Vscale := by
    calc
      B ^ 2 * Vscale * (∑ x ∈ bad, p x) =
          ∑ x ∈ bad, B ^ 2 * Vscale * p x := by
            rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ bad, p x * (X x) ^ 2 :=
        Finset.sum_le_sum hpoint
      _ ≤ ∑ x, p x * (X x) ^ 2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun x hx hxbad => mul_nonneg (hp x) (sq_nonneg (X x)))
      _ ≤ Vscale := hsecond
  have hcancelV : B ^ 2 * (∑ x ∈ bad, p x) ≤ 1 := by
    apply le_of_mul_le_mul_right _ hV
    convert hmul using 1 <;> ring
  have hfinal : (∑ x ∈ bad, p x) ≤ 1 / B ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hB)).2
    simpa [mul_comm] using hcancelV
  simpa [bad] using hfinal

/-- The actual conditional centered mean after revealing the complement of the
rooted-antichain descendant subtrees. -/
noncomputable def antichainConditionalMean
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (I : IndepFinset G) : ℝ :=
  ActualMartingaleProjection.martingaleProjection C R
    (R.antichainObservedSet (G := G) A) I

/-- The conditional means have second moment at most the global variance. -/
theorem antichainConditionalMean_secondMoment_le_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) :
    (∑ I : IndepFinset G, C.law.probability I *
      (R.antichainConditionalMean (G := G) C A I) ^ 2) ≤ C.variance := by
  classical
  rw [show (∑ I : IndepFinset G, C.law.probability I *
      (R.antichainConditionalMean (G := G) C A I) ^ 2) =
      ∑ u ∈ R.antichainObservedSet (G := G) A,
        R.vertexVarianceContribution (G := G) C u by
    exact ActualMartingaleProjection.expectation_sq_sum_eta C R _]
  rw [← R.sum_vertexVarianceContribution_eq_variance (G := G) C]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun u hu hnot => R.vertexVarianceContribution_nonneg (G := G) C u)

/-- D.34 Chebyshev bound for the actual conditional centered mean. -/
theorem antichainConditionalMean_chebyshev_D34
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (B : ℝ) (hB : 0 < B) :
    (∑ I ∈ Finset.univ.filter (fun I : IndepFinset G =>
      B * Real.sqrt C.variance <
        |R.antichainConditionalMean (G := G) C A I|),
      C.law.probability I) ≤ 1 / B ^ 2 := by
  classical
  exact finite_weighted_chebyshev
    (fun I : IndepFinset G => C.law.probability I)
    (fun I => R.antichainConditionalMean (G := G) C A I)
    C.variance B (fun I => C.law.probability_nonneg I)
    (canonicalFirstRecovery_variance_pos C) hB
    (R.antichainConditionalMean_secondMoment_le_variance (G := G) C A)

/-- Finite union-bound extraction: an event of mass at least `p0` retains
mass `p0-q0` after removing a bad event of mass at most `q0`. -/
theorem finite_event_sdiff_mass_lower
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (good bad : Finset Ω) (hp : ∀ x, 0 ≤ p x)
    (p0 q0 : ℝ) (hgood : p0 ≤ ∑ x ∈ good, p x)
    (hbad : (∑ x ∈ bad, p x) ≤ q0) :
    p0 - q0 ≤ ∑ x ∈ good \ bad, p x := by
  have hsplit := Finset.sum_sdiff (s₁ := good ∩ bad) (s₂ := good)
    (f := p) (Finset.inter_subset_left)
  have hinter : (∑ x ∈ good ∩ bad, p x) ≤ ∑ x ∈ bad, p x :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun x hx hnot => hp x)
  have heq : good \ (good ∩ bad) = good \ bad := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at hsplit
  linarith

/-- D.34: after requiring both macroscopic conditional variance and bounded
conditional displacement, a fixed positive amount of the original global
canonical mass remains. -/
theorem antichain_jointGood_mass_lower_bound_D34
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (A : Finset V)
    (hA : R.IsRootedAntichain (G := G) A)
    (c B : ℝ) (hc1 : c ≤ 1) (hB : 0 < B)
    (hlarge : c * C.variance ≤
      ∑ u ∈ A, R.subtreeVarianceMass (G := G) C u) :
    (c / 2) / (784 - c / 2) - 1 / B ^ 2 ≤
      ∑ I ∈ Finset.univ.filter (fun I : IndepFinset G =>
        (c / 2) * C.variance ≤
          ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u ∧
        |R.antichainConditionalMean (G := G) C A I| ≤
          B * Real.sqrt C.variance), C.law.probability I := by
  classical
  let good := Finset.univ.filter (fun I : IndepFinset G =>
    (c / 2) * C.variance ≤
      ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u)
  let bad := Finset.univ.filter (fun I : IndepFinset G =>
    B * Real.sqrt C.variance <
      |R.antichainConditionalMean (G := G) C A I|)
  have hg := R.exposedConditionalVariance_goodMass_lower_bound_D33
    (G := G) C hz A hA c (canonicalFirstRecovery_variance_pos C) hc1 hlarge
  have hb := R.antichainConditionalMean_chebyshev_D34 (G := G) C A B hB
  have hsdiff := finite_event_sdiff_mass_lower
    (fun I : IndepFinset G => C.law.probability I) good bad
    (fun I => C.law.probability_nonneg I)
    ((c / 2) / (784 - c / 2)) (1 / B ^ 2)
    (by simpa [good] using hg) (by simpa [bad] using hb)
  have heq : good \ bad = Finset.univ.filter (fun I : IndepFinset G =>
      (c / 2) * C.variance ≤
        ∑ u ∈ A, R.exposedConditionalVariance (G := G) C I u ∧
      |R.antichainConditionalMean (G := G) C A I| ≤
        B * Real.sqrt C.variance) := by
    ext I
    simp only [good, bad, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ,
      true_and, not_lt]
  rw [← heq]
  exact hsdiff

/-- The omitted contribution outside `D`. -/
noncomputable def omittedVarianceContribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (D : Finset V) : ℝ :=
  ∑ u ∈ outsideSet D, R.vertexVarianceContribution (G := G) C u

/-- Exact exposed-boundary identity (D.43), valid for every actual
ancestor-closed set and hence in particular for `S(α)`. -/
theorem omittedVarianceContribution_eq_sum_exposedBoundary
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D) :
    R.omittedVarianceContribution (G := G) C D =
      ∑ u ∈ R.exposedBoundary (G := G) D,
        R.subtreeVarianceMass (G := G) C u := by
  classical
  have hA := R.exposedBoundary_isRootedAntichain (G := G) C.isForest hD
  have hdisj := R.rootedAntichain_pairwiseDisjoint_descendants
    (G := G) C.isForest hA
  unfold omittedVarianceContribution
  rw [← R.exposedBoundary_biUnion_descendants (G := G) hD]
  unfold exposedDescendantUnion
  rw [Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro u hu
  exact (R.subtreeVarianceMass_eq_sum_descendants (G := G) C u).symm

/-- Every exposed omitted component of `S(α)` has subtree variance mass
strictly below the retention threshold. -/
theorem subtreeVarianceMass_lt_of_mem_exposedBoundary_retainedVarianceSet
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (alpha : ℝ) {u : V}
    (hu : u ∈ R.exposedBoundary (G := G)
      (R.retainedVarianceSet (G := G) C alpha)) :
    R.subtreeVarianceMass (G := G) C u < alpha * C.variance := by
  have huout := (R.mem_exposedBoundary (G := G)
    (R.retainedVarianceSet (G := G) C alpha) u).mp hu |>.1
  rw [R.mem_retainedVarianceSet (G := G)] at huout
  exact lt_of_not_ge huout

/-- The contribution with displacement larger than `b`, restricted to a finite
vertex set `S`.  This is `G_S(b)` from (D.46). -/
noncomputable def largeDisplacementContributionOn
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (b : ℝ) : ℝ :=
  ∑ u ∈ S, if b < |R.conditionalMeanDifference (G := G) C u| then
    R.vertexVarianceContribution (G := G) C u else 0

/-- The local estimate (D.49) with an arbitrary uniform upper bound `m` for
the actual vertex contributions. -/
theorem occupationProbability_lt_scaledContributionBound
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {b m : ℝ} (hb : 1 < b)
    (hm : ∀ v, R.vertexVarianceContribution (G := G) C v ≤ m)
    (u : V) (hu : b < |R.conditionalMeanDifference (G := G) C u|) :
    R.occupationProbability (G := G) C u < 784 * m / b ^ 2 := by
  let p := R.occupationProbability (G := G) C u
  let q := R.vacancyProbability (G := G) C u
  let a := R.parentAbsentProbability (G := G) C u
  let d := R.conditionalMeanDifference (G := G) C u
  have hp : 0 < p := R.occupationProbability_pos (G := G) C u
  have hq : (1 : ℝ) / 28 < q :=
    R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz u
  have ha : (1 : ℝ) / 28 < a :=
    R.one_div_twentyEight_lt_parentAbsentProbability (G := G) C hz u
  have haq : (1 : ℝ) / 784 < a * q := by nlinarith
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hdsq : b ^ 2 < d ^ 2 := by
    change b < |d| at hu
    nlinarith [sq_abs d]
  have hsmall : b ^ 2 / 784 < (a * q) * d ^ 2 := by
    have h1 : b ^ 2 / 784 < (a * q) * b ^ 2 := by
      nlinarith [sq_pos_of_pos hb0]
    exact h1.trans_le
      (mul_le_mul_of_nonneg_left hdsq.le (by nlinarith [ha.le, hq.le]))
  have hg : p * (b ^ 2 / 784) <
      R.vertexVarianceContribution (G := G) C u := by
    unfold vertexVarianceContribution
    change p * (b ^ 2 / 784) < a * p * q * d ^ 2
    calc
      p * (b ^ 2 / 784) < p * ((a * q) * d ^ 2) :=
        mul_lt_mul_of_pos_left hsmall hp
      _ = a * p * q * d ^ 2 := by ring
  have hgm := hm u
  have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb0
  apply (lt_div_iff₀ hb2).2
  nlinarith [hg.trans_le hgm]

/-- The pointwise heart of (D.47), abstracted over a scale `x` known to
strictly dominate the conditional occupation probability of the counted
vertex. -/
theorem pointwise_largeDisplacement_estimate_of_occupation_lt
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {b x : ℝ} (hb : 1 < b)
    (hx : x < 1) (u : V)
    (hu : b < |R.conditionalMeanDifference (G := G) C u|)
    (hpx : R.occupationProbability (G := G) C u < x) :
    R.vertexVarianceContribution (G := G) C u ≤
      (b / (b - 1)) ^ 2 * 28 * x * Real.log (27 / x) *
        (∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v) := by
  classical
  let p : V → ℝ := fun v => R.occupationProbability (G := G) C v
  let q : V → ℝ := fun v => R.vacancyProbability (G := G) C v
  let d : V → ℝ := fun v => R.conditionalMeanDifference (G := G) C v
  let a : V → ℝ := fun v => R.parentAbsentProbability (G := G) C v
  let s := R.children (G := G) u
  let z := ∑ v ∈ s, p v * d v
  let A := ∑ v ∈ s, p v / q v
  let B := ∑ v ∈ s, p v * q v * d v ^ 2
  let H := ∑ v ∈ s, R.vertexVarianceContribution (G := G) C v
  let r := b / (b - 1)
  have hp : 0 < p u := R.occupationProbability_pos (G := G) C u
  have hq : 0 < q u := R.vacancyProbability_pos (G := G) C u
  have ha0 : 0 ≤ a u := R.parentAbsentProbability_nonneg (G := G) C u
  have ha1 : a u ≤ 1 := R.parentAbsentProbability_le_one (G := G) C u
  have hq1 : q u ≤ 1 := by
    have h := R.occupationProbability_add_vacancyProbability (G := G) C u
    have hp0 := R.occupationProbability_nonneg (G := G) C u
    change p u + q u = 1 at h
    linarith
  have hdrec := R.conditionalMeanDifference_eq_one_sub_sum (G := G) C u
  change d u = 1 - z at hdrec
  have hdsq : d u ^ 2 ≤ r ^ 2 * z ^ 2 :=
    displacement_sq_le_ratio_sq_mul_sq hb hu hdrec
  have hr0 : 0 ≤ r ^ 2 := sq_nonneg r
  have hA0 : 0 ≤ A := by
    apply Finset.sum_nonneg
    intro v hv
    exact div_nonneg (R.occupationProbability_nonneg (G := G) C v)
      (R.vacancyProbability_pos (G := G) C v).le
  have hB0 : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro v hv
    exact mul_nonneg
      (mul_nonneg (R.occupationProbability_nonneg (G := G) C v)
        (R.vacancyProbability_pos (G := G) C v).le)
      (sq_nonneg _)
  have hzsq : z ^ 2 ≤ A * B := R.weightedChildCauchy (G := G) C u d
  have hqB : q u * B ≤ H :=
    R.vacancy_mul_sum_child_weightedSquares_le (G := G) C u
  have hAlog : A ≤ 28 * Real.log (27 / p u) :=
    R.sum_child_occupationOdds_le (G := G) C hz u
  have hx0 : 0 < x := lt_trans hp hpx
  have hplog : p u * Real.log (27 / p u) ≤
      x * Real.log (27 / x) :=
    mul_log_twentySeven_div_mono hp hpx.le hx
  have hlogp0 : 0 ≤ Real.log (27 / p u) := by
    exact (Real.log_pos (by
      apply (lt_div_iff₀ hp).2
      have hp1 := R.occupationProbability_lt_twentySeven_div_twentyEight
        (G := G) C hz u
      nlinarith)).le
  have hH0 : 0 ≤ H := by
    apply Finset.sum_nonneg
    intro v hv
    exact R.vertexVarianceContribution_nonneg (G := G) C v
  have hmain : a u * p u * q u * d u ^ 2 ≤
      r ^ 2 * 28 * (p u * Real.log (27 / p u)) * H := by
    calc
      a u * p u * q u * d u ^ 2 ≤ p u * q u * (r ^ 2 * z ^ 2) := by
        have hleft := mul_le_mul_of_nonneg_left hdsq
          (mul_nonneg (mul_nonneg ha0 hp.le) hq.le)
        have haDrop : a u * p u * q u * (r ^ 2 * z ^ 2) ≤
            p u * q u * (r ^ 2 * z ^ 2) := by
          have hap : a u * p u ≤ p u := by
            calc
              a u * p u ≤ 1 * p u := mul_le_mul_of_nonneg_right ha1 hp.le
              _ = p u := one_mul _
          have hapq : a u * p u * q u ≤ p u * q u :=
            mul_le_mul_of_nonneg_right hap hq.le
          exact mul_le_mul_of_nonneg_right hapq
            (mul_nonneg hr0 (sq_nonneg z))
        exact hleft.trans haDrop
      _ ≤ p u * q u * (r ^ 2 * (A * B)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hzsq hr0)
          (mul_nonneg hp.le hq.le)
      _ = r ^ 2 * p u * A * (q u * B) := by ring
      _ ≤ r ^ 2 * p u * A * H := by
        exact mul_le_mul_of_nonneg_left hqB
          (mul_nonneg (mul_nonneg hr0 hp.le) hA0)
      _ ≤ r ^ 2 * p u * (28 * Real.log (27 / p u)) * H := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAlog (mul_nonneg hr0 hp.le)) hH0
      _ = r ^ 2 * 28 * (p u * Real.log (27 / p u)) * H := by ring
  unfold vertexVarianceContribution
  change a u * p u * q u * d u ^ 2 ≤
    r ^ 2 * 28 * x * Real.log (27 / x) * H
  exact hmain.trans <| by
    have hr28 : 0 ≤ r ^ 2 * (28 : ℝ) := mul_nonneg hr0 (by norm_num)
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hplog hr28) hH0
    convert hh using 1 <;> ring

/-- Appendix D equation (D.47), in the slightly stronger form allowing any
positive common upper bound `m` for the vertex contributions.  Taking `m` to
be their finite maximum gives the manuscript statement exactly. -/
theorem largeDisplacementContributionOn_le
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) {b m : ℝ} (hz : C.activity < 27) (hb : 1 < b)
    (hm : 0 < m)
    (hgm : ∀ u, R.vertexVarianceContribution (G := G) C u ≤ m)
    (hx : 784 * m / b ^ 2 < 1) :
    R.largeDisplacementContributionOn (G := G) C S b ≤
      (b / (b - 1)) ^ 2 * 28 * (784 * m / b ^ 2) *
        Real.log (27 / (784 * m / b ^ 2)) * C.variance := by
  classical
  let x := 784 * m / b ^ 2
  let K := (b / (b - 1)) ^ 2 * 28 * x * Real.log (27 / x)
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  have hx0 : 0 < x := by
    dsimp [x]
    exact div_pos (mul_pos (by norm_num) hm) (sq_pos_of_pos hb0)
  have hlog : 0 < Real.log (27 / x) := Real.log_pos <| by
    apply (lt_div_iff₀ hx0).2
    dsimp [x] at hx ⊢
    nlinarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ u : V,
      (if b < |R.conditionalMeanDifference (G := G) C u| then
          R.vertexVarianceContribution (G := G) C u else 0) ≤
        K * ∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v := by
    intro u
    split
    · rename_i hu
      have hpx : R.occupationProbability (G := G) C u < x := by
        dsimp [x]
        exact R.occupationProbability_lt_scaledContributionBound
          (G := G) C hz hb hgm u hu
      exact R.pointwise_largeDisplacement_estimate_of_occupation_lt
        (G := G) C hz hb hx u hu hpx
    · exact mul_nonneg hK <| by
        apply Finset.sum_nonneg
        intro v hv
        exact R.vertexVarianceContribution_nonneg (G := G) C v
  calc
    R.largeDisplacementContributionOn (G := G) C S b ≤
        ∑ u ∈ S, K * ∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v := by
      unfold largeDisplacementContributionOn
      exact Finset.sum_le_sum fun u hu => hpoint u
    _ = K * ∑ u ∈ S, ∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v := by
      rw [Finset.mul_sum]
    _ ≤ K * ∑ u, ∑ v ∈ R.children (G := G) u,
          R.vertexVarianceContribution (G := G) C v := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun u _ _ => by
          apply Finset.sum_nonneg
          intro v hv
          exact R.vertexVarianceContribution_nonneg (G := G) C v)
    _ ≤ K * ∑ v, R.vertexVarianceContribution (G := G) C v := by
      exact mul_le_mul_of_nonneg_left
        (R.sum_sum_children_le_sum C
          (fun v => R.vertexVarianceContribution (G := G) C v)
          (fun v => R.vertexVarianceContribution_nonneg (G := G) C v)) hK
    _ = (b / (b - 1)) ^ 2 * 28 * (784 * m / b ^ 2) *
        Real.log (27 / (784 * m / b ^ 2)) * C.variance := by
      rw [R.sum_vertexVarianceContribution_eq_variance (G := G) C]

/-- Exact manuscript form of (D.47), with `m` definitionally the maximum
actual vertex contribution. -/
theorem D47
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) {b : ℝ} (hz : C.activity < 27) (hb : 1 < b)
    (hx : 784 * R.maxVertexVarianceContribution (G := G) C / b ^ 2 < 1) :
    R.largeDisplacementContributionOn (G := G) C S b ≤
      (b / (b - 1)) ^ 2 * 28 *
        (784 * R.maxVertexVarianceContribution (G := G) C / b ^ 2) *
        Real.log (27 /
          (784 * R.maxVertexVarianceContribution (G := G) C / b ^ 2)) *
        C.variance := by
  exact R.largeDisplacementContributionOn_le (G := G) C S hz hb
    (R.maxVertexVarianceContribution_pos (G := G) C)
    (R.vertexVarianceContribution_le_max (G := G) C) hx

/-- Sequential consequence of (D.47): if a positive upper bound `mₙ` is
small relative to the squared displacement cutoff `bₙ`, then the restricted
large-displacement contribution is negligible, uniformly in the chosen sets.
This is the analytic contribution estimate used in D.6 before inserting
`bₙ = ε √Vₙ`. -/
theorem largeDisplacementContributionOn_tendsto_zero
    {W : ℕ → Type u} [∀ n, Fintype (W n)]
    (Γ : ∀ n, SimpleGraph (W n))
    (C : ∀ n, CanonicalFirstRecoveryState (Γ n))
    (R : ∀ n, ComponentRooting (Γ n))
    (S : ∀ n, Finset (W n)) (b m : ℕ → ℝ)
    (hz : ∀ n, (C n).activity < 27)
    (hmpos : ∀ n, 0 < m n)
    (hm : ∀ n u,
      (R n).vertexVarianceContribution (G := Γ n) (C n) u ≤ m n)
    (hb : Tendsto b atTop atTop)
    (hscale : Tendsto (fun n => m n / (b n) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (R n).largeDisplacementContributionOn (G := Γ n)
        (C n) (S n) (b n) / (C n).variance) atTop (𝓝 0) := by
  let x : ℕ → ℝ := fun n => 784 * m n / (b n) ^ 2
  have hx : Tendsto x atTop (𝓝 0) := by
    have h := hscale.const_mul (784 : ℝ)
    convert h using 1
    · funext n
      dsimp [x]
      ring
    · simp
  have hb2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ b n := (tendsto_atTop.1 hb) 2
  have hxpos : ∀ᶠ n in atTop, 0 < x n := by
    filter_upwards [hb2] with n hbn
    dsimp [x]
    exact div_pos (mul_pos (by norm_num) (hmpos n))
      (sq_pos_of_pos (by linarith))
  have hxlog : Tendsto (fun n => x n * Real.log (27 / x n))
      atTop (𝓝 0) :=
    tendsto_mul_log_twentySeven_div x hx hxpos
  have hupper : Tendsto (fun n => 112 * (x n * Real.log (27 / x n)))
      atTop (𝓝 0) := by
    simpa using hxlog.const_mul (112 : ℝ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
  · exact Eventually.of_forall fun n => by
      exact div_nonneg (by
        unfold largeDisplacementContributionOn
        apply Finset.sum_nonneg
        intro v hv
        split
        · exact (R n).vertexVarianceContribution_nonneg (G := Γ n) (C n) v
        · norm_num) (canonicalFirstRecovery_variance_pos (C n)).le
  · filter_upwards [hb2, hxpos,
      hx.eventually (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
      with n hbn hxn hxlt
    have hb1 : 1 < b n := by linarith
    have hfinite := (R n).largeDisplacementContributionOn_le (G := Γ n)
      (C n) (S n) (hz n) hb1 (hmpos n) (hm n) hxlt
    have hV := canonicalFirstRecovery_variance_pos (C n)
    have hratio0 : 0 ≤ b n / (b n - 1) :=
      div_nonneg (by linarith) (by linarith)
    have hratio2 : b n / (b n - 1) ≤ 2 := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith
    have hratiosq : (b n / (b n - 1)) ^ 2 ≤ 4 := by nlinarith
    have hlog0 : 0 ≤ Real.log (27 / x n) :=
      (Real.log_pos (by
        apply (lt_div_iff₀ hxn).2
        nlinarith)).le
    have hnormalized :
        (R n).largeDisplacementContributionOn (G := Γ n)
            (C n) (S n) (b n) / (C n).variance ≤
          (b n / (b n - 1)) ^ 2 * 28 * x n * Real.log (27 / x n) := by
      apply (div_le_iff₀ hV).2
      simpa [x] using hfinite
    calc
      (R n).largeDisplacementContributionOn (G := Γ n)
          (C n) (S n) (b n) / (C n).variance ≤
        (b n / (b n - 1)) ^ 2 * 28 * x n * Real.log (27 / x n) :=
          hnormalized
      _ ≤ 4 * 28 * x n * Real.log (27 / x n) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hratiosq (by norm_num)) hxn.le) hlog0
      _ = 112 * (x n * Real.log (27 / x n)) := by ring

/-- Literal pointwise bound used in (D.48); this is proved from the
occupation indicators and the genuine probability bounds, not postulated. -/
theorem abs_eta_le_one
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    |ActualMartingaleProjection.eta C R I u| ≤ 1 := by
  classical
  by_cases hparent :
      ActualMartingaleProjection.parentOccupationIndicator R I u = 0
  · rw [ActualMartingaleProjection.eta, hparent]
    simp only [sub_zero]
    by_cases hu : u ∈ I.val
    · rw [ActualMartingaleProjection.occupationIndicator]
      simp only [if_pos hu]
      rw [abs_of_nonneg]
      · linarith [R.occupationProbability_nonneg (G := G) C u]
      · linarith [R.occupationProbability_le_one (G := G) C u]
    · rw [ActualMartingaleProjection.occupationIndicator]
      simp only [if_neg hu, zero_sub, abs_neg, mul_one]
      rw [abs_of_nonneg (R.occupationProbability_nonneg (G := G) C u)]
      exact R.occupationProbability_le_one (G := G) C u
  · rw [ActualMartingaleProjection.eta_eq_zero_of_parentOccupationIndicator_ne_zero
      C R I u hparent]
    norm_num

theorem allowedOutside_mean_eq_sum_exposedAllowedPiece
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
      C.activity C.activity_pos).mean =
      ∑ u ∈ R.exposedBoundary (G := G) D,
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).mean := by
  classical
  change (hardCoreLaw
      (G.induce {x | x ∈ ActualMartingaleProjection.allowedOutsideVertices D I})
      C.activity C.activity_pos).mean = _
  rw [R.allowedOutsideVertices_eq_exposedAllowedUnion_D25 (G := G) C hD I]
  exact hardCoreLaw_mean_induceFinset_biUnion G
    (R.exposedBoundary (G := G) D)
    (fun u => R.exposedAllowedPiece (G := G) I u)
    (R.exposedAllowedPiece_pairwiseDisjoint (G := G) C hD I)
    (by
      intro u hu v hv huv x hxu y hyv
      exact R.exposedAllowedPiece_noCrossEdges (G := G) C hD I
        u hu v hv huv hxu hyv)
    C.activity C.activity_pos

private theorem phase_neg_sum_eq_prod
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℝ) (θ : ℝ) :
    FiniteLatticeLaw.phase θ (-∑ i ∈ s, m i) =
      ∏ i ∈ s, FiniteLatticeLaw.phase θ (-m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [show -(m a + ∑ i ∈ s, m i) = -m a + -(∑ i ∈ s, m i) by ring]
      rw [FiniteLatticeLaw.phase_add, ih]

 theorem allowedOutside_centeredCharacteristic_eq_prod_exposedAllowedPiece
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {D : Finset V} (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) (theta : ℝ) :
    (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
      C.activity C.activity_pos).centeredCharacteristic theta =
      ∏ u ∈ R.exposedBoundary (G := G) D,
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).centeredCharacteristic theta := by
  classical
  rw [FiniteLatticeLaw.centeredCharacteristic_eq_phase_mul]
  rw [R.allowedOutside_characteristic_eq_prod_exposedAllowedPiece_D25 (G := G) C hD I theta]
  rw [R.allowedOutside_mean_eq_sum_exposedAllowedPiece (G := G) C hD I]
  rw [phase_neg_sum_eq_prod]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u hu
  rw [FiniteLatticeLaw.centeredCharacteristic_eq_phase_mul]

theorem martingaleProjection_eq_restriction_card_add_allowedOutside_mean
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (D : Finset V) (hD : ActualMartingaleProjection.AncestorClosed R D)
    (I : IndepFinset G) :
    ActualMartingaleProjection.martingaleProjection C R D I =
      ((ActualMartingaleProjection.restriction D I).card : ℝ) +
      (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
        C.activity C.activity_pos).mean - C.index := by
  classical
  rw [← ActualMartingaleProjection.conditionalExpectation_centeredOccupationCount_eq_martingaleProjection
    C R D hD I]
  rw [ActualMartingaleProjection.conditionalExpectation_eq_allowedOutside]
  let H := hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
    C.activity C.activity_pos
  change (∑ T, H.probability T *
      ActualMartingaleProjection.centeredOccupationCount C
        (ActualMartingaleProjection.glueAllowedOutside D I T)) = _
  unfold ActualMartingaleProjection.centeredOccupationCount
  unfold ActualMartingaleProjection.occupationCount
  simp only [ActualMartingaleProjection.glueAllowedOutside_card, Nat.cast_add]
  unfold FiniteLatticeLaw.mean
  calc
    (∑ T, H.probability T *
        (((ActualMartingaleProjection.restriction D I).card : ℝ) +
          (T.val.card : ℝ) - C.index)) =
      (∑ T, H.probability T * (T.val.card : ℝ)) +
        (∑ T, H.probability T) *
          (((ActualMartingaleProjection.restriction D I).card : ℝ) - C.index) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro T hT
            ring
    _ = ((ActualMartingaleProjection.restriction D I).card : ℝ) +
        (∑ T, H.probability T * (T.val.card : ℝ)) - C.index := by
          rw [H.probability_sum]
          ring
    _ = _ := by rfl

theorem conditionalCenteredCharacteristic_eq_phase_mul_allowedOutside
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (D : Finset V) (I : IndepFinset G) (theta : ℝ) :
    ActualMartingaleProjection.conditionalExpectationComplex C D
      (fun J => FiniteLatticeLaw.phase theta
        (ActualMartingaleProjection.centeredOccupationCount C J)) I =
    FiniteLatticeLaw.phase theta (((ActualMartingaleProjection.restriction D I).card : ℝ) +
      (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
        C.activity C.activity_pos).mean - C.index) *
    (hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
      C.activity C.activity_pos).centeredCharacteristic theta := by
  classical
  rw [ActualMartingaleProjection.conditionalExpectationComplex_eq_allowedOutside]
  unfold FiniteLatticeLaw.centeredCharacteristic
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  let H := hardCoreLaw (ActualMartingaleProjection.AllowedOutsideGraph D I)
    C.activity C.activity_pos
  change (H.probability T : ℂ) * FiniteLatticeLaw.phase theta
      (ActualMartingaleProjection.centeredOccupationCount C
        (ActualMartingaleProjection.glueAllowedOutside D I T)) =
    FiniteLatticeLaw.phase theta
        (((ActualMartingaleProjection.restriction D I).card : ℝ) +
          H.mean - C.index) *
      ((H.probability T : ℂ) * FiniteLatticeLaw.phase theta
        ((T.val.card : ℝ) - H.mean))
  have harg :
      ActualMartingaleProjection.centeredOccupationCount C
          (ActualMartingaleProjection.glueAllowedOutside D I T) =
        (((ActualMartingaleProjection.restriction D I).card : ℝ) +
          H.mean - C.index) + ((T.val.card : ℝ) - H.mean) := by
    unfold ActualMartingaleProjection.centeredOccupationCount
    unfold ActualMartingaleProjection.occupationCount
    rw [ActualMartingaleProjection.glueAllowedOutside_card]
    simp only [Nat.cast_add]
    ring
  rw [harg, FiniteLatticeLaw.phase_add]
  ring

theorem antichainConditionalCenteredCharacteristic_eq_phase_mul_product
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (A : Finset V) (hA : R.IsRootedAntichain (G := G) A)
    (I : IndepFinset G) (theta : ℝ) :
    ActualMartingaleProjection.conditionalExpectationComplex C
      (R.antichainObservedSet (G := G) A)
      (fun J => FiniteLatticeLaw.phase theta
        (ActualMartingaleProjection.centeredOccupationCount C J)) I =
    FiniteLatticeLaw.phase theta
      (R.antichainConditionalMean (G := G) C A I) *
      ∏ u ∈ A,
        (hardCoreLaw
          (G.induce {x | x ∈ R.exposedAllowedPiece (G := G) I u})
          C.activity C.activity_pos).centeredCharacteristic theta := by
  let D := R.antichainObservedSet (G := G) A
  have hD : ActualMartingaleProjection.AncestorClosed R D :=
    R.antichainObservedSet_ancestorClosed (G := G) A
  rw [R.conditionalCenteredCharacteristic_eq_phase_mul_allowedOutside
    (G := G) C D I theta]
  rw [← R.martingaleProjection_eq_restriction_card_add_allowedOutside_mean
    (G := G) C D hD I]
  rw [R.allowedOutside_centeredCharacteristic_eq_prod_exposedAllowedPiece
    (G := G) C hD I theta]
  rw [R.exposedBoundary_antichainObservedSet (G := G) C A hA]
  rfl

end ComponentRooting

open Forest
open MeasureTheory
open ProbabilityTheory
open Forest.CanonicalCompactnessWrapper

structure ActualAntichainMixingSequence (S : CanonicalSequence) where
  rooting : ∀ n, ComponentRooting (S.graph n)
  antichain : ∀ n, Finset (Fin (S.order n))
  isRootedAntichain : ∀ n,
    (rooting n).IsRootedAntichain (G := S.graph n) (antichain n)
  c : ℝ
  B : ℝ
  c_pos : 0 < c
  c_le_one : c ≤ 1
  B_pos : 0 < B
  large : ∀ n, c * S.V n ≤
    ∑ u ∈ antichain n,
      (rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u

namespace ActualAntichainMixingSequence
variable {S : CanonicalSequence} (D : ActualAntichainMixingSequence S)

def conditionalVariance (n : ℕ) (I : IndepFinset (S.graph n)) : ℝ :=
  ∑ u ∈ D.antichain n,
    (D.rooting n).exposedConditionalVariance (G := S.graph n) (S.state n) I u

def conditionalMean (n : ℕ) (I : IndepFinset (S.graph n)) : ℝ :=
  (D.rooting n).antichainConditionalMean (G := S.graph n)
    (S.state n) (D.antichain n) I

def Good (n : ℕ) (I : IndepFinset (S.graph n)) : Prop :=
  (D.c / 2) * S.V n ≤ D.conditionalVariance n I ∧
  |D.conditionalMean n I| ≤ D.B * Real.sqrt (S.V n)

instance goodDecidable (n : ℕ) (I : IndepFinset (S.graph n)) :
    Decidable (D.Good n I) := Classical.propDecidable _

theorem conditionalMean_eq_of_restriction_eq (n : ℕ)
    {I J : IndepFinset (S.graph n)}
    (hIJ : ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) I =
      ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) J) :
    D.conditionalMean n I = D.conditionalMean n J := by
  let R := D.rooting n
  let A := D.antichain n
  let E := R.antichainObservedSet (G := S.graph n) A
  have hE : ActualMartingaleProjection.AncestorClosed R E :=
    R.antichainObservedSet_ancestorClosed (G := S.graph n) A
  unfold conditionalMean ComponentRooting.antichainConditionalMean
  rw [← ActualMartingaleProjection.conditionalExpectation_centeredOccupationCount_eq_martingaleProjection
    (S.state n) R E hE I]
  rw [← ActualMartingaleProjection.conditionalExpectation_centeredOccupationCount_eq_martingaleProjection
    (S.state n) R E hE J]
  exact ActualMartingaleProjection.conditionalExpectation_eq_of_restriction_eq
    (S.state n) E _ hIJ

theorem conditionalVariance_eq_of_restriction_eq (n : ℕ)
    {I J : IndepFinset (S.graph n)}
    (hIJ : ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) I =
      ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) J) :
    D.conditionalVariance n I = D.conditionalVariance n J := by
  classical
  let R := D.rooting n
  let A := D.antichain n
  let E := R.antichainObservedSet (G := S.graph n) A
  have hboundary : R.exposedBoundary (G := S.graph n) E = A :=
    R.exposedBoundary_antichainObservedSet (G := S.graph n)
      (S.state n) A (D.isRootedAntichain n)
  unfold conditionalVariance ComponentRooting.exposedConditionalVariance
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have huB : u ∈ R.exposedBoundary (G := S.graph n) E := by
    rw [hboundary]
    exact hu
  have hpind : ActualMartingaleProjection.parentOccupationIndicator R I u =
      ActualMartingaleProjection.parentOccupationIndicator R J u := by
    unfold ActualMartingaleProjection.parentOccupationIndicator
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpu : R.IsChild (G := S.graph n) p u
    · simp only [if_pos hpu]
      have hpE : p ∈ E := by
        rcases (R.mem_exposedBoundary (G := S.graph n) E u).mp huB with
          ⟨_, hroot | ⟨q, hqE, hqu⟩⟩
        · exact False.elim (R.not_isChild_of_eq_root (G := S.graph n) hroot hpu)
        · have hpq : p = q := R.isChild_unique (G := S.graph n)
            (S.state n).isForest hpu hqu
          simpa [hpq] using hqE
      rw [ActualMartingaleProjection.occupationIndicator_eq_of_restriction_eq hpE hIJ]
    · simp only [if_neg hpu]
  rw [hpind]

theorem good_iff_of_restriction_eq (n : ℕ)
    {I J : IndepFinset (S.graph n)}
    (hIJ : ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) I =
      ActualMartingaleProjection.restriction
      ((D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)) J) :
    D.Good n I ↔ D.Good n J := by
  unfold Good
  rw [D.conditionalMean_eq_of_restriction_eq n hIJ,
    D.conditionalVariance_eq_of_restriction_eq n hIJ]

theorem restrictedGlobalCharacteristic_eq_conditionalProduct
    (n : ℕ) (t : ℝ) :
    (∑ I : IndepFinset (S.graph n), ((S.state n).law.probability I : ℂ) *
      (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
        FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
          (ActualMartingaleProjection.centeredOccupationCount (S.state n) I))) =
    ∑ I : IndepFinset (S.graph n), ((S.state n).law.probability I : ℂ) *
      (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
        (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
          (D.conditionalMean n I) *
          ∏ u ∈ D.antichain n,
            (hardCoreLaw
              ((S.graph n).induce {x | x ∈ (D.rooting n).exposedAllowedPiece
                (G := S.graph n) I u})
              (S.state n).activity (S.state n).activity_pos).centeredCharacteristic
                (t / Real.sqrt (S.V n)))) := by
  let E := (D.rooting n).antichainObservedSet (G := S.graph n) (D.antichain n)
  let h : IndepFinset (S.graph n) → ℂ := fun I =>
    ((if D.Good n I then 1 else 0 : ℝ) : ℂ)
  let f : IndepFinset (S.graph n) → ℂ := fun I =>
    FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
      (ActualMartingaleProjection.centeredOccupationCount (S.state n) I)
  have hh : ∀ I J, ActualMartingaleProjection.restriction E I =
      ActualMartingaleProjection.restriction E J → h I = h J := by
    intro I J hIJ
    have hg := D.good_iff_of_restriction_eq n hIJ
    dsimp [h]
    by_cases hI : D.Good n I <;> by_cases hJ : D.Good n J <;> simp_all
  have ht := ActualMartingaleProjection.lawExpectation_fiberInvariant_mul_conditionalExpectationComplex
    (S.state n) E h f hh
  rw [show E = (D.rooting n).antichainObservedSet
      (G := S.graph n) (D.antichain n) by rfl] at ht
  have hfac := fun I => (D.rooting n).antichainConditionalCenteredCharacteristic_eq_phase_mul_product
    (G := S.graph n) (S.state n) (D.antichain n)
    (D.isRootedAntichain n) I (t / Real.sqrt (S.V n))
  unfold f h at ht
  simp only [hfac] at ht
  exact ht.symm

def rectangle : Set (ℝ × ℝ) :=
  Set.Icc (-D.B) D.B ×ˢ Set.Icc (D.c / 2) 784

abbrev Rectangle := {x : ℝ × ℝ // x ∈ D.rectangle}

private theorem rectangle_nonempty : D.rectangle.Nonempty := by
  refine ⟨(0, D.c / 2), ?_⟩
  exact ⟨⟨by linarith [D.B_pos], D.B_pos.le⟩,
    ⟨le_rfl, by linarith [D.c_le_one]⟩⟩

private theorem rectangle_compact : IsCompact D.rectangle :=
  isCompact_Icc.prod isCompact_Icc

private theorem normalizedMean_mem_Icc (n : ℕ)
    (I : IndepFinset (S.graph n)) (hI : D.Good n I) :
    D.conditionalMean n I / Real.sqrt (S.V n) ∈ Set.Icc (-D.B) D.B := by
  have hs : 0 < Real.sqrt (S.V n) := Real.sqrt_pos.2 (S.variance_pos n)
  constructor
  · have hneg := neg_abs_le (D.conditionalMean n I)
    apply (le_div_iff₀ hs).2
    nlinarith [hI.2]
  · exact (div_le_iff₀ hs).2 ((le_abs_self _).trans hI.2)

private theorem normalizedVariance_mem_Icc (n : ℕ)
    (I : IndepFinset (S.graph n)) (hI : D.Good n I) :
    D.conditionalVariance n I / S.V n ∈ Set.Icc (D.c / 2) 784 := by
  have hV := S.variance_pos n
  constructor
  · exact (le_div_iff₀ hV).2 hI.1
  · apply (div_le_iff₀ hV).2
    exact (D.rooting n).sum_exposedConditionalVariance_le_variance_D27
      (G := S.graph n) (S.state n) (S.activity_lt n) (D.antichain n)
      (D.isRootedAntichain n) I

def point (n : ℕ) (I : {I : IndepFinset (S.graph n) // D.Good n I}) : D.Rectangle :=
  ⟨(D.conditionalMean n I / Real.sqrt (S.V n),
      D.conditionalVariance n I / S.V n),
    ⟨D.normalizedMean_mem_Icc n I I.property,
      D.normalizedVariance_mem_Icc n I I.property⟩⟩

def mixingMeasure (n : ℕ) : FiniteMeasure D.Rectangle :=
  ∑ I : {I : IndepFinset (S.graph n) // D.Good n I},
    Real.toNNReal ((S.state n).law.probability I) • finiteDirac (D.point n I)

theorem mixingMeasure_mass_coe (n : ℕ) :
    ((D.mixingMeasure n).mass : ℝ) =
      ∑ I ∈ Finset.univ.filter (fun I : IndepFinset (S.graph n) => D.Good n I),
        (S.state n).law.probability I := by
  classical
  rw [show (∑ I ∈ Finset.univ.filter (fun I : IndepFinset (S.graph n) => D.Good n I),
        (S.state n).law.probability I) =
      ∑ I : {I : IndepFinset (S.graph n) // D.Good n I},
        (S.state n).law.probability I by
    exact (Finset.sum_subtype (Finset.univ.filter fun I : IndepFinset (S.graph n) => D.Good n I)
      (fun I => by simp) (fun I => (S.state n).law.probability I))]
  simp only [mixingMeasure, finiteMeasure_mass_sum,
    finiteMeasure_mass_smul, finiteDirac_mass, mul_one, NNReal.coe_sum]
  apply Finset.sum_congr rfl
  intro I hI
  exact Real.coe_toNNReal _ ((S.state n).law.probability_nonneg I)

theorem mixingMeasure_mass_lower_D35 (p0 : ℝ)
    (hp0 : p0 ≤ (D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2)
    (n : ℕ) : p0 ≤ ((D.mixingMeasure n).mass : ℝ) := by
  rw [D.mixingMeasure_mass_coe n]
  have h := (D.rooting n).antichain_jointGood_mass_lower_bound_D34
    (G := S.graph n) (S.state n) (S.activity_lt n) (D.antichain n)
    (D.isRootedAntichain n) D.c D.B D.c_le_one D.B_pos (D.large n)
  have heq :
      Finset.univ.filter (fun I : IndepFinset (S.graph n) => D.Good n I) =
      Finset.univ.filter (fun I : IndepFinset (S.graph n) =>
        (D.c / 2) * (S.state n).variance ≤
            ∑ u ∈ D.antichain n,
              (D.rooting n).exposedConditionalVariance
                (G := S.graph n) (S.state n) I u ∧
          |(D.rooting n).antichainConditionalMean
              (G := S.graph n) (S.state n) (D.antichain n) I| ≤
            D.B * Real.sqrt (S.state n).variance) := by
    ext I
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  rw [heq]
  exact hp0.trans h

theorem mixingMeasure_mass_le_one_D35 (n : ℕ) :
    (D.mixingMeasure n).mass ≤ 1 := by
  apply NNReal.coe_le_coe.1
  rw [D.mixingMeasure_mass_coe n]
  calc
    (∑ I ∈ Finset.univ.filter (fun I : IndepFinset (S.graph n) => D.Good n I),
      (S.state n).law.probability I) ≤
        ∑ I : IndepFinset (S.graph n), (S.state n).law.probability I := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro I hI hnot
      exact (S.state n).law.probability_nonneg I
    _ = 1 := (S.state n).law.probability_sum

/-- D.35: positive compact-subtype weak extraction for the literal global-law
mixing subprobabilities. -/
theorem exists_compact_mixing_limit_D35 (p0 : ℝ) (hp0 : 0 < p0)
    (hbelow : p0 ≤ (D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2) :
    ∃ q : ℝ≥0, ∃ π : ProbabilityMeasure D.Rectangle, ∃ φ : ℕ → ℕ,
      Real.toNNReal p0 ≤ q ∧ q ≤ 1 ∧ StrictMono φ ∧
      Tendsto (D.mixingMeasure ∘ φ) atTop
        (𝓝 (q • π.toFiniteMeasure)) := by
  letI : CompactSpace D.Rectangle :=
    isCompact_iff_compactSpace.mp D.rectangle_compact
  letI : Nonempty D.Rectangle := D.rectangle_nonempty.to_subtype
  apply exists_subseq_finiteMeasure_compact_normalize_D35
  · intro n
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hp0.le]
    exact D.mixingMeasure_mass_lower_D35 p0 hbelow n
  · exact D.mixingMeasure_mass_le_one_D35


/-- The same mixing subprobability, viewed on the ambient parameter plane. -/
def ambientMixingMeasure (n : ℕ) : FiniteMeasure (ℝ × ℝ) :=
  (D.mixingMeasure n).map Subtype.val

private theorem map_subtype_mass
    (μ : FiniteMeasure D.Rectangle) :
    (μ.map Subtype.val).mass = μ.mass := by
  change (μ.map Subtype.val) Set.univ = μ Set.univ
  rw [FiniteMeasure.map_apply _ continuous_subtype_val.measurable MeasurableSet.univ]
  rfl

@[simp] theorem ambientMixingMeasure_mass (n : ℕ) :
    (D.ambientMixingMeasure n).mass = (D.mixingMeasure n).mass := by
  exact D.map_subtype_mass (D.mixingMeasure n)

theorem ambientMixingMeasure_compl_rectangle (n : ℕ) :
    D.ambientMixingMeasure n D.rectangleᶜ = 0 := by
  have hrect : IsCompact D.rectangle := isCompact_Icc.prod isCompact_Icc
  rw [ambientMixingMeasure,
    FiniteMeasure.map_apply _ continuous_subtype_val.measurable
      hrect.isClosed.measurableSet.compl]
  simp [Rectangle]

/-- Ambient-plane form of D.35, with positive mass, subprobability mass and
support in the fixed compact rectangle. -/
theorem exists_ambient_mixing_limit_D35 (p0 : ℝ) (hp0 : 0 < p0)
    (hbelow : p0 ≤ (D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2) :
    ∃ φ : ℕ → ℕ, ∃ ν : FiniteMeasure (ℝ × ℝ),
      StrictMono φ ∧
      Tendsto (D.ambientMixingMeasure ∘ φ) atTop (𝓝 ν) ∧
      Real.toNNReal p0 ≤ ν.mass ∧ ν.mass ≤ 1 ∧
      ν D.rectangleᶜ = 0 := by
  obtain ⟨q, π, φ, hq, hq1, hφ, hlim⟩ :=
    D.exists_compact_mixing_limit_D35 p0 hp0 hbelow
  let ν : FiniteMeasure (ℝ × ℝ) :=
    (q • π.toFiniteMeasure).map Subtype.val
  have hmassν : ν.mass = q := by
    change ((q • π.toFiniteMeasure).map Subtype.val).mass = q
    rw [D.map_subtype_mass]
    simp [FiniteMeasure.mass]
  refine ⟨φ, ν, hφ, ?_, ?_, ?_, ?_⟩
  · have hm := FiniteMeasure.tendsto_map_of_tendsto_of_continuous
      (D.mixingMeasure ∘ φ) (q • π.toFiniteMeasure) hlim
      continuous_subtype_val
    simpa [ambientMixingMeasure, Function.comp_def, ν] using hm
  · rw [hmassν]
    exact hq
  · rw [hmassν]
    exact hq1
  · change ((q • π.toFiniteMeasure).map Subtype.val) D.rectangleᶜ = 0
    have hrect : IsCompact D.rectangle := isCompact_Icc.prod isCompact_Icc
    rw [FiniteMeasure.map_apply _ continuous_subtype_val.measurable
      hrect.isClosed.measurableSet.compl]
    simp [Rectangle]
def gaussianDensityKernel (x : ℝ) (z : D.Rectangle) : ℝ :=
  (Real.sqrt (2 * Real.pi * z.1.2))⁻¹ *
    Real.exp (-((x - z.1.1) ^ 2) / (2 * z.1.2))

theorem gaussianDensityKernel_pos (x : ℝ) (z : D.Rectangle) :
    0 < D.gaussianDensityKernel x z := by
  have hw : 0 < z.1.2 := lt_of_lt_of_le (half_pos D.c_pos) z.2.2.1
  dsimp [gaussianDensityKernel]
  positivity

theorem continuous_gaussianDensityKernel (x : ℝ) :
    Continuous (D.gaussianDensityKernel x) := by
  unfold gaussianDensityKernel
  have hwc : Continuous (fun z : D.Rectangle => z.1.2) := by fun_prop
  have hw0 : ∀ z : D.Rectangle, z.1.2 ≠ 0 := fun z => by
    have hw : 0 < z.1.2 := lt_of_lt_of_le (half_pos D.c_pos) z.2.2.1
    exact ne_of_gt hw
  have hsqrt : Continuous (fun z : D.Rectangle =>
      Real.sqrt (2 * Real.pi * z.1.2)) :=
    (continuous_const.mul hwc).sqrt
  have hsqrt0 : ∀ z : D.Rectangle,
      Real.sqrt (2 * Real.pi * z.1.2) ≠ 0 := fun z => by
    have hw : 0 < z.1.2 := lt_of_lt_of_le (half_pos D.c_pos) z.2.2.1
    positivity
  have hnum : Continuous (fun z : D.Rectangle => -((x - z.1.1) ^ 2)) := by
    fun_prop
  have hden : Continuous (fun z : D.Rectangle => 2 * z.1.2) :=
    continuous_const.mul hwc
  exact (hsqrt.inv₀ hsqrt0).mul
    (Real.continuous_exp.comp (hnum.div hden (fun z => by
      exact mul_ne_zero (by norm_num) (hw0 z))))

def gaussianMixtureDensity (ν : FiniteMeasure D.Rectangle) (x : ℝ) : ℝ :=
  ∫ z, D.gaussianDensityKernel x z ∂ν

theorem gaussianDensityKernel_integrable
    (ν : FiniteMeasure D.Rectangle) (x : ℝ) :
    Integrable (D.gaussianDensityKernel x) ν := by
  have hrect : IsCompact D.rectangle := isCompact_Icc.prod isCompact_Icc
  letI : CompactSpace D.Rectangle :=
    isCompact_iff_compactSpace.mp (by simpa [Rectangle] using hrect)
  exact (D.continuous_gaussianDensityKernel x).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem gaussianMixtureDensity_pos
    (ν : FiniteMeasure D.Rectangle) (hν : 0 < ν.mass) (x : ℝ) :
    0 < D.gaussianMixtureDensity ν x := by
  rw [gaussianMixtureDensity]
  rw [integral_pos_iff_support_of_nonneg
    (fun z => (D.gaussianDensityKernel_pos x z).le)
    (D.gaussianDensityKernel_integrable ν x)]
  have hsupp : Function.support (D.gaussianDensityKernel x) = Set.univ := by
    ext z
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (D.gaussianDensityKernel_pos x z)
  rw [hsupp, Measure.measure_univ_pos]
  intro hzero
  apply (ne_of_gt hν)
  simp [FiniteMeasure.mass, hzero]

theorem gaussianMixtureDensity_zero_pos_D37
    (q : ℝ≥0) (hq : 0 < q) (π : ProbabilityMeasure D.Rectangle) :
    0 < D.gaussianMixtureDensity (q • π.toFiniteMeasure) 0 := by
  apply D.gaussianMixtureDensity_pos
  simpa using hq

def gaussianCharacteristicKernel (t : ℝ) (z : D.Rectangle) : ℂ :=
  Complex.exp (((t * z.1.1 : ℝ) : ℂ) * Complex.I -
    ((z.1.2 * t ^ 2 / 2 : ℝ) : ℂ))

theorem phase_mul_conditionalGaussian_eq_kernel
    (n : ℕ) (I : IndepFinset (S.graph n)) (hI : D.Good n I) (t : ℝ) :
    FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
      Complex.exp (((-((t / Real.sqrt (S.V n)) ^ 2 / 2 *
        D.conditionalVariance n I) : ℝ) : ℂ)) =
    D.gaussianCharacteristicKernel t (D.point n ⟨I, hI⟩) := by
  have hV : 0 < S.V n := S.variance_pos n
  have hs : 0 < Real.sqrt (S.V n) := Real.sqrt_pos.2 hV
  have hs2 : (Real.sqrt (S.V n)) ^ 2 = S.V n := by
    exact (Real.sq_sqrt hV.le)
  rw [FiniteLatticeLaw.phase, ← Complex.exp_add]
  apply congrArg Complex.exp
  simp only [point]
  push_cast
  have hs2c : (Real.sqrt (S.V n) : ℂ) ^ 2 = (S.V n : ℂ) := by
    exact_mod_cast hs2
  have hinv : ((Real.sqrt (S.V n) : ℂ)⁻¹) ^ 2 = ((S.V n : ℂ)⁻¹) := by
    rw [inv_pow, hs2c]
  ring_nf
  rw [hinv]
  ring

theorem mixingMeasure_integral_gaussianCharacteristicKernel
    (n : ℕ) (t : ℝ) :
    ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure n =
      ∑ I : {I : IndepFinset (S.graph n) // D.Good n I},
        ((S.state n).law.probability I : ℂ) *
          D.gaussianCharacteristicKernel t (D.point n I) := by
  classical
  unfold mixingMeasure
  rw [MeasureTheory.FiniteMeasure.toMeasure_sum]
  rw [MeasureTheory.integral_finset_sum_measure]
  · refine @Finset.sum_congr _ ℂ
      (@Finset.univ _ (finiteSubtypeAppendixD (D.Good n)))
      (@Finset.univ _ (finiteSubtypeAppendixD (D.Good n))) _ _ _ rfl ?_
    intro I hI
    rw [MeasureTheory.FiniteMeasure.toMeasure_smul]
    rw [MeasureTheory.integral_smul_nnreal_measure]
    rw [show (↑(finiteDirac (D.point n I)) :
      Measure D.Rectangle) = Measure.dirac (D.point n I) by rfl]
    rw [MeasureTheory.integral_dirac]
    change (((((S.state n).law.probability I).toNNReal : ℝ) : ℂ) *
      D.gaussianCharacteristicKernel t (D.point n I)) = _
    rw [Real.coe_toNNReal _ ((S.state n).law.probability_nonneg I)]
  · intro I hI
    apply MeasureTheory.Integrable.smul_measure
    · exact MeasureTheory.integrable_dirac (by simp)
    · exact ENNReal.coe_ne_top

theorem mixingIntegral_eq_fullGoodGaussian (n : ℕ) (t : ℝ) :
    ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure n =
    ∑ I : IndepFinset (S.graph n), ((S.state n).law.probability I : ℂ) *
      (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
        (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
          Complex.exp (((-((t / Real.sqrt (S.V n)) ^ 2 / 2 *
            D.conditionalVariance n I) : ℝ) : ℂ)))) := by
  classical
  letI : Fintype {I : IndepFinset (S.graph n) // D.Good n I} :=
    finiteSubtypeAppendixD (D.Good n)
  rw [D.mixingMeasure_integral_gaussianCharacteristicKernel n t]
  calc
    (∑ I : {I : IndepFinset (S.graph n) // D.Good n I},
        ((S.state n).law.probability I : ℂ) *
          D.gaussianCharacteristicKernel t (D.point n I)) =
      ∑ I : {I : IndepFinset (S.graph n) // D.Good n I},
        ((S.state n).law.probability I : ℂ) *
          (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
            Complex.exp (((-((t / Real.sqrt (S.V n)) ^ 2 / 2 *
              D.conditionalVariance n I) : ℝ) : ℂ))) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [D.phase_mul_conditionalGaussian_eq_kernel n I I.property t]
    _ = ∑ I ∈ Finset.univ.filter (fun I : IndepFinset (S.graph n) => D.Good n I),
        ((S.state n).law.probability I : ℂ) *
          (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
            Complex.exp (((-((t / Real.sqrt (S.V n)) ^ 2 / 2 *
              D.conditionalVariance n I) : ℝ) : ℂ))) := by
        symm
        exact Finset.sum_subtype _ (fun I => by simp) _
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro I hI
      by_cases h : D.Good n I <;> simp [h]

theorem restrictedCharacteristic_gaussian_norm_le_D30 (n : ℕ) (t : ℝ) :
    ‖(∑ I : IndepFinset (S.graph n), ((S.state n).law.probability I : ℂ) *
      (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
        FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
          (ActualMartingaleProjection.centeredOccupationCount (S.state n) I))) -
      ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure n‖ ≤
    ∑ I : IndepFinset (S.graph n), (S.state n).law.probability I *
      ComponentRooting.exposedConditionalGaussianProductError (S.state n) (D.rooting n)
        (D.antichain n) I t := by
  classical
  rw [D.restrictedGlobalCharacteristic_eq_conditionalProduct n t,
    D.mixingIntegral_eq_fullGoodGaussian n t]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ I : IndepFinset (S.graph n),
        ‖((S.state n).law.probability I : ℂ) *
          (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
            (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
              ∏ u ∈ D.antichain n,
                (hardCoreLaw
                  ((S.graph n).induce {x | x ∈ (D.rooting n).exposedAllowedPiece
                    (G := S.graph n) I u})
                  (S.state n).activity (S.state n).activity_pos).centeredCharacteristic
                    (t / Real.sqrt (S.V n)))) -
          ((S.state n).law.probability I : ℂ) *
          (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
            (FiniteLatticeLaw.phase (t / Real.sqrt (S.V n)) (D.conditionalMean n I) *
              Complex.exp (((-((t / Real.sqrt (S.V n)) ^ 2 / 2 *
                D.conditionalVariance n I) : ℝ) : ℂ))))‖ := by
          exact norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases h : D.Good n I
      · simp only [h, if_true, Complex.ofReal_one, one_mul]
        rw [← mul_sub, ← mul_sub]
        simp only [norm_mul, FiniteLatticeLaw.phase, Complex.norm_exp,
          Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.exp_zero,
          mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ((S.state n).law.probability_nonneg I)]
        unfold ComponentRooting.exposedConditionalGaussianProductError
        unfold conditionalVariance CanonicalSequence.V
        simp only [one_mul]
        exact le_rfl
      · simp only [h, if_false, Complex.ofReal_zero, zero_mul, mul_zero, sub_self,
          norm_zero]
        exact mul_nonneg ((S.state n).law.probability_nonneg I) (norm_nonneg _)

theorem continuous_gaussianCharacteristicKernel (t : ℝ) :
    Continuous (D.gaussianCharacteristicKernel t) := by
  unfold gaussianCharacteristicKernel
  fun_prop

theorem restrictedCharacteristic_norm_tendsto_zero_of_diffuse_D30
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon)
    (t : ℝ) :
    Tendsto
      (fun n => ‖(∑ I : IndepFinset (S.graph n),
        ((S.state n).law.probability I : ℂ) *
          (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
            FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
              (ActualMartingaleProjection.centeredOccupationCount (S.state n) I))) -
        ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure n‖)
      atTop (𝓝 0) := by
  have herr :=
    ComponentRooting.exposedConditionalGaussianProductError_tendsto_zero_of_diffuse_D30
      (fun n => Fin (S.order n)) S.graph S.state D.rooting D.antichain
      D.isRootedAntichain S.activity_lt S.variance_pos S.variance_tendsto
      hdiffuse t
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0)) herr
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      D.restrictedCharacteristic_gaussian_norm_le_D30 n t

def standardizedConfiguration (D : ActualAntichainMixingSequence S)
    (n : ℕ) (I : IndepFinset (S.graph n)) : ℝ :=
  (((S.state n).law.stat I : ℝ) - ((S.state n).index : ℝ)) /
    Real.sqrt (S.V n)

private theorem measurable_standardizedConfiguration (n : ℕ) :
    Measurable (D.standardizedConfiguration n) := measurable_of_finite _

noncomputable def goodStandardizedSubmeasure (n : ℕ) : FiniteMeasure ℝ :=
  ((actualConfigurationLaw (S.state n)).toFiniteMeasure.restrict
      {I | D.Good n I}).map (D.standardizedConfiguration n)

theorem goodStandardizedSubmeasure_le_fullMap (n : ℕ) :
    (D.goodStandardizedSubmeasure n : Measure ℝ) ≤
      (((actualConfigurationLaw (S.state n)).toFiniteMeasure.map
        (D.standardizedConfiguration n) : FiniteMeasure ℝ) : Measure ℝ) := by
  unfold goodStandardizedSubmeasure
  simpa only [FiniteMeasure.toMeasure_map, FiniteMeasure.restrict_measure_eq] using
    Measure.map_mono (Measure.restrict_le_self :
      ((actualConfigurationLaw (S.state n) : Measure (IndepFinset (S.graph n))).restrict
        {I | D.Good n I}) ≤ (actualConfigurationLaw (S.state n) : Measure _))
      (D.measurable_standardizedConfiguration n)

theorem fullStandardizedConfigurationLaw_eq (n : ℕ) :
    ((actualConfigurationLaw (S.state n)).toFiniteMeasure.map
        (D.standardizedConfiguration n)) =
      (S.standardizedLaw n).toFiniteMeasure := by
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  change
    (∫ x, f x ∂Measure.map (D.standardizedConfiguration n)
      (actualConfigurationLaw (S.state n) : Measure (IndepFinset (S.graph n)))) =
      ∫ x, f x ∂(S.standardizedLaw n : Measure ℝ)
  rw [MeasureTheory.integral_map
      (D.measurable_standardizedConfiguration n).aemeasurable
      f.continuous.aestronglyMeasurable,
    S.integral_standardizedLaw_of_continuous n f.continuous]
  change
    (∫ I, f (D.standardizedConfiguration n I)
      ∂(actualConfigurationPMF (S.state n)).toMeasure) =
      ∑ k : Fin (S.order n + 1),
        (S.state n).law.rankMass (k : ℕ) * f (S.standardizedRank n k)
  rw [PMF.integral_eq_sum]
  simp only [actualConfigurationPMF_apply_toReal, smul_eq_mul]
  let g : ℕ → ℝ := fun k =>
    f (((k : ℝ) - ((S.state n).index : ℝ)) / Real.sqrt (S.V n))
  have hstat : ∀ I : IndepFinset (S.graph n),
      (S.state n).law.stat I ≤ S.order n := by
    intro I
    simpa [CanonicalFirstRecoveryState.order] using
      hardCoreLaw_stat_le_order (S.graph n) (S.state n).activity
        (S.state n).activity_pos I
  have hgroup := (S.state n).law.sum_probability_mul_eq_sum_rankMass
    (S.order n) hstat g
  change
    (∑ I : IndepFinset (S.graph n),
      (S.state n).law.probability I * g ((S.state n).law.stat I)) =
      ∑ k : Fin (S.order n + 1),
        (S.state n).law.rankMass (k : ℕ) * g (k : ℕ)
  calc
    _ = ∑ k ∈ Finset.range (S.order n + 1),
          (S.state n).law.rankMass k * g k := hgroup
    _ = _ := by
      symm
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (S.state n).law.rankMass k * g k)
        (S.order n + 1)

theorem goodStandardizedSubmeasure_le_standardizedLaw (n : ℕ) :
    (D.goodStandardizedSubmeasure n : Measure ℝ) ≤
      (S.standardizedLaw n : Measure ℝ) := by
  calc
    (D.goodStandardizedSubmeasure n : Measure ℝ) ≤
        (((actualConfigurationLaw (S.state n)).toFiniteMeasure.map
          (D.standardizedConfiguration n) : FiniteMeasure ℝ) : Measure ℝ) :=
      D.goodStandardizedSubmeasure_le_fullMap n
    _ = (S.standardizedLaw n : Measure ℝ) := by
      exact congrArg FiniteMeasure.toMeasure
        (D.fullStandardizedConfigurationLaw_eq n)

/-- Domination of finite real measures is closed under simultaneous weak convergence. -/
theorem goodStandardizedSubmeasure_integral_exp (n : ℕ) (t : ℝ) :
    (∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
      ∂D.goodStandardizedSubmeasure n) =
    ∑ I : IndepFinset (S.graph n), ((S.state n).law.probability I : ℂ) *
      (((if D.Good n I then 1 else 0 : ℝ) : ℂ) *
        FiniteLatticeLaw.phase (t / Real.sqrt (S.V n))
          (ActualMartingaleProjection.centeredOccupationCount (S.state n) I)) := by
  classical
  unfold goodStandardizedSubmeasure
  change ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) ∂Measure.map
      (D.standardizedConfiguration n)
      ((actualConfigurationLaw (S.state n) : Measure (IndepFinset (S.graph n))).restrict
        {I | D.Good n I}) = _
  rw [MeasureTheory.integral_map
    (measurable_of_finite (D.standardizedConfiguration n)).aemeasurable
    (by fun_prop : Continuous (fun x : ℝ =>
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable]
  rw [← MeasureTheory.integral_indicator (show MeasurableSet {I : IndepFinset (S.graph n) |
    D.Good n I} from by exact MeasurableSet.of_discrete)]
  change (∫ I, ({I : IndepFinset (S.graph n) | D.Good n I}.indicator
      (fun I => Complex.exp (((t * D.standardizedConfiguration n I : ℝ) : ℂ) * Complex.I)) I)
      ∂(actualConfigurationPMF (S.state n)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [actualConfigurationPMF_apply_toReal, smul_eq_mul]
  by_cases h : D.Good n I
  · simp only [Set.indicator, Set.mem_setOf_eq, h, if_true,
      Complex.ofReal_one, one_mul]
    change ((S.state n).law.probability I : ℂ) *
      Complex.exp (((t * D.standardizedConfiguration n I : ℝ) : ℂ) * Complex.I) = _
    congr 1
    unfold standardizedConfiguration ActualMartingaleProjection.centeredOccupationCount
    unfold ActualMartingaleProjection.occupationCount
    unfold CanonicalFirstRecoveryState.law hardCoreLaw
    rw [FiniteLatticeLaw.phase]
    apply congrArg Complex.exp
    push_cast
    ring
  · simp [Set.indicator, h]

theorem finiteRealMeasure_toMeasure_le_of_tendsto
    {ι : Type*} {L : Filter ι} [NeBot L]
    {μs νs : ι → FiniteMeasure ℝ} {μ ν : FiniteMeasure ℝ}
    (hμ : Tendsto μs L (𝓝 μ)) (hν : Tendsto νs L (𝓝 ν))
    (hle : ∀ i, (μs i : Measure ℝ) ≤ (νs i : Measure ℝ)) :
    (μ : Measure ℝ) ≤ (ν : Measure ℝ) := by
  have htest : ∀ f : BoundedContinuousFunction ℝ ℝ≥0,
      (∫⁻ x, f x ∂(μ : Measure ℝ)) ≤ ∫⁻ x, f x ∂(ν : Measure ℝ) := by
    intro f
    exact le_of_tendsto_of_tendsto'
      ((FiniteMeasure.tendsto_iff_forall_lintegral_tendsto).1 hμ f)
      ((FiniteMeasure.tendsto_iff_forall_lintegral_tendsto).1 hν f)
      (fun i => lintegral_mono' (hle i) le_rfl)
  have hclosed : ∀ F : Set ℝ, IsClosed F →
      (μ : Measure ℝ) F ≤ (ν : Measure ℝ) F := by
    intro F hF
    exact le_of_tendsto_of_tendsto'
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (μ : Measure ℝ))
      (HasOuterApproxClosed.tendsto_lintegral_apprSeq hF (ν : Measure ℝ))
      (fun n => htest (hF.apprSeq n))
  refine Measure.le_iff.2 fun A hA => ?_
  rw [hA.measure_eq_iSup_isClosed_of_ne_top
    (measure_ne_top (μ : Measure ℝ) A)]
  refine iSup_le fun F => ?_
  refine iSup_le fun hFA => ?_
  refine iSup_le fun hF => ?_
  exact (hclosed F hF).trans (measure_mono hFA)

theorem goodStandardizedSubmeasure_gaussianCharacteristic_norm_tendsto_zero
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon)
    (t : ℝ) :
    Tendsto (fun n => ‖
      (∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
        ∂D.goodStandardizedSubmeasure n) -
      ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure n‖)
      atTop (𝓝 0) := by
  simpa only [D.goodStandardizedSubmeasure_integral_exp] using
    D.restrictedCharacteristic_norm_tendsto_zero_of_diffuse_D30 hdiffuse t

theorem gaussianCharacteristic_integral_tendsto_D36
    (μ : ℕ → FiniteMeasure D.Rectangle) (ν : FiniteMeasure D.Rectangle)
    (hμ : Tendsto μ atTop (𝓝 ν)) (t : ℝ) :
    Tendsto (fun n => ∫ z, D.gaussianCharacteristicKernel t z ∂μ n)
      atTop (𝓝 (∫ z, D.gaussianCharacteristicKernel t z ∂ν)) := by
  have hrect : IsCompact D.rectangle := isCompact_Icc.prod isCompact_Icc
  letI : CompactSpace D.Rectangle :=
    isCompact_iff_compactSpace.mp (by simpa [Rectangle] using hrect)
  let f : BoundedContinuousFunction D.Rectangle ℂ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨D.gaussianCharacteristicKernel t,
        D.continuous_gaussianCharacteristicKernel t⟩
  have h :=
    (FiniteMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hμ f
  simpa [f] using h

theorem goodStandardizedSubmeasure_integral_exp_tendsto_D36
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : FiniteMeasure D.Rectangle)
    (hμ : Tendsto (fun n => D.mixingMeasure (φ n)) atTop (𝓝 ν))
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon)
    (t : ℝ) :
    Tendsto (fun n =>
      ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
        ∂D.goodStandardizedSubmeasure (φ n))
      atTop (𝓝 (∫ z, D.gaussianCharacteristicKernel t z ∂ν)) := by
  let A : ℕ → ℂ := fun n =>
    ∫ x : ℝ, Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)
      ∂D.goodStandardizedSubmeasure (φ n)
  let M : ℕ → ℂ := fun n =>
    ∫ z, D.gaussianCharacteristicKernel t z ∂D.mixingMeasure (φ n)
  have hnorm : Tendsto (fun n => ‖A n - M n‖) atTop (𝓝 0) := by
    exact (D.goodStandardizedSubmeasure_gaussianCharacteristic_norm_tendsto_zero
      hdiffuse t).comp hφ.tendsto_atTop
  have hdiff : Tendsto (fun n => A n - M n) atTop (𝓝 0) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa using hnorm
  have hM : Tendsto M atTop
      (𝓝 (∫ z, D.gaussianCharacteristicKernel t z ∂ν)) := by
    exact D.gaussianCharacteristic_integral_tendsto_D36
      (fun n => D.mixingMeasure (φ n)) ν hμ t
  have hadd := hdiff.add hM
  simpa only [A, M, zero_add, sub_add_cancel] using hadd


def gaussianVarianceNNReal (z : D.Rectangle) : ℝ≥0 :=
  ⟨z.1.2, (lt_of_lt_of_le (half_pos D.c_pos) z.2.2.1).le⟩

@[simp] theorem coe_gaussianVarianceNNReal (z : D.Rectangle) :
    (D.gaussianVarianceNNReal z : ℝ) = z.1.2 := rfl

theorem gaussianVarianceNNReal_ne_zero (z : D.Rectangle) :
    D.gaussianVarianceNNReal z ≠ 0 := by
  apply ne_of_gt
  exact_mod_cast lt_of_lt_of_le (half_pos D.c_pos) z.2.2.1

theorem gaussianDensityKernel_eq_gaussianPDFReal (x : ℝ) (z : D.Rectangle) :
    D.gaussianDensityKernel x z =
      gaussianPDFReal z.1.1 (D.gaussianVarianceNNReal z) x := by
  rfl

theorem continuous_gaussianDensityKernel_uncurry :
    Continuous (fun p : D.Rectangle × ℝ => D.gaussianDensityKernel p.2 p.1) := by
  unfold gaussianDensityKernel
  have hwc : Continuous (fun p : D.Rectangle × ℝ => p.1.1.2) := by fun_prop
  have hw0 : ∀ p : D.Rectangle × ℝ, p.1.1.2 ≠ 0 := fun p => by
    exact ne_of_gt (lt_of_lt_of_le (half_pos D.c_pos) p.1.2.2.1)
  have hsqrt : Continuous (fun p : D.Rectangle × ℝ =>
      Real.sqrt (2 * Real.pi * p.1.1.2)) :=
    (continuous_const.mul hwc).sqrt
  have hsqrt0 : ∀ p : D.Rectangle × ℝ,
      Real.sqrt (2 * Real.pi * p.1.1.2) ≠ 0 := fun p => by
    have hw : 0 < p.1.1.2 := lt_of_lt_of_le (half_pos D.c_pos) p.1.2.2.1
    positivity
  have hnum : Continuous (fun p : D.Rectangle × ℝ => -((p.2 - p.1.1.1) ^ 2)) := by
    fun_prop
  have hden : Continuous (fun p : D.Rectangle × ℝ => 2 * p.1.1.2) :=
    continuous_const.mul hwc
  exact (hsqrt.inv₀ hsqrt0).mul
    (Real.continuous_exp.comp (hnum.div hden (fun p => by
      exact mul_ne_zero (by norm_num) (hw0 p))))

theorem gaussianDensityKernel_nonneg (x : ℝ) (z : D.Rectangle) :
    0 ≤ D.gaussianDensityKernel x z := (D.gaussianDensityKernel_pos x z).le

theorem gaussianDensityKernel_integral_eq_one (z : D.Rectangle) :
    ∫ x : ℝ, D.gaussianDensityKernel x z = 1 := by
  rw [funext (D.gaussianDensityKernel_eq_gaussianPDFReal · z)]
  exact integral_gaussianPDFReal_eq_one _ (D.gaussianVarianceNNReal_ne_zero z)

theorem gaussianDensityKernel_integral_norm_eq_one (z : D.Rectangle) :
    ∫ x : ℝ, ‖D.gaussianDensityKernel x z‖ = 1 := by
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (D.gaussianDensityKernel_nonneg _ z)]
  exact D.gaussianDensityKernel_integral_eq_one z

theorem gaussianDensityKernel_integrable_prod
    (ν : FiniteMeasure D.Rectangle) :
    Integrable (fun p : D.Rectangle × ℝ => D.gaussianDensityKernel p.2 p.1)
      ((ν : Measure D.Rectangle).prod volume) := by
  apply (integrable_prod_iff
    D.continuous_gaussianDensityKernel_uncurry.aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall fun z => by
      rw [funext (D.gaussianDensityKernel_eq_gaussianPDFReal · z)]
      exact integrable_gaussianPDFReal _ _
  · simp_rw [D.gaussianDensityKernel_integral_norm_eq_one]
    exact integrable_const 1

theorem gaussianMixtureDensity_integrable (ν : FiniteMeasure D.Rectangle) :
    Integrable (D.gaussianMixtureDensity ν) volume := by
  unfold gaussianMixtureDensity
  exact (D.gaussianDensityKernel_integrable_prod ν).integral_prod_right


theorem gaussianMixtureDensity_nonneg (ν : FiniteMeasure D.Rectangle) (x : ℝ) :
    0 ≤ D.gaussianMixtureDensity ν x := by
  unfold gaussianMixtureDensity
  exact integral_nonneg (fun z => D.gaussianDensityKernel_nonneg x z)

theorem gaussianMixtureDensity_measurable (ν : FiniteMeasure D.Rectangle) :
    Measurable (D.gaussianMixtureDensity ν) := by
  unfold gaussianMixtureDensity
  exact D.continuous_gaussianDensityKernel_uncurry.stronglyMeasurable.integral_prod_left'.measurable

theorem gaussianMixtureDensity_integral_eq_mass (ν : FiniteMeasure D.Rectangle) :
    ∫ x : ℝ, D.gaussianMixtureDensity ν x = (ν.mass : ℝ) := by
  unfold gaussianMixtureDensity
  rw [← integral_integral_swap (D.gaussianDensityKernel_integrable_prod ν)]
  simp_rw [D.gaussianDensityKernel_integral_eq_one]
  simp [FiniteMeasure.mass]

noncomputable def gaussianMixtureMeasure (ν : FiniteMeasure D.Rectangle) : FiniteMeasure ℝ :=
  ⟨volume.withDensity (fun x => ENNReal.ofReal (D.gaussianMixtureDensity ν x)),
    MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (D.gaussianMixtureDensity_integrable ν).hasFiniteIntegral⟩

@[simp] theorem gaussianMixtureMeasure_toMeasure (ν : FiniteMeasure D.Rectangle) :
    (D.gaussianMixtureMeasure ν : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (D.gaussianMixtureDensity ν x)) := rfl

@[simp] theorem gaussianMixtureMeasure_mass (ν : FiniteMeasure D.Rectangle) :
    (D.gaussianMixtureMeasure ν).mass = ν.mass := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass, D.gaussianMixtureMeasure_toMeasure,
    MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (D.gaussianMixtureDensity_integrable ν)
    (Filter.Eventually.of_forall (D.gaussianMixtureDensity_nonneg ν))]
  rw [D.gaussianMixtureDensity_integral_eq_mass]
  simp


theorem gaussianCharacteristicIntegrand_integrable
    (ν : FiniteMeasure D.Rectangle) (t : ℝ) :
    Integrable (fun p : D.Rectangle × ℝ =>
      (D.gaussianDensityKernel p.2 p.1 : ℂ) *
        Complex.exp ((t : ℂ) * (p.2 : ℂ) * Complex.I))
      ((ν : Measure D.Rectangle).prod volume) := by
  apply (D.gaussianDensityKernel_integrable_prod ν).mono'
  · have hk : Continuous (fun p : D.Rectangle × ℝ =>
        (D.gaussianDensityKernel p.2 p.1 : ℂ)) :=
      Complex.continuous_ofReal.comp D.continuous_gaussianDensityKernel_uncurry
    exact (hk.mul (by fun_prop : Continuous (fun p : D.Rectangle × ℝ =>
      Complex.exp ((t : ℂ) * (p.2 : ℂ) * Complex.I)))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun p => by
      rw [norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : ((((t : ℂ) * (p.2 : ℂ) * Complex.I)).re) = 0 := by simp
      rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (D.gaussianDensityKernel_nonneg p.2 p.1)]

theorem charFun_gaussianMixtureMeasure (ν : FiniteMeasure D.Rectangle) (t : ℝ) :
    charFun (D.gaussianMixtureMeasure ν : Measure ℝ) t =
      ∫ z, D.gaussianCharacteristicKernel t z ∂ν := by
  rw [charFun_apply_real, D.gaussianMixtureMeasure_toMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul
    (D.gaussianMixtureDensity_measurable ν).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => by simp)]
  simp_rw [ENNReal.toReal_ofReal (D.gaussianMixtureDensity_nonneg ν _)]
  unfold gaussianMixtureDensity
  have houter :
      (∫ x : ℝ, (∫ z : D.Rectangle, D.gaussianDensityKernel x z ∂ν) •
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂volume) =
      ∫ x : ℝ, ∫ z : D.Rectangle, (D.gaussianDensityKernel x z : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ν ∂volume := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Complex.real_smul]
    calc
      (↑(∫ z : D.Rectangle, D.gaussianDensityKernel x z ∂ν) : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) =
          (∫ z : D.Rectangle, (D.gaussianDensityKernel x z : ℂ) ∂ν) *
            Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) := by
              congr 1
              exact (integral_ofReal (𝕜 := ℂ)
                (μ := (ν : Measure D.Rectangle))
                (f := fun z => D.gaussianDensityKernel x z)).symm
      _ = ∫ z : D.Rectangle, (D.gaussianDensityKernel x z : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ν :=
        (MeasureTheory.integral_mul_const _ _).symm
  calc
    _ = ∫ x : ℝ, ∫ z : D.Rectangle, (D.gaussianDensityKernel x z : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂ν ∂volume := by
      simpa only using houter
    _ = ∫ z : D.Rectangle, ∫ x : ℝ, (D.gaussianDensityKernel x z : ℂ) *
          Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂volume ∂ν := by
      rw [← integral_integral_swap
        (D.gaussianCharacteristicIntegrand_integrable ν t)]
    _ = ∫ z, D.gaussianCharacteristicKernel t z ∂ν := by
      apply integral_congr_ae
      filter_upwards with z
      simp_rw [D.gaussianDensityKernel_eq_gaussianPDFReal]
      have hreal :
          (∫ x : ℝ, (gaussianPDFReal (z : ℝ × ℝ).1
              (D.gaussianVarianceNNReal z) x : ℂ) *
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂volume) =
          ∫ x : ℝ, gaussianPDFReal (z : ℝ × ℝ).1
              (D.gaussianVarianceNNReal z) x •
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂volume := by
        apply integral_congr_ae
        filter_upwards with x
        exact Complex.real_smul.symm
      rw [hreal]
      calc
        (∫ x : ℝ, gaussianPDFReal (z : ℝ × ℝ).1
              (D.gaussianVarianceNNReal z) x •
                Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I) ∂volume) =
            ∫ x : ℝ, Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)
              ∂gaussianReal (z : ℝ × ℝ).1 (D.gaussianVarianceNNReal z) :=
          (integral_gaussianReal_eq_integral_smul
            (E := ℂ) (μ := (z : ℝ × ℝ).1)
            (v := D.gaussianVarianceNNReal z)
            (f := fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I))
            (D.gaussianVarianceNNReal_ne_zero z)).symm
        _ = charFun (gaussianReal (z : ℝ × ℝ).1
              (D.gaussianVarianceNNReal z)) t := by
          rw [charFun_apply_real]
        _ = D.gaussianCharacteristicKernel t z := by
          rw [charFun_gaussianReal]
          unfold gaussianCharacteristicKernel
          apply congrArg Complex.exp
          simp only [D.coe_gaussianVarianceNNReal]
          push_cast
          ring

lemma charFun_normalize_of_ne_zero (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0) (t : ℝ) :
    charFun (μ.normalize : Measure ℝ) t =
      μ.mass⁻¹ • charFun (μ : Measure ℝ) t := by
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero μ hμ]
  rw [charFun_apply_real, MeasureTheory.integral_smul_nnreal_measure]
  rw [← charFun_apply_real]
  rfl

theorem finiteMeasure_tendsto_of_charFun_tendsto
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0)
    (hchar : ∀ t : ℝ, Tendsto (fun n => charFun (μs n : Measure ℝ) t)
      atTop (𝓝 (charFun (μ : Measure ℝ) t))) :
    Tendsto μs atTop (𝓝 μ) := by
  have hmassReal : Tendsto (fun n => ((μs n).mass : ℝ)) atTop
      (𝓝 (μ.mass : ℝ)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp (hchar 0)
    have hzero : ∀ η : FiniteMeasure ℝ,
        (charFun (η : Measure ℝ) 0).re = (η.mass : ℝ) := by
      intro η
      rw [charFun_zero]
      change ((η : Measure ℝ) univ).toReal = (η.mass : ℝ)
      rw [← η.ennreal_coeFn_eq_coeFn_toMeasure]
      exact ENNReal.coe_toReal _
    have hfun : (Complex.re ∘ fun n => charFun (μs n : Measure ℝ) 0) =
        (fun n => ((μs n).mass : ℝ)) := by
      funext n
      exact hzero (μs n)
    rw [hfun, hzero μ] at h
    exact h
  have hmass : Tendsto (fun n => (μs n).mass) atTop (𝓝 μ.mass) :=
    NNReal.tendsto_coe.mp hmassReal
  have hmass0 : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hμ
  have hne : ∀ᶠ n in atTop, μs n ≠ 0 := by
    have hmem : ({0}ᶜ : Set ℝ≥0) ∈ 𝓝 μ.mass :=
      isOpen_compl_singleton.mem_nhds hmass0
    have := hmass hmem
    filter_upwards [this] with n hn
    apply ((μs n).mass_nonzero_iff).mp
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hn
  have hnorm : Tendsto (fun n => (μs n).normalize) atTop (𝓝 μ.normalize) := by
    apply (ProbabilityMeasure.tendsto_iff_tendsto_charFun).2
    intro t
    have hinvReal : Tendsto (fun n => (((μs n).mass : ℝ)⁻¹)) atTop
        (𝓝 (((μ.mass : ℝ)⁻¹))) := hmassReal.inv₀ (by exact_mod_cast hmass0)
    have hinvComplex : Tendsto (fun n => ((((μs n).mass : ℝ)⁻¹ : ℝ) : ℂ)) atTop
        (𝓝 ((((μ.mass : ℝ)⁻¹ : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hinvReal
    have hmul := hinvComplex.mul (hchar t)
    rw [charFun_normalize_of_ne_zero μ hμ t]
    change Tendsto (fun n => charFun ((μs n).normalize : Measure ℝ) t) atTop
      (𝓝 (((((μ.mass : ℝ)⁻¹ : ℝ) : ℂ)) * charFun (μ : Measure ℝ) t))
    apply hmul.congr'
    filter_upwards [hne] with n hn
    rw [charFun_normalize_of_ne_zero (μs n) hn t]
    rfl
  exact FiniteMeasure.tendsto_of_tendsto_normalize_testAgainstNN_of_tendsto_mass
    hnorm hmass

theorem goodStandardizedSubmeasure_tendsto_gaussianMixtureMeasure_D36
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : FiniteMeasure D.Rectangle)
    (hν : ν ≠ 0)
    (hμ : Tendsto (fun n => D.mixingMeasure (φ n)) atTop (𝓝 ν))
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon) :
    Tendsto (fun n => D.goodStandardizedSubmeasure (φ n)) atTop
      (𝓝 (D.gaussianMixtureMeasure ν)) := by
  apply finiteMeasure_tendsto_of_charFun_tendsto
  · rw [← FiniteMeasure.mass_nonzero_iff, D.gaussianMixtureMeasure_mass]
    exact ν.mass_nonzero_iff.mpr hν
  · intro t
    rw [D.charFun_gaussianMixtureMeasure ν t]
    have h := D.goodStandardizedSubmeasure_integral_exp_tendsto_D36
      φ hφ ν hμ hdiffuse t
    simpa only [charFun_apply_real, Complex.ofReal_mul] using h

theorem gaussianMixtureMeasure_le_of_tendsto_standardizedLaw_D36
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (ν : FiniteMeasure D.Rectangle)
    (π : ProbabilityMeasure ℝ) (hν : ν ≠ 0)
    (hμ : Tendsto (fun n => D.mixingMeasure (φ n)) atTop (𝓝 ν))
    (hdiffuse : ∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon)
    (hπ : Tendsto (fun n => S.standardizedLaw (φ n)) atTop (𝓝 π)) :
    (D.gaussianMixtureMeasure ν : Measure ℝ) ≤ (π : Measure ℝ) := by
  have hπfin : Tendsto (fun n => (S.standardizedLaw (φ n)).toFiniteMeasure)
      atTop (𝓝 π.toFiniteMeasure) := by
    rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds] at hπ
    exact hπ
  exact finiteRealMeasure_toMeasure_le_of_tendsto
    (D.goodStandardizedSubmeasure_tendsto_gaussianMixtureMeasure_D36
      φ hφ ν hν hμ hdiffuse)
    hπfin (fun n => D.goodStandardizedSubmeasure_le_standardizedLaw (φ n))

lemma continuous_gaussianMixtureDensity (ν : FiniteMeasure D.Rectangle) :
    Continuous (D.gaussianMixtureDensity ν) := by
  have hrect : IsCompact D.rectangle := isCompact_Icc.prod isCompact_Icc
  letI : CompactSpace D.Rectangle :=
    isCompact_iff_compactSpace.mp (by simpa [Rectangle] using hrect)
  have huncurry : Continuous (Function.uncurry
      (fun x : ℝ => fun z : D.Rectangle => D.gaussianDensityKernel x z)) := by
    exact D.continuous_gaussianDensityKernel_uncurry.comp
      (continuous_snd.prodMk continuous_fst)
  have h := continuous_parametric_integral_of_continuous
    (μ := (ν : Measure D.Rectangle)) huncurry (s := Set.univ) isCompact_univ
  simpa only [gaussianMixtureDensity, Measure.restrict_univ] using h

/-- Pointwise density domination extracted from domination of two absolutely
continuous finite measures, using continuity to upgrade an a.e. inequality. -/
theorem gaussianMixtureDensity_le_of_measure_le
    (ν : FiniteMeasure D.Rectangle) (f : ℝ → ℝ)
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hle : (D.gaussianMixtureMeasure ν : Measure ℝ) ≤
      volume.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∀ x, D.gaussianMixtureDensity ν x ≤ f x := by
  have haeE : (fun x => ENNReal.ofReal (D.gaussianMixtureDensity ν x)) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal (f x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
      (D.gaussianMixtureDensity_measurable ν).ennreal_ofReal
    intro s hs hst
    rw [← withDensity_apply _ hs, ← withDensity_apply _ hs]
    exact hle s
  have haeR : D.gaussianMixtureDensity ν ≤ᵐ[volume] f := by
    filter_upwards [haeE] with x hx
    exact (ENNReal.ofReal_le_ofReal_iff (hf0 x)).mp hx
  have haeMax : (fun x => max (D.gaussianMixtureDensity ν x) (f x)) =ᵐ[volume] f := by
    filter_upwards [haeR] with x hx
    exact max_eq_right hx
  have heq : (fun x => max (D.gaussianMixtureDensity ν x) (f x)) = f :=
    Measure.eq_of_ae_eq haeMax
      ((continuous_gaussianMixtureDensity D ν).max hf) hf
  intro x
  have := congrFun heq x
  rw [max_eq_right_iff] at this
  exact this


open Forest.CanonicalCompactnessWrapper.CanonicalSequence
open Erdos993.MeasureFourierInversion

/-- D.36--D.40 center contradiction after a nonzero compact mixing limit has
been extracted.  The only remaining input is the independently proved
exact-center decay. -/
theorem not_diffuse_of_mixing_subsequence_D36_D40
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (q : ℝ≥0) (hq : 0 < q) (πmix : ProbabilityMeasure D.Rectangle)
    (ν : ProbabilityMeasure ℝ) (A : ℝ → ℝ)
    (hmix : Tendsto (fun n => D.mixingMeasure (φ n)) atTop
      (𝓝 (q • πmix.toFiniteMeasure)))
    (hweak : Tendsto (S.standardizedLaw ∘ φ) atTop (𝓝 ν))
    (hA : FullDomainEnvelope
      (fun n => S.zeroExtendedCharacteristic (φ n)) (charFun ν) A)
    (hcenter : Tendsto (fun n => Real.sqrt (S.V (φ n)) *
      S.centeredMass (φ n) 0) atTop (𝓝 0)) :
    ¬ (∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon) := by
  intro hdiffuse
  have hmix_ne : q • πmix.toFiniteMeasure ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff]
    simpa using hq.ne'
  have hweak' : Tendsto (fun n => S.standardizedLaw (φ n)) atTop (𝓝 ν) := by
    simpa only [Function.comp_apply] using hweak
  have hle :
      (D.gaussianMixtureMeasure (q • πmix.toFiniteMeasure) : Measure ℝ) ≤
        (ν : Measure ℝ) :=
    D.gaussianMixtureMeasure_le_of_tendsto_standardizedLaw_D36
      φ hφ (q • πmix.toFiniteMeasure) ν hmix_ne hmix hdiffuse hweak'
  have hpack := probabilityFourierInversionUpToTwo_of_fullDomainEnvelope hA
  have hle' :
      (D.gaussianMixtureMeasure (q • πmix.toFiniteMeasure) : Measure ℝ) ≤
        volume.withDensity
          (fun x => ENNReal.ofReal (inverseCharFunDensity (ν : Measure ℝ) x)) := by
    rw [← hpack.measure_eq]
    exact hle
  have hdensity_le := D.gaussianMixtureDensity_le_of_measure_le
    (q • πmix.toFiniteMeasure)
    (inverseCharFunDensity (ν : Measure ℝ))
    hpack.density_continuous hpack.density_nonneg hle'
  have hf0 : 0 < inverseCharFunDensity (ν : Measure ℝ) 0 :=
    (D.gaussianMixtureDensity_zero_pos_D37 q hq πmix).trans_le (hdensity_le 0)
  have hD40 := centeredMass_zero_scaled_tendsto_D40 S ν φ A hφ hweak hA
  have heq : inverseCharFunDensity (ν : Measure ℝ) 0 = 0 :=
    tendsto_nhds_unique hD40 hcenter
  linarith

/-- The diffuse alternative is impossible whenever the D.35 good-event lower
bound is positive.  Weak convergence and the full-domain envelope are extracted
only after the mixing subsequence, so all limits refer to the same canonical
laws. -/
theorem diffuseAntichainExclusion_of_goodMassPositive
    (hpositive : 0 < (D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2) :
    ¬ (∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ D.antichain n,
        (D.rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon) := by
  intro hdiffuse
  let p0 : ℝ := ((D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2) / 2
  have hp0 : 0 < p0 := half_pos hpositive
  have hp0le : p0 ≤ (D.c / 2) / (784 - D.c / 2) - 1 / D.B ^ 2 := by
    dsimp [p0]
    linarith
  obtain ⟨q, πmix, φ, hq0, hq1, hφ, hmix⟩ :=
    D.exists_compact_mixing_limit_D35 p0 hp0 hp0le
  have hq : 0 < q := by
    have hpnn : 0 < Real.toNNReal p0 := Real.toNNReal_pos.mpr hp0
    exact lt_of_lt_of_le hpnn hq0
  let T : CanonicalSequence := S.subsequence φ hφ
  obtain ⟨ν, ψ, hψ, hweakT, hcharT, hA_T⟩ :=
    AppendixA.CanonicalSequence.exists_subseq_fullDomainEnvelope_A4 T
  let χ : ℕ → ℕ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  have hmixχ : Tendsto (fun n => D.mixingMeasure (χ n)) atTop
      (𝓝 (q • πmix.toFiniteMeasure)) := by
    simpa [χ, Function.comp_def] using hmix.comp hψ.tendsto_atTop
  have hweakχ : Tendsto (S.standardizedLaw ∘ χ) atTop (𝓝 ν) := by
    simpa [T, χ, Function.comp_def] using hweakT
  have hAχ : FullDomainEnvelope
      (fun n => S.zeroExtendedCharacteristic (χ n)) (charFun ν)
      (AppendixA.appendixA4Envelope 27) := by
    simpa [T, χ, Function.comp_def] using hA_T
  have hcenter : Tendsto (fun n => Real.sqrt (S.V (χ n)) *
      S.centeredMass (χ n) 0) atTop (𝓝 0) :=
    S.centeredMass_zero_scaled_tendsto_zero_D39.comp hχ.tendsto_atTop
  exact D.not_diffuse_of_mixing_subsequence_D36_D40 χ hχ q hq πmix ν
    (AppendixA.appendixA4Envelope 27) hmixχ hweakχ hAχ hcenter hdiffuse


end ActualAntichainMixingSequence

namespace ComponentRooting

/-- Diagonal strictly increasing selector used in the sequential form of D.5.
At stage `j` it chooses a later index satisfying the `j`-th predicate. -/
private noncomputable def diagonalIndex
    (P : ℕ → ℕ → Prop)
    (hP : ∀ j N, ∃ n, N < n ∧ P j n) : ℕ → ℕ :=
  fun j => Nat.rec (Classical.choose (hP 0 0))
    (fun k prev => Classical.choose (hP (k + 1) prev)) j

private theorem diagonalIndex_spec
    (P : ℕ → ℕ → Prop)
    (hP : ∀ j N, ∃ n, N < n ∧ P j n) :
    StrictMono (diagonalIndex P hP) ∧
      ∀ j, P j (diagonalIndex P hP j) := by
  let φ := diagonalIndex P hP
  have hsucc : ∀ j, φ j < φ (j + 1) := by
    intro j
    exact (Classical.choose_spec (hP (j + 1) (φ j))).1
  refine ⟨strictMono_nat_of_lt_succ hsucc, ?_⟩
  intro j
  cases j with
  | zero => exact (Classical.choose_spec (hP 0 0)).2
  | succ j => exact (Classical.choose_spec (hP (j + 1) (φ j))).2

/-- Sequential D.2--D.40 exclusion of a diffuse rooted antichain carrying a
fixed positive fraction of the canonical variance.  The auxiliary truncation
constant is chosen inside the proof, so the statement assumes neither a good-
event mass bound nor any center/activity premise. -/
theorem diffuseAntichainExclusion
    (S : CanonicalSequence)
    (rooting : ∀ n, ComponentRooting (S.graph n))
    (antichain : ∀ n, Finset (Fin (S.order n)))
    (hanti : ∀ n, (rooting n).IsRootedAntichain
      (G := S.graph n) (antichain n))
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hlarge : ∀ n, c * S.V n ≤
      ∑ u ∈ antichain n,
        (rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u) :
    ¬ (∀ epsilon > 0,
      ∀ᶠ n in atTop, ∀ u ∈ antichain n,
        (rooting n).subtreeVarianceMass (G := S.graph n) (S.state n) u /
          (S.state n).variance < epsilon) := by
  let a : ℝ := (c / 2) / (784 - c / 2)
  have hden : 0 < 784 - c / 2 := by linarith
  have ha : 0 < a := div_pos (half_pos hc) hden
  let B : ℝ := Real.sqrt (2 / a)
  have hBa : 0 ≤ 2 / a := (div_pos (by norm_num) ha).le
  have hB : 0 < B := Real.sqrt_pos.2 (div_pos (by norm_num) ha)
  have hBsq : B ^ 2 = 2 / a := Real.sq_sqrt hBa
  have hinv : 1 / B ^ 2 = a / 2 := by
    rw [hBsq]
    field_simp [ha.ne']
  have hpositive : 0 < (c / 2) / (784 - c / 2) - 1 / B ^ 2 := by
    rw [show (c / 2) / (784 - c / 2) = a by rfl, hinv]
    linarith
  let D : ActualAntichainMixingSequence S :=
    { rooting := rooting
      antichain := antichain
      isRootedAntichain := hanti
      c := c
      B := B
      c_pos := hc
      c_le_one := hc1
      B_pos := hB
      large := hlarge }
  exact D.diffuseAntichainExclusion_of_goodMassPositive hpositive

/-- Appendix D Lemma D.5, quantitative finite-branch approximation.  For every
fixed error tolerance a single positive subtree-mass threshold eventually
captures all but that tolerance of the actual vertex variance contributions.
The proof uses exposed roots only under the original canonical law. -/
theorem finiteBranchApproximation_D5
    (S : CanonicalSequence)
    (rooting : ∀ n, ComponentRooting (S.graph n))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ᶠ n in atTop,
        (rooting n).omittedVarianceContribution (G := S.graph n)
          (S.state n)
          ((rooting n).retainedVarianceSet (G := S.graph n)
            (S.state n) alpha) ≤ epsilon * S.V n := by
  by_contra hnone
  push Not at hnone
  let alpha : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  let P : ℕ → ℕ → Prop := fun j n =>
    epsilon * S.V n <
      (rooting n).omittedVarianceContribution (G := S.graph n)
        (S.state n)
        ((rooting n).retainedVarianceSet (G := S.graph n)
          (S.state n) (alpha j))
  have hP : ∀ j N, ∃ n, N < n ∧ P j n := by
    intro j N
    have ha0 : 0 < alpha j := by
      dsimp [alpha]
      positivity
    have ha1 : alpha j ≤ 1 := by
      dsimp [alpha]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (j : ℝ) + 1)).2
      norm_num
    have hfreq : ∃ᶠ n in atTop, P j n := by
      simpa [P] using hnone (alpha j) ha0 ha1
    obtain ⟨n, hn, hPn⟩ := (frequently_atTop.1 hfreq) (N + 1)
    exact ⟨n, by omega, hPn⟩
  let φ := diagonalIndex P hP
  have hφspec := diagonalIndex_spec P hP
  have hφ : StrictMono φ := hφspec.1
  have hPφ : ∀ j, P j (φ j) := hφspec.2
  let T : CanonicalSequence := S.subsequence φ hφ
  let R : ∀ j, ComponentRooting (T.graph j) := fun j => rooting (φ j)
  let A : ∀ j, Finset (Fin (T.order j)) := fun j =>
    (R j).exposedBoundary (G := T.graph j)
      ((R j).retainedVarianceSet (G := T.graph j) (T.state j) (alpha j))
  have hanti : ∀ j, (R j).IsRootedAntichain (G := T.graph j) (A j) := by
    intro j
    exact (R j).exposedBoundary_isRootedAntichain
      (G := T.graph j) (T.state j).isForest
      ((R j).retainedVarianceSet_ancestorClosed
        (G := T.graph j) (T.state j) (alpha j))
  let c : ℝ := min epsilon 1
  have hc : 0 < c := lt_min hepsilon (by norm_num)
  have hc1 : c ≤ 1 := min_le_right _ _
  have hlarge : ∀ j, c * T.V j ≤
      ∑ u ∈ A j,
        (R j).subtreeVarianceMass (G := T.graph j) (T.state j) u := by
    intro j
    have hcp : c ≤ epsilon := min_le_left _ _
    have hV0 : 0 ≤ T.V j := (T.variance_pos j).le
    have hfail := hPφ j
    change epsilon * S.V (φ j) < _ at hfail
    have hid := (R j).omittedVarianceContribution_eq_sum_exposedBoundary
      (G := T.graph j) (T.state j)
      ((R j).retainedVarianceSet_ancestorClosed
        (G := T.graph j) (T.state j) (alpha j))
    change c * T.V j ≤ _
    rw [← hid]
    exact (mul_le_mul_of_nonneg_right hcp hV0).trans hfail.le
  have hnotdiff := ComponentRooting.diffuseAntichainExclusion
    T R A hanti c hc hc1 hlarge
  apply hnotdiff
  intro delta hdelta
  have halpha : Tendsto alpha atTop (𝓝 0) := by
    simpa [alpha] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  filter_upwards [halpha.eventually (eventually_lt_nhds hdelta)] with j haj
  intro u hu
  have huE := (R j).subtreeVarianceMass_lt_of_mem_exposedBoundary_retainedVarianceSet
    (G := T.graph j) (T.state j) (alpha j) hu
  have hV := T.variance_pos j
  apply (div_lt_iff₀ hV).2
  exact huE.trans (mul_lt_mul_of_pos_right haj hV)

end ComponentRooting

end

end ActualRootedVariance
end Erdos993
