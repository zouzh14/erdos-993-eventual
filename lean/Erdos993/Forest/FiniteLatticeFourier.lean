import Erdos993.Forest.UniformFourthMoment
import Erdos993.Forest.UniformCharacteristicGap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Finite Fourier identities for Appendix A

This module proves the finite-law algebra and elementary trigonometric estimates used in
Lemma A.5.  All statements are for the concrete `FiniteLatticeLaw`; no analytic envelope
or forest estimate is assumed.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators ENNReal

universe u

namespace FiniteLatticeLaw

variable {α : Type u} [Fintype α]

/-- The centered real value of the lattice statistic. -/
def centeredValue (L : FiniteLatticeLaw α) (a : α) : ℝ :=
  (L.stat a : ℝ) - L.mean

/-- A centered moment of the finite lattice law. -/
def centeredMoment (L : FiniteLatticeLaw α) (k : ℕ) : ℝ :=
  ∑ a, L.probability a * L.centeredValue a ^ k

/-- A moment of the difference of two independent copies. -/
def symmetrizedMoment (L : FiniteLatticeLaw α) (k : ℕ) : ℝ :=
  ∑ a, ∑ b, L.probability a * L.probability b *
    (L.centeredValue a - L.centeredValue b) ^ k

@[simp] theorem centeredMoment_zero (L : FiniteLatticeLaw α) :
    L.centeredMoment 0 = 1 := by
  simp [centeredMoment, ← Finset.sum_mul, L.probability_sum]

@[simp] theorem centeredMoment_one (L : FiniteLatticeLaw α) :
    L.centeredMoment 1 = 0 := by
  rw [centeredMoment]
  simp only [pow_one, centeredValue]
  calc
    (∑ a, L.probability a * ((L.stat a : ℝ) - L.mean)) =
        (∑ a, L.probability a * (L.stat a : ℝ)) -
          L.mean * (∑ a, L.probability a) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = 0 := by rw [L.probability_sum]; simp [mean]

@[simp] theorem centeredMoment_two (L : FiniteLatticeLaw α) :
    L.centeredMoment 2 = L.variance := by
  rfl

/-- The second moment of an independent-copy difference is twice the variance. -/
theorem symmetrizedMoment_two (L : FiniteLatticeLaw α) :
    L.symmetrizedMoment 2 = 2 * L.variance := by
  rw [symmetrizedMoment]
  have hm1 : (∑ a, L.probability a * L.centeredValue a) = 0 := by
    simpa [centeredMoment] using L.centeredMoment_one
  have hm2 : (∑ a, L.probability a * L.centeredValue a ^ 2) = L.variance := by
    simpa [centeredMoment] using L.centeredMoment_two
  have hinner : ∀ a,
      (∑ b, L.probability a * L.probability b *
          (L.centeredValue a - L.centeredValue b) ^ 2) =
        L.probability a * L.centeredValue a ^ 2 +
          L.variance * L.probability a := by
    intro a
    calc
      (∑ b, L.probability a * L.probability b *
          (L.centeredValue a - L.centeredValue b) ^ 2) =
        ∑ b,
          ((L.probability a * L.centeredValue a ^ 2) * L.probability b +
          (L.probability b * L.centeredValue b ^ 2) * L.probability a -
          2 * (L.probability a * L.centeredValue a) *
            (L.probability b * L.centeredValue b)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = (L.probability a * L.centeredValue a ^ 2) *
            (∑ b, L.probability b) +
          (∑ b, L.probability b * L.centeredValue b ^ 2) *
            L.probability a -
          2 * (L.probability a * L.centeredValue a) *
            (∑ b, L.probability b * L.centeredValue b) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
      _ = L.probability a * L.centeredValue a ^ 2 +
          L.variance * L.probability a := by
        rw [L.probability_sum, hm1, hm2]
        ring
  calc
    (∑ a, ∑ b, L.probability a * L.probability b *
        (L.centeredValue a - L.centeredValue b) ^ 2) =
        ∑ a, (L.probability a * L.centeredValue a ^ 2 +
          L.variance * L.probability a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    _ = 2 * L.variance := by
      rw [Finset.sum_add_distrib, hm2, ← Finset.mul_sum,
        L.probability_sum]
      ring

/-- Pointwise fourth-power symmetrization estimate. -/
theorem sub_pow_four_le_eight (x y : ℝ) :
    (x - y) ^ 4 ≤ 8 * (x ^ 4 + y ^ 4) := by
  have hquad : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg (x + y)]
  have hleft : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  have hright : 0 ≤ 2 * (x ^ 2 + y ^ 2) := by positivity
  have hsquare := mul_self_le_mul_self hleft hquad
  have hcross : 2 * (x ^ 2 * y ^ 2) ≤ x ^ 4 + y ^ 4 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  nlinarith

/-- The fourth moment of an independent-copy difference is bounded by sixteen times
its centered fourth moment.  This coarse bound suffices for the small-frequency window. -/
theorem symmetrizedMoment_four_le (L : FiniteLatticeLaw α) :
    L.symmetrizedMoment 4 ≤ 16 * L.centeredMoment 4 := by
  rw [symmetrizedMoment]
  have hm4 : (∑ a, L.probability a * L.centeredValue a ^ 4) =
      L.centeredMoment 4 := by rfl
  have hinner : ∀ a,
      (∑ b, L.probability a * L.probability b *
          (8 * (L.centeredValue a ^ 4 + L.centeredValue b ^ 4))) =
        8 * (L.probability a * L.centeredValue a ^ 4 +
          L.probability a * L.centeredMoment 4) := by
    intro a
    calc
      (∑ b, L.probability a * L.probability b *
          (8 * (L.centeredValue a ^ 4 + L.centeredValue b ^ 4))) =
        ∑ b, 8 * ((L.probability a * L.centeredValue a ^ 4) *
              L.probability b +
            L.probability a *
              (L.probability b * L.centeredValue b ^ 4)) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = 8 * ((L.probability a * L.centeredValue a ^ 4) *
              (∑ b, L.probability b) +
            L.probability a *
              (∑ b, L.probability b * L.centeredValue b ^ 4)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 8 * (L.probability a * L.centeredValue a ^ 4 +
          L.probability a * L.centeredMoment 4) := by
        rw [L.probability_sum, hm4]
        ring
  calc
    (∑ a, ∑ b, L.probability a * L.probability b *
        (L.centeredValue a - L.centeredValue b) ^ 4) ≤
      ∑ a, ∑ b, L.probability a * L.probability b *
        (8 * (L.centeredValue a ^ 4 + L.centeredValue b ^ 4)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (sub_pow_four_le_eight (L.centeredValue a) (L.centeredValue b))
        (mul_nonneg (L.probability_nonneg a) (L.probability_nonneg b))
    _ = 16 * L.centeredMoment 4 := by
      calc
        (∑ a, ∑ b, L.probability a * L.probability b *
            (8 * (L.centeredValue a ^ 4 + L.centeredValue b ^ 4))) =
          ∑ a, 8 * (L.probability a * L.centeredValue a ^ 4 +
            L.probability a * L.centeredMoment 4) := by
            apply Finset.sum_congr rfl
            intro a _
            exact hinner a
        _ = 16 * L.centeredMoment 4 := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, hm4,
            ← Finset.sum_mul, L.probability_sum]
          ring

/-- A global fourth-order lower Taylor bound for `1 - cos`.  The coefficient `1`
is deliberately coarse: on `|t| ≤ 1` it follows from `Real.cos_bound`, and outside
that interval the polynomial lower bound is nonpositive. -/
theorem one_sub_cos_ge_sq_div_two_sub_pow_four (t : ℝ) :
    t ^ 2 / 2 - t ^ 4 ≤ 1 - Real.cos t := by
  by_cases ht : |t| ≤ 1
  · have h := Real.cos_bound ht
    have habspow : |t| ^ 4 = t ^ 4 := by
      calc
        |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
        _ = (t ^ 2) ^ 2 := by rw [sq_abs]
        _ = t ^ 4 := by ring
    rw [habspow] at h
    have hupper := (abs_le.mp h).2
    have hcoeff : t ^ 4 * (5 / 96 : ℝ) ≤ t ^ 4 := by
      have ht4 : 0 ≤ t ^ 4 := by positivity
      nlinarith
    calc
      t ^ 2 / 2 - t ^ 4 ≤ t ^ 2 / 2 - t ^ 4 * (5 / 96 : ℝ) := by
        linarith
      _ ≤ 1 - Real.cos t := by linarith
  · have ht1 : 1 < |t| := lt_of_not_ge ht
    have ht_sq : 1 < t ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg t]
    have hpoly : t ^ 2 / 2 - t ^ 4 ≤ 0 := by
      nlinarith [sq_nonneg (t ^ 2)]
    exact hpoly.trans (sub_nonneg.mpr (Real.cos_le_one t))

@[simp] theorem phase_re (θ x : ℝ) : (phase θ x).re = Real.cos (θ * x) := by
  simp [phase, Complex.exp_re]

@[simp] theorem phase_im (θ x : ℝ) : (phase θ x).im = Real.sin (θ * x) := by
  simp [phase, Complex.exp_im]

/-- Real part of the centered finite characteristic function. -/
theorem centeredCharacteristic_re (L : FiniteLatticeLaw α) (θ : ℝ) :
    (L.centeredCharacteristic θ).re =
      ∑ a, L.probability a * Real.cos (θ * L.centeredValue a) := by
  simp [centeredCharacteristic, centeredValue, phase, Complex.exp_re]

/-- Imaginary part of the centered finite characteristic function. -/
theorem centeredCharacteristic_im (L : FiniteLatticeLaw α) (θ : ℝ) :
    (L.centeredCharacteristic θ).im =
      ∑ a, L.probability a * Real.sin (θ * L.centeredValue a) := by
  simp [centeredCharacteristic, centeredValue, phase, Complex.exp_im]

/-- Independent-copy identity for the squared characteristic modulus. -/
theorem characteristicModulus_sq_eq_symmetrized_cos
    (L : FiniteLatticeLaw α) (θ : ℝ) :
    L.characteristicModulus θ ^ 2 =
      ∑ a, ∑ b, L.probability a * L.probability b *
        Real.cos (θ * (L.centeredValue a - L.centeredValue b)) := by
  rw [characteristicModulus, Complex.sq_norm, Complex.normSq_apply,
    L.centeredCharacteristic_re, L.centeredCharacteristic_im]
  calc
    (∑ a, L.probability a * Real.cos (θ * L.centeredValue a)) *
          (∑ a, L.probability a * Real.cos (θ * L.centeredValue a)) +
        (∑ a, L.probability a * Real.sin (θ * L.centeredValue a)) *
          (∑ a, L.probability a * Real.sin (θ * L.centeredValue a)) =
      ∑ a, ∑ b,
        ((L.probability a * Real.cos (θ * L.centeredValue a)) *
            (L.probability b * Real.cos (θ * L.centeredValue b)) +
          (L.probability a * Real.sin (θ * L.centeredValue a)) *
            (L.probability b * Real.sin (θ * L.centeredValue b))) := by
      rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    _ = ∑ a, ∑ b, L.probability a * L.probability b *
        Real.cos (θ * (L.centeredValue a - L.centeredValue b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [show θ * (L.centeredValue a - L.centeredValue b) =
          θ * L.centeredValue a - θ * L.centeredValue b by ring,
        Real.cos_sub]
      ring

/-- Loss of squared modulus as the independent-copy average of `1 - cos`. -/
theorem one_sub_characteristicModulus_sq_eq
    (L : FiniteLatticeLaw α) (θ : ℝ) :
    1 - L.characteristicModulus θ ^ 2 =
      ∑ a, ∑ b, L.probability a * L.probability b *
        (1 - Real.cos (θ * (L.centeredValue a - L.centeredValue b))) := by
  rw [L.characteristicModulus_sq_eq_symmetrized_cos]
  have hweight :
      (∑ a, ∑ b, L.probability a * L.probability b) = 1 := by
    simp [← Finset.mul_sum, L.probability_sum]
  calc
    1 - ∑ a, ∑ b, L.probability a * L.probability b *
        Real.cos (θ * (L.centeredValue a - L.centeredValue b)) =
      (∑ a, ∑ b, L.probability a * L.probability b) -
        ∑ a, ∑ b, L.probability a * L.probability b *
          Real.cos (θ * (L.centeredValue a - L.centeredValue b)) := by rw [hweight]
    _ = ∑ a, ∑ b, L.probability a * L.probability b *
        (1 - Real.cos (θ * (L.centeredValue a - L.centeredValue b))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- The finite fourth-order curvature inequality used in Lemma A.5. -/
theorem one_sub_characteristicModulus_sq_ge
    (L : FiniteLatticeLaw α) (θ : ℝ) :
    θ ^ 2 * L.variance - θ ^ 4 * L.symmetrizedMoment 4 ≤
      1 - L.characteristicModulus θ ^ 2 := by
  rw [L.one_sub_characteristicModulus_sq_eq]
  have hV : L.variance = L.symmetrizedMoment 2 / 2 := by
    rw [L.symmetrizedMoment_two]
    ring
  rw [hV]
  calc
    θ ^ 2 * (L.symmetrizedMoment 2 / 2) - θ ^ 4 * L.symmetrizedMoment 4 =
      ∑ a, ∑ b, L.probability a * L.probability b *
        ((θ * (L.centeredValue a - L.centeredValue b)) ^ 2 / 2 -
          (θ * (L.centeredValue a - L.centeredValue b)) ^ 4) := by
      unfold symmetrizedMoment
      simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ a, ∑ b, L.probability a * L.probability b *
        (1 - Real.cos (θ * (L.centeredValue a - L.centeredValue b))) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left
        (one_sub_cos_ge_sq_div_two_sub_pow_four
          (θ * (L.centeredValue a - L.centeredValue b)))
        (mul_nonneg (L.probability_nonneg a) (L.probability_nonneg b))

end FiniteLatticeLaw

end
end Forest
end Erdos993
