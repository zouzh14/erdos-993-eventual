import Erdos993.Forest.FiniteLatticeFourier

/-!
# Lemma A.5: uniform small-frequency curvature

This module combines the concrete fourth-moment theorem A.3 and characteristic-gap
theorem A.4.  It proves an actual lower bound for every finite forest and every
`0 < z ≤ Z`; the logarithmic loss is the existing `EReal` quantity, so zeros of the
characteristic function remain `+∞` rather than being silently coerced through
`Real.log 0`.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators ENNReal

universe u

/-- A concrete positive scale on which the fourth-order curvature estimate closes. -/
def smallFrequencyScale (Z : ℝ) : ℝ :=
  min 1 (1 / (64 * UniformFourthMoment.C4 Z))

/-- The concrete lower-bound coefficient in Lemma A.5. -/
def smallFrequencyConstant (Z : ℝ) : ℝ :=
  min (uniformGapConstant Z / Real.pi ^ 2) (1 / 4)

 theorem C4_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < UniformFourthMoment.C4 Z := by
  rw [UniformFourthMoment.C4_eq_polynomial]
  have h1Z : 0 < 1 + Z := by linarith
  positivity

 theorem smallFrequencyScale_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < smallFrequencyScale Z := by
  unfold smallFrequencyScale
  apply lt_min
  · norm_num
  · exact one_div_pos.mpr (mul_pos (by norm_num) (C4_pos hZ))

 theorem smallFrequencyScale_le_one (Z : ℝ) : smallFrequencyScale Z ≤ 1 := by
  exact min_le_left _ _

 theorem smallFrequencyConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < smallFrequencyConstant Z := by
  unfold smallFrequencyConstant
  apply lt_min
  · exact div_pos (uniformGapConstant_pos hZ) (sq_pos_of_pos Real.pi_pos)
  · norm_num

/-- Jordan's inequality in the exact squared half-angle form used to pass from A.4
to a bound in the scale variable `variance * θ²`. -/
theorem sq_div_pi_sq_le_sin_half_sq {θ : ℝ} (hθ : |θ| ≤ Real.pi) :
    θ ^ 2 / Real.pi ^ 2 ≤ Real.sin (θ / 2) ^ 2 := by
  let a : ℝ := |θ| / 2
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hapi : a ≤ Real.pi / 2 := by dsimp [a]; linarith
  have hjordan : 2 / Real.pi * a ≤ Real.sin a :=
    Real.mul_le_sin ha0 hapi
  have hsin0 : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 (hapi.trans (by linarith [Real.pi_pos]))
  have hsquares : (2 / Real.pi * a) ^ 2 ≤ Real.sin a ^ 2 := by
    have hleft0 : 0 ≤ 2 / Real.pi * a := by positivity
    nlinarith
  have hsina : Real.sin a ^ 2 = Real.sin (θ / 2) ^ 2 := by
    dsimp [a]
    by_cases hθ0 : 0 ≤ θ
    · rw [abs_of_nonneg hθ0]
    · have hθle : θ ≤ 0 := le_of_not_ge hθ0
      rw [abs_of_nonpos hθle]
      have : -θ / 2 = -(θ / 2) := by ring
      rw [this, Real.sin_neg]
      ring
  have hpi0 : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  calc
    θ ^ 2 / Real.pi ^ 2 = (2 / Real.pi * a) ^ 2 := by
      dsimp [a]
      have hratio : 2 / Real.pi * (|θ| / 2) = |θ| / Real.pi := by
        field_simp
      rw [hratio, div_pow, sq_abs]
    _ ≤ Real.sin a ^ 2 := hsquares
    _ = Real.sin (θ / 2) ^ 2 := hsina

/-- **Lemma A.5 (uniform small-frequency curvature).**  For every finite acyclic
simple graph and every bounded positive activity, the `EReal` logarithmic loss is
linear in `variance * θ²` throughout a concrete uniform window. -/
theorem uniformSmallFrequencyCurvature
    {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi)
    (hsmall : (hardCoreLaw G z hz).variance * θ ^ 2 ≤ smallFrequencyScale Z) :
    ((smallFrequencyConstant Z *
      ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) ≤
        (hardCoreLaw G z hz).logarithmicLoss θ := by
  let μ := hardCoreLaw G z hz
  let C := UniformFourthMoment.C4 Z
  let x := μ.variance * θ ^ 2
  have hV0 : 0 ≤ μ.variance := μ.variance_nonneg
  have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg _
  have hx0 : 0 ≤ x := mul_nonneg hV0 hθ2
  by_cases hV : μ.variance ≤ 1
  · have hgap := SimpleGraph.IsAcyclic.uniformCharacteristicFunctionGap
      G hG Z z θ hZ hz hzZ hθ
    have hsin := sq_div_pi_sq_le_sin_half_sq hθ
    have hk0 : 0 ≤ uniformGapConstant Z :=
      uniformGapConstant_nonneg hZ.le
    have hconst : smallFrequencyConstant Z ≤
        uniformGapConstant Z / Real.pi ^ 2 := min_le_left _ _
    have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hreal : smallFrequencyConstant Z * x ≤
        uniformGapConstant Z * min μ.variance 1 * Real.sin (θ / 2) ^ 2 := by
      rw [min_eq_left hV]
      have hleft := mul_le_mul_of_nonneg_right hconst hx0
      have hsinmul := mul_le_mul_of_nonneg_left hsin
        (mul_nonneg hk0 hV0)
      dsimp [x] at hleft ⊢
      calc
        smallFrequencyConstant Z * (μ.variance * θ ^ 2) ≤
            (uniformGapConstant Z / Real.pi ^ 2) *
              (μ.variance * θ ^ 2) := hleft
        _ = (uniformGapConstant Z * μ.variance) *
              (θ ^ 2 / Real.pi ^ 2) := by field_simp
        _ ≤ (uniformGapConstant Z * μ.variance) *
              Real.sin (θ / 2) ^ 2 := hsinmul
        _ = uniformGapConstant Z * μ.variance *
              Real.sin (θ / 2) ^ 2 := by ring
    exact (EReal.coe_le_coe_iff.mpr hreal).trans hgap
  · have hV1 : 1 ≤ μ.variance := le_of_not_ge hV
    have hC0 : 0 ≤ C := by
      dsimp [C]
      exact UniformFourthMoment.C4_nonneg_of_nonneg hZ.le
    have hCpos : 0 < C := by
      dsimp [C]
      exact C4_pos hZ
    have hm4 : μ.centeredMoment 4 ≤
        C * μ.variance * (1 + μ.variance) := by
      dsimp [μ, C]
      simpa [FiniteLatticeLaw.centeredMoment,
        FiniteLatticeLaw.centeredValue] using
        UniformFourthMoment.uniformFourthMoment_A3_card hG z Z hZ hz hzZ
    have hm4large : μ.centeredMoment 4 ≤
        2 * C * μ.variance ^ 2 := by
      calc
        μ.centeredMoment 4 ≤ C * μ.variance * (1 + μ.variance) := hm4
        _ ≤ 2 * C * μ.variance ^ 2 := by
          nlinarith [mul_nonneg hC0 hV0, sq_nonneg μ.variance]
    have hsym : μ.symmetrizedMoment 4 ≤
        32 * C * μ.variance ^ 2 := by
      calc
        μ.symmetrizedMoment 4 ≤ 16 * μ.centeredMoment 4 :=
          μ.symmetrizedMoment_four_le
        _ ≤ 16 * (2 * C * μ.variance ^ 2) := by linarith
        _ = 32 * C * μ.variance ^ 2 := by ring
    have hxfrac : x ≤ 1 / (64 * C) :=
      le_trans hsmall (min_le_right _ _)
    have hxC : 64 * C * x ≤ 1 := by
      have hraw := (le_div_iff₀ (mul_pos (by norm_num) hCpos)).mp hxfrac
      nlinarith
    have hquadratic : 32 * C * x ^ 2 ≤ x / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hxC hx0
      nlinarith
    have hfourth : θ ^ 4 * μ.symmetrizedMoment 4 ≤ x / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hsym (by positivity : 0 ≤ θ ^ 4)
      calc
        θ ^ 4 * μ.symmetrizedMoment 4 ≤
            θ ^ 4 * (32 * C * μ.variance ^ 2) := hmul
        _ = 32 * C * x ^ 2 := by dsimp [x]; ring
        _ ≤ x / 2 := hquadratic
    have hcurvature := μ.one_sub_characteristicModulus_sq_ge θ
    have hsquareloss : x / 2 ≤ 1 - μ.characteristicModulus θ ^ 2 := by
      dsimp [x] at hcurvature ⊢
      linarith
    have hmod0 := μ.characteristicModulus_nonneg θ
    have hmod1 := μ.characteristicModulus_le_one θ
    have hlinear : x / 4 ≤ 1 - μ.characteristicModulus θ := by
      have hfactor : 1 - μ.characteristicModulus θ ^ 2 ≤
          2 * (1 - μ.characteristicModulus θ) := by
        nlinarith
      linarith
    have hconst : smallFrequencyConstant Z ≤ 1 / 4 := min_le_right _ _
    have hreal : smallFrequencyConstant Z * x ≤
        1 - μ.characteristicModulus θ := by
      calc
        smallFrequencyConstant Z * x ≤ (1 / 4 : ℝ) * x :=
          mul_le_mul_of_nonneg_right hconst hx0
        _ = x / 4 := by ring
        _ ≤ 1 - μ.characteristicModulus θ := hlinear
    exact (EReal.coe_le_coe_iff.mpr hreal).trans
      (FiniteLatticeLaw.one_sub_characteristicModulus_le_logarithmicLoss μ θ)

end
end AppendixA
end Forest
end Erdos993
