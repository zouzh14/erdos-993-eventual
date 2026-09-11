import Mathlib

namespace Erdos993.Forest

open Set

/-- The classical rational lower bound for `log (1+r)`. -/
theorem two_mul_div_le_log_one_add (r : ℝ) (hr : 0 ≤ r) :
    2 * r / (2 + r) ≤ Real.log (1 + r) := by
  let f : ℝ → ℝ := fun x => Real.log (1 + x) - 2 * x / (2 + x)
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · intro x hx
      change 0 ≤ x at hx
      have h1 : 1 + x ≠ 0 := by linarith
      have h2 : 2 + x ≠ 0 := by linarith
      exact (((continuousAt_const.add continuousAt_id).log h1).sub
        ((continuousAt_const.mul continuousAt_id).div
          (continuousAt_const.add continuousAt_id) h2)).continuousWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      change 0 < x at hx
      have h1 : 1 + x ≠ 0 := by linarith
      have h2 : 2 + x ≠ 0 := by linarith
      exact ((((hasDerivAt_const x 1).add (hasDerivAt_id x)).log h1).sub
        (((hasDerivAt_id x).const_mul 2).div
          ((hasDerivAt_const x 2).add (hasDerivAt_id x)) h2)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      change 0 < x at hx
      have h1 : 1 + x ≠ 0 := by linarith
      have h2 : 2 + x ≠ 0 := by linarith
      have hdlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
        convert ((hasDerivAt_const x 1).add (hasDerivAt_id x)).log h1 using 1 <;>
          norm_num
      have hdrat : HasDerivAt (fun y : ℝ => 2 * y / (2 + y))
          ((2 * (2 + x) - 2 * x) / (2 + x) ^ 2) x := by
        convert ((hasDerivAt_id x).const_mul 2).div
          ((hasDerivAt_const x 2).add (hasDerivAt_id x)) h2 using 1 <;>
          norm_num
      have hd0 := hdlog.sub hdrat
      have hd : HasDerivAt f (x ^ 2 / ((1 + x) * (2 + x) ^ 2)) x := by
        convert hd0 using 1
        · field_simp
          ring
      rw [hd.deriv]
      exact div_nonneg (sq_nonneg x) (mul_nonneg (by linarith) (sq_nonneg (2 + x)))
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show r ∈ Ici 0 by exact hr) hr
  simpa [f] using h

/-- The rational lower bound implies the denominator estimate used in B.39. -/
theorem activity_div_log_one_add_le (z : ℝ) (hz : 0 < z) :
    z / Real.log (1 + z) ≤ 1 + z / 2 := by
  have hlog := two_mul_div_le_log_one_add z hz.le
  have hlogpos : 0 < Real.log (1 + z) := Real.log_pos (by linarith)
  apply (div_le_iff₀ hlogpos).2
  have hfac : 0 ≤ 1 + z / 2 := by linarith
  have h := mul_le_mul_of_nonneg_left hlog hfac
  calc
    z = (1 + z / 2) * (2 * z / (2 + z)) := by
      field_simp
    _ ≤ (1 + z / 2) * Real.log (1 + z) := h

/-- The second-order Taylor lower bound for the real exponential on the
nonnegative half-line. -/
theorem one_add_add_sq_div_two_le_exp (Y : ℝ) (hY : 0 ≤ Y) :
    1 + Y + Y ^ 2 / 2 ≤ Real.exp Y := by
  let f : ℝ → ℝ := fun x => Real.exp x - (1 + x + x ^ 2 / 2)
  have hmono : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (Real.continuous_exp.sub
        (continuous_const.add continuous_id |>.add
          (continuous_id.pow 2 |>.div_const 2))).continuousOn
    · exact (Real.differentiable_exp.sub
        (differentiable_const 1 |>.add differentiable_id |>.add
          (differentiable_id.pow 2 |>.div_const 2))).differentiableOn
    · intro x hx
      have hdpoly : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2 / 2) (1 + x) x := by
        convert (((hasDerivAt_const x 1).add (hasDerivAt_id x)).add
          ((hasDerivAt_id x).pow 2 |>.div_const 2)) using 1 <;>
          simp only [id_eq] <;> ring
      have hd : HasDerivAt f (Real.exp x - (1 + x)) x := by
        exact (Real.hasDerivAt_exp x).sub hdpoly
      rw [hd.deriv]
      linarith [Real.add_one_le_exp x]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp) (show Y ∈ Ici 0 by exact hY) hY
  simpa [f] using h

/-- The purely rational endpoint in the B.39 estimate. -/
theorem rational_majorant_le_fifteen_sixteenths
    (z Y : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (hY : 0 ≤ Y) :
    z * (1 + z / 2) * Y / (z + (1 + Y + Y ^ 2 / 2)) ≤ (15 / 16 : ℝ) := by
  have hq : 0 < 1 + Y + Y ^ 2 / 2 := by nlinarith [sq_nonneg Y]
  have hdenz : 0 < z + (1 + Y + Y ^ 2 / 2) := by linarith
  have hden15 : 0 < (3 / 2 : ℝ) + (1 + Y + Y ^ 2 / 2) := by linarith
  have hznonneg : 0 ≤ z := hz.le
  have hgap : 0 ≤ (3 / 2 : ℝ) - z := by linarith
  have hbracket :
      0 ≤ (3 / 2 : ℝ) * z / 2 + (1 + Y + Y ^ 2 / 2) *
        (1 + ((3 / 2 : ℝ) + z) / 2) := by positivity
  have hcross :
      z * (1 + z / 2) * Y * ((3 / 2 : ℝ) + (1 + Y + Y ^ 2 / 2)) ≤
        ((3 / 2 : ℝ) * (1 + (3 / 2 : ℝ) / 2) * Y) *
          (z + (1 + Y + Y ^ 2 / 2)) := by
    have hprod : 0 ≤ Y * ((3 / 2 : ℝ) - z) *
        ((3 / 2 : ℝ) * z / 2 + (1 + Y + Y ^ 2 / 2) *
          (1 + ((3 / 2 : ℝ) + z) / 2)) :=
      mul_nonneg (mul_nonneg hY hgap) hbracket
    nlinarith
  have hmono :
      z * (1 + z / 2) * Y / (z + (1 + Y + Y ^ 2 / 2)) ≤
        ((3 / 2 : ℝ) * (1 + (3 / 2 : ℝ) / 2) * Y) /
          ((3 / 2 : ℝ) + (1 + Y + Y ^ 2 / 2)) :=
    (div_le_div_iff₀ hdenz hden15).2 hcross
  calc
    z * (1 + z / 2) * Y / (z + (1 + Y + Y ^ 2 / 2)) ≤
        ((3 / 2 : ℝ) * (1 + (3 / 2 : ℝ) / 2) * Y) /
          ((3 / 2 : ℝ) + (1 + Y + Y ^ 2 / 2)) := hmono
    _ = ((21 / 8 : ℝ) * Y) / ((5 / 2 : ℝ) + Y + Y ^ 2 / 2) := by ring
    _ ≤ (15 / 16 : ℝ) := by
      apply (div_le_iff₀ (by nlinarith [sq_nonneg Y] :
        0 < (5 / 2 : ℝ) + Y + Y ^ 2 / 2)).2
      nlinarith [sq_nonneg (5 * Y - 9)]

/-- Scalar B.39: the exact low-activity quadratic contraction constant. -/
theorem lowActivity_quadratic_scalar
    (z Y : ℝ) (hz : 0 < z) (hz15 : z ≤ 3 / 2) (hY : 0 ≤ Y) :
    (z / (z + Real.exp Y)) * ((z / Real.log (1 + z)) * Y) ≤ (15 / 16 : ℝ) := by
  have hlogpos : 0 < Real.log (1 + z) := Real.log_pos (by linarith)
  have hzlog : z / Real.log (1 + z) ≤ 1 + z / 2 :=
    activity_div_log_one_add_le z hz
  have hexp : 1 + Y + Y ^ 2 / 2 ≤ Real.exp Y :=
    one_add_add_sq_div_two_le_exp Y hY
  have hpolypos : 0 < 1 + Y + Y ^ 2 / 2 := by nlinarith [sq_nonneg Y]
  have hdenpoly : 0 < z + (1 + Y + Y ^ 2 / 2) := by linarith
  have hdenexp : 0 < z + Real.exp Y := by positivity
  have hfrac :
      z / (z + Real.exp Y) ≤ z / (z + (1 + Y + Y ^ 2 / 2)) := by
    apply div_le_div_of_nonneg_left hz.le hdenpoly
    linarith
  have hleft : 0 ≤ z / (z + Real.exp Y) := div_nonneg hz.le hdenexp.le
  have hright : 0 ≤ (1 + z / 2) * Y := mul_nonneg (by linarith) hY
  calc
    (z / (z + Real.exp Y)) * ((z / Real.log (1 + z)) * Y) ≤
        (z / (z + Real.exp Y)) * ((1 + z / 2) * Y) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hzlog hY) hleft
    _ ≤ (z / (z + (1 + Y + Y ^ 2 / 2))) * ((1 + z / 2) * Y) :=
      mul_le_mul_of_nonneg_right hfrac hright
    _ = z * (1 + z / 2) * Y / (z + (1 + Y + Y ^ 2 / 2)) := by ring
    _ ≤ (15 / 16 : ℝ) := rational_majorant_le_fifteen_sixteenths z Y hz hz15 hY

noncomputable def expPoly5 (Y : ℝ) : ℝ :=
  1 + Y + Y^2/2 + Y^3/6 + Y^4/24 + Y^5/120

lemma expPoly5_le_exp (Y : ℝ) (hY : 0 ≤ Y) : expPoly5 Y ≤ Real.exp Y := by
  have h := Real.sum_le_exp_of_nonneg hY 6
  norm_num [expPoly5, Finset.sum_range_succ] at h ⊢
  nlinarith

lemma cubic_poly_nonneg (Y : ℝ) (hY : 0 ≤ Y) :
    0 ≤ 3*Y^5 + 15*Y^4 + 60*Y^3 - 549*Y^2 + 360*Y + 900 := by
  by_cases h1 : Y ≤ 1
  · have hy2 : Y^2 ≤ Y := by nlinarith [mul_nonneg hY (sub_nonneg.2 h1)]
    have h3 : 0 ≤ Y^3 := by positivity
    have h4 : 0 ≤ Y^4 := by positivity
    have h5 : 0 ≤ Y^5 := by positivity
    nlinarith
  · have hy1 : 1 ≤ Y := le_of_not_ge h1
    by_cases h2 : Y ≤ 2
    · let s := 2-Y
      have hs0 : 0 ≤ s := by dsimp [s]; linarith
      have hs1 : s ≤ 1 := by dsimp [s]; linarith
      have hs3 : s^3 ≤ s^2 := by nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hs1)]
      have hs5 : s^5 ≤ s^2 := by
        have hs2 : s^2 ≤ 1 := by nlinarith [sq_nonneg (s-1)]
        nlinarith [mul_nonneg (sq_nonneg s) (sub_nonneg.2 hs2)]
      have hs2n : 0 ≤ s^2 := sq_nonneg s
      have hs4 : 0 ≤ s^4 := by positivity
      nlinarith
    · let t := Y-2
      have ht : 0 ≤ t := by dsimp [t]; linarith
      have ht3 : 0 ≤ t^3 := by positivity
      have ht4 : 0 ≤ t^4 := by positivity
      have ht5 : 0 ≤ t^5 := by positivity
      have hsq : 0 ≤ (411*t-198)^2 := sq_nonneg _
      nlinarith

lemma cubic_rational_endpoint (Y : ℝ) (hY : 0 ≤ Y) :
    ((3/2 : ℝ) * (81/64) * Y^2) / ((3/2 : ℝ) + expPoly5 Y) ≤ (15/16 : ℝ) := by
  have hp := cubic_poly_nonneg Y hY
  have hden : 0 < (3/2 : ℝ) + expPoly5 Y := by
    unfold expPoly5
    positivity
  apply (div_le_iff₀ hden).2
  unfold expPoly5
  nlinarith

/-- Scalar B.43 via a fifth-order Taylor lower bound. -/
theorem lowActivity_cubic_scalar (z Y : ℝ) (hz : 0 < z)
    (hz15 : z ≤ 3/2) (hY : 0 ≤ Y) :
    (z / (z + Real.exp Y)) * ((9/8 : ℝ) * Y)^2 ≤ (15/16 : ℝ) := by
  have hpoly := expPoly5_le_exp Y hY
  have hp0 : 0 < expPoly5 Y := by unfold expPoly5; positivity
  have he0 : 0 < Real.exp Y := Real.exp_pos Y
  have hdenz : 0 < z + Real.exp Y := by positivity
  have hdenp : 0 < z + expPoly5 Y := by positivity
  have hfrac1 : z / (z + Real.exp Y) ≤ z / (z + expPoly5 Y) := by
    apply div_le_div_of_nonneg_left hz.le hdenp
    linarith
  have hden15 : 0 < (3/2 : ℝ) + expPoly5 Y := by positivity
  have hfrac2 : z / (z + expPoly5 Y) ≤ (3/2 : ℝ) / ((3/2 : ℝ) + expPoly5 Y) := by
    apply (div_le_div_iff₀ hdenp hden15).2
    nlinarith
  have hsq : 0 ≤ ((9/8 : ℝ) * Y)^2 := sq_nonneg _
  calc
    (z / (z + Real.exp Y)) * ((9/8 : ℝ) * Y)^2 ≤
      (z / (z + expPoly5 Y)) * ((9/8 : ℝ) * Y)^2 :=
        mul_le_mul_of_nonneg_right hfrac1 hsq
    _ ≤ ((3/2 : ℝ) / ((3/2 : ℝ) + expPoly5 Y)) * ((9/8 : ℝ) * Y)^2 :=
        mul_le_mul_of_nonneg_right hfrac2 hsq
    _ = ((3/2 : ℝ) * (81/64) * Y^2) / ((3/2 : ℝ) + expPoly5 Y) := by ring
    _ ≤ (15/16 : ℝ) := cubic_rational_endpoint Y hY

/-- Uniform child log-odds comparison used in B.42. -/
theorem odds_div_sqrt_le_nine_eighths_log (r : ℝ)
    (hr : 0 ≤ r) (hr15 : r ≤ 3/2) :
    r / Real.sqrt (1+r) ≤ (9/8 : ℝ) * Real.log (1+r) := by
  have hs : 0 < Real.sqrt (1+r) := Real.sqrt_pos.2 (by linarith)
  have hsq : (2+r)^2 ≤ (81/16 : ℝ) * (1+r) := by
    have hr2 : r^2 ≤ (3/2 : ℝ)*r := by nlinarith [mul_nonneg hr (sub_nonneg.2 hr15)]
    nlinarith
  have hlin : 2+r ≤ (9/4 : ℝ) * Real.sqrt (1+r) := by
    have hsquare := Real.sq_sqrt (by linarith : 0 ≤ 1+r)
    nlinarith [sq_nonneg ((2+r) - (9/4 : ℝ)*Real.sqrt (1+r))]
  have hrat : r / Real.sqrt (1+r) ≤ (9/8 : ℝ) * (2*r/(2+r)) := by
    by_cases hzero : r = 0
    · simp [hzero]
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hzero)
      apply (div_le_iff₀ hs).2
      rw [show (9/8 : ℝ) * (2*r/(2+r)) * Real.sqrt (1+r) =
        ((9/4 : ℝ)*r*Real.sqrt (1+r))/(2+r) by ring]
      apply (le_div_iff₀ (by linarith : 0 < 2+r)).2
      have hh := mul_le_mul_of_nonneg_left hlin hr
      nlinarith
  have hlog := two_mul_div_le_log_one_add r hr
  nlinarith

end Erdos993.Forest
