import Erdos993.Forest.TransferMatrixAlgebra

/-!
# Two-row transfer payment

Zero-safe geometric and decrement estimates used in Appendix A, Sublemma A.8.2.
-/

namespace Erdos993.Forest.AppendixA

noncomputable section
set_option maxHeartbeats 800000

/-- The direction from one endpoint of a triangle to its sum is paid by the
triangle deficit.  This is the argument-free rationalization used in A.51. -/
theorem endpoint_chordal_le_triangle_deficit
    (A R : ℝ) (u v : ℂ)
    (hA : 0 ≤ A) (hR : 0 ≤ R) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    A / 2 * ‖u - v‖ ^ 2 ≤
      A + ‖(R : ℂ) * v - (A : ℂ) * u‖ - R := by
  let Y := ‖(R : ℂ) * v - (A : ℂ) * u‖
  let d := ‖u - v‖
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have hnormR : ‖(R : ℂ) * v‖ = R := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR, hv, mul_one]
  have hnormA : ‖(A : ℂ) * u‖ = A := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, hu, mul_one]
  have hupper : Y ≤ R + A := by
    dsimp [Y]
    exact (norm_sub_le _ _).trans_eq (by rw [hnormR, hnormA])
  have hlowerRA : R - A ≤ Y := by
    have htri : ‖(R : ℂ) * v‖ ≤
        ‖(R : ℂ) * v - (A : ℂ) * u‖ + ‖(A : ℂ) * u‖ := by
      calc
        ‖(R : ℂ) * v‖ =
            ‖((R : ℂ) * v - (A : ℂ) * u) + (A : ℂ) * u‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    rw [hnormR, hnormA] at htri
    exact sub_le_iff_le_add.mpr htri
  have hlowerAR : A - R ≤ Y := by
    have htri : ‖(A : ℂ) * u‖ ≤
        ‖(A : ℂ) * u - (R : ℂ) * v‖ + ‖(R : ℂ) * v‖ := by
      calc
        ‖(A : ℂ) * u‖ =
            ‖((A : ℂ) * u - (R : ℂ) * v) + (R : ℂ) * v‖ := by congr 1 <;> ring
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev, show ‖(R : ℂ) * v - (A : ℂ) * u‖ = Y by rfl,
      hnormR, hnormA] at htri
    exact sub_le_iff_le_add.mpr htri
  have hcross :
      (((R : ℂ) * v) * starRingEnd ℂ ((A : ℂ) * u)).re =
        R * A * (v * starRingEnd ℂ u).re := by
    have hcpx :
        ((R : ℂ) * v) * starRingEnd ℂ ((A : ℂ) * u) =
          (((R * A : ℝ) : ℂ) * (v * starRingEnd ℂ u)) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hcpx, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hYsq :
      Y ^ 2 = R ^ 2 + A ^ 2 - 2 * R * A * (v * starRingEnd ℂ u).re := by
    dsimp [Y]
    rw [norm_sub_sq]
    rw [hnormR, hnormA, hcross]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hduv : ‖v - u‖ = d := by
    dsimp [d]
    rw [norm_sub_rev]
  have hdsq :
      d ^ 2 = 2 - 2 * (v * starRingEnd ℂ u).re := by
    have h := norm_sub_sq v u
    rw [hduv, hv, hu] at h
    nlinarith
  have hid : Y ^ 2 = (R - A) ^ 2 + A * R * d ^ 2 := by
    rw [hYsq, hdsq]
    ring
  by_cases hRzero : R = 0
  · have hbase : A / 2 * d ^ 2 ≤ 2 * A := by
      have hdle : d ≤ 2 := by
        dsimp [d]
        calc
          ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le _ _
          _ = 2 := by rw [hu, hv]; norm_num
      have hdsqle : d ^ 2 ≤ 4 := by nlinarith
      nlinarith [mul_nonneg hA (sq_nonneg d)]
    subst R
    dsimp [Y, d] at *
    simp only [Complex.ofReal_zero, zero_mul, zero_sub, sub_zero]
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hA, hu, mul_one]
    nlinarith
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hRzero)
    apply (mul_le_mul_iff_right₀ hRpos).mp
    by_cases hRA : A ≤ R
    · have hD0 : 0 ≤ A + Y - R := by linarith
      have hfac0 : 0 ≤ Y + R - A := by linarith
      have hfac : A * R * d ^ 2 = (A + Y - R) * (Y + R - A) := by
        nlinarith [hid]
      have hfac_le : Y + R - A ≤ 2 * R := by linarith
      have hmul := mul_le_mul_of_nonneg_left hfac_le hD0
      rw [← hfac] at hmul
      nlinarith
    · have hAR : R ≤ A := le_of_not_ge hRA
      have hD0 : 0 ≤ A + Y - R := by linarith
      have hfac0 : 0 ≤ Y - A + R := by linarith
      have hfac : A * R * d ^ 2 = (A + Y - R) * (Y - A + R) := by
        nlinarith [hid]
      have hfac_le : Y - A + R ≤ 2 * R := by linarith
      have hmul := mul_le_mul_of_nonneg_left hfac_le hD0
      rw [← hfac] at hmul
      nlinarith

/-- Normalizing a nonzero complex number gives a unit vector. -/
theorem norm_div_norm (z : ℂ) (hz : z ≠ 0) :
    ‖z / (‖z‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (norm_pos_iff.mpr hz)]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- Reconstruction after normalization. -/
theorem norm_mul_div_norm (z : ℂ) (hz : z ≠ 0) :
    (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by
  field_simp [norm_ne_zero_iff.mpr hz]

/-- Radial distance to the normalized direction. -/
theorem norm_sub_div_norm (z : ℂ) (hz : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖z - z / (‖z‖ : ℂ)‖ = 1 - ‖z‖ := by
  let uz := z / (‖z‖ : ℂ)
  have huz : ‖uz‖ = 1 := norm_div_norm z hz
  have hrec : (‖z‖ : ℂ) * uz = z := norm_mul_div_norm z hz
  have heq : z - uz = ((‖z‖ - 1 : ℝ) : ℂ) * uz := by
    calc
      z - uz = (‖z‖ : ℂ) * uz - uz := congrArg (fun w : ℂ => w - uz) hrec.symm
      _ = ((‖z‖ - 1 : ℝ) : ℂ) * uz := by
        push_cast
        ring
  rw [heq, norm_mul, huz, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hz1)]
  ring

/-- A raw chord is controlled by two directional chords and the two radial
defects.  This is the zero-safe replacement for the circular triangle
inequality in A.50. -/
theorem raw_chord_sq_le_directions
    (a p x s : ℂ)
    (ha0 : a ≠ 0) (hp0 : p ≠ 0) (hx0 : x ≠ 0) (hs0 : s ≠ 0)
    (ha1 : ‖a‖ ≤ 1) (hp1 : ‖p‖ ≤ 1) :
    ‖a - p‖ ^ 2 ≤
      4 * (‖x / (‖x‖ : ℂ) - s / (‖s‖ : ℂ)‖ ^ 2 +
        ‖(a / (‖a‖ : ℂ)) * (s / (‖s‖ : ℂ)) -
          (p / (‖p‖ : ℂ)) * (x / (‖x‖ : ℂ))‖ ^ 2 +
        (1 - ‖a‖) + (1 - ‖p‖)) := by
  let ua := a / (‖a‖ : ℂ)
  let vp := p / (‖p‖ : ℂ)
  let ux := x / (‖x‖ : ℂ)
  let us := s / (‖s‖ : ℂ)
  let d0 := ‖ux - us‖
  let d1 := ‖ua * us - vp * ux‖
  let dn := ‖ua - vp‖
  have hua : ‖ua‖ = 1 := norm_div_norm a ha0
  have hvp : ‖vp‖ = 1 := norm_div_norm p hp0
  have hux : ‖ux‖ = 1 := norm_div_norm x hx0
  have hus : ‖us‖ = 1 := norm_div_norm s hs0
  have hdir : dn ≤ d1 + d0 := by
    have heq : (ua - vp) * ux =
        (ua * us - vp * ux) - ua * (us - ux) := by ring
    have hnormeq : dn = ‖(ua - vp) * ux‖ := by
      rw [norm_mul, hux, mul_one]
    rw [hnormeq, heq]
    calc
      ‖(ua * us - vp * ux) - ua * (us - ux)‖ ≤
          ‖ua * us - vp * ux‖ + ‖ua * (us - ux)‖ := norm_sub_le _ _
      _ = d1 + d0 := by
        dsimp [d1, d0]
        rw [norm_mul, hua, one_mul]
        congr 1
        exact norm_sub_rev us ux
  have hdirsq : dn ^ 2 ≤ 2 * (d1 ^ 2 + d0 ^ 2) := by
    have hd00 : 0 ≤ d0 := norm_nonneg _
    have hd10 : 0 ≤ d1 := norm_nonneg _
    have hdn0 : 0 ≤ dn := norm_nonneg _
    have hsq : (d1 + d0) ^ 2 ≤ 2 * (d1 ^ 2 + d0 ^ 2) := by
      nlinarith [sq_nonneg (d1 - d0)]
    nlinarith
  let da := 1 - ‖a‖
  let dp := 1 - ‖p‖
  have hda0 : 0 ≤ da := sub_nonneg.mpr ha1
  have hdp0 : 0 ≤ dp := sub_nonneg.mpr hp1
  have hda1 : da ≤ 1 := by dsimp [da]; linarith [norm_nonneg a]
  have hdp1 : dp ≤ 1 := by dsimp [dp]; linarith [norm_nonneg p]
  have hrad : da ^ 2 ≤ da := by nlinarith
  have hradp : dp ^ 2 ≤ dp := by nlinarith
  have he : (da + dp) ^ 2 ≤ 2 * (da + dp) := by
    nlinarith [sq_nonneg (da - dp)]
  have hraw : ‖a - p‖ ≤ da + dn + dp := by
    calc
      ‖a - p‖ = ‖(a - ua) + (ua - vp) + (vp - p)‖ := by
        congr 1
        ring
      _ ≤ ‖(a - ua) + (ua - vp)‖ + ‖vp - p‖ :=
        norm_add_le _ _
      _ ≤ (‖a - ua‖ + ‖ua - vp‖) + ‖vp - p‖ :=
        add_le_add (norm_add_le _ _) (le_refl _)
      _ = da + dn + dp := by
        rw [show ‖a - ua‖ = da by
          dsimp [ua, da]
          exact norm_sub_div_norm a ha0 ha1]
        rw [show ‖vp - p‖ = dp by
          rw [norm_sub_rev]
          dsimp [vp, dp]
          exact norm_sub_div_norm p hp0 hp1]
  have hraw0 : 0 ≤ ‖a - p‖ := norm_nonneg _
  have hsum0 : 0 ≤ da + dn + dp := by positivity
  have hrawsq : ‖a - p‖ ^ 2 ≤ (da + dn + dp) ^ 2 :=
    (sq_le_sq₀ hraw0 hsum0).2 hraw
  have hsplit : (da + dn + dp) ^ 2 ≤ 2 * dn ^ 2 + 4 * (da + dp) := by
    have htwo : (dn + (da + dp)) ^ 2 ≤
        2 * (dn ^ 2 + (da + dp) ^ 2) := by
      nlinarith [sq_nonneg (dn - (da + dp))]
    nlinarith
  dsimp [ua, vp, ux, us, d0, d1, dn, da, dp] at *
  nlinarith

/-- The triangle part of A.49 is nonnegative and is bounded by the whole
one-row decrement. -/
theorem triangleDeficit_le_decrement
    (K : TransferCoefficient) (r : ComplexRow) (hK : K.Admissible) :
    0 ≤ K.q * ‖r.fst‖ + ‖r.snd‖ -
          ‖(K.q : ℂ) * r.fst + r.snd‖ ∧
    K.q * ‖r.fst‖ + ‖r.snd‖ -
          ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
      r.normOne - (K.applyRow r).normOne := by
  let D := K.q * ‖r.fst‖ + ‖r.snd‖ -
    ‖(K.q : ℂ) * r.fst + r.snd‖
  have htri : ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
      K.q * ‖r.fst‖ + ‖r.snd‖ := by
    calc
      ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
          ‖(K.q : ℂ) * r.fst‖ + ‖r.snd‖ := norm_add_le _ _
      _ = K.q * ‖r.fst‖ + ‖r.snd‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hK.q_nonneg]
  have hD0 : 0 ≤ D := sub_nonneg.mpr htri
  have ha0 : 0 ≤ 1 - ‖K.a‖ := sub_nonneg.mpr hK.norm_a_le_one
  have hc0 : 0 ≤ 1 - ‖K.c‖ := sub_nonneg.mpr hK.norm_c_le_one
  have hmix0 : 0 ≤ ‖(K.q : ℂ) * r.fst + r.snd‖ := norm_nonneg _
  have hx0 : 0 ≤ ‖r.fst‖ := norm_nonneg _
  constructor
  · exact hD0
  · rw [K.decrement_identity r hK.q_nonneg hK.b_nonneg
      hK.q_add_b hK.norm_phase]
    nlinarith [mul_nonneg ha0 hmix0,
      mul_nonneg (mul_nonneg hK.b_nonneg hc0) hx0]

/-- Every admissible update has a nonnegative decrement. -/
theorem transferDecrement_nonneg
    (K : TransferCoefficient) (r : ComplexRow) (hK : K.Admissible) :
    0 ≤ r.normOne - (K.applyRow r).normOne := by
  exact sub_nonneg.mpr (K.normOne_applyRow_le r hK.q_nonneg hK.b_nonneg
    hK.q_add_b hK.norm_a_le_one hK.norm_c_le_one hK.norm_phase)

set_option maxHeartbeats 8000000 in
/-- Argument-free Sublemma A.8.2.  Two consecutive admissible rows pay the
weighted radial/chordal energy of the first coefficient.  The explicit
constant depends only on the common vacancy floor `η`. -/
theorem two_row_chordal_payment
    (K J : TransferCoefficient) (r : ComplexRow) (η : ℝ)
    (hK : K.Admissible) (hJ : J.Admissible)
    (hη : 0 < η) (hqK : η ≤ K.q) (hqJ : η ≤ J.q) :
    ‖r.fst‖ *
        (K.q * (1 - ‖K.a‖ ^ 2) +
          K.b * (1 - ‖K.c‖ ^ 2) +
          K.q * K.b * ‖K.a - K.phase * K.c‖ ^ 2) ≤
      (64 / η ^ 2) *
        ((r.normOne - (K.applyRow r).normOne) +
          ((K.applyRow r).normOne -
            (J.applyRow (K.applyRow r)).normOne)) := by
  let x := r.fst
  let y := r.snd
  let S := (K.q : ℂ) * x + y
  let X := ‖x‖
  let Y := ‖y‖
  let R := ‖S‖
  let A := ‖K.a‖
  let C := ‖K.c‖
  let p := K.phase * K.c
  let Δ0 := r.normOne - (K.applyRow r).normOne
  let Δ1 := (K.applyRow r).normOne -
    (J.applyRow (K.applyRow r)).normOne
  let D0 := K.q * X + Y - R
  let D1 := J.q * ‖(K.applyRow r).fst‖ + ‖(K.applyRow r).snd‖ -
    ‖(J.q : ℂ) * (K.applyRow r).fst + (K.applyRow r).snd‖
  have hq1 : K.q ≤ 1 := by linarith [hK.q_add_b, hK.b_nonneg]
  have hb1 : K.b ≤ 1 := by linarith [hK.q_add_b, hK.q_nonneg]
  have hqJ1 : J.q ≤ 1 := by linarith [hJ.q_add_b, hJ.b_nonneg]
  have hη1 : η ≤ 1 := hqK.trans hq1
  have hη0 : 0 ≤ η := hη.le
  have hηsq0 : 0 < η ^ 2 := sq_pos_of_pos hη
  have hrate0 : 0 ≤ 64 / η ^ 2 := div_nonneg (by norm_num) hηsq0.le
  have hηsq1 : η ^ 2 ≤ 1 := by nlinarith
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hR0 : 0 ≤ R := norm_nonneg _
  have hA0 : 0 ≤ A := norm_nonneg _
  have hC0 : 0 ≤ C := norm_nonneg _
  have hA1 : A ≤ 1 := hK.norm_a_le_one
  have hC1 : C ≤ 1 := hK.norm_c_le_one
  have hpNorm : ‖p‖ = C := by dsimp [p, C]; rw [norm_mul, hK.norm_phase, one_mul]
  have hΔ00 : 0 ≤ Δ0 := by
    dsimp [Δ0]
    exact transferDecrement_nonneg K r hK
  have hΔ10 : 0 ≤ Δ1 := by
    dsimp [Δ1]
    exact transferDecrement_nonneg J (K.applyRow r) hJ
  have hD0pair := triangleDeficit_le_decrement K r hK
  have hD00 : 0 ≤ D0 := by simpa [D0, X, Y, R, S, x, y] using hD0pair.1
  have hD0Δ : D0 ≤ Δ0 := by simpa [D0, X, Y, R, S, x, y, Δ0] using hD0pair.2
  have hdecomp : Δ0 = D0 + (1 - A) * R + K.b * (1 - C) * X := by
    dsimp [Δ0, D0, A, C, R, S, X, Y, x, y]
    rw [K.decrement_identity r hK.q_nonneg hK.b_nonneg
      hK.q_add_b hK.norm_phase]
  have hD1pair := triangleDeficit_le_decrement J (K.applyRow r) hJ
  have hD10 : 0 ≤ D1 := by simpa [D1] using hD1pair.1
  have hD1Δ : D1 ≤ Δ1 := by simpa [D1, Δ1] using hD1pair.2
  have hda0 : 0 ≤ 1 - A := sub_nonneg.mpr hA1
  have hdc0 : 0 ≤ 1 - C := sub_nonneg.mpr hC1
  have hmix : R ≤ K.q * X + Y := by
    dsimp [R, S, X, Y, x, y]
    calc
      ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
          ‖(K.q : ℂ) * r.fst‖ + ‖r.snd‖ := norm_add_le _ _
      _ = K.q * ‖r.fst‖ + ‖r.snd‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hK.q_nonneg]
  have hqXda : K.q * X * (1 - A) ≤ Δ0 := by
    have hqx : K.q * X ≤ D0 + R := by
      dsimp [D0]
      linarith
    have hmul := mul_le_mul_of_nonneg_right hqx hda0
    have hDscale : D0 * (1 - A) ≤ D0 :=
      mul_le_of_le_one_right hD00 (by linarith [hA0])
    calc
      K.q * X * (1 - A) ≤ (D0 + R) * (1 - A) := hmul
      _ = D0 * (1 - A) + (1 - A) * R := by ring
      _ ≤ D0 + (1 - A) * R := add_le_add hDscale (le_refl _)
      _ ≤ Δ0 := by
        rw [hdecomp]
        exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hK.b_nonneg hdc0) hX0)
  have hbXdc : K.b * X * (1 - C) ≤ Δ0 := by
    rw [hdecomp]
    have hfirst : 0 ≤ D0 + (1 - A) * R := by positivity
    nlinarith
  have hradA : K.q * X * (1 - A ^ 2) ≤ 2 * Δ0 := by
    have hs : 1 - A ^ 2 ≤ 2 * (1 - A) := by nlinarith [sq_nonneg (1 - A)]
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hK.q_nonneg hX0)
    nlinarith
  have hradC : K.b * X * (1 - C ^ 2) ≤ 2 * Δ0 := by
    have hs : 1 - C ^ 2 ≤ 2 * (1 - C) := by nlinarith [sq_nonneg (1 - C)]
    have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hK.b_nonneg hX0)
    nlinarith
  have hradial :
      X * (K.q * (1 - A ^ 2) + K.b * (1 - C ^ 2)) ≤ 4 * Δ0 := by
    nlinarith
  have hchord_le : ‖K.a - p‖ ≤ 2 := by
    calc
      ‖K.a - p‖ ≤ ‖K.a‖ + ‖p‖ := norm_sub_le _ _
      _ = A + C := by rw [hpNorm]
      _ ≤ 2 := by linarith
  have hchordsq : ‖K.a - p‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (K.a - p)]
  have finish_of_phase
      (hphasePay : K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤
        60 * Δ0 + (64 / η ^ 2) * Δ1) :
      X * (K.q * (1 - A ^ 2) + K.b * (1 - C ^ 2) +
          K.q * K.b * ‖K.a - p‖ ^ 2) ≤
        (64 / η ^ 2) * (Δ0 + Δ1) := by
    have hcoef : 64 ≤ 64 / η ^ 2 := by
      rw [le_div_iff₀ hηsq0]
      nlinarith
    have hscale := mul_le_mul_of_nonneg_right hcoef hΔ00
    nlinarith
  change X * (K.q * (1 - A ^ 2) + K.b * (1 - C ^ 2) +
      K.q * K.b * ‖K.a - p‖ ^ 2) ≤
    (64 / η ^ 2) * (Δ0 + Δ1)
  by_cases hXz : X = 0
  · simp only [hXz, zero_mul]
    exact mul_nonneg hrate0 (add_nonneg hΔ00 hΔ10)
  by_cases hRsmall : R < K.q * X / 2
  · apply finish_of_phase
    have hDlarge : K.q * X / 2 ≤ D0 := by
      dsimp [D0]
      linarith
    have hp0 : K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * D0 := by
      calc
        K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤
            (K.q * K.b * X) * 4 :=
          mul_le_mul_of_nonneg_left hchordsq
            (mul_nonneg (mul_nonneg hK.q_nonneg hK.b_nonneg) hX0)
        _ ≤ (K.q * X) * 4 := by
          have hbase : K.q * K.b * X ≤ K.q * X := by
            calc
              K.q * K.b * X = K.b * (K.q * X) := by ring
              _ ≤ 1 * (K.q * X) :=
                mul_le_mul_of_nonneg_right hb1 (mul_nonneg hK.q_nonneg hX0)
              _ = K.q * X := one_mul _
          exact mul_le_mul_of_nonneg_right hbase (by norm_num)
        _ ≤ 8 * D0 := by nlinarith
    have hpaid := hp0.trans (mul_le_mul_of_nonneg_left hD0Δ (by norm_num))
    calc
      K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * Δ0 := hpaid
      _ ≤ 60 * Δ0 :=
        mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 60) hΔ00
      _ ≤ 60 * Δ0 + (64 / η ^ 2) * Δ1 :=
        le_add_of_nonneg_right (mul_nonneg hrate0 hΔ10)
  by_cases hAsmall : A < 1 / 2
  · apply finish_of_phase
    have hhalf : (1 / 2 : ℝ) ≤ 1 - A := by linarith
    have hlarge : K.q * X / 2 ≤ K.q * X * (1 - A) := by
      rw [div_eq_mul_inv]
      norm_num
      exact mul_le_mul_of_nonneg_left hhalf (mul_nonneg hK.q_nonneg hX0)
    have hp0 : K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * Δ0 := by
      calc
        K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤
            (K.q * K.b * X) * 4 :=
          mul_le_mul_of_nonneg_left hchordsq
            (mul_nonneg (mul_nonneg hK.q_nonneg hK.b_nonneg) hX0)
        _ ≤ (K.q * X) * 4 := by
          have hbase : K.q * K.b * X ≤ K.q * X := by
            calc
              K.q * K.b * X = K.b * (K.q * X) := by ring
              _ ≤ 1 * (K.q * X) :=
                mul_le_mul_of_nonneg_right hb1 (mul_nonneg hK.q_nonneg hX0)
              _ = K.q * X := one_mul _
          exact mul_le_mul_of_nonneg_right hbase (by norm_num)
        _ ≤ 8 * (K.q * X * (1 - A)) := by nlinarith
        _ ≤ 8 * Δ0 := mul_le_mul_of_nonneg_left hqXda (by norm_num)
    calc
      K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * Δ0 := hp0
      _ ≤ 60 * Δ0 :=
        mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 60) hΔ00
      _ ≤ 60 * Δ0 + (64 / η ^ 2) * Δ1 :=
        le_add_of_nonneg_right (mul_nonneg hrate0 hΔ10)
  by_cases hCsmall : C < 1 / 2
  · apply finish_of_phase
    have hhalf : (1 / 2 : ℝ) ≤ 1 - C := by linarith
    have hlarge : K.b * X / 2 ≤ K.b * X * (1 - C) := by
      rw [div_eq_mul_inv]
      norm_num
      exact mul_le_mul_of_nonneg_left hhalf (mul_nonneg hK.b_nonneg hX0)
    have hp0 : K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * Δ0 := by
      calc
        K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤
            (K.q * K.b * X) * 4 :=
          mul_le_mul_of_nonneg_left hchordsq
            (mul_nonneg (mul_nonneg hK.q_nonneg hK.b_nonneg) hX0)
        _ ≤ (K.b * X) * 4 := by
          have hbase : K.q * K.b * X ≤ K.b * X := by
            calc
              K.q * K.b * X = K.q * (K.b * X) := by ring
              _ ≤ 1 * (K.b * X) :=
                mul_le_mul_of_nonneg_right hq1 (mul_nonneg hK.b_nonneg hX0)
              _ = K.b * X := one_mul _
          exact mul_le_mul_of_nonneg_right hbase (by norm_num)
        _ ≤ 8 * (K.b * X * (1 - C)) := by nlinarith
        _ ≤ 8 * Δ0 := mul_le_mul_of_nonneg_left hbXdc (by norm_num)
    calc
      K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤ 8 * Δ0 := hp0
      _ ≤ 60 * Δ0 :=
        mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 60) hΔ00
      _ ≤ 60 * Δ0 + (64 / η ^ 2) * Δ1 :=
        le_add_of_nonneg_right (mul_nonneg hrate0 hΔ10)
  by_cases hbzero : K.b = 0
  · apply finish_of_phase
    rw [hbzero]
    simp only [mul_zero, zero_mul]
    exact add_nonneg (mul_nonneg (by norm_num) hΔ00)
      (mul_nonneg hrate0 hΔ10)
  · have hXpos : 0 < X := lt_of_le_of_ne hX0 (Ne.symm hXz)
    have hqpos : 0 < K.q := lt_of_lt_of_le hη hqK
    have hRlarge : K.q * X / 2 ≤ R := le_of_not_gt hRsmall
    have hRpos : 0 < R := lt_of_lt_of_le (by positivity : 0 < K.q * X / 2) hRlarge
    have hAhalf : 1 / 2 ≤ A := le_of_not_gt hAsmall
    have hChalf : 1 / 2 ≤ C := le_of_not_gt hCsmall
    have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hAhalf
    have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hChalf
    have hx0 : x ≠ 0 := norm_pos_iff.mp (by simpa [X] using hXpos)
    have hS0 : S ≠ 0 := norm_pos_iff.mp (by simpa [R] using hRpos)
    have ha0 : K.a ≠ 0 := norm_pos_iff.mp (by simpa [A] using hApos)
    have hp0 : p ≠ 0 := norm_pos_iff.mp (by rw [hpNorm]; exact hCpos)
    let ux := x / (X : ℂ)
    let us := S / (R : ℂ)
    let ua := K.a / (A : ℂ)
    let vp := p / (C : ℂ)
    let d0 := ‖ux - us‖
    let d1 := ‖ua * us - vp * ux‖
    have hux : ‖ux‖ = 1 := by simpa [ux, X] using norm_div_norm x hx0
    have hus : ‖us‖ = 1 := by simpa [us, R] using norm_div_norm S hS0
    have hua : ‖ua‖ = 1 := by simpa [ua, A] using norm_div_norm K.a ha0
    have hvp : ‖vp‖ = 1 := by simpa [vp, C, hpNorm] using norm_div_norm p hp0
    have hrecx : (X : ℂ) * ux = x := by simpa [ux, X] using norm_mul_div_norm x hx0
    have hrecS : (R : ℂ) * us = S := by simpa [us, R] using norm_mul_div_norm S hS0
    have hreca : (A : ℂ) * ua = K.a := by simpa [ua, A] using norm_mul_div_norm K.a ha0
    have hrecp : (C : ℂ) * vp = p := by
      have := norm_mul_div_norm p hp0
      rw [hpNorm] at this
      simpa [vp] using this
    have hcur0 := endpoint_chordal_le_triangle_deficit
      (K.q * X) R ux us (mul_nonneg hK.q_nonneg hX0) hR0 hux hus
    have hcur : K.q * X / 2 * d0 ^ 2 ≤ D0 := by
      have hqxrec : ((K.q * X : ℝ) : ℂ) * ux = (K.q : ℂ) * x := by
        rw [Complex.ofReal_mul, mul_assoc, hrecx]
      have hvec : (R : ℂ) * us - ((K.q * X : ℝ) : ℂ) * ux = y := by
        rw [hrecS, hqxrec]
        dsimp [S]
        ring
      dsimp [d0]
      rw [hvec] at hcur0
      simpa [D0, Y] using hcur0
    let U := J.q * A * R
    let W := K.b * C * X
    have hU0 : 0 ≤ U := by
      dsimp [U]
      exact mul_nonneg (mul_nonneg hJ.q_nonneg hA0) hR0
    have hW0 : 0 ≤ W := by
      dsimp [W]
      exact mul_nonneg (mul_nonneg hK.b_nonneg hC0) hX0
    have hbpos : 0 < K.b := lt_of_le_of_ne hK.b_nonneg (Ne.symm hbzero)
    have hWpos : 0 < W := by
      dsimp [W]
      exact mul_pos (mul_pos hbpos hCpos) hXpos
    have hUlower : η ^ 2 * X / 4 ≤ U := by
      have hJA : η * (1 / 2 : ℝ) ≤ J.q * A :=
        mul_le_mul hqJ hAhalf (by norm_num) hJ.q_nonneg
      have hηX : η * X / 2 ≤ K.q * X / 2 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hqK hX0) (by norm_num)
      have hRη : η * X / 2 ≤ R := hηX.trans hRlarge
      calc
        η ^ 2 * X / 4 = (η * (1 / 2)) * (η * X / 2) := by ring
        _ ≤ (J.q * A) * R :=
          mul_le_mul hJA hRη (by positivity)
            (mul_nonneg hJ.q_nonneg hA0)
        _ = U := rfl
    have hWlower : K.b * X / 2 ≤ W := by
      calc
        K.b * X / 2 = (K.b * X) * (1 / 2) := by ring
        _ ≤ (K.b * X) * C :=
          mul_le_mul_of_nonneg_left hChalf (mul_nonneg hK.b_nonneg hX0)
        _ = W := by dsimp [W]; ring
    have hnext0 := two_vector_deficit_chordal U W (ua * us) (vp * ux)
      hU0 hW0 (by rw [norm_mul, hua, hus, mul_one])
      (by rw [norm_mul, hvp, hux, mul_one])
    have hnext : U * W * d1 ^ 2 ≤ 2 * (U + W) * D1 := by
      have hxrow : (K.applyRow r).fst = ((A * R : ℝ) : ℂ) * (ua * us) := by
        simp only [TransferCoefficient.applyRow_fst]
        rw [show (K.q : ℂ) * r.fst + r.snd = S by rfl]
        rw [← hreca, ← hrecS]
        push_cast
        ring
      have hyrow : (K.applyRow r).snd = (W : ℂ) * (vp * ux) := by
        simp only [TransferCoefficient.applyRow_snd]
        calc
          ((K.b : ℂ) * K.phase * K.c) * r.fst =
              (K.b : ℂ) * p * x := by dsimp [p, x]; ring
          _ = (W : ℂ) * (vp * ux) := by
            rw [← hrecp, ← hrecx]
            dsimp [W]
            push_cast
            ring
      have hqrow :
          ((J.q : ℂ) * (K.applyRow r).fst + (K.applyRow r).snd) =
            (U : ℂ) * (ua * us) + (W : ℂ) * (vp * ux) := by
        rw [hxrow, hyrow]
        dsimp [U]
        push_cast
        ring
      have hxnorm : ‖(K.applyRow r).fst‖ = A * R := by
        rw [hxrow, norm_mul, norm_mul, hua, hus, mul_one,
          Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg hA0 hR0)]
        ring
      have hynorm : ‖(K.applyRow r).snd‖ = W := by
        rw [hyrow, norm_mul, norm_mul, hvp, hux, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hW0, mul_one]
      have hD1form : D1 = U + W -
          ‖(U : ℂ) * (ua * us) + (W : ℂ) * (vp * ux)‖ := by
        change J.q * ‖(K.applyRow r).fst‖ + ‖(K.applyRow r).snd‖ -
          ‖(J.q : ℂ) * (K.applyRow r).fst + (K.applyRow r).snd‖ = _
        rw [hxnorm, hynorm, hqrow]
        change J.q * (A * R) + W - _ = U + W - _
        dsimp only [U]
        ring
      rw [hD1form]
      simpa [d1, mul_assoc, mul_left_comm, mul_comm] using hnext0
    have hcoef : η ^ 2 * K.b * X * (U + W) ≤ 8 * (U * W) := by
      have htermU : η ^ 2 * K.b * X * U ≤ 2 * (U * W) := by
        have hbx : K.b * X ≤ 2 * W := by
          calc
            K.b * X = 2 * (K.b * X / 2) := by ring
            _ ≤ 2 * W := mul_le_mul_of_nonneg_left hWlower (by norm_num)
        calc
          η ^ 2 * K.b * X * U = η ^ 2 * ((K.b * X) * U) := by ring
          _ ≤ 1 * ((K.b * X) * U) :=
            mul_le_mul_of_nonneg_right hηsq1
              (mul_nonneg (mul_nonneg hK.b_nonneg hX0) hU0)
          _ = (K.b * X) * U := one_mul _
          _ ≤ (2 * W) * U := mul_le_mul_of_nonneg_right hbx hU0
          _ = 2 * (U * W) := by ring
      have htermW : η ^ 2 * K.b * X * W ≤ 4 * (U * W) := by
        have hex : η ^ 2 * X ≤ 4 * U := by
          calc
            η ^ 2 * X = 4 * (η ^ 2 * X / 4) := by ring
            _ ≤ 4 * U := mul_le_mul_of_nonneg_left hUlower (by norm_num)
        calc
          η ^ 2 * K.b * X * W = K.b * ((η ^ 2 * X) * W) := by ring
          _ ≤ 1 * ((η ^ 2 * X) * W) :=
            mul_le_mul_of_nonneg_right hb1
              (mul_nonneg (mul_nonneg hηsq0.le hX0) hW0)
          _ = (η ^ 2 * X) * W := one_mul _
          _ ≤ (4 * U) * W := mul_le_mul_of_nonneg_right hex hW0
          _ = 4 * (U * W) := by ring
      calc
        η ^ 2 * K.b * X * (U + W) =
            η ^ 2 * K.b * X * U + η ^ 2 * K.b * X * W := by ring
        _ ≤ 2 * (U * W) + 4 * (U * W) := add_le_add htermU htermW
        _ = 6 * (U * W) := by ring
        _ ≤ 8 * (U * W) :=
          mul_le_mul_of_nonneg_right (by norm_num : (6 : ℝ) ≤ 8)
            (mul_nonneg hU0 hW0)
    have hsumpos : 0 < U + W :=
      lt_of_lt_of_le hWpos (le_add_of_nonneg_left hU0)
    have hd10 : 0 ≤ d1 ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_right hcoef hd10
    have hchain : η ^ 2 * K.b * X * (U + W) * d1 ^ 2 ≤
        16 * (U + W) * D1 := by
      calc
        _ ≤ 8 * (U * W) * d1 ^ 2 := hscaled
        _ = 8 * (U * W * d1 ^ 2) := by ring
        _ ≤ 8 * (2 * (U + W) * D1) :=
          mul_le_mul_of_nonneg_left hnext (by norm_num : (0 : ℝ) ≤ 8)
        _ = 16 * (U + W) * D1 := by ring
    have hcancel : η ^ 2 * (K.b * X * d1 ^ 2) ≤ 16 * D1 := by
      apply le_of_mul_le_mul_left (a := U + W) _ hsumpos
      calc
        (U + W) * (η ^ 2 * (K.b * X * d1 ^ 2)) =
            η ^ 2 * K.b * X * (U + W) * d1 ^ 2 := by ring
        _ ≤ 16 * (U + W) * D1 := hchain
        _ = (U + W) * (16 * D1) := by ring
    have hd1pay : K.b * X * d1 ^ 2 ≤ (16 / η ^ 2) * D1 := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hηsq0).2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcancel
    have hraw := raw_chord_sq_le_directions K.a p x S ha0 hp0 hx0 hS0
      hA1 (by rw [hpNorm]; exact hC1)
    have hraw' : ‖K.a - p‖ ^ 2 ≤
        4 * (d0 ^ 2 + d1 ^ 2 + (1 - A) + (1 - C)) := by
      simpa [ux, us, ua, vp, d0, d1, X, R, A, C, hpNorm] using hraw
    apply finish_of_phase
    have hphaseExpand := mul_le_mul_of_nonneg_left hraw'
      (mul_nonneg (mul_nonneg hK.q_nonneg hK.b_nonneg) hX0)
    have hd0pay : K.q * K.b * X * d0 ^ 2 ≤ 2 * D0 := by
      calc
        K.q * K.b * X * d0 ^ 2 = K.b * (K.q * X * d0 ^ 2) := by ring
        _ ≤ 1 * (K.q * X * d0 ^ 2) :=
          mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (mul_nonneg hK.q_nonneg hX0) (sq_nonneg d0))
        _ = 2 * (K.q * X / 2 * d0 ^ 2) := by ring
        _ ≤ 2 * D0 := mul_le_mul_of_nonneg_left hcur (by norm_num)
    have hd1pay' : K.q * K.b * X * d1 ^ 2 ≤ (16 / η ^ 2) * D1 := by
      calc
        K.q * K.b * X * d1 ^ 2 = K.q * (K.b * X * d1 ^ 2) := by ring
        _ ≤ 1 * (K.b * X * d1 ^ 2) :=
          mul_le_mul_of_nonneg_right hq1
            (mul_nonneg (mul_nonneg hK.b_nonneg hX0) (sq_nonneg d1))
        _ = K.b * X * d1 ^ 2 := one_mul _
        _ ≤ (16 / η ^ 2) * D1 := hd1pay
    have hdaPay : K.q * K.b * X * (1 - A) ≤ Δ0 := by
      calc
        K.q * K.b * X * (1 - A) = K.b * (K.q * X * (1 - A)) := by ring
        _ ≤ 1 * (K.q * X * (1 - A)) :=
          mul_le_mul_of_nonneg_right hb1
            (mul_nonneg (mul_nonneg hK.q_nonneg hX0) hda0)
        _ = K.q * X * (1 - A) := one_mul _
        _ ≤ Δ0 := hqXda
    have hdcPay : K.q * K.b * X * (1 - C) ≤ Δ0 := by
      calc
        K.q * K.b * X * (1 - C) = K.q * (K.b * X * (1 - C)) := by ring
        _ ≤ 1 * (K.b * X * (1 - C)) :=
          mul_le_mul_of_nonneg_right hq1
            (mul_nonneg (mul_nonneg hK.b_nonneg hX0) hdc0)
        _ = K.b * X * (1 - C) := one_mul _
        _ ≤ Δ0 := hbXdc
    have hd0pay' : K.q * K.b * X * d0 ^ 2 ≤ 2 * Δ0 :=
      hd0pay.trans (mul_le_mul_of_nonneg_left hD0Δ (by norm_num))
    have hd1payΔ : K.q * K.b * X * d1 ^ 2 ≤ (16 / η ^ 2) * Δ1 :=
      hd1pay'.trans (mul_le_mul_of_nonneg_left hD1Δ
        (div_nonneg (by norm_num) hηsq0.le))
    have hsumPay :
        K.q * K.b * X *
            (d0 ^ 2 + d1 ^ 2 + (1 - A) + (1 - C)) ≤
          4 * Δ0 + (16 / η ^ 2) * Δ1 := by
      calc
        K.q * K.b * X *
            (d0 ^ 2 + d1 ^ 2 + (1 - A) + (1 - C)) =
          K.q * K.b * X * d0 ^ 2 + K.q * K.b * X * d1 ^ 2 +
            K.q * K.b * X * (1 - A) + K.q * K.b * X * (1 - C) := by ring
        _ ≤ 2 * Δ0 + (16 / η ^ 2) * Δ1 + Δ0 + Δ0 :=
          add_le_add (add_le_add (add_le_add hd0pay' hd1payΔ) hdaPay) hdcPay
        _ = 4 * Δ0 + (16 / η ^ 2) * Δ1 := by ring
    calc
      K.q * K.b * X * ‖K.a - p‖ ^ 2 ≤
          K.q * K.b * X *
            (4 * (d0 ^ 2 + d1 ^ 2 + (1 - A) + (1 - C))) := hphaseExpand
      _ = 4 * (K.q * K.b * X *
            (d0 ^ 2 + d1 ^ 2 + (1 - A) + (1 - C))) := by ring
      _ ≤ 4 * (4 * Δ0 + (16 / η ^ 2) * Δ1) :=
        mul_le_mul_of_nonneg_left hsumPay (by norm_num)
      _ = 16 * Δ0 + (64 / η ^ 2) * Δ1 := by ring
      _ ≤ 60 * Δ0 + (64 / η ^ 2) * Δ1 := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right (by norm_num : (16 : ℝ) ≤ 60) hΔ00)
          (le_refl _)

end
end Erdos993.Forest.AppendixA
