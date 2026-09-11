import Erdos993.Forest.TransferMatrixPathData

namespace Erdos993.Forest.AppendixA

open Erdos993.ActualRootedVariance Erdos993.UniformFourthMoment

noncomputable section
set_option maxHeartbeats 800000

/-- `exp (-x)` is dominated by the elementary reciprocal bound. -/
theorem exp_neg_le_one_div_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x) := by
  have h := Real.add_one_le_exp x
  have hp : 0 < Real.exp x := Real.exp_pos _
  rw [Real.exp_neg, one_div]
  rw [inv_le_inv₀ hp (by positivity)]
  simpa [add_comm] using h

/-- Elementary lower bound for exponential loss. -/
theorem div_one_add_le_one_sub_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have h := exp_neg_le_one_div_one_add hx
  have hden : 0 < 1 + x := by positivity
  rw [show x / (1 + x) = 1 - 1 / (1 + x) by field_simp; ring]
  linarith

noncomputable def barrierM (a : ℝ) : ℝ := min a 1
noncomputable def barrierD (Z a : ℝ) : ℝ := (1 / (1 + Z)) * (a / (1 + a))
noncomputable def barrierT (Z a : ℝ) : ℝ := 1 + 2 * Z / barrierM a
noncomputable def barrierRateConstant (Z a : ℝ) : ℝ :=
  min (barrierD Z a / barrierT Z a) (barrierM a / 2)

theorem barrierM_pos {a : ℝ} (ha : 0 < a) : 0 < barrierM a := by
  simp [barrierM, ha]

theorem barrierD_pos {Z a : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    0 < barrierD Z a := by
  unfold barrierD
  positivity

theorem barrierT_one_le {Z a : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    1 ≤ barrierT Z a := by
  have hm := barrierM_pos ha
  have hterm : 0 ≤ 2 * Z / barrierM a := by positivity
  dsimp [barrierT]
  linarith

theorem barrierRateConstant_pos {Z a : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    0 < barrierRateConstant Z a := by
  unfold barrierRateConstant
  have hd := barrierD_pos hZ ha
  have hT : 0 < barrierT Z a := lt_of_lt_of_le zero_lt_one (barrierT_one_le hZ ha)
  have hm := barrierM_pos ha
  positivity

/-- Explicit zero-safe scalar form of (A.58). -/
theorem scalar_barrier_contraction
    (Z a q b r h Λ : ℝ)
    (hZ : 0 < Z) (ha : 0 < a)
    (hq : 1 / (1 + Z) ≤ q) (hb : 0 ≤ b) (hqb : q + b = 1)
    (hr0 : 0 ≤ r) (hr : r ≤ Real.exp (-a * h * Λ))
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hΛ : 0 ≤ Λ)
    (hodds : b / q ≤ Z * Real.exp (-Λ)) :
    q * r + b ≤ Real.exp (-barrierRateConstant Z a * h * Λ) := by
  let η := 1 / (1 + Z)
  let t := h * Λ
  let m := barrierM a
  let d := barrierD Z a
  let T := barrierT Z a
  let c := barrierRateConstant Z a
  have hη : 0 < η := by dsimp [η]; positivity
  have hqpos : 0 < q := lt_of_lt_of_le hη hq
  have hq0 : 0 ≤ q := hqpos.le
  have hq1 : q ≤ 1 := by linarith
  have ht0 : 0 ≤ t := mul_nonneg hh0 hΛ
  have htΛ : t ≤ Λ := by dsimp [t]; nlinarith
  have hm : 0 < m := barrierM_pos ha
  have hm_a : m ≤ a := by dsimp [m, barrierM]; exact min_le_left _ _
  have hm_1 : m ≤ 1 := by dsimp [m, barrierM]; exact min_le_right _ _
  have hd : 0 < d := barrierD_pos hZ ha
  have hT1 : 1 ≤ T := barrierT_one_le hZ ha
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hc : 0 < c := barrierRateConstant_pos hZ ha
  have hc_d : c ≤ d := by
    dsimp [c, barrierRateConstant]
    exact (min_le_left _ _).trans (div_le_self hd.le hT1)
  have hc_dT : c ≤ d / T := by
    dsimp [c, barrierRateConstant]
    exact min_le_left _ _
  have hc_m2 : c ≤ m / 2 := by
    dsimp [c, barrierRateConstant]
    exact min_le_right _ _
  have hsum0 : 0 ≤ q * r + b := add_nonneg (mul_nonneg hq0 hr0) hb
  have hsum1 : q * r + b ≤ 1 := by
    have hre : Real.exp (-a * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_nonneg ha.le ht0]
    have hr1 : r ≤ 1 := by
      rw [show -a * h * Λ = -a * t by dsimp [t]; ring] at hr
      exact hr.trans hre
    nlinarith
  have hdefect (u : ℝ) (hu : 0 ≤ u) (hru : r ≤ Real.exp (-a * u)) :
      η * (a * u / (1 + a * u)) ≤ 1 - (q * r + b) := by
    have hloss : a * u / (1 + a * u) ≤ 1 - Real.exp (-a * u) := by
      convert div_one_add_le_one_sub_exp_neg (mul_nonneg ha.le hu) using 1 <;> ring
    have hqr : q * (1 - Real.exp (-a * u)) ≤ q * (1 - r) := by
      exact mul_le_mul_of_nonneg_left (by linarith) hq0
    have hηq : η ≤ q := by exact hq
    have hloss0 : 0 ≤ a * u / (1 + a * u) := by positivity
    have hηloss : η * (a * u / (1 + a * u)) ≤
        q * (1 - Real.exp (-a * u)) :=
      (mul_le_mul_of_nonneg_right hηq hloss0).trans
        (mul_le_mul_of_nonneg_left hloss hq0)
    rw [show 1 - (q * r + b) = q * (1 - r) by linarith]
    exact hηloss.trans hqr
  rw [show -a * h * Λ = -a * t by dsimp [t]; ring] at hr
  by_cases ht1 : t ≤ 1
  · have hfrac : (a / (1 + a)) * t ≤ a * t / (1 + a * t) := by
      have hnum : 0 ≤ a * t := mul_nonneg ha.le ht0
      have hdent : 0 < 1 + a * t := by positivity
      have hdenle : 1 + a * t ≤ 1 + a := by nlinarith
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left hnum hdent hdenle
    have hpaid : d * t ≤ 1 - (q * r + b) := by
      have hmul := mul_le_mul_of_nonneg_left hfrac hη.le
      have hassoc : d * t = η * ((a / (1 + a)) * t) := by
        dsimp [d, barrierD, η]
        ring
      rw [hassoc]
      exact hmul.trans (hdefect t ht0 hr)
    have hlin : q * r + b ≤ 1 - c * t := by
      have := mul_le_mul_of_nonneg_right hc_d ht0
      linarith
    have hexp := one_sub_le_exp_neg (c * t)
    have hct : c * t = barrierRateConstant Z a * h * Λ := by
      dsimp [c, t]
      ring
    exact hlin.trans (by simpa [hct] using hexp)
  · have ht1' : 1 ≤ t := le_of_not_ge ht1
    have hfrac1 : a / (1 + a) ≤ a * t / (1 + a * t) := by
      have hden : 0 < 1 + a := by positivity
      have hdent : 0 < 1 + a * t := by positivity
      rw [div_le_div_iff₀ hden hdent]
      nlinarith
    have hpaid : d ≤ 1 - (q * r + b) := by
      have hmul := mul_le_mul_of_nonneg_left hfrac1 hη.le
      have hdeq : d = η * (a / (1 + a)) := by rfl
      rw [hdeq]
      exact hmul.trans (hdefect t ht0 hr)
    by_cases htT : t ≤ T
    · have hlin : q * r + b ≤ 1 - c * t := by
        have hcT : c * T ≤ d := by
          apply (le_div_iff₀ hT0).mp hc_dT
        have hct : c * t ≤ c * T := mul_le_mul_of_nonneg_left htT hc.le
        linarith
      have hct : c * t = barrierRateConstant Z a * h * Λ := by
        dsimp [c, t]
        ring
      exact hlin.trans (by
        simpa [hct] using one_sub_le_exp_neg (c * t))
    · have hTt : T ≤ t := le_of_not_ge htT
      have hLexp : Real.exp (-Λ) ≤ Real.exp (-t) := by
        rw [Real.exp_le_exp]
        linarith
      have hrexpm : r ≤ Real.exp (-m * t) := by
        exact hr.trans (by rw [Real.exp_le_exp]; nlinarith)
      have hbexp : b ≤ Z * Real.exp (-t) := by
        have hbq' : b ≤ (Z * Real.exp (-Λ)) * q :=
          (div_le_iff₀ hqpos).mp hodds
        have hbq : b ≤ q * (Z * Real.exp (-Λ)) := by nlinarith
        calc
          b ≤ q * (Z * Real.exp (-Λ)) := hbq
          _ ≤ 1 * (Z * Real.exp (-Λ)) := by
            exact mul_le_mul_of_nonneg_right hq1 (mul_nonneg hZ.le (Real.exp_pos _).le)
          _ = Z * Real.exp (-Λ) := by ring
          _ ≤ Z * Real.exp (-t) := mul_le_mul_of_nonneg_left hLexp hZ.le
      have hTZ : Z ≤ m * T / 2 := by
        have hmne : m ≠ 0 := ne_of_gt hm
        dsimp [T, barrierT]
        rw [show barrierM a = m by rfl]
        field_simp
        nlinarith
      have htZ : Z ≤ m * t / 2 := by
        have hmon := mul_le_mul_of_nonneg_left hTt hm.le
        nlinarith
      have hcoef : 1 + Z ≤ Real.exp (m * t / 2) := by
        linarith [Real.add_one_le_exp (m * t / 2)]
      have hexpmt : Real.exp (-t) ≤ Real.exp (-m * t) := by
        rw [Real.exp_le_exp]
        nlinarith
      have hsumexp : q * r + b ≤ (1 + Z) * Real.exp (-m * t) := by
        calc
          q * r + b ≤ r + b := by nlinarith [mul_nonneg (sub_nonneg.mpr hq1) hr0]
          _ ≤ Real.exp (-m*t) + Z * Real.exp (-t) := add_le_add hrexpm hbexp
          _ ≤ Real.exp (-m*t) + Z * Real.exp (-m*t) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hexpmt hZ.le)
          _ = (1+Z) * Real.exp (-m*t) := by ring
      have hhalf : (1 + Z) * Real.exp (-m * t) ≤ Real.exp (-(m/2) * t) := by
        have hp := mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-m*t)).le
        rw [← Real.exp_add] at hp
        convert hp using 1 <;> ring
      have hrate : Real.exp (-(m/2)*t) ≤ Real.exp (-c*t) := by
        rw [Real.exp_le_exp]
        nlinarith
      exact hsumexp.trans (hhalf.trans (hrate.trans (by
        apply le_of_eq
        congr 1
        dsimp [c, t]
        ring)))

/-- The side vacancy product is exactly the exponential of minus its
logarithmic barrier. -/
theorem exp_neg_sideLogBarrier_eq_sideVacancyProduct
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    Real.exp (-sideLogBarrier R z u v) = sideVacancyProduct R z u v := by
  rw [sideLogBarrier, neg_neg]
  exact Real.exp_log (sideVacancyProduct_pos R z hz u v)

/-- The one-norm update is bounded by the scalar factor used in (A.58). -/
theorem TransferCoefficient.normOne_applyRow_le_scalarFactor
    (K : TransferCoefficient) (r : ComplexRow) (hK : K.Admissible) :
    (K.applyRow r).normOne ≤
      (K.q * ‖K.a‖ + K.b) * r.normOne := by
  rw [K.normOne_applyRow r hK.b_nonneg hK.norm_phase]
  have htri : ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
      K.q * ‖r.fst‖ + ‖r.snd‖ := by
    calc
      ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
          ‖(K.q : ℂ) * r.fst‖ + ‖r.snd‖ := norm_add_le _ _
      _ = K.q * ‖r.fst‖ + ‖r.snd‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hK.q_nonneg]
  have ha0 : 0 ≤ ‖K.a‖ := norm_nonneg _
  have hc0 : 0 ≤ ‖K.c‖ := norm_nonneg _
  have hfirst := mul_le_mul_of_nonneg_left htri ha0
  have hsecond : K.b * ‖K.c‖ * ‖r.fst‖ ≤ K.b * ‖r.fst‖ := by
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hK.norm_c_le_one hK.b_nonneg)
      (norm_nonneg _)).trans_eq (by ring)
  have hfactorA : ‖K.a‖ ≤ K.q * ‖K.a‖ + K.b := by
    have hba : 0 ≤ K.b * (1 - ‖K.a‖) :=
      mul_nonneg hK.b_nonneg (sub_nonneg.mpr hK.norm_a_le_one)
    nlinarith [hK.q_add_b]
  have hfactor0 : 0 ≤ K.q * ‖K.a‖ + K.b :=
    add_nonneg (mul_nonneg hK.q_nonneg ha0) hK.b_nonneg
  calc
    ‖K.a‖ * ‖(K.q : ℂ) * r.fst + r.snd‖ +
        K.b * ‖K.c‖ * ‖r.fst‖ ≤
      ‖K.a‖ * (K.q * ‖r.fst‖ + ‖r.snd‖) +
        K.b * ‖r.fst‖ := add_le_add hfirst hsecond
    _ = (K.q * ‖K.a‖ + K.b) * ‖r.fst‖ +
        ‖K.a‖ * ‖r.snd‖ := by ring
    _ ≤ (K.q * ‖K.a‖ + K.b) * ‖r.fst‖ +
        (K.q * ‖K.a‖ + K.b) * ‖r.snd‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactorA (norm_nonneg _))
    _ = (K.q * ‖K.a‖ + K.b) * r.normOne := by
      simp only [ComplexRow.normOne]
      ring

/-- The concrete exponent coefficient in the side-barrier estimate. -/
noncomputable def actualSideBarrierRateConstant (Z : ℝ) : ℝ :=
  barrierRateConstant Z (sideRootGapConstant Z / (1 + Z))

/-- The coefficient in the genuine side-forest radial estimate is positive. -/
theorem sideRootGapConstant_div_one_add_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < sideRootGapConstant Z / (1 + Z) := by
  have hgap : 0 < sideRootGapConstant Z := by
    unfold sideRootGapConstant
    exact mul_pos (uniformGapConstant_pos hZ) (sq_pos_of_pos (by positivity))
  exact div_pos hgap (by linarith)

/-- Genuine A.58 for one actual downward edge. -/
theorem actualTransferCoefficient_scalar_barrier
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    {u v : V} (huv : R.IsChild (G := G) u v) :
    let K := actualTransferCoefficient R z hz θ u v
    K.q * ‖K.a‖ + K.b ≤
      Real.exp (-actualSideBarrierRateConstant Z *
        Real.sin (θ / 2) ^ 2 * sideLogBarrier R z u v) := by
  let K := actualTransferCoefficient R z hz θ u v
  let aZ := sideRootGapConstant Z / (1 + Z)
  let h := Real.sin (θ / 2) ^ 2
  let Λ := sideLogBarrier R z u v
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have haZ : 0 < aZ := by
    dsimp [aZ]
    exact sideRootGapConstant_div_one_add_pos hZ
  have hK := actualTransferCoefficient_admissible R z hz θ u v
  have hqfloor : 1 / (1 + Z) ≤ K.q := by
    dsimp [K, actualTransferCoefficient]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
      hG R z Z hz hzZ u
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ]
    exact sideLogBarrier_nonneg R z hz u v
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    dsimp [h]
    exact Real.sin_sq_le_one _
  have hr0 : 0 ≤ ‖K.a‖ := norm_nonneg _
  have hr : ‖K.a‖ ≤ Real.exp (-aZ * h * Λ) := by
    have hs := norm_sideCharacteristicA_le_exp_neg_sideLogBarrier
      hG R Z z θ hz hzZ hθ u v
    dsimp [K, actualTransferCoefficient, aZ, h, Λ]
    convert hs using 1 <;> ring
  have hodds : K.b / K.q ≤ Z * Real.exp (-Λ) := by
    have hqpos : 0 < K.q := lt_of_lt_of_le (by positivity) hqfloor
    have hrec :=
      rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_child_vacancy_mul_side
        hG R z hz huv
    have heq : K.b / K.q = z * rootedVacancyProbabilityAt R z v *
        sideVacancyProduct R z u v := by
      apply (div_eq_iff hqpos.ne').2
      dsimp [K, actualTransferCoefficient]
      rw [hrec]
      ring
    rw [heq, ← exp_neg_sideLogBarrier_eq_sideVacancyProduct R z hz u v]
    have hqv0 := (rootedVacancyProbabilityAt_pos R z hz v).le
    have hqv1 := rootedVacancyProbabilityAt_le_one R z hz v
    have hz0 := hz.le
    have hprod : z * rootedVacancyProbabilityAt R z v ≤ Z := by
      calc
        z * rootedVacancyProbabilityAt R z v ≤
            Z * rootedVacancyProbabilityAt R z v :=
          mul_le_mul_of_nonneg_right hzZ hqv0
        _ ≤ Z * 1 := mul_le_mul_of_nonneg_left hqv1 hZ.le
        _ = Z := mul_one _
    exact mul_le_mul_of_nonneg_right hprod (Real.exp_pos _).le
  have hs := scalar_barrier_contraction Z aZ K.q K.b ‖K.a‖ h Λ
    hZ haZ hqfloor hK.b_nonneg hK.q_add_b hr0 hr hh0 hh1 hΛ0 hodds
  simpa [K, aZ, h, Λ, actualSideBarrierRateConstant] using hs

/-- Iterated genuine side-barrier contraction along every child chain. -/
theorem actualTransferList_normOne_le_exp_neg_sideBarrier
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi) :
    ∀ (l : List V), l.IsChain (R.IsChild (G := G)) → ∀ r : ComplexRow,
      (applyTransferList r (actualTransferCoefficients R z hz θ l)).normOne ≤
        Real.exp (-actualSideBarrierRateConstant Z *
          Real.sin (θ / 2) ^ 2 * actualSideLogBarrierSumList R z l) *
          r.normOne
  | [], _, r => by
      simp [actualTransferCoefficients, actualSideLogBarrierSumList]
  | [_], _, r => by
      simp [actualTransferCoefficients, actualSideLogBarrierSumList]
  | u :: v :: rest, hchain, r => by
      let K := actualTransferCoefficient R z hz θ u v
      let c := actualSideBarrierRateConstant Z
      let h := Real.sin (θ / 2) ^ 2
      let Λ := sideLogBarrier R z u v
      let S := actualSideLogBarrierSumList R z (v :: rest)
      have huv : R.IsChild (G := G) u v := hchain.rel_head
      have htail : (v :: rest).IsChain (R.IsChild (G := G)) := hchain.tail
      have ih := actualTransferList_normOne_le_exp_neg_sideBarrier
        hG R Z z θ hz hzZ hθ (v :: rest) htail (K.applyRow r)
      have hscalar := actualTransferCoefficient_scalar_barrier
        hG R Z z θ hz hzZ hθ huv
      have hK := actualTransferCoefficient_admissible R z hz θ u v
      have hrow := K.normOne_applyRow_le_scalarFactor r hK
      have hhead : (K.applyRow r).normOne ≤ Real.exp (-c * h * Λ) * r.normOne := by
        calc
          (K.applyRow r).normOne ≤ (K.q * ‖K.a‖ + K.b) * r.normOne := hrow
          _ ≤ Real.exp (-c * h * Λ) * r.normOne := by
            apply mul_le_mul_of_nonneg_right
            · simpa [K, c, h, Λ] using hscalar
            · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
      simp only [actualTransferCoefficients, applyTransferList_cons]
      change (applyTransferList (K.applyRow r)
        (actualTransferCoefficients R z hz θ (v :: rest))).normOne ≤ _
      have iht : (applyTransferList (K.applyRow r)
          (actualTransferCoefficients R z hz θ (v :: rest))).normOne ≤
          Real.exp (-c * h * S) * (K.applyRow r).normOne := by
        simpa [c, h, S] using ih
      calc
        (applyTransferList (K.applyRow r)
            (actualTransferCoefficients R z hz θ (v :: rest))).normOne ≤
            Real.exp (-c * h * S) * (K.applyRow r).normOne := iht
        _ ≤ Real.exp (-c * h * S) *
            (Real.exp (-c * h * Λ) * r.normOne) :=
          mul_le_mul_of_nonneg_left hhead (Real.exp_pos _).le
        _ = (Real.exp (-c * h * S) * Real.exp (-c * h * Λ)) *
              r.normOne := by ring
        _ = Real.exp (-c * h * (Λ + S)) * r.normOne := by
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring
        _ = Real.exp (-actualSideBarrierRateConstant Z *
              Real.sin (θ / 2) ^ 2 *
                actualSideLogBarrierSumList R z (u :: v :: rest)) *
              r.normOne := by
          simp only [actualSideLogBarrierSumList]
          rfl

/-- Side-barrier contraction for the concrete coefficient row of a downward
path, with a constant depending only on `Z`. -/
theorem DownwardPath.actualTransferRow_normOne_le_exp_neg_sideBarrier
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (P : DownwardPath R) :
    (P.actualTransferRow z hz θ).normOne ≤
      Real.exp (-actualSideBarrierRateConstant Z * Real.sin (θ / 2) ^ 2 *
        P.actualSideLogBarrierSum z) := by
  have h := actualTransferList_normOne_le_exp_neg_sideBarrier
    hG R Z z θ hz hzZ hθ P.vertices P.isChain (⟨1, 0⟩ : ComplexRow)
  simpa [DownwardPath.actualTransferRow, DownwardPath.actualSideLogBarrierSum,
    ComplexRow.normOne] using h

end
end Erdos993.Forest.AppendixA
