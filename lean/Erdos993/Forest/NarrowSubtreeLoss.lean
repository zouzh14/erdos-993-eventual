import Erdos993.Forest.TransferMatrixCharacteristic

/-!
# Direct loss for high-scale narrow descendant subtrees

This module proves Appendix A, equation (A.66), directly from the actual
root-variance comparisons (A.29)--(A.30) and the concrete one-row
Fourier/barrier contraction.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators ENNReal
open ActualRootedVariance UniformFourthMoment

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA66 (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtypeA66 {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Characteristic modulus of the root-vacant deletion forest. -/
noncomputable def vacantCharacteristicModulusAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    z hz).characteristicModulus θ

/-- Characteristic modulus of the closed-root deletion forest. -/
noncomputable def occupiedCharacteristicModulusAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u)) z hz).characteristicModulus θ

/-- Scale `x_U = θ² V_U` of an actual descendant subtree. -/
noncomputable def descendantScaleAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) (u : V) : ℝ :=
  θ ^ 2 * subtreeVarianceAt R z hz u

/-- The fixed high-scale threshold used before (A.61). -/
noncomputable def highScaleThreshold (Z : ℝ) : ℝ :=
  4 * rootVarianceUpperConstant Z * Real.pi ^ 2 + 1

/-- Exact high-scale narrow-root predicate from (A.60): the closed-root
forest is a maximal-modulus choice and has less than `1/(2A_Z)` of the
root-vacant variance scale. -/
def IsHighScaleNarrow
    (R : ComponentRooting G) (Z z : ℝ) (hz : 0 < z) (θ : ℝ) (u : V) : Prop :=
  highScaleThreshold Z ≤ descendantScaleAt R z hz θ u ∧
  vacantCharacteristicModulusAt R z hz θ u ≤
    occupiedCharacteristicModulusAt R z hz θ u ∧
  θ ^ 2 * rootOccupiedVarianceAt R z hz u <
    (θ ^ 2 * rootVacantVarianceAt R z hz u) /
      (2 * rootVarianceUpperConstant Z)

/-- Explicit A.66 rate, depending only on the activity ceiling `Z`. -/
noncomputable def narrowHighScaleRateConstant (Z : ℝ) : ℝ :=
  actualSideBarrierRateConstant Z /
    (8 * rootVarianceUpperConstant Z * Real.pi ^ 2)

/-- The direct proof gives no additive loss, so the A.66 offset is zero. -/
noncomputable def narrowHighScaleOffsetConstant (_Z : ℝ) : ℝ := 0

/-- The A.66 rate is positive for every positive ceiling. -/
theorem narrowHighScaleRateConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < narrowHighScaleRateConstant Z := by
  have hA : 0 < rootVarianceUpperConstant Z := by
    unfold rootVarianceUpperConstant
    linarith
  have hc : 0 < actualSideBarrierRateConstant Z := by
    unfold actualSideBarrierRateConstant
    exact barrierRateConstant_pos hZ (sideRootGapConstant_div_one_add_pos hZ)
  unfold narrowHighScaleRateConstant
  positivity

/-- A modulus exponential upper bound implies the corresponding extended-real
logarithmic-loss lower bound, including the zero-modulus case. -/
theorem FiniteLatticeLaw.coe_le_logarithmicLoss_of_modulus_le_exp_neg
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α)
    (θ s : ℝ) (hs : 0 ≤ s)
    (hM : L.characteristicModulus θ ≤ Real.exp (-s)) :
    (s : EReal) ≤ L.logarithmicLoss θ := by
  by_cases hzero : L.characteristicModulus θ = 0
  · simp [FiniteLatticeLaw.logarithmicLoss, hzero]
  · have hMpos : 0 < L.characteristicModulus θ :=
      lt_of_le_of_ne (L.characteristicModulus_nonneg θ) (Ne.symm hzero)
    rw [FiniteLatticeLaw.logarithmicLoss,
      ENNReal.log_ofReal_of_pos hMpos]
    rw [← EReal.coe_neg, EReal.coe_le_coe_iff]
    have hlog := Real.log_le_log hMpos hM
    rw [Real.log_exp] at hlog
    linarith

/-- The full root vacancy barrier is the side barrier with the impossible
self-child removed. -/
theorem sideLogBarrier_self_eq_rootVarianceLogBarrierAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    sideLogBarrier R z u u = rootVarianceLogBarrierAt R z u := by
  classical
  have huu : u ∉ R.children (G := G) u := by
    intro hu
    have hchild : R.IsChild (G := G) u u :=
      (R.mem_children (G := G) u u).mp hu
    exact R.not_mem_descendants_child (G := G) hchild
      (R.self_mem_descendants (G := G) u)
  unfold sideLogBarrier sideVacancyProduct rootVarianceLogBarrierAt
  rw [Finset.erase_eq_self.mpr huu]
  rw [Real.log_prod (fun v hv => (rootedVacancyProbabilityAt_pos R z hz v).ne')]
  simpa only [Finset.sum_neg_distrib]

/-- Characteristic modulus is the norm of the uncentered characteristic;
the centering phase has unit norm. -/
theorem FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (θ : ℝ) :
    L.characteristicModulus θ = ‖L.characteristic θ‖ := by
  rw [FiniteLatticeLaw.characteristicModulus,
    FiniteLatticeLaw.norm_centeredCharacteristic_eq]

/-- The root-vacant characteristic modulus pays the full root vacancy barrier;
this is the no-distinguished-child form of (A.57). -/
theorem vacantCharacteristicModulusAt_le_exp_neg_rootBarrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V) :
    vacantCharacteristicModulusAt R z hz θ u ≤
      Real.exp (-((sideRootGapConstant Z / (1 + Z)) *
        rootVarianceLogBarrierAt R z u * Real.sin (θ / 2) ^ 2)) := by
  have hs := norm_sideCharacteristicA_le_exp_neg_sideLogBarrier
    hG R Z z θ hz hzZ hθ u u
  have huu : u ∉ R.children (G := G) u := by
    intro hu
    have hchild : R.IsChild (G := G) u u :=
      (R.mem_children (G := G) u u).mp hu
    exact R.not_mem_descendants_child (G := G) hchild
      (R.self_mem_descendants (G := G) u)
  have hnorm : ‖sideCharacteristicA R z hz θ u u‖ =
      vacantCharacteristicModulusAt R z hz θ u := by
    classical
    unfold sideCharacteristicA vacantCharacteristicModulusAt
    rw [Finset.erase_eq_self.mpr huu, norm_prod,
      hardCoreLaw_characteristicModulus_deleteSubtreeRoot_eq_prod_children
        hG R z θ hz u]
    apply Finset.prod_congr rfl
    intro v hv
    exact (FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66
      (R.subtreeLawAt z hz v) θ).symm
  rw [hnorm, sideLogBarrier_self_eq_rootVarianceLogBarrierAt R z hz u] at hs
  convert hs using 1 <;> ring

/-- Exact full-root odds identity in terms of the root vacancy barrier. -/
theorem rootedOccupation_div_vacancy_le_ceiling_mul_exp_neg_rootBarrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedOccupationProbabilityAt R z u /
        rootedVacancyProbabilityAt R z u ≤
      Z * Real.exp (-rootVarianceLogBarrierAt R z u) := by
  have hq := rootedVacancyProbabilityAt_pos R z hz u
  have hrec := rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_prod_children
    hG R z hz u
  have heq : rootedOccupationProbabilityAt R z u /
      rootedVacancyProbabilityAt R z u =
      z * ∏ v ∈ R.children (G := G) u,
        rootedVacancyProbabilityAt R z v := by
    apply (div_eq_iff hq.ne').2
    rw [hrec]
    ring
  have hprod : (∏ v ∈ R.children (G := G) u,
      rootedVacancyProbabilityAt R z v) =
      Real.exp (-rootVarianceLogBarrierAt R z u) := by
    calc
      (∏ v ∈ R.children (G := G) u,
          rootedVacancyProbabilityAt R z v) =
          sideVacancyProduct R z u u := by
            simp [sideVacancyProduct, Finset.erase_eq_self.mpr (show
              u ∉ R.children (G := G) u from by
                intro hu
                have hchild : R.IsChild (G := G) u u :=
                  (R.mem_children (G := G) u u).mp hu
                exact R.not_mem_descendants_child (G := G) hchild
                  (R.self_mem_descendants (G := G) u))]
      _ = Real.exp (-sideLogBarrier R z u u) :=
        (exp_neg_sideLogBarrier_eq_sideVacancyProduct R z hz u u).symm
      _ = Real.exp (-rootVarianceLogBarrierAt R z u) := by
        rw [sideLogBarrier_self_eq_rootVarianceLogBarrierAt R z hz u]
  rw [heq, hprod]
  exact mul_le_mul_of_nonneg_right hzZ (Real.exp_pos _).le

/-- Genuine one-row scalar barrier estimate for a whole rooted descendant
subtree, with no distinguished-child factor. -/
theorem subtreeCharacteristicModulus_le_exp_neg_rootBarrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V) :
    (R.subtreeLawAt z hz u).characteristicModulus θ ≤
      Real.exp (-actualSideBarrierRateConstant Z *
        Real.sin (θ / 2) ^ 2 * rootVarianceLogBarrierAt R z u) := by
  let q := rootedVacancyProbabilityAt R z u
  let b := rootedOccupationProbabilityAt R z u
  let r := vacantCharacteristicModulusAt R z hz θ u
  let h := Real.sin (θ / 2) ^ 2
  let Λ := rootVarianceLogBarrierAt R z u
  let aZ := sideRootGapConstant Z / (1 + Z)
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hqfloor : 1 / (1 + Z) ≤ q := by
    dsimp [q]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ u
  have hb0 : 0 ≤ b := by dsimp [b]; exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hqb : q + b = 1 := by
    dsimp [q, b]
    simpa [add_comm] using rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hr0 : 0 ≤ r := by dsimp [r]; exact FiniteLatticeLaw.characteristicModulus_nonneg _ _
  have hr : r ≤ Real.exp (-aZ * h * Λ) := by
    have hs := vacantCharacteristicModulusAt_le_exp_neg_rootBarrier
      hG R Z z θ hz hzZ hθ u
    dsimp [r, aZ, h, Λ]
    convert hs using 1 <;> ring
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by dsimp [h]; exact Real.sin_sq_le_one _
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ, rootVarianceLogBarrierAt]
    exact Finset.sum_nonneg fun v hv =>
      neg_nonneg.mpr (Real.log_nonpos
        (rootedVacancyProbabilityAt_pos R z hz v).le
        (rootedVacancyProbabilityAt_le_one R z hz v))
  have hodds : b / q ≤ Z * Real.exp (-Λ) := by
    dsimp [b, q, Λ]
    exact rootedOccupation_div_vacancy_le_ceiling_mul_exp_neg_rootBarrier
      hG R Z z hz hzZ u
  have hscalar := scalar_barrier_contraction Z aZ q b r h Λ
    hZ (sideRootGapConstant_div_one_add_pos hZ)
    hqfloor hb0 hqb hr0 hr hh0 hh1 hΛ0 hodds
  have hmix := hardCoreLaw_characteristicModulus_vertexDeletion_le
    (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) z θ hz
  have hmix' : (R.subtreeLawAt z hz u).characteristicModulus θ ≤
      q * r + (1 - q) := by
    simpa [q, r, vacantCharacteristicModulusAt,
      ActualRootedVariance.ComponentRooting.subtreeLawAt,
      rootedVacancyProbabilityAt, UniformFourthMoment.rootedQAt,
      UniformFourthMoment.rootedPAt] using hmix
  have hone : 1 - q = b := by linarith [hqb]
  rw [hone] at hmix'
  exact hmix'.trans (by
    simpa [actualSideBarrierRateConstant, aZ, h, Λ] using hscalar)

/-- Modulus form of the direct high-scale narrow estimate. -/
theorem highScaleNarrow_characteristicModulus_le_exp_A66
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V)
    (hnarrow : IsHighScaleNarrow R Z z hz θ u) :
    (R.subtreeLawAt z hz u).characteristicModulus θ ≤
      Real.exp (-narrowHighScaleRateConstant Z *
        descendantScaleAt R z hz θ u) := by
  let A := rootVarianceUpperConstant Z
  let VT := subtreeVarianceAt R z hz u
  let VQ := rootVacantVarianceAt R z hz u
  let VR := rootOccupiedVarianceAt R z hz u
  let Λ := rootVarianceLogBarrierAt R z u
  let xT := descendantScaleAt R z hz θ u
  let c0 := actualSideBarrierRateConstant Z
  let c66 := narrowHighScaleRateConstant Z
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hA : 0 < A := by dsimp [A, rootVarianceUpperConstant]; linarith
  have hθsq0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hθsqpi : θ ^ 2 ≤ Real.pi ^ 2 := by
    calc
      θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
      _ ≤ Real.pi ^ 2 :=
        (sq_le_sq₀ (abs_nonneg θ) Real.pi_pos.le).2 hθ
  have hxhigh : 4 * A * Real.pi ^ 2 < xT := by
    dsimp [IsHighScaleNarrow, highScaleThreshold] at hnarrow
    dsimp [A, xT]
    linarith [hnarrow.1]
  have h29 := subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
    hG R Z z hz hzZ u
  have hb1 := rootedOccupationProbabilityAt_le_one R z hz u
  have hxQmul : xT ≤ 2 * A * (θ ^ 2 * VQ) := by
    have hscaled := mul_le_mul_of_nonneg_left h29 hθsq0
    have herror : θ ^ 2 * (2 * rootedOccupationProbabilityAt R z u) ≤
        2 * Real.pi ^ 2 := by
      nlinarith [hθsqpi,
        (rootedOccupationProbabilityAt_pos R z hz u).le, hb1]
    have hbound : xT ≤ A * (θ ^ 2 * VQ) + 2 * Real.pi ^ 2 := by
      dsimp [xT, descendantScaleAt, A, VQ]
      nlinarith
    have hA1 : 1 ≤ A := by
      dsimp [A, rootVarianceUpperConstant]
      nlinarith
    have hfour : 4 * Real.pi ^ 2 < xT := by
      have hpi0 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      nlinarith [hxhigh]
    nlinarith
  have hxQ : xT / (2 * A) ≤ θ ^ 2 * VQ := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * A)).2
    nlinarith [hxQmul]
  have h30 := rootVacantVarianceAt_le_rootVarianceUpperConstant_mul_occupied_add_log
    hG R Z z hz hzZ u
  change VQ ≤ A * VR + 2 * Λ at h30
  have hnarVar : θ ^ 2 * VR < (θ ^ 2 * VQ) / (2 * A) := by
    dsimp [IsHighScaleNarrow, A, VQ, VR] at hnarrow
    exact hnarrow.2.2
  have hQbarMul : θ ^ 2 * VQ < 4 * (θ ^ 2 * Λ) := by
    have hscaled := mul_le_mul_of_nonneg_left h30 hθsq0
    have hmul : A * (θ ^ 2 * VR) < (θ ^ 2 * VQ) / 2 := by
      calc
        A * (θ ^ 2 * VR) < A * ((θ ^ 2 * VQ) / (2 * A)) :=
          mul_lt_mul_of_pos_left hnarVar hA
        _ = (θ ^ 2 * VQ) / 2 := by field_simp [hA.ne']
    nlinarith
  have hQbar : (θ ^ 2 * VQ) / 4 < θ ^ 2 * Λ := by
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [hQbarMul]
  have hxbar : xT / (8 * A) < θ ^ 2 * Λ := by
    apply (div_lt_iff₀ (by positivity : 0 < 8 * A)).2
    have hmul := mul_lt_mul_of_pos_left hQbarMul (show 0 < 2 * A by positivity)
    nlinarith [hxQmul]
  have hsin := sq_div_pi_sq_le_sin_half_sq hθ
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ, rootVarianceLogBarrierAt]
    exact Finset.sum_nonneg fun v hv =>
      neg_nonneg.mpr (Real.log_nonpos
        (rootedVacancyProbabilityAt_pos R z hz v).le
        (rootedVacancyProbabilityAt_le_one R z hz v))
  have hexponent : c66 * xT ≤ c0 * Real.sin (θ / 2) ^ 2 * Λ := by
    have hc0 : 0 < c0 := by
      dsimp [c0, actualSideBarrierRateConstant]
      exact barrierRateConstant_pos hZ (sideRootGapConstant_div_one_add_pos hZ)
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hθΛ : θ ^ 2 / Real.pi ^ 2 * Λ ≤
        Real.sin (θ / 2) ^ 2 * Λ :=
      mul_le_mul_of_nonneg_right hsin hΛ0
    have hx : xT / (8 * A * Real.pi ^ 2) ≤
        θ ^ 2 / Real.pi ^ 2 * Λ := by
      calc
        xT / (8 * A * Real.pi ^ 2) =
            (xT / (8 * A)) / Real.pi ^ 2 := by ring
        _ ≤ (θ ^ 2 * Λ) / Real.pi ^ 2 :=
          div_le_div_of_nonneg_right (le_of_lt hxbar) hpi.le
        _ = θ ^ 2 / Real.pi ^ 2 * Λ := by ring
    dsimp [c66, narrowHighScaleRateConstant, c0]
    calc
      actualSideBarrierRateConstant Z /
            (8 * rootVarianceUpperConstant Z * Real.pi ^ 2) * xT =
          actualSideBarrierRateConstant Z *
            (xT / (8 * A * Real.pi ^ 2)) := by
              dsimp [A]
              field_simp
      _ ≤ actualSideBarrierRateConstant Z *
            (θ ^ 2 / Real.pi ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_left hx hc0.le
      _ ≤ actualSideBarrierRateConstant Z *
            (Real.sin (θ / 2) ^ 2 * Λ) :=
          mul_le_mul_of_nonneg_left hθΛ hc0.le
      _ = actualSideBarrierRateConstant Z *
            Real.sin (θ / 2) ^ 2 * Λ := by ring
  have hroot := subtreeCharacteristicModulus_le_exp_neg_rootBarrier
    hG R Z z θ hz hzZ hθ u
  exact hroot.trans (by
    rw [Real.exp_le_exp]
    dsimp [c0, c66, xT, Λ] at hexponent ⊢
    nlinarith)

/-- Appendix A, equation (A.66), for every actual high-scale narrow
descendant subtree.  The offset is explicitly zero. -/
theorem highScaleNarrow_logarithmicLoss_A66
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V)
    (hnarrow : IsHighScaleNarrow R Z z hz θ u) :
    ((narrowHighScaleRateConstant Z * descendantScaleAt R z hz θ u -
        narrowHighScaleOffsetConstant Z : ℝ) : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hscale0 : 0 ≤ descendantScaleAt R z hz θ u :=
    mul_nonneg (sq_nonneg θ) (FiniteLatticeLaw.variance_nonneg _)
  have hrate0 := (narrowHighScaleRateConstant_pos
    (lt_of_lt_of_le hz hzZ)).le
  have hmod : (R.subtreeLawAt z hz u).characteristicModulus θ ≤
      Real.exp (-(narrowHighScaleRateConstant Z *
        descendantScaleAt R z hz θ u)) := by
    convert highScaleNarrow_characteristicModulus_le_exp_A66
      hG R Z z θ hz hzZ hθ u hnarrow using 1 <;> ring
  simpa [narrowHighScaleOffsetConstant] using
    FiniteLatticeLaw.coe_le_logarithmicLoss_of_modulus_le_exp_neg
      (R.subtreeLawAt z hz u) θ
      (narrowHighScaleRateConstant Z * descendantScaleAt R z hz θ u)
      (mul_nonneg hrate0 hscale0) hmod

end
end AppendixA
end Forest
end Erdos993
