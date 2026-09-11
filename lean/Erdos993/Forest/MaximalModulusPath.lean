import Erdos993.Forest.MaximalModulusPathData

/-!
# Maximal-modulus path estimates (Appendix A.9)
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment
open ActualRootedVariance.ComponentRooting

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA9Path (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace MaximalModulusTrace

noncomputable def rBarrierMass
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → ℝ
  | .stop _ => 0
  | .qStep _ _ tail => tail.rBarrierMass
  | .rStep (u := u) _ _ _ tail =>
      rootVarianceLogBarrierAt R z u + tail.rBarrierMass

noncomputable def pathOccupationMass
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  DownwardPath.initialSum (rootedOccupationProbabilityAt R z) τ.vertices

noncomputable def terminalVariance
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  DownwardPath.terminalValue (subtreeVarianceAt R z hz) τ.vertices

noncomputable def filledSideVariance
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  DownwardPath.sideSum R (subtreeVarianceAt R z hz) τ.vertices

noncomputable def qDiscardedVariance
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) : ℝ :=
  ∑ w ∈ (R.children (G := G) u).erase v, subtreeVarianceAt R z hz w

noncomputable def rDiscardedVariance
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u c v : V) : ℝ :=
  (∑ w ∈ (R.children (G := G) c).erase v,
      subtreeVarianceAt R z hz w) +
    ∑ d ∈ (R.children (G := G) u).erase c,
      ∑ w ∈ R.children (G := G) d, subtreeVarianceAt R z hz w

noncomputable def discardedVariance
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → ℝ
  | .stop _ => 0
  | .qStep (u := u) (v := v) _ _ tail =>
      qDiscardedVariance R z hz u v + tail.discardedVariance
  | .rStep (u := u) (c := c) (v := v) _ _ _ tail =>
      rDiscardedVariance R z hz u c v + tail.discardedVariance

/-- The concrete quantity `K` from (A.62). -/
noncomputable def K
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  θ ^ 2 * (τ.pathOccupationMass + τ.rBarrierMass)

noncomputable def discardedScale
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  θ ^ 2 * τ.discardedVariance

noncomputable def terminalScale
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : ℝ :=
  θ ^ 2 * τ.terminalVariance

lemma rootedOccupation_le_neg_log_vacancy_A9
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u ≤
      -Real.log (rootedVacancyProbabilityAt R z u) := by
  have hq := rootedVacancyProbabilityAt_pos R z hz u
  have hlog := Real.log_le_sub_one_of_pos hq
  have hsum := rootedOccupationProbabilityAt_add_vacancy R z hz u
  linarith

lemma rootBarrier_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 ≤ rootVarianceLogBarrierAt R z u := by
  unfold rootVarianceLogBarrierAt
  exact Finset.sum_nonneg fun v hv =>
    (rootedOccupation_le_neg_log_vacancy_A9 R z hz v).trans'
      (rootedOccupationProbabilityAt_pos R z hz v).le

lemma sum_occupation_erase_le_rootBarrier
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u c : V) :
    (∑ d ∈ (R.children (G := G) u).erase c,
      rootedOccupationProbabilityAt R z d) ≤
      rootVarianceLogBarrierAt R z u := by
  unfold rootVarianceLogBarrierAt
  calc
    _ ≤ ∑ d ∈ (R.children (G := G) u).erase c,
        -Real.log (rootedVacancyProbabilityAt R z d) := by
      exact Finset.sum_le_sum fun d hd =>
        rootedOccupation_le_neg_log_vacancy_A9 R z hz d
    _ ≤ ∑ d ∈ R.children (G := G) u,
        -Real.log (rootedVacancyProbabilityAt R z d) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun d hd hdc =>
        neg_nonneg.mpr (Real.log_nonpos
          (rootedVacancyProbabilityAt_pos R z hz d).le
          (rootedVacancyProbabilityAt_le_one R z hz d))

lemma nonneg_pathOccupationMass
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : 0 ≤ τ.pathOccupationMass := by
  unfold pathOccupationMass
  exact DownwardPath.initialSum_nonneg _
    (fun v => (rootedOccupationProbabilityAt_pos R z hz v).le) _

lemma nonneg_terminalVariance
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : 0 ≤ τ.terminalVariance := by
  unfold terminalVariance
  exact DownwardPath.terminalValue_nonneg _
    (fun v => (R.subtreeLawAt z hz v).variance_nonneg) _

lemma nonneg_discardedVariance
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : 0 ≤ τ.discardedVariance := by
  induction τ with
  | stop => simp [discardedVariance]
  | qStep huv hmax tail ih =>
      simp only [discardedVariance, qDiscardedVariance]
      exact add_nonneg
        (Finset.sum_nonneg fun w hw => (R.subtreeLawAt z hz w).variance_nonneg) ih
  | rStep huc hcv hmax tail ih =>
      simp only [discardedVariance, rDiscardedVariance]
      exact add_nonneg (add_nonneg
        (Finset.sum_nonneg fun w hw => (R.subtreeLawAt z hz w).variance_nonneg)
        (Finset.sum_nonneg fun d hd => Finset.sum_nonneg fun w hw =>
          (R.subtreeLawAt z hz w).variance_nonneg)) ih

lemma nonneg_rBarrierMass
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : 0 ≤ τ.rBarrierMass := by
  induction τ with
  | stop => simp [rBarrierMass]
  | qStep huv hmax tail ih => simpa [rBarrierMass]
  | rStep huc hcv hmax tail ih =>
      simp only [rBarrierMass]
      exact add_nonneg (rootBarrier_nonneg R z hz _) ih

/-- Coefficient absorbing both the A.29 vacant-variance constant and the
factor `2` in the occupation/barrier contribution. -/
noncomputable def maximalModulusSideVarianceConstant (Z : ℝ) : ℝ :=
  max 2 (rootVarianceUpperConstant Z)

/-- The filled side forest is controlled by the actual discarded R/Q
components and the R-choice barrier charges. -/
theorem filledSideVariance_le_discarded_add_barrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.filledSideVariance ≤
      maximalModulusSideVarianceConstant Z * τ.discardedVariance +
        2 * τ.rBarrierMass := by
  let A := maximalModulusSideVarianceConstant Z
  have hA1 : 1 ≤ A :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
  induction τ with
  | stop u => simp [filledSideVariance, discardedVariance, rBarrierMass,
      DownwardPath.sideSum]
  | @qStep u v huv hmax tail ih =>
      have hlocal0 : 0 ≤ qDiscardedVariance R z hz u v := by
        unfold qDiscardedVariance
        exact Finset.sum_nonneg fun w hw =>
          (R.subtreeLawAt z hz w).variance_nonneg
      change DownwardPath.sideSum R (subtreeVarianceAt R z hz)
          (u :: tail.vertices) ≤
        maximalModulusSideVarianceConstant Z *
          (qDiscardedVariance R z hz u v + tail.discardedVariance) +
            2 * tail.rBarrierMass
      rw [tail.vertices_eq_cons_tail]
      simp only [DownwardPath.sideSum]
      unfold filledSideVariance at ih
      rw [tail.vertices_eq_cons_tail] at ih
      unfold qDiscardedVariance at hlocal0 ⊢
      dsimp [A] at hA1
      nlinarith
  | @rStep u c v huc hcv hmax tail ih =>
      have hside :
          (∑ d ∈ (R.children (G := G) u).erase c,
              subtreeVarianceAt R z hz d) ≤
            A * (∑ d ∈ (R.children (G := G) u).erase c,
                ∑ w ∈ R.children (G := G) d,
                  subtreeVarianceAt R z hz w) +
              2 * rootVarianceLogBarrierAt R z u := by
        have hs := Finset.sum_le_sum (s := (R.children (G := G) u).erase c)
          (fun d hd =>
            subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
              hG R Z z hz hzZ d)
        have hb := sum_occupation_erase_le_rootBarrier R z hz u c
        dsimp [A] at hs ⊢
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
        simp_rw [R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz] at hs
        have hB0 : 0 ≤ ∑ d ∈ (R.children (G := G) u).erase c,
            ∑ w ∈ R.children (G := G) d,
              subtreeVarianceAt R z hz w := by
          exact Finset.sum_nonneg fun d hd => Finset.sum_nonneg fun w hw =>
            (R.subtreeLawAt z hz w).variance_nonneg
        have hrootA : rootVarianceUpperConstant Z ≤
            maximalModulusSideVarianceConstant Z :=
          le_max_right _ _
        have hmul := mul_le_mul_of_nonneg_right hrootA hB0
        nlinarith
      have hinner0 : 0 ≤ ∑ w ∈ (R.children (G := G) c).erase v,
          subtreeVarianceAt R z hz w := by
        exact Finset.sum_nonneg fun w hw =>
          (R.subtreeLawAt z hz w).variance_nonneg
      change DownwardPath.sideSum R (subtreeVarianceAt R z hz)
          (u :: c :: tail.vertices) ≤
        maximalModulusSideVarianceConstant Z *
          (rDiscardedVariance R z hz u c v + tail.discardedVariance) +
            2 * (rootVarianceLogBarrierAt R z u + tail.rBarrierMass)
      rw [tail.vertices_eq_cons_tail]
      simp only [DownwardPath.sideSum]
      unfold filledSideVariance at ih
      rw [tail.vertices_eq_cons_tail] at ih
      unfold rDiscardedVariance
      dsimp [A] at hA1
      nlinarith

end MaximalModulusTrace

/-- A public A.63 constant depending only on the ceiling `Z`. -/
noncomputable def maximalModulusPathVarianceConstant (Z : ℝ) : ℝ :=
  max 1 (pathVarianceConstant Z *
    MaximalModulusTrace.maximalModulusSideVarianceConstant Z)

namespace MaximalModulusTrace

/-- Appendix A, (A.63), proved from the actual A.7 path estimate. -/
theorem scale_le_K_terminal_discarded_A63
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    descendantScaleAt R z hz θ u ≤
      maximalModulusPathVarianceConstant Z *
        (τ.K + τ.terminalScale + τ.discardedScale) := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hθ0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hA1 : 1 ≤ maximalModulusSideVarianceConstant Z :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _)
  by_cases hτ : τ.choiceCount = 0
  · cases τ with
    | stop u =>
        simp [K, pathOccupationMass, rBarrierMass,
          terminalScale, terminalVariance, discardedScale, discardedVariance,
          descendantScaleAt, maximalModulusPathVarianceConstant,
          DownwardPath.initialSum, DownwardPath.terminalValue]
        have hc : 1 ≤ max 1
            (pathVarianceConstant Z * maximalModulusSideVarianceConstant Z) :=
          le_max_left _ _
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right hc
            (mul_nonneg hθ0 (R.subtreeLawAt z hz u).variance_nonneg))
    | qStep huv hmax tail => simp [choiceCount] at hτ
    | rStep huc hcv hmax tail => simp [choiceCount] at hτ
  · let P := τ.toDownwardPath hτ
    have h7 := varianceAlongDownwardPath_le hG R Z z hz hzZ P
    have hverts : P.vertices = τ.vertices := τ.toDownwardPath_vertices hτ
    have hstart : P.start = u := by
      dsimp [P]
      cases τ with
      | stop u => exact False.elim (hτ rfl)
      | qStep huv hmax tail => rfl
      | rStep huc hcv hmax tail => rfl
    have hside := τ.filledSideVariance_le_discarded_add_barrier hG R Z z hz hzZ
    have hocc0 := τ.nonneg_pathOccupationMass
    have hterm0 := τ.nonneg_terminalVariance
    have hdisc0 := τ.nonneg_discardedVariance
    have hbar0 := τ.nonneg_rBarrierMass
    have hpathC0 := (pathVarianceConstant_pos Z hZ).le
    rw [hstart] at h7
    dsimp [DownwardPath.occupationMass, DownwardPath.terminalSubtreeVariance,
      DownwardPath.sideForestVariance] at h7
    rw [hverts] at h7
    change subtreeVarianceAt R z hz u ≤
      pathVarianceConstant Z *
        (τ.pathOccupationMass + τ.terminalVariance + τ.filledSideVariance) at h7
    have hreal : subtreeVarianceAt R z hz u ≤
        pathVarianceConstant Z * maximalModulusSideVarianceConstant Z *
          (τ.pathOccupationMass + τ.rBarrierMass + τ.terminalVariance +
            τ.discardedVariance) := by
      calc
        _ ≤ pathVarianceConstant Z *
            (τ.pathOccupationMass + τ.terminalVariance + τ.filledSideVariance) := h7
        _ ≤ pathVarianceConstant Z *
            (τ.pathOccupationMass + τ.terminalVariance +
              (maximalModulusSideVarianceConstant Z * τ.discardedVariance +
                2 * τ.rBarrierMass)) := by
          apply mul_le_mul_of_nonneg_left _ hpathC0
          nlinarith [hside]
        _ ≤ pathVarianceConstant Z * maximalModulusSideVarianceConstant Z *
            (τ.pathOccupationMass + τ.rBarrierMass + τ.terminalVariance +
              τ.discardedVariance) := by
          have hA2 : 2 ≤ maximalModulusSideVarianceConstant Z :=
            le_max_left _ _
          have hoc : τ.pathOccupationMass ≤
              maximalModulusSideVarianceConstant Z * τ.pathOccupationMass := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hA1 hocc0
          have hte : τ.terminalVariance ≤
              maximalModulusSideVarianceConstant Z * τ.terminalVariance := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hA1 hterm0
          have hba : 2 * τ.rBarrierMass ≤
              maximalModulusSideVarianceConstant Z * τ.rBarrierMass :=
            mul_le_mul_of_nonneg_right hA2 hbar0
          have hins :
              τ.pathOccupationMass + τ.terminalVariance +
                  (maximalModulusSideVarianceConstant Z * τ.discardedVariance +
                    2 * τ.rBarrierMass) ≤
                maximalModulusSideVarianceConstant Z *
                  (τ.pathOccupationMass + τ.rBarrierMass + τ.terminalVariance +
                    τ.discardedVariance) := by
            nlinarith
          calc
            _ ≤ pathVarianceConstant Z *
                (maximalModulusSideVarianceConstant Z *
                  (τ.pathOccupationMass + τ.rBarrierMass + τ.terminalVariance +
                    τ.discardedVariance)) :=
              mul_le_mul_of_nonneg_left hins hpathC0
            _ = _ := by ring
    unfold descendantScaleAt K terminalScale discardedScale
    have hc : pathVarianceConstant Z * maximalModulusSideVarianceConstant Z ≤
        maximalModulusPathVarianceConstant Z :=
      le_max_right _ _
    nlinarith [mul_le_mul_of_nonneg_left hreal hθ0,
      mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ θ ^ 2 *
          (τ.pathOccupationMass + τ.rBarrierMass + τ.terminalVariance +
            τ.discardedVariance))]

end MaximalModulusTrace
end
end AppendixA
end Forest
end Erdos993
