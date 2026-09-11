import Erdos993.Forest.RecursiveDecomposition

/-!
# Scale accounting for Appendix A.10

This file exposes the high-scale nonnarrow deletion estimate (A.61), relates
A.9's terminal/discarded variance account to the concrete recursive family,
and derives (A.67)--(A.69).
-/

set_option maxHeartbeats 5000000

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment
open ActualRootedVariance.ComponentRooting

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA10Scale (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Reciprocal of the manuscript's `δ_Z=(4 A_Z²)⁻¹`. -/
noncomputable def recursiveDeletionScaleConstant (Z : ℝ) : ℝ :=
  4 * rootVarianceUpperConstant Z ^ 2

/-- The final A.67 constant, absorbing both A.63 and A.61. -/
noncomputable def recursiveScaleConstant (Z : ℝ) : ℝ :=
  maximalModulusPathVarianceConstant Z * recursiveDeletionScaleConstant Z

lemma rootVarianceUpperConstant_pos_A10 {Z : ℝ} (hZ : 0 < Z) :
    0 < rootVarianceUpperConstant Z := by
  unfold rootVarianceUpperConstant
  linarith

lemma rootVarianceUpperConstant_one_le_A10 {Z : ℝ} (hZ : 0 < Z) :
    1 ≤ rootVarianceUpperConstant Z := by
  unfold rootVarianceUpperConstant
  linarith

lemma recursiveDeletionScaleConstant_one_le {Z : ℝ} (hZ : 0 < Z) :
    1 ≤ recursiveDeletionScaleConstant Z := by
  have hA := rootVarianceUpperConstant_one_le_A10 hZ
  unfold recursiveDeletionScaleConstant
  nlinarith [sq_nonneg (rootVarianceUpperConstant Z)]

lemma recursiveScaleConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < recursiveScaleConstant Z := by
  have hC : 0 < maximalModulusPathVarianceConstant Z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hD : 0 < recursiveDeletionScaleConstant Z :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (recursiveDeletionScaleConstant_one_le hZ)
  exact mul_pos hC hD

/-- The high-scale part of (A.29): `x_T ≤ 2 A_Z x_Q`. -/
theorem highScale_scale_le_two_mul_vacantScale
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V)
    (hhigh : highScaleThreshold Z ≤ descendantScaleAt R z hz θ u) :
    descendantScaleAt R z hz θ u ≤
      2 * rootVarianceUpperConstant Z *
        (θ ^ 2 * rootVacantVarianceAt R z hz u) := by
  let A := rootVarianceUpperConstant Z
  let xT := descendantScaleAt R z hz θ u
  let VQ := rootVacantVarianceAt R z hz u
  have hA : 0 < A := rootVarianceUpperConstant_pos_A10
    (lt_of_lt_of_le hz hzZ)
  have hA1 : 1 ≤ A := rootVarianceUpperConstant_one_le_A10
    (lt_of_lt_of_le hz hzZ)
  have hθsq0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have h29 := subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
    hG R Z z hz hzZ u
  have hb1 := rootedOccupationProbabilityAt_le_one R z hz u
  have herror : θ ^ 2 * (2 * rootedOccupationProbabilityAt R z u) ≤
      2 * Real.pi ^ 2 := by
    have hθsqpi : θ ^ 2 ≤ Real.pi ^ 2 := by
      calc
        θ ^ 2 = |θ| ^ 2 := (sq_abs θ).symm
        _ ≤ Real.pi ^ 2 :=
          (sq_le_sq₀ (abs_nonneg θ) Real.pi_pos.le).2 hθ
    nlinarith [hθsqpi,
      (rootedOccupationProbabilityAt_pos R z hz u).le, hb1]
  have hscaled := mul_le_mul_of_nonneg_left h29 hθsq0
  have hbound : xT ≤ A * (θ ^ 2 * VQ) + 2 * Real.pi ^ 2 := by
    dsimp [xT, descendantScaleAt, A, VQ]
    nlinarith
  have hxhigh : 4 * A * Real.pi ^ 2 < xT := by
    dsimp [highScaleThreshold] at hhigh
    dsimp [xT, A]
    linarith
  have hfour : 4 * Real.pi ^ 2 < xT := by
    have hpi0 : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    nlinarith
  nlinarith

/-- The Q-deletion component scales sum exactly to the vacant variance scale. -/
theorem sum_children_descendantScaleAt_eq_vacantScale
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (∑ v ∈ R.children (G := G) u, descendantScaleAt R z hz θ v) =
      θ ^ 2 * rootVacantVarianceAt R z hz u := by
  simp only [descendantScaleAt]
  rw [← Finset.mul_sum,
    ← R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u]

/-- The R-deletion component scales sum exactly to the occupied variance scale. -/
theorem sum_grandchildren_descendantScaleAt_eq_occupiedScale
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (∑ v ∈ grandchildrenAt R u, descendantScaleAt R z hz θ v) =
      θ ^ 2 * rootOccupiedVarianceAt R z hz u := by
  simp only [descendantScaleAt]
  rw [← Finset.mul_sum,
    RecursiveDecomposition.sum_grandchildrenAt_eq_sum_children hG R u
      (fun v => subtreeVarianceAt R z hz v)]
  have hflat :
      (∑ c ∈ R.children (G := G) u,
        ∑ v ∈ R.children (G := G) c, subtreeVarianceAt R z hz v) =
      ∑ c ∈ R.children (G := G) u, rootVacantVarianceAt R z hz c := by
    apply Finset.sum_congr rfl
    intro c hc
    exact (R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz c).symm
  rw [hflat, ← R.occupiedVarianceAt_eq_sum_vacantVarianceAt hG z hz u]

/-- A.61 when the maximal deletion is Q. -/
theorem qDeletion_scale_control_A61
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V)
    (hhigh : highScaleThreshold Z ≤ descendantScaleAt R z hz θ u) :
    descendantScaleAt R z hz θ u ≤
      recursiveDeletionScaleConstant Z *
        ∑ v ∈ R.children (G := G) u,
          descendantScaleAt R z hz θ v := by
  let A := rootVarianceUpperConstant Z
  let xQ := θ ^ 2 * rootVacantVarianceAt R z hz u
  have hbase := highScale_scale_le_two_mul_vacantScale
    hG R Z z θ hz hzZ hθ u hhigh
  have hA1 : 1 ≤ A := rootVarianceUpperConstant_one_le_A10
    (lt_of_lt_of_le hz hzZ)
  have hVQ0 : 0 ≤ rootVacantVarianceAt R z hz u := by
    change 0 ≤ R.vacantVarianceAt z hz u
    rw [R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u]
    exact Finset.sum_nonneg fun v hv =>
      (R.subtreeLawAt z hz v).variance_nonneg
  have hxQ0 : 0 ≤ xQ := mul_nonneg (sq_nonneg θ) hVQ0
  have hcoeff : 2 * A ≤ 4 * A ^ 2 := by nlinarith
  rw [sum_children_descendantScaleAt_eq_vacantScale hG R z θ hz u]
  exact hbase.trans (mul_le_mul_of_nonneg_right hcoeff hxQ0)

/-- A.61 when the maximal deletion is R and the high-scale root is not narrow. -/
theorem rDeletion_scale_control_A61
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V)
    (hhigh : highScaleThreshold Z ≤ descendantScaleAt R z hz θ u)
    (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
      occupiedCharacteristicModulusAt R z hz θ u)
    (hnarrow : ¬ IsHighScaleNarrow R Z z hz θ u) :
    descendantScaleAt R z hz θ u ≤
      recursiveDeletionScaleConstant Z *
        ∑ v ∈ grandchildrenAt R u,
          descendantScaleAt R z hz θ v := by
  let A := rootVarianceUpperConstant Z
  let xQ := θ ^ 2 * rootVacantVarianceAt R z hz u
  let xR := θ ^ 2 * rootOccupiedVarianceAt R z hz u
  have hA : 0 < A := rootVarianceUpperConstant_pos_A10
    (lt_of_lt_of_le hz hzZ)
  have hbase := highScale_scale_le_two_mul_vacantScale
    hG R Z z θ hz hzZ hθ u hhigh
  have hnotthird : ¬ xR < xQ / (2 * A) := by
    intro hthird
    apply hnarrow
    exact ⟨hhigh, hmax, hthird⟩
  have hQRdiv : xQ / (2 * A) ≤ xR := le_of_not_gt hnotthird
  have hQR : xQ ≤ (2 * A) * xR := by
    have := (div_le_iff₀ (by positivity : 0 < 2 * A)).mp hQRdiv
    nlinarith
  rw [sum_grandchildren_descendantScaleAt_eq_occupiedScale
    hG R z θ hz u]
  dsimp [recursiveDeletionScaleConstant, A, xQ, xR] at *
  nlinarith

namespace MaximalModulusTrace

/-- The path terminal variance is the subtree variance at the recorded terminal root. -/
theorem terminalVariance_eq_subtreeVarianceAt
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z}
    {θ : ℝ} {u : V} (τ : MaximalModulusTrace R z hz θ u) :
    τ.terminalVariance = subtreeVarianceAt R z hz τ.terminalRoot := by
  induction τ with
  | stop u => rfl
  | @qStep u v huv hmax tail ih =>
      unfold terminalVariance
      change DownwardPath.terminalValue (subtreeVarianceAt R z hz)
        (u :: tail.vertices) = _
      rw [tail.vertices_eq_cons_tail]
      simp only [DownwardPath.terminalValue, terminalRoot]
      rw [← tail.vertices_eq_cons_tail]
      exact ih
  | @rStep u c v huc hcv hmax tail ih =>
      unfold terminalVariance
      change DownwardPath.terminalValue (subtreeVarianceAt R z hz)
        (u :: c :: tail.vertices) = _
      rw [tail.vertices_eq_cons_tail]
      simp only [DownwardPath.terminalValue, terminalRoot]
      rw [← tail.vertices_eq_cons_tail]
      exact ih

end MaximalModulusTrace

namespace RecursiveDecomposition

/-- Sum of scales of the concrete A.10 recursive family. -/
noncomputable def familyScale
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) : ℝ :=
  ∑ v ∈ D.family, descendantScaleAt R z hz θ v

lemma familyScale_nonneg
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    0 ≤ D.familyScale := by
  unfold familyScale
  exact Finset.sum_nonneg fun v hv => mul_nonneg (sq_nonneg θ)
    (R.subtreeLawAt z hz v).variance_nonneg

/-- A.9 terminal scale is the scale at its recorded terminal root. -/
theorem toTrace_terminalScale_eq
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    D.toTrace.terminalScale =
      descendantScaleAt R z hz θ D.toTrace.terminalRoot := by
  unfold MaximalModulusTrace.terminalScale descendantScaleAt
  rw [D.toTrace.terminalVariance_eq_subtreeVarianceAt]

lemma sum_qDiscardedRoots_scale_eq
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u v : V) :
    (∑ w ∈ MaximalModulusTrace.qDiscardedRoots R u v,
      descendantScaleAt R z hz θ w) =
      θ ^ 2 * MaximalModulusTrace.qDiscardedVariance R z hz u v := by
  unfold MaximalModulusTrace.qDiscardedRoots
    MaximalModulusTrace.qDiscardedVariance descendantScaleAt
  rw [← Finset.mul_sum]

lemma sum_rDiscardedRoots_scale_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) {u c v : V}
    (huc : R.IsChild (G := G) u c) (hcv : R.IsChild (G := G) c v) :
    (∑ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v,
      descendantScaleAt R z hz θ w) =
      θ ^ 2 * MaximalModulusTrace.rDiscardedVariance R z hz u c v := by
  rw [RecursiveDecomposition.sum_rDiscardedRoots_eq hG R huc hcv
    (fun w => descendantScaleAt R z hz θ w)]
  unfold MaximalModulusTrace.rDiscardedVariance descendantScaleAt
  simp_rw [← Finset.mul_sum]
  ring

/-- A.61 plus A.9: the terminal/discarded scale account is absorbed by the
scale sum of the actual recursive family. -/
theorem terminal_add_discardedScale_le_familyScale
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (hX0 : highScaleThreshold Z ≤ X0)
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    D.toTrace.terminalScale + D.toTrace.discardedScale ≤
      recursiveDeletionScaleConstant Z * D.familyScale := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hC1 : 1 ≤ recursiveDeletionScaleConstant Z :=
    recursiveDeletionScaleConstant_one_le hZ
  induction D with
  | retained u hretain =>
      have hx0 : 0 ≤ descendantScaleAt R z hz θ u :=
        mul_nonneg (sq_nonneg θ) (R.subtreeLawAt z hz u).variance_nonneg
      simp [RecursiveDecomposition.toTrace, MaximalModulusTrace.terminalScale,
        MaximalModulusTrace.terminalVariance, MaximalModulusTrace.vertices,
        DownwardPath.terminalValue, MaximalModulusTrace.discardedScale,
        MaximalModulusTrace.discardedVariance, familyScale,
        RecursiveDecomposition.family, descendantScaleAt]
      simpa [descendantScaleAt] using
        (mul_le_mul_of_nonneg_right hC1 hx0)
  | splitQ u hretain hmax hsplit =>
      have hhigh : highScaleThreshold Z ≤ descendantScaleAt R z hz θ u := by
        have hx : X0 < descendantScaleAt R z hz θ u :=
          lt_of_not_ge (fun h => hretain (Or.inl h))
        exact hX0.trans hx.le
      have h61 := qDeletion_scale_control_A61 hG R Z z θ hz hzZ hθ u hhigh
      simpa [RecursiveDecomposition.toTrace, MaximalModulusTrace.terminalScale,
        MaximalModulusTrace.terminalVariance, MaximalModulusTrace.vertices,
        DownwardPath.terminalValue, MaximalModulusTrace.discardedScale,
        MaximalModulusTrace.discardedVariance, familyScale,
        RecursiveDecomposition.family, descendantScaleAt] using h61
  | splitR u hretain hmax hsplit =>
      have hhigh : highScaleThreshold Z ≤ descendantScaleAt R z hz θ u := by
        have hx : X0 < descendantScaleAt R z hz θ u :=
          lt_of_not_ge (fun h => hretain (Or.inl h))
        exact hX0.trans hx.le
      have hnarrow : ¬ IsHighScaleNarrow R Z z hz θ u :=
        fun hn => hretain (Or.inr hn)
      have h61 := rDeletion_scale_control_A61 hG R Z z θ hz hzZ hθ u
        hhigh hmax hnarrow
      simpa [RecursiveDecomposition.toTrace, MaximalModulusTrace.terminalScale,
        MaximalModulusTrace.terminalVariance, MaximalModulusTrace.vertices,
        DownwardPath.terminalValue, MaximalModulusTrace.discardedScale,
        MaximalModulusTrace.discardedVariance, familyScale,
        RecursiveDecomposition.family, descendantScaleAt] using h61
  | @qStep u v hretain hmax hone huv tail ih =>
      have hlocal0 : 0 ≤ ∑ w ∈ MaximalModulusTrace.qDiscardedRoots R u v,
          descendantScaleAt R z hz θ w :=
        Finset.sum_nonneg fun w hw => mul_nonneg (sq_nonneg θ)
          (R.subtreeLawAt z hz w).variance_nonneg
      have hlocal := mul_le_mul_of_nonneg_right hC1 hlocal0
      rw [familyScale, RecursiveDecomposition.family,
        Finset.sum_union
          (RecursiveDecomposition.disjoint_qDiscardedRoots_family hG huv tail)]
      rw [toTrace_terminalScale_eq] at ih ⊢
      simp only [RecursiveDecomposition.toTrace,
        MaximalModulusTrace.terminalRoot,
        MaximalModulusTrace.discardedScale,
        MaximalModulusTrace.discardedVariance] at ih ⊢
      rw [mul_add, ← sum_qDiscardedRoots_scale_eq R z θ hz u v]
      change descendantScaleAt R z hz θ tail.toTrace.terminalRoot +
          θ ^ 2 * tail.toTrace.discardedVariance ≤
        recursiveDeletionScaleConstant Z *
          (∑ x ∈ tail.family, descendantScaleAt R z hz θ x) at ih
      rw [mul_add]
      norm_num at hlocal
      linarith
  | @rStep u c v hretain hmax hone huc hcv tail ih =>
      have hlocal0 : 0 ≤ ∑ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v,
          descendantScaleAt R z hz θ w :=
        Finset.sum_nonneg fun w hw => mul_nonneg (sq_nonneg θ)
          (R.subtreeLawAt z hz w).variance_nonneg
      have hlocal := mul_le_mul_of_nonneg_right hC1 hlocal0
      rw [familyScale, RecursiveDecomposition.family,
        Finset.sum_union
          (RecursiveDecomposition.disjoint_rDiscardedRoots_family hG huc hcv tail)]
      rw [toTrace_terminalScale_eq] at ih ⊢
      simp only [RecursiveDecomposition.toTrace,
        MaximalModulusTrace.terminalRoot,
        MaximalModulusTrace.discardedScale,
        MaximalModulusTrace.discardedVariance] at ih ⊢
      rw [mul_add, ← sum_rDiscardedRoots_scale_eq hG R z θ hz huc hcv]
      change descendantScaleAt R z hz θ tail.toTrace.terminalRoot +
          θ ^ 2 * tail.toTrace.discardedVariance ≤
        recursiveDeletionScaleConstant Z *
          (∑ x ∈ tail.family, descendantScaleAt R z hz θ x) at ih
      rw [mul_add]
      norm_num at hlocal
      linarith

/-- Appendix A, (A.67), derived from the concrete A.9 trace and A.61. -/
theorem scale_le_K_add_familyScale_A67
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (hX0 : highScaleThreshold Z ≤ X0)
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    descendantScaleAt R z hz θ u ≤
      recursiveScaleConstant Z * (D.K + D.familyScale) := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hD1 : 1 ≤ recursiveDeletionScaleConstant Z :=
    recursiveDeletionScaleConstant_one_le hZ
  have hTD := D.terminal_add_discardedScale_le_familyScale
    hG hzZ hθ hX0
  have hK0 : 0 ≤ D.K := by
    unfold RecursiveDecomposition.K MaximalModulusTrace.K
    exact mul_nonneg (sq_nonneg θ)
      (add_nonneg D.toTrace.nonneg_pathOccupationMass
        D.toTrace.nonneg_rBarrierMass)
  have hsum : D.K + D.toTrace.terminalScale + D.toTrace.discardedScale ≤
      recursiveDeletionScaleConstant Z * (D.K + D.familyScale) := by
    have hDK := mul_le_mul_of_nonneg_right hD1 hK0
    nlinarith
  have hC0 : 0 ≤ maximalModulusPathVarianceConstant Z :=
    (le_max_left (1 : ℝ) _).trans' (by norm_num)
  have h63 := D.toTrace.scale_le_K_terminal_discarded_A63
    hG R Z z θ hz hzZ
  have hmul := mul_le_mul_of_nonneg_left hsum hC0
  exact h63.trans (by
    simpa [recursiveScaleConstant, mul_assoc] using hmul)

end RecursiveDecomposition

/-- The manuscript constant `a₀=1/(2C₁)`. -/
noncomputable def recursiveA0 (Z : ℝ) : ℝ :=
  1 / (2 * recursiveScaleConstant Z)

lemma recursiveA0_pos {Z : ℝ} (hZ : 0 < Z) : 0 < recursiveA0 Z := by
  unfold recursiveA0
  exact one_div_pos.mpr (mul_pos (by norm_num) (recursiveScaleConstant_pos hZ))

/-- Appendix A, (A.69), from (A.67) in the small-`K` branch. -/
theorem child_scale_sum_A69
    {Z X K S : ℝ} (hZ : 0 < Z)
    (h67 : X ≤ recursiveScaleConstant Z * (K + S))
    (hK : K < X / (2 * recursiveScaleConstant Z)) :
    recursiveA0 Z * X ≤ S := by
  have hC : 0 < recursiveScaleConstant Z := recursiveScaleConstant_pos hZ
  have hden : 0 < 2 * recursiveScaleConstant Z := mul_pos (by norm_num) hC
  have hm := (lt_div_iff₀ hden).mp hK
  have hCK : recursiveScaleConstant Z * K < X / 2 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  unfold recursiveA0
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ hden).2
  nlinarith

/-- The two alternatives in (A.68) for a finite component family. -/
def ScaleFamilyDichotomy
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (θ σ X : ℝ) (s : Finset V) : Prop :=
  (∀ v ∈ s, descendantScaleAt R z hz θ v ≤ σ * X) ∨
    ∃ v ∈ s, ∃ w ∈ s, v ≠ w ∧
      σ * X < descendantScaleAt R z hz θ v ∧
      σ * X < descendantScaleAt R z hz θ w

/-- A finite root family whose heavy subfamily is not a singleton satisfies
exactly the structural alternative used in (A.68). -/
theorem scaleFamilyDichotomy_of_not_heavy_singleton
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (θ σ X : ℝ) (s : Finset V)
    (hsplit : ¬ ∃ v : V, heavyRootsIn R z hz θ σ X s = {v}) :
    ScaleFamilyDichotomy R z hz θ σ X s := by
  let H := heavyRootsIn R z hz θ σ X s
  by_cases he : H.Nonempty
  · obtain ⟨v, hv⟩ := he
    have hne : H ≠ {v} := fun h => hsplit ⟨v, h⟩
    have hw : ∃ w ∈ H, w ≠ v := by
      by_contra hn
      push_neg at hn
      apply hne
      ext w
      constructor
      · intro hw
        simpa [hn w hw]
      · intro hw
        have hwv : w = v := Finset.mem_singleton.mp hw
        subst w
        exact hv
    obtain ⟨w, hw, hwv⟩ := hw
    right
    have hv' := (mem_heavyRootsIn R z hz θ σ X s v).mp hv
    have hw' := (mem_heavyRootsIn R z hz θ σ X s w).mp hw
    exact ⟨v, hv'.1, w, hw'.1, Ne.symm hwv, hv'.2, hw'.2⟩
  · left
    intro v hv
    by_contra hn
    have : v ∈ H := (mem_heavyRootsIn R z hz θ σ X s v).2
      ⟨hv, lt_of_not_ge hn⟩
    exact he ⟨v, this⟩

namespace RecursiveDecomposition

/-- Appendix A, (A.68): the actual recursively produced family is either
uniformly small, has two heavy members, or the directly retained endpoint is a
large narrow subtree (the manuscript's stated exception). -/
theorem family_scale_dichotomy_or_large_narrow_A68
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (hX0σ : X0 ≤ σ * X)
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    ScaleFamilyDichotomy R z hz θ σ X D.family ∨
      (IsHighScaleNarrow R Z z hz θ D.toTrace.terminalRoot ∧
        σ * X < descendantScaleAt R z hz θ D.toTrace.terminalRoot) := by
  induction D with
  | retained u hretain =>
      rcases hretain with hsmall | hnarrow
      · left; left
        intro v hv
        simp only [RecursiveDecomposition.family, Finset.mem_singleton] at hv
        subst v
        exact hsmall.trans hX0σ
      · by_cases hs : descendantScaleAt R z hz θ u ≤ σ * X
        · left; left
          intro v hv
          have hvu : v = u := by
            simpa [RecursiveDecomposition.family] using hv
          subst v
          exact hs
        · right
          simpa [RecursiveDecomposition.toTrace,
            MaximalModulusTrace.terminalRoot] using
            And.intro hnarrow (lt_of_not_ge hs)
  | splitQ u hretain hmax hsplit =>
      left
      exact scaleFamilyDichotomy_of_not_heavy_singleton
        R z hz θ σ X (R.children (G := G) u) hsplit
  | splitR u hretain hmax hsplit =>
      left
      exact scaleFamilyDichotomy_of_not_heavy_singleton
        R z hz θ σ X (grandchildrenAt R u) hsplit
  | @qStep u v hretain hmax hone huv tail ih =>
      have hlocal : ∀ w ∈ MaximalModulusTrace.qDiscardedRoots R u v,
          descendantScaleAt R z hz θ w ≤ σ * X := by
        intro w hw
        have hwdata : w ≠ v ∧ R.IsChild (G := G) u w := by
          simpa [MaximalModulusTrace.qDiscardedRoots] using hw
        by_contra hn
        have wh : w ∈ qHeavyRoots R z hz θ σ X u :=
          (mem_qHeavyRoots R z hz θ σ X u w).2
            ⟨hwdata.2, lt_of_not_ge hn⟩
        have : w = v := by simpa [hone] using wh
        exact hwdata.1 this
      rcases ih with htail | hex
      · left
        rcases htail with hsmall | htwo
        · left
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hlocal w hw
          · exact hsmall w hw
        · right
          obtain ⟨a, ha, b, hb, hab, hha, hhb⟩ := htwo
          exact ⟨a, Finset.mem_union_right _ ha,
            b, Finset.mem_union_right _ hb, hab, hha, hhb⟩
      · right
        simpa [RecursiveDecomposition.toTrace,
          MaximalModulusTrace.terminalRoot] using hex
  | @rStep u c v hretain hmax hone huc hcv tail ih =>
      have hlocal : ∀ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v,
          descendantScaleAt R z hz θ w ≤ σ * X := by
        intro w hw
        have hwroot : w ∈ grandchildrenAt R u := by
          simp only [grandchildrenAt, Finset.mem_biUnion]
          rcases Finset.mem_union.mp hw with hw | hw
          · have hwc : R.IsChild (G := G) c w := by
              simpa using (Finset.mem_erase.mp hw).2
            exact ⟨c, (R.mem_children (G := G) u c).mpr huc,
              (R.mem_children (G := G) c w).mpr hwc⟩
          · rcases Finset.mem_biUnion.mp hw with ⟨d, hd, hwd⟩
            have hdu : R.IsChild (G := G) u d := by
              simpa using (Finset.mem_erase.mp hd).2
            exact ⟨d, (R.mem_children (G := G) u d).mpr hdu, hwd⟩
        have hwne : w ≠ v := by
          intro hwv
          subst w
          rcases Finset.mem_union.mp hw with hw | hw
          · exact (Finset.mem_erase.mp hw).1 rfl
          · rcases Finset.mem_biUnion.mp hw with ⟨d, hd, hvd⟩
            have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
            exact hdc (isChild_unique (G := G) hG R hcv
              ((R.mem_children (G := G) d v).mp hvd)).symm
        by_contra hn
        have wh : w ∈ rHeavyRoots R z hz θ σ X u :=
          (mem_rHeavyRoots R z hz θ σ X u w).2
            ⟨hwroot, lt_of_not_ge hn⟩
        have : w = v := by simpa [hone] using wh
        exact hwne this
      rcases ih with htail | hex
      · left
        rcases htail with hsmall | htwo
        · left
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hlocal w hw
          · exact hsmall w hw
        · right
          obtain ⟨a, ha, b, hb, hab, hha, hhb⟩ := htwo
          exact ⟨a, Finset.mem_union_right _ ha,
            b, Finset.mem_union_right _ hb, hab, hha, hhb⟩
      · right
        simpa [RecursiveDecomposition.toTrace,
          MaximalModulusTrace.terminalRoot] using hex

end RecursiveDecomposition

end
end AppendixA
end Forest
end Erdos993
