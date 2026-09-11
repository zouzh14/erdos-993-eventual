import Erdos993.Forest.RecursiveDecompositionGain

/-!
# Full-domain Appendix A.3 and A.4 assembly

This module closes the rooted A.10 recursion, lifts the result over forest
components, and exposes both the stronger `H_α` envelope (A.3) and the exact
logarithmic/polynomial forms of manuscript equation (A.4).
-/

open scoped BigOperators

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

lemma boundedScaleH_eq_self_of_nonneg_of_le_one
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : boundedScaleH α x = x := by
  unfold boundedScaleH
  rw [min_eq_left]
  by_cases hx : x = 0
  · subst x
    exact Real.rpow_nonneg (by norm_num) α
  · have hxp : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    simpa using Real.rpow_le_rpow_of_exponent_ge hxp hx1 hα1.le

/-- Finite subadditivity of the manuscript envelope
`H_α(x) = min x (x^α)` on nonnegative inputs. -/
theorem boundedScaleH_sum_le_sum
    {ι : Type*} {s : Finset ι} {x : ι → ℝ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) :
    boundedScaleH α (∑ i ∈ s, x i) ≤
      ∑ i ∈ s, boundedScaleH α (x i) := by
  classical
  let S : ℝ := ∑ i ∈ s, x i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i hi => hx0 i hi
  by_cases hS1 : S ≤ 1
  · have hxiS : ∀ i ∈ s, x i ≤ S := by
      intro i hi
      dsimp [S]
      exact Finset.single_le_sum hx0 hi
    rw [boundedScaleH_eq_self_of_nonneg_of_le_one hα0 hα1 hS0 hS1]
    dsimp [S]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i hi
    symm
    exact boundedScaleH_eq_self_of_nonneg_of_le_one hα0 hα1
      (hx0 i hi) ((hxiS i hi).trans hS1)
  · have hS1' : 1 ≤ S := le_of_not_ge hS1
    have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS1'
    have hterm : ∀ i ∈ s,
        (x i / S) * boundedScaleH α S ≤ boundedScaleH α (x i) := by
      intro i hi
      apply boundedScaleH_chord hα0 hα1 (hx0 i hi) hS1'
      dsimp [S]
      exact Finset.single_le_sum hx0 hi
    have hsumdiv : ∑ i ∈ s, x i / S = 1 := by
      rw [← Finset.sum_div]
      dsimp [S]
      exact div_self hSpos.ne'
    calc
      boundedScaleH α (∑ i ∈ s, x i) = boundedScaleH α S := rfl
      _ = (∑ i ∈ s, x i / S) * boundedScaleH α S := by rw [hsumdiv, one_mul]
      _ = ∑ i ∈ s, (x i / S) * boundedScaleH α S := by rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ s, boundedScaleH α (x i) := Finset.sum_le_sum hterm

/-- Global scalar comparison used to pass from the stronger `H_α` envelope
in (A.3) to the manuscript's logarithmic envelope in (A.4).  The factor
`α / 2` works uniformly, including at `x = 0`. -/
lemma log_one_add_le_boundedScaleH
    {α x : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hx0 : 0 ≤ x) :
    (α / 2) * Real.log (1 + x) ≤ boundedScaleH α x := by
  have hlog0 : 0 ≤ Real.log (1 + x) :=
    Real.log_nonneg (by linarith)
  by_cases hx1 : x ≤ 1
  · rw [boundedScaleH_eq_self_of_nonneg_of_le_one hα0 hα1 hx0 hx1]
    have hcoef : α / 2 ≤ 1 := by linarith
    calc
      (α / 2) * Real.log (1 + x) ≤ 1 * Real.log (1 + x) :=
        mul_le_mul_of_nonneg_right hcoef hlog0
      _ = Real.log (1 + x) := one_mul _
      _ ≤ x := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
        linarith
  · have hx : 1 ≤ x := le_of_not_ge hx1
    have hxpos : 0 < x := zero_lt_one.trans_le hx
    have harg : 1 + x ≤ 2 * x := by linarith
    have hlogsum : Real.log (1 + x) ≤ Real.log 2 + Real.log x := by
      calc
        Real.log (1 + x) ≤ Real.log (2 * x) :=
          Real.strictMonoOn_log.monotoneOn
            (show 1 + x ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; linarith)
            (show 2 * x ∈ Set.Ioi (0 : ℝ) by simp only [Set.mem_Ioi]; positivity) harg
        _ = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
    have hlog2nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at this ⊢
      exact this
    have hαlog2 : α * Real.log 2 ≤ 1 := by
      calc
        α * Real.log 2 ≤ 1 * Real.log 2 :=
          mul_le_mul_of_nonneg_right hα1.le hlog2nonneg
        _ = Real.log 2 := one_mul _
        _ ≤ 1 := hlog2le
    have hxp : 0 < x ^ α := Real.rpow_pos_of_pos hxpos α
    have hxpow1 : 1 ≤ x ^ α := Real.one_le_rpow hx hα0.le
    have hαlogx : α * Real.log x ≤ x ^ α := by
      have hh := Real.log_le_sub_one_of_pos hxp
      rw [Real.log_rpow hxpos α] at hh
      linarith
    have htwice : α * Real.log (1 + x) ≤ 2 * x ^ α := by
      calc
        α * Real.log (1 + x) ≤ α * (Real.log 2 + Real.log x) :=
          mul_le_mul_of_nonneg_left hlogsum hα0.le
        _ = α * Real.log 2 + α * Real.log x := by ring
        _ ≤ 1 + x ^ α := add_le_add hαlog2 hαlogx
        _ ≤ 2 * x ^ α := by linarith
    have hhalf : (α / 2) * Real.log (1 + x) ≤ x ^ α := by linarith
    unfold boundedScaleH
    rw [min_eq_right]
    · exact hhalf
    · exact Real.rpow_le_self_of_one_le hx hα1.le

/-- The A.65 direct branch after explicitly absorbing its additive offset. -/
theorem maximalPath_direct_boundedScaleH
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic)
    {R : ActualRootedVariance.ComponentRooting G} {Z z θ X α : ℝ}
    (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    {u : V} (τ : MaximalModulusTrace R z hz θ u)
    (hα : 0 < α) (hX0 : 0 ≤ X)
    (habsorb :
      4 * recursiveScaleConstant Z * maximalModulusPathLossOffsetConstant Z /
          maximalModulusPathLossRateConstant Z ≤ X)
    (hK : X / (2 * recursiveScaleConstant Z) ≤ τ.K) :
    (((maximalModulusPathLossRateConstant Z /
          (4 * recursiveScaleConstant Z)) * boundedScaleH α X : ℝ) : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  let r := maximalModulusPathLossRateConstant Z
  let C := recursiveScaleConstant Z
  let o := maximalModulusPathLossOffsetConstant Z
  have hr : 0 < r := MaximalModulusTrace.maximalModulusPathLossRateConstant_pos hZ
  have hC : 0 < C := recursiveScaleConstant_pos hZ
  have ho : 0 ≤ o := by
    dsimp [o, maximalModulusPathLossOffsetConstant]
    exact (actualA43RateConstant_pos hZ).le
  have hp : 0 < r / (4 * C) := div_pos hr (mul_pos (by norm_num) hC)
  have habsorb' : 4 * C * o / r ≤ X := by simpa [C, r, o] using habsorb
  have hoq : o ≤ (r / (4 * C)) * X := by
    calc
      o = (r / (4 * C)) * (4 * C * o / r) := by field_simp [hr.ne', hC.ne']
      _ ≤ (r / (4 * C)) * X := mul_le_mul_of_nonneg_left habsorb' hp.le
  have hHX : boundedScaleH α X ≤ X := min_le_left _ _
  have hreal : (r / (4 * C)) * boundedScaleH α X ≤ r * τ.K - o := by
    have hfirst : (r / (4 * C)) * boundedScaleH α X ≤
        (r / (4 * C)) * X := mul_le_mul_of_nonneg_left hHX hp.le
    have hsecond : (r / (4 * C)) * X ≤ r * (X / (2 * C)) - o := by
      have heq : r * (X / (2 * C)) = 2 * ((r / (4 * C)) * X) := by
        field_simp [hC.ne']
        ring
      rw [heq]
      linarith
    have hthird : r * (X / (2 * C)) - o ≤ r * τ.K - o := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left hK hr.le) o
    exact hfirst.trans (hsecond.trans hthird)
  exact (EReal.coe_le_coe_iff.mpr (by simpa [r, C, o] using hreal)).trans
    (τ.logarithmicLoss_ge_K_A65 hG R Z z θ hz hzZ hθ)

private theorem subtreeLogarithmicLoss_nonneg
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (R : ActualRootedVariance.ComponentRooting G) (z θ : ℝ) (hz : 0 < z)
    (u : V) :
    (0 : EReal) ≤ (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  apply FiniteLatticeLaw.coe_le_logarithmicLoss_of_modulus_le_exp_neg
    (R.subtreeLawAt z hz u) θ 0 (le_refl 0)
  simpa using (R.subtreeLawAt z hz u).characteristicModulus_le_one θ

/-- The terminal loss is one of the nonnegative summands in the exact A.64
account. -/
theorem MaximalModulusTrace.terminalLoss_le_accountedLoss
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    {R : ActualRootedVariance.ComponentRooting G} {z θ : ℝ} {hz : 0 < z}
    {u : V} (τ : MaximalModulusTrace R z hz θ u) :
    τ.terminalLoss ≤ τ.accountedLoss := by
  induction τ with
  | stop u => rfl
  | @qStep u v huv hmax tail ih =>
      change tail.terminalLoss ≤
        MaximalModulusTrace.qDiscardedLoss R z θ hz u v + tail.accountedLoss
      calc
        tail.terminalLoss ≤ tail.accountedLoss := ih
        _ = 0 + tail.accountedLoss := (zero_add _).symm
        _ ≤ MaximalModulusTrace.qDiscardedLoss R z θ hz u v +
              tail.accountedLoss := by
          have hq : (0 : EReal) ≤
              MaximalModulusTrace.qDiscardedLoss R z θ hz u v := by
            unfold MaximalModulusTrace.qDiscardedLoss
            exact Finset.sum_nonneg fun w hw => subtreeLogarithmicLoss_nonneg R z θ hz w
          simpa [add_comm] using add_le_add_right hq tail.accountedLoss
  | @rStep u c v huc hcv hmax tail ih =>
      change tail.terminalLoss ≤
        MaximalModulusTrace.rDiscardedLoss R z θ hz u c v + tail.accountedLoss
      calc
        tail.terminalLoss ≤ tail.accountedLoss := ih
        _ = 0 + tail.accountedLoss := (zero_add _).symm
        _ ≤ MaximalModulusTrace.rDiscardedLoss R z θ hz u c v +
              tail.accountedLoss := by
          have hr : (0 : EReal) ≤
              MaximalModulusTrace.rDiscardedLoss R z θ hz u c v := by
            unfold MaximalModulusTrace.rDiscardedLoss
            apply add_nonneg
            · exact Finset.sum_nonneg fun w hw => subtreeLogarithmicLoss_nonneg R z θ hz w
            · exact Finset.sum_nonneg fun d hd =>
                Finset.sum_nonneg fun w hw => subtreeLogarithmicLoss_nonneg R z θ hz w
          simpa [add_comm] using add_le_add_right hr tail.accountedLoss

/-- The A.66 direct branch at a narrow terminal subtree, propagated to the
original subtree by the exact A.64 account. -/
theorem narrowTerminal_direct_boundedScaleH
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic)
    {R : ActualRootedVariance.ComponentRooting G} {Z z θ X σ α : ℝ}
    (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    {u : V} (τ : MaximalModulusTrace R z hz θ u)
    (hα : 0 < α) (hX0 : 0 ≤ X) (hσ0 : 0 < σ)
    (hnarrow : IsHighScaleNarrow R Z z hz θ τ.terminalRoot)
    (hlarge : σ * X < descendantScaleAt R z hz θ τ.terminalRoot) :
    (((narrowHighScaleRateConstant Z * σ) * boundedScaleH α X : ℝ) : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hn : 0 < narrowHighScaleRateConstant Z := narrowHighScaleRateConstant_pos hZ
  have hH : boundedScaleH α X ≤ X := min_le_left _ _
  have hreal : (narrowHighScaleRateConstant Z * σ) * boundedScaleH α X ≤
      narrowHighScaleRateConstant Z *
        descendantScaleAt R z hz θ τ.terminalRoot := by
    calc
      (narrowHighScaleRateConstant Z * σ) * boundedScaleH α X ≤
          (narrowHighScaleRateConstant Z * σ) * X :=
        mul_le_mul_of_nonneg_left hH (mul_nonneg hn.le hσ0.le)
      _ = narrowHighScaleRateConstant Z * (σ * X) := by ring
      _ ≤ narrowHighScaleRateConstant Z *
          descendantScaleAt R z hz θ τ.terminalRoot :=
        mul_le_mul_of_nonneg_left hlarge.le hn.le
  have h66 := highScaleNarrow_logarithmicLoss_A66
    hG R Z z θ hz hzZ hθ τ.terminalRoot hnarrow
  have hterminal :
      (((narrowHighScaleRateConstant Z * σ) * boundedScaleH α X : ℝ) : EReal) ≤
        τ.terminalLoss := by
    exact (EReal.coe_le_coe_iff.mpr hreal).trans (by
      simpa [MaximalModulusTrace.terminalLoss,
        narrowHighScaleOffsetConstant] using h66)
  exact hterminal.trans
    (τ.terminalLoss_le_accountedLoss.trans
      (τ.accountedLoss_le_subtreeLoss_A64 hG R z θ hz))

/-- Explicit Z-only scale above which both direct estimates have absorbed all
offsets and the A.10 gain hypotheses hold. -/
noncomputable def appendixA1ScaleThreshold (Z : ℝ) : ℝ :=
  max 1
    (max (highScaleThreshold Z / recursiveSigma Z)
      (max (1 / recursiveSigma Z)
        (4 * recursiveScaleConstant Z * maximalModulusPathLossOffsetConstant Z /
          maximalModulusPathLossRateConstant Z)))

lemma appendixA1ScaleThreshold_pos (Z : ℝ) : 0 < appendixA1ScaleThreshold Z := by
  unfold appendixA1ScaleThreshold
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

lemma highScaleThreshold_div_sigma_le_appendixA1ScaleThreshold (Z : ℝ) :
    highScaleThreshold Z / recursiveSigma Z ≤ appendixA1ScaleThreshold Z := by
  unfold appendixA1ScaleThreshold
  exact (le_max_left _ _).trans (le_max_right _ _)

lemma one_div_sigma_le_appendixA1ScaleThreshold (Z : ℝ) :
    1 / recursiveSigma Z ≤ appendixA1ScaleThreshold Z := by
  unfold appendixA1ScaleThreshold
  exact (le_max_left _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)

lemma pathOffsetThreshold_le_appendixA1ScaleThreshold (Z : ℝ) :
    4 * recursiveScaleConstant Z * maximalModulusPathLossOffsetConstant Z /
        maximalModulusPathLossRateConstant Z ≤ appendixA1ScaleThreshold Z := by
  unfold appendixA1ScaleThreshold
  exact (le_max_right _ _).trans (le_max_right _ _) |>.trans (le_max_right _ _)

/-- Explicit positive coefficient in the rooted and forest A.3 envelope. -/
noncomputable def appendixA1HConstant (Z : ℝ) : ℝ :=
  min (boundedScaleHAlphaConstant Z (appendixA1ScaleThreshold Z)
      (recursiveAlpha Z))
    (min
      (maximalModulusPathLossRateConstant Z /
        (4 * recursiveScaleConstant Z))
      (narrowHighScaleRateConstant Z * recursiveSigma Z))

lemma appendixA1HConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < appendixA1HConstant Z := by
  unfold appendixA1HConstant
  apply lt_min
  · exact boundedScaleHAlphaConstant_pos hZ (appendixA1ScaleThreshold_pos Z)
  · apply lt_min
    · exact div_pos
        (MaximalModulusTrace.maximalModulusPathLossRateConstant_pos hZ)
        (mul_pos (by norm_num) (recursiveScaleConstant_pos hZ))
    · exact mul_pos (narrowHighScaleRateConstant_pos hZ) (recursiveSigma_pos hZ)

lemma appendixA1HConstant_le_bounded (Z : ℝ) :
    appendixA1HConstant Z ≤
      boundedScaleHAlphaConstant Z (appendixA1ScaleThreshold Z)
        (recursiveAlpha Z) := by
  unfold appendixA1HConstant
  exact min_le_left _ _

lemma appendixA1HConstant_le_path (Z : ℝ) :
    appendixA1HConstant Z ≤
      maximalModulusPathLossRateConstant Z /
        (4 * recursiveScaleConstant Z) := by
  unfold appendixA1HConstant
  exact (min_le_right _ _).trans (min_le_left _ _)

lemma appendixA1HConstant_le_narrow (Z : ℝ) :
    appendixA1HConstant Z ≤
      narrowHighScaleRateConstant Z * recursiveSigma Z := by
  unfold appendixA1HConstant
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem subtreeOrder_lt_of_isDescendant_of_ne
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (R : ActualRootedVariance.ComponentRooting G) {u v : V}
    (hdesc : R.IsDescendant (G := G) u v) (hne : v ≠ u) :
    R.subtreeOrder (G := G) v < R.subtreeOrder (G := G) u := by
  unfold ActualRootedVariance.ComponentRooting.subtreeOrder
  apply Finset.card_lt_card
  constructor
  · exact descendants_subset_of_isDescendant R hdesc
  · intro hrev
    have huv : u ∈ R.descendants (G := G) v :=
      hrev (R.self_mem_descendants (G := G) u)
    have hvudesc : R.IsDescendant (G := G) v u :=
      (R.mem_descendants (G := G) v u).mp huv
    have hforward := ActualRootedVariance.ComponentRooting.depth_lt_of_isDescendant_of_ne
      (G := G) R hdesc hne.symm
    have hback := ActualRootedVariance.ComponentRooting.depth_le_of_isDescendant
      (G := G) R hvudesc
    omega

lemma recursiveDecomposition_eq_retained
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (R : ActualRootedVariance.ComponentRooting G) (Z z : ℝ) (hz : 0 < z)
    (θ X σ X0 : ℝ) (u : V)
    (hret : IsA10Retained R Z z hz θ X0 u) :
    recursiveDecomposition R Z z hz θ X σ X0 u =
      .retained u hret := by
  rw [recursiveDecomposition]
  simp [hret]

/-- Rooted-subtree form of the full-domain H-envelope, proved by strong
induction using the actual A.10 decomposition. -/
theorem rootedSubtree_boundedScaleH_A3
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ActualRootedVariance.ComponentRooting G)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V) :
    (((appendixA1HConstant Z) *
        boundedScaleH (recursiveAlpha Z)
          (descendantScaleAt R z hz θ u) : ℝ) : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    let X := descendantScaleAt R z hz θ u
    let T := appendixA1ScaleThreshold Z
    let α := recursiveAlpha Z
    let c := appendixA1HConstant Z
    have hX0 : 0 ≤ X :=
      mul_nonneg (sq_nonneg θ) (R.subtreeLawAt z hz u).variance_nonneg
    have hc : 0 < c := appendixA1HConstant_pos hZ
    have hH0 : 0 ≤ boundedScaleH α X := by
      exact le_min hX0 (Real.rpow_nonneg hX0 α)
    by_cases hbounded : X ≤ T
    · have hb := boundedScaleHAlpha
        (R.Subtree (G := G) u) (hG.induce _) Z z θ T α hZ hz hzZ
        (appendixA1ScaleThreshold_pos Z) (recursiveAlpha_pos hZ)
        (recursiveAlpha_lt_one hZ) hθ (by
          simpa [X, T, descendantScaleAt, subtreeVarianceAt, mul_comm] using hbounded)
      have hcle : c ≤ boundedScaleHAlphaConstant Z T α := by
        simpa [c, T, α] using appendixA1HConstant_le_bounded Z
      have hreal : c * boundedScaleH α X ≤
          boundedScaleHAlphaConstant Z T α * boundedScaleH α X :=
        mul_le_mul_of_nonneg_right hcle hH0
      exact (EReal.coe_le_coe_iff.mpr hreal).trans (by
        simpa [X, T, α, c, ActualRootedVariance.ComponentRooting.subtreeLawAt,
          descendantScaleAt, subtreeVarianceAt, mul_comm] using hb)
    · have hTX : T < X := lt_of_not_ge hbounded
      have hXpos : 0 < X := (appendixA1ScaleThreshold_pos Z).trans hTX
      let D : RecursiveDecomposition R Z z hz θ X (recursiveSigma Z)
          (highScaleThreshold Z) u :=
        recursiveDecomposition R Z z hz θ X (recursiveSigma Z)
          (highScaleThreshold Z) u
      by_cases hK : X / (2 * recursiveScaleConstant Z) ≤ D.K
      · have hdirect := maximalPath_direct_boundedScaleH hG hz hzZ hθ D.toTrace
          (recursiveAlpha_pos hZ) hX0
          ((pathOffsetThreshold_le_appendixA1ScaleThreshold Z).trans hTX.le) hK
        have hcle : c ≤ maximalModulusPathLossRateConstant Z /
            (4 * recursiveScaleConstant Z) := by
          simpa [c] using appendixA1HConstant_le_path Z
        have hreal : c * boundedScaleH α X ≤
            (maximalModulusPathLossRateConstant Z /
              (4 * recursiveScaleConstant Z)) * boundedScaleH α X :=
          mul_le_mul_of_nonneg_right hcle hH0
        exact (EReal.coe_le_coe_iff.mpr hreal).trans (by
          simpa [X, α, c] using hdirect)
      · have hK' : D.K < X / (2 * recursiveScaleConstant Z) := lt_of_not_ge hK
        have hX0σ : highScaleThreshold Z ≤ recursiveSigma Z * X := by
          have hs := recursiveSigma_pos hZ
          calc
            highScaleThreshold Z = recursiveSigma Z *
                (highScaleThreshold Z / recursiveSigma Z) := by
              field_simp [hs.ne']
            _ ≤ recursiveSigma Z * T :=
              mul_le_mul_of_nonneg_left
                (highScaleThreshold_div_sigma_le_appendixA1ScaleThreshold Z) hs.le
            _ ≤ recursiveSigma Z * X := mul_le_mul_of_nonneg_left hTX.le hs.le
        have hσX : 1 ≤ recursiveSigma Z * X := by
          have hs := recursiveSigma_pos hZ
          calc
            1 = recursiveSigma Z * (1 / recursiveSigma Z) := by field_simp [hs.ne']
            _ ≤ recursiveSigma Z * T :=
              mul_le_mul_of_nonneg_left
                (one_div_sigma_le_appendixA1ScaleThreshold Z) hs.le
            _ ≤ recursiveSigma Z * X := mul_le_mul_of_nonneg_left hTX.le hs.le
        by_cases hnarrow :
            IsHighScaleNarrow R Z z hz θ D.toTrace.terminalRoot ∧
              recursiveSigma Z * X <
                descendantScaleAt R z hz θ D.toTrace.terminalRoot
        · have hdirect := narrowTerminal_direct_boundedScaleH hG hz hzZ hθ D.toTrace
            (recursiveAlpha_pos hZ) hX0 (recursiveSigma_pos hZ) hnarrow.1 hnarrow.2
          have hcle : c ≤ narrowHighScaleRateConstant Z * recursiveSigma Z := by
            simpa [c] using appendixA1HConstant_le_narrow Z
          have hreal : c * boundedScaleH α X ≤
              (narrowHighScaleRateConstant Z * recursiveSigma Z) *
                boundedScaleH α X := mul_le_mul_of_nonneg_right hcle hH0
          exact (EReal.coe_le_coe_iff.mpr hreal).trans (by
            simpa [X, α, c] using hdirect)
        · have hdich : ScaleFamilyDichotomy R z hz θ (recursiveSigma Z) X D.family :=
            (D.family_scale_dichotomy_or_large_narrow_A68 hG hX0σ).resolve_right hnarrow
          have hgain := D.boundedScaleH_family_gain_A70 hG hzZ hθ le_rfl
            hX0σ rfl hσX hK' hnarrow
          have hslt : recursiveSigma Z * X < X :=
            mul_lt_of_lt_one_left hXpos (recursiveSigma_lt_one hZ)
          have hnotretain : ¬ IsA10Retained R Z z hz θ (highScaleThreshold Z) u := by
            intro hret
            rcases hret with hsmall | hnar
            · exact (not_lt_of_ge hsmall) (hX0σ.trans_lt hslt)
            · have hterm : D.toTrace.terminalRoot = u := by
                have heq := recursiveDecomposition_eq_retained R Z z hz θ X
                  (recursiveSigma Z) (highScaleThreshold Z) u (Or.inr hnar)
                simpa [D, heq, RecursiveDecomposition.toTrace,
                  MaximalModulusTrace.terminalRoot]
              exact hnarrow ⟨by simpa [hterm] using hnar, by
                rw [hterm]
                simpa [X] using hslt⟩
          have hstrict := D.familyRoot_isStrictDescendant hG hnotretain
          have hchild : ∀ v ∈ D.family,
              (((c * boundedScaleH α
                  (descendantScaleAt R z hz θ v) : ℝ) : EReal) ≤
                (R.subtreeLawAt z hz v).logarithmicLoss θ) := by
            intro v hv
            obtain ⟨hdesc, hne⟩ := hstrict v hv
            have hlt := subtreeOrder_lt_of_isDescendant_of_ne R hdesc hne
            have hiv := ih (R.subtreeOrder (G := G) v)
              (by simpa [horder] using hlt) v rfl
            simpa [c, α] using hiv
          have hsumloss :
              (∑ v ∈ D.family,
                ((c * boundedScaleH α
                  (descendantScaleAt R z hz θ v) : ℝ) : EReal)) ≤ D.familyLoss := by
            unfold RecursiveDecomposition.familyLoss
            exact Finset.sum_le_sum fun v hv => hchild v hv
          have hHle : boundedScaleH α X ≤
              ∑ v ∈ D.family,
                boundedScaleH α (descendantScaleAt R z hz θ v) := by
            have hzeta := recursiveZeta_pos Z
            have hfactor : boundedScaleH α X ≤
                (1 + recursiveZeta Z) * boundedScaleH α X := by
              nlinarith [mul_nonneg hzeta.le hH0]
            exact hfactor.trans hgain.le
          have hreal : c * boundedScaleH α X ≤
              ∑ v ∈ D.family,
                c * boundedScaleH α (descendantScaleAt R z hz θ v) := by
            rw [← Finset.mul_sum]
            exact mul_le_mul_of_nonneg_left hHle hc.le
          have hcoe :
              (((c * boundedScaleH α X : ℝ) : EReal)) ≤
                ∑ v ∈ D.family,
                  ((c * boundedScaleH α
                    (descendantScaleAt R z hz θ v) : ℝ) : EReal) := by
            have hmap : ∀ s : Finset V,
                (((∑ v ∈ s, c * boundedScaleH α
                    (descendantScaleAt R z hz θ v) : ℝ) : ℝ) : EReal) =
                  ∑ v ∈ s, ((c * boundedScaleH α
                    (descendantScaleAt R z hz θ v) : ℝ) : EReal) := by
              intro s
              induction s using Finset.induction_on with
              | empty => simp
              | @insert a s ha ihs => simp [Finset.sum_insert, ha, ihs]
            have hh := EReal.coe_le_coe_iff.mpr hreal
            rw [hmap D.family] at hh
            exact hh
          exact hcoe.trans
            (hsumloss.trans (D.familyLoss_le_subtreeLoss_A10 hG))

/-- Appendix A, equation (A.3), for every finite acyclic graph at bounded
positive activity.  Both constants are explicit functions of `Z`. -/
theorem hardCoreLaw_boundedScaleH_A3
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    (((appendixA1HConstant Z) * boundedScaleH (recursiveAlpha Z)
        ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  classical
  let R := ActualRootedVariance.defaultComponentRooting G
  let c := appendixA1HConstant Z
  let α := recursiveAlpha Z
  have hroots : ∀ r ∈ R.componentRoots (G := G),
      (((c * boundedScaleH α
        (descendantScaleAt R z hz θ r) : ℝ) : EReal) ≤
          (R.subtreeLawAt z hz r).logarithmicLoss θ) := by
    intro r hr
    simpa [c, α] using rootedSubtree_boundedScaleH_A3 hG R Z z θ hZ hz hzZ hθ r
  have hsumloss :
      (∑ r ∈ R.componentRoots (G := G),
          ((c * boundedScaleH α
            (descendantScaleAt R z hz θ r) : ℝ) : EReal)) ≤
        (hardCoreLaw G z hz).logarithmicLoss θ := by
    rw [hardCoreLaw_logarithmicLoss_eq_sum_componentRoots G R z θ hz]
    exact Finset.sum_le_sum fun r hr => hroots r hr
  have hvar := R.variance_eq_sum_componentRoot_subtreeVarianceAt z hz
  have hscale : (hardCoreLaw G z hz).variance * θ ^ 2 =
      ∑ r ∈ R.componentRoots (G := G), descendantScaleAt R z hz θ r := by
    rw [hvar, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    simp [descendantScaleAt, subtreeVarianceAt, mul_comm]
  have hsub := boundedScaleH_sum_le_sum
    (s := R.componentRoots (G := G)) (x := fun r => descendantScaleAt R z hz θ r)
    (recursiveAlpha_pos hZ) (recursiveAlpha_lt_one hZ)
    (fun r hr => mul_nonneg (sq_nonneg θ) (R.subtreeLawAt z hz r).variance_nonneg)
  rw [← hscale] at hsub
  have hreal : c * boundedScaleH α ((hardCoreLaw G z hz).variance * θ ^ 2) ≤
      ∑ r ∈ R.componentRoots (G := G),
        c * boundedScaleH α (descendantScaleAt R z hz θ r) := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsub (appendixA1HConstant_pos hZ).le
  have hmap : ∀ s : Finset V,
      (((∑ r ∈ s, c * boundedScaleH α
          (descendantScaleAt R z hz θ r) : ℝ) : ℝ) : EReal) =
        ∑ r ∈ s, ((c * boundedScaleH α
          (descendantScaleAt R z hz θ r) : ℝ) : EReal) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ihs => simp [Finset.sum_insert, ha, ihs]
  have hcoe := EReal.coe_le_coe_iff.mpr hreal
  rw [hmap (R.componentRoots (G := G))] at hcoe
  exact (by simpa [c, α] using hcoe.trans hsumloss)

/-- Explicit positive Z-only constant retained for the stronger exponential
`H_α` envelope used by the canonical adapter. -/
noncomputable def appendixA4Constant (Z : ℝ) : ℝ := appendixA1HConstant Z

lemma appendixA4Constant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < appendixA4Constant Z := appendixA1HConstant_pos hZ

/-- Explicit positive Z-only constant in the exact logarithmic manuscript
(A.4).  It is `c_Z α_Z / 2`, where `c_Z` and `α_Z` are the explicit
constants from (A.3). -/
noncomputable def appendixA4LogConstant (Z : ℝ) : ℝ :=
  appendixA1HConstant Z * recursiveAlpha Z / 2

lemma appendixA4LogConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < appendixA4LogConstant Z := by
  unfold appendixA4LogConstant
  exact div_pos (mul_pos (appendixA1HConstant_pos hZ) (recursiveAlpha_pos hZ))
    (by norm_num)

/-- The global scalar absorption which turns the `H_α` right-hand side of
(A.3) into the logarithm in (A.4). -/
lemma appendixA4_log_le_boundedScaleH
    {Z x : ℝ} (hZ : 0 < Z) (hx0 : 0 ≤ x) :
    appendixA4LogConstant Z * Real.log (1 + x) ≤
      appendixA1HConstant Z * boundedScaleH (recursiveAlpha Z) x := by
  have hs := log_one_add_le_boundedScaleH
    (recursiveAlpha_pos hZ) (recursiveAlpha_lt_one hZ) hx0
  have hc := appendixA1HConstant_pos hZ
  have hm := mul_le_mul_of_nonneg_left hs hc.le
  unfold appendixA4LogConstant
  convert hm using 1 <;> ring

/-- Exact manuscript equation (A.4), in logarithmic-loss form:
`ℓ_{F,z}(θ) ≥ γ_Z log (1 + V_{F,z} θ²)`. -/
theorem hardCoreLaw_logarithmicLoss_ge_log_A4
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    (((appendixA4LogConstant Z) *
        Real.log (1 + (hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  let x := (hardCoreLaw G z hz).variance * θ ^ 2
  have hx0 : 0 ≤ x :=
    mul_nonneg (hardCoreLaw G z hz).variance_nonneg (sq_nonneg θ)
  have hscalar := appendixA4_log_le_boundedScaleH hZ hx0
  have hA3 := hardCoreLaw_boundedScaleH_A3 G hG Z z θ hZ hz hzZ hθ
  have hcoe := EReal.coe_le_coe_iff.mpr hscalar
  exact (by simpa [x] using hcoe.trans hA3)

/-- The stronger exponential `H_α` envelope obtained directly from (A.3),
including the zero-modulus case.  This is retained (rather than weakened) for
the concrete canonical full-domain adapter. -/
theorem hardCoreLaw_characteristicModulus_le_exp_A4
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    (hardCoreLaw G z hz).characteristicModulus θ ≤
      Real.exp (-(appendixA4Constant Z) *
        boundedScaleH (recursiveAlpha Z)
          ((hardCoreLaw G z hz).variance * θ ^ 2)) := by
  let μ := hardCoreLaw G z hz
  let q := appendixA4Constant Z * boundedScaleH (recursiveAlpha Z)
    (μ.variance * θ ^ 2)
  have hmain := hardCoreLaw_boundedScaleH_A3 G hG Z z θ hZ hz hzZ hθ
  by_cases hm : μ.characteristicModulus θ = 0
  · rw [hm]
    exact (Real.exp_pos _).le
  · have hmpos : 0 < μ.characteristicModulus θ :=
      lt_of_le_of_ne (μ.characteristicModulus_nonneg θ) (Ne.symm hm)
    have hreal : q ≤ -Real.log (μ.characteristicModulus θ) := by
      rw [FiniteLatticeLaw.logarithmicLoss,
        ENNReal.log_ofReal_of_pos hmpos] at hmain
      exact_mod_cast hmain
    calc
      μ.characteristicModulus θ = Real.exp (Real.log (μ.characteristicModulus θ)) :=
        (Real.exp_log hmpos).symm
      _ ≤ Real.exp (-q) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by simp [q, μ, appendixA4Constant]

/-- Exact manuscript equation (A.4), equivalently expressed as the polynomial
modulus envelope `M_{F,z}(θ) ≤ (1 + V_{F,z} θ²)⁻ᵞ`. -/
theorem hardCoreLaw_characteristicModulus_le_rpow_A4
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    (hardCoreLaw G z hz).characteristicModulus θ ≤
      (1 + (hardCoreLaw G z hz).variance * θ ^ 2) ^
        (-(appendixA4LogConstant Z)) := by
  let x := (hardCoreLaw G z hz).variance * θ ^ 2
  have hx0 : 0 ≤ x :=
    mul_nonneg (hardCoreLaw G z hz).variance_nonneg (sq_nonneg θ)
  have hstrong := hardCoreLaw_characteristicModulus_le_exp_A4
    G hG Z z θ hZ hz hzZ hθ
  have hscalar := appendixA4_log_le_boundedScaleH hZ hx0
  have hscalar' : appendixA4LogConstant Z * Real.log (1 + x) ≤
      appendixA4Constant Z * boundedScaleH (recursiveAlpha Z) x := by
    simpa [appendixA4Constant] using hscalar
  calc
    (hardCoreLaw G z hz).characteristicModulus θ ≤
        Real.exp (-(appendixA4Constant Z) * boundedScaleH (recursiveAlpha Z) x) := by
      simpa [x] using hstrong
    _ ≤ Real.exp (-(appendixA4LogConstant Z) * Real.log (1 + x)) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (1 + x) ^ (-(appendixA4LogConstant Z)) := by
      rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x)]
      congr 1
      ring
    _ = _ := by rfl

end
end AppendixA
end Forest
end Erdos993
