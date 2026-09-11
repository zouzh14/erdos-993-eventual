import Erdos993.Forest.TransferMatrixOccupation

/-!
# Genuine transfer-matrix contraction along a decorated downward path

This module completes Lemma A.8, equation (A.43), using the actual hard-core
side-forest characteristic factors, rooted occupation/vacancy probabilities,
and the actual complex terminal vector.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section
set_option maxHeartbeats 3000000
open scoped BigOperators
open ActualRootedVariance UniformFourthMoment

universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Coefficient multiplying the summed neighboring relative decrements. -/
noncomputable def actualOccupationNeighborConstant (Z : ℝ) : ℝ :=
  2 + 2 * occupationTwoRowConstant Z +
    4 * actualOccupationShiftConstant Z * occupationTwoRowConstant Z +
    actualOccupationShiftConstant Z

/-- Occupation-decay rate before combination with the side-barrier estimate. -/
noncomputable def actualOccupationDecayConstant (Z : ℝ) : ℝ :=
  1 / (3 * actualOccupationNeighborConstant Z)

/-- The concrete two-row payment constant is positive. -/
theorem occupationTwoRowConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < occupationTwoRowConstant Z := by
  let η : ℝ := 1 / (1 + Z)
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < sideRootGapConstant Z := by
    unfold sideRootGapConstant
    exact mul_pos (uniformGapConstant_pos hZ) (sq_pos_of_pos hη)
  dsimp [occupationTwoRowConstant, η]
  exact div_pos (div_pos (by norm_num) (sq_pos_of_pos hη)) (mul_pos hκ hη)

/-- The barrier-assisted adjacent-occupation constant is positive. -/
theorem actualOccupationShiftConstant_pos (Z : ℝ) :
    0 < actualOccupationShiftConstant Z := by
  unfold actualOccupationShiftConstant
  positivity

/-- The local-neighbor bookkeeping constant is positive. -/
theorem actualOccupationNeighborConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < actualOccupationNeighborConstant Z := by
  have hC := occupationTwoRowConstant_pos hZ
  have hB := actualOccupationShiftConstant_pos Z
  unfold actualOccupationNeighborConstant
  nlinarith [mul_pos hB hC]

/-- The occupation-decay rate is positive. -/
theorem actualOccupationDecayConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < actualOccupationDecayConstant Z := by
  unfold actualOccupationDecayConstant
  exact one_div_pos.mpr (mul_pos (by norm_num) (actualOccupationNeighborConstant_pos hZ))

/-- The occupation payment after summation, before the positive side-barrier
estimate is used to absorb its barrier slack. -/
theorem DownwardPath.actualTransferRow_normOne_le_exp_occupationSlack
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (P : DownwardPath R) :
    (P.actualTransferRow z hz θ).normOne ≤
      Real.exp (
        actualOccupationDecayConstant Z -
          actualOccupationDecayConstant Z * Real.sin (θ / 2) ^ 2 *
            P.occupationMass R z +
          Real.sin (θ / 2) ^ 2 * P.actualSideLogBarrierSum z / 3) := by
  rw [← P.actualTransferRowAt_edgeCount z hz θ]
  let n := P.edgeCount
  let h := Real.sin (θ / 2) ^ 2
  let C := occupationTwoRowConstant Z
  let B := actualOccupationShiftConstant Z
  let M := actualOccupationNeighborConstant Z
  let α := actualOccupationDecayConstant Z
  let N : ℕ → ℝ := fun k => (P.actualTransferRowAt z hz θ k).normOne
  let X : ℕ → ℝ := fun k => ‖(P.actualTransferRowAt z hz θ k).fst‖
  let b : ℕ → ℝ := fun k => P.actualOccupationAt z k
  let Λ : ℕ → ℝ := fun k => P.actualSideLogBarrierAt z k
  change N n ≤ Real.exp
    (α - α * h * P.occupationMass R z + h * P.actualSideLogBarrierSum z / 3)
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hn : 0 < n := by dsimp [n]; exact P.edgeCount_pos
  have hh0 : 0 ≤ h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by dsimp [h]; exact Real.sin_sq_le_one _
  have hCpos : 0 < C := by dsimp [C]; exact occupationTwoRowConstant_pos hZ
  have hBpos : 0 < B := by dsimp [B]; exact actualOccupationShiftConstant_pos Z
  have hMpos : 0 < M := by dsimp [M]; exact actualOccupationNeighborConstant_pos hZ
  have hαpos : 0 < α := by dsimp [α]; exact actualOccupationDecayConstant_pos hZ
  by_cases hzero : N n = 0
  · rw [hzero]
    exact (Real.exp_pos _).le
  have hNn0 : 0 ≤ N n := by
    dsimp [N, ComplexRow.normOne]
    positivity
  have hNn : 0 < N n := lt_of_le_of_ne hNn0 (Ne.symm hzero)
  have hNpos : ∀ k, k ≤ n → 0 < N k := by
    intro k hk
    have hprefix := applyTransferList_normOne_le_take
      (⟨1, 0⟩ : ComplexRow)
      (actualTransferCoefficients R z hz θ P.vertices)
      (actualTransferCoefficients_admissible R z hz θ P.vertices) k
    have hle : N n ≤ N k := by
      dsimp [N, n]
      rw [P.actualTransferRowAt_edgeCount]
      exact hprefix
    exact lt_of_lt_of_le hNn hle
  have hNmono : ∀ k, k < n → N (k + 1) ≤ N k := by
    intro k hk
    have hk' : k < P.edgeCount := by simpa [n] using hk
    dsimp [N]
    rw [P.actualTransferRowAt_succ z hz θ hk']
    have hK := actualTransferCoefficient_admissible R z hz θ
      (P.vertexAt k) (P.vertexAt (k + 1))
    exact (P.actualTransferCoefficientAt z hz θ k).normOne_applyRow_le
      (P.actualTransferRowAt z hz θ k) hK.q_nonneg hK.b_nonneg
      hK.q_add_b hK.norm_a_le_one hK.norm_c_le_one hK.norm_phase
  have hX0 : X 0 = N 0 := by
    simp [X, N, ComplexRow.normOne]
  have hXnonneg : ∀ k, k ≤ n → 0 ≤ X k := by
    intro k hk
    exact norm_nonneg _
  have hXle : ∀ k, k ≤ n → X k ≤ N k := by
    intro k hk
    dsimp [X, N, ComplexRow.normOne]
    exact le_add_of_nonneg_right (norm_nonneg _)
  have hb0 : ∀ k, k < n → 0 ≤ b k := by
    intro k hk
    dsimp [b, DownwardPath.actualOccupationAt]
    exact (rootedOccupationProbabilityAt_pos R z hz (P.vertexAt k)).le
  have hb1 : ∀ k, k < n → b k ≤ 1 := by
    intro k hk
    dsimp [b, DownwardPath.actualOccupationAt]
    exact rootedOccupationProbabilityAt_le_one R z hz (P.vertexAt k)
  have hΛ0 : ∀ k, k < n → 0 ≤ Λ k := by
    intro k hk
    dsimp [Λ, DownwardPath.actualSideLogBarrierAt]
    exact sideLogBarrier_nonneg R z hz (P.vertexAt k) (P.vertexAt (k + 1))
  have hsecond : ∀ k, k < n →
      N (k + 1) - X (k + 1) ≤ b k * X k := by
    intro k hk
    have hk' : k < P.edgeCount := by simpa [n] using hk
    dsimp [N, X]
    rw [P.actualTransferRowAt_succ z hz θ hk']
    have hK := actualTransferCoefficient_admissible R z hz θ
      (P.vertexAt k) (P.vertexAt (k + 1))
    have hs := TransferCoefficient.norm_applyRow_snd_le
      (P.actualTransferCoefficientAt z hz θ k)
      (P.actualTransferRowAt z hz θ k) hK
    change
      ‖((P.actualTransferCoefficientAt z hz θ k).applyRow
          (P.actualTransferRowAt z hz θ k)).fst‖ +
        ‖((P.actualTransferCoefficientAt z hz θ k).applyRow
          (P.actualTransferRowAt z hz θ k)).snd‖ -
        ‖((P.actualTransferCoefficientAt z hz θ k).applyRow
          (P.actualTransferRowAt z hz θ k)).fst‖ ≤
        (P.actualTransferCoefficientAt z hz θ k).b *
          ‖(P.actualTransferRowAt z hz θ k).fst‖
    linarith
  have hshift : ∀ k, k + 1 < n → b (k + 1) ≤ B * (b k + Λ k) := by
    intro k hk
    have hk' : k < P.edgeCount := by simpa [n] using (show k < n by omega)
    have hc := P.isChild_vertexAt hk'
    dsimp [b, B, Λ, DownwardPath.actualOccupationAt,
      DownwardPath.actualSideLogBarrierAt]
    exact child_occupation_le_parent_add_sideBarrier hG R Z z hz hzZ hc
  have hpay : ∀ k, k + 1 < n →
      X k * b k * h ≤ C *
        ((N k - N (k + 1)) + (N (k + 1) - N (k + 2))) := by
    intro k hk
    have hk0 : k < P.edgeCount := by simpa [n] using (show k < n by omega)
    have hk1 : k + 1 < P.edgeCount := by simpa [n] using hk
    have hp := actualTransferCoefficient_two_row_occupation_payment
      hG R Z z θ hz hzZ hθ
      (P.isChild_vertexAt hk0) (P.isChild_vertexAt hk1)
      (P.actualTransferRowAt z hz θ k)
    rw [show N (k + 1) =
        ((P.actualTransferCoefficientAt z hz θ k).applyRow
          (P.actualTransferRowAt z hz θ k)).normOne by
      dsimp [N]
      rw [P.actualTransferRowAt_succ z hz θ hk0]]
    rw [show N (k + 2) =
        ((P.actualTransferCoefficientAt z hz θ (k + 1)).applyRow
          ((P.actualTransferCoefficientAt z hz θ k).applyRow
            (P.actualTransferRowAt z hz θ k))).normOne by
      dsimp [N]
      rw [P.actualTransferRowAt_succ z hz θ hk1,
        P.actualTransferRowAt_succ z hz θ hk0]]
    dsimp [X, b, h, C, DownwardPath.actualOccupationAt,
      DownwardPath.actualTransferCoefficientAt] at hp ⊢
    exact hp
  have hsum := occupation_sum_relativeDrop n h C B N X b Λ hn hh0 hh1
    hCpos.le hBpos.le hNpos hNmono hX0 hXnonneg hXle hb0 hb1 hΛ0
    hsecond hshift hpay
  have hOccSum : (∑ k ∈ Finset.range n, b k) = P.occupationMass R z := by
    dsimp [n, b]
    exact P.sum_range_actualOccupationAt z
  have hBarSum : (∑ k ∈ Finset.range n, Λ k) =
      P.actualSideLogBarrierSum z := by
    dsimp [n, Λ]
    exact P.sum_range_actualSideLogBarrierAt z
  rw [hOccSum, hBarSum] at hsum
  have htel := relativeDrop_exponential_telescope N n hNpos hNmono
  have hN0 : N 0 = 1 := by simp [N, ComplexRow.normOne]
  rw [hN0, mul_one] at htel
  let D := ∑ k ∈ Finset.range n, relativeDrop N k
  let O := P.occupationMass R z
  let L := P.actualSideLogBarrierSum z
  have hscalar : -D ≤ α - α * h * O + h * L / 3 := by
    have hden : 0 < 3 * M := mul_pos (by norm_num) hMpos
    have hαeq : α = 1 / (3 * M) := by rfl
    have heq : α - α * h * O + h * L / 3 =
        (1 - h * O + M * h * L) / (3 * M) := by
      rw [hαeq]
      field_simp [hMpos.ne']
    rw [heq]
    apply (le_div_iff₀ hden).2
    dsimp [D, O, L]
    dsimp [M, actualOccupationNeighborConstant] at hsum ⊢
    nlinarith
  calc
    N n ≤ Real.exp (-D) := by simpa [D] using htel
    _ ≤ Real.exp (α - α * h * O + h * L / 3) :=
      Real.exp_le_exp.mpr hscalar

/-- Positivity of the genuine side-barrier decay rate. -/
theorem actualSideBarrierRateConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < actualSideBarrierRateConstant Z := by
  unfold actualSideBarrierRateConstant
  exact barrierRateConstant_pos hZ (sideRootGapConstant_div_one_add_pos hZ)

/-- Final A.8 exponent rate, obtained by interpolating occupation decay and
side-barrier decay. -/
noncomputable def actualA43RateConstant (Z : ℝ) : ℝ :=
  let α := actualOccupationDecayConstant Z
  let γ := actualSideBarrierRateConstant Z
  (γ / (α + γ + (1 / 3 : ℝ))) * α

/-- Final A.8 prefactor.  Both constants depend only on the activity ceiling. -/
noncomputable def actualA43PrefactorConstant (Z : ℝ) : ℝ :=
  Real.exp (actualA43RateConstant Z)

/-- The final A.8 rate is strictly positive. -/
theorem actualA43RateConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < actualA43RateConstant Z := by
  have hα := actualOccupationDecayConstant_pos hZ
  have hγ := actualSideBarrierRateConstant_pos hZ
  unfold actualA43RateConstant
  exact mul_pos (div_pos hγ (by positivity)) hα

/-- The final A.8 prefactor is strictly positive. -/
theorem actualA43PrefactorConstant_pos (Z : ℝ) :
    0 < actualA43PrefactorConstant Z := by
  unfold actualA43PrefactorConstant
  exact Real.exp_pos _

/-- Genuine row contraction (A.43) for every concrete decorated downward path. -/
theorem DownwardPath.actualTransferRow_normOne_le_A43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (P : DownwardPath R) :
    (P.actualTransferRow z hz θ).normOne ≤
      actualA43PrefactorConstant Z *
        Real.exp (-actualA43RateConstant Z * Real.sin (θ / 2) ^ 2 *
          (P.occupationMass R z + P.actualSideLogBarrierSum z)) := by
  let N := (P.actualTransferRow z hz θ).normOne
  let h := Real.sin (θ / 2) ^ 2
  let O := P.occupationMass R z
  let L := P.actualSideLogBarrierSum z
  let α := actualOccupationDecayConstant Z
  let γ := actualSideBarrierRateConstant Z
  let w := γ / (α + γ + (1 / 3 : ℝ))
  let c := w * α
  change N ≤ Real.exp c * Real.exp (-c * h * (O + L))
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hα : 0 < α := by dsimp [α]; exact actualOccupationDecayConstant_pos hZ
  have hγ : 0 < γ := by dsimp [γ]; exact actualSideBarrierRateConstant_pos hZ
  have hden : 0 < α + γ + (1 / 3 : ℝ) := by positivity
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    apply (div_le_one hden).2
    nlinarith [hα]
  by_cases hzero : N = 0
  · rw [hzero]
    positivity
  have hN0 : 0 ≤ N := by
    dsimp [N, ComplexRow.normOne]
    positivity
  have hN : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hzero)
  have hOcc : N ≤ Real.exp (α - α * h * O + h * L / 3) := by
    dsimp [N, α, h, O, L]
    exact P.actualTransferRow_normOne_le_exp_occupationSlack
      hG R Z z θ hz hzZ hθ
  have hBar : N ≤ Real.exp (-γ * h * L) := by
    dsimp [N, γ, h, L]
    exact P.actualTransferRow_normOne_le_exp_neg_sideBarrier
      hG R Z z θ hz hzZ hθ
  have hlogOcc : Real.log N ≤ α - α * h * O + h * L / 3 := by
    rw [← Real.exp_le_exp]
    rw [Real.exp_log hN]
    exact hOcc
  have hlogBar : Real.log N ≤ -γ * h * L := by
    rw [← Real.exp_le_exp]
    rw [Real.exp_log hN]
    exact hBar
  have hlog : Real.log N ≤ c - c * h * (O + L) := by
    calc
      Real.log N = w * Real.log N + (1 - w) * Real.log N := by ring
      _ ≤ w * (α - α * h * O + h * L / 3) +
          (1 - w) * (-γ * h * L) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hlogOcc hw0)
          (mul_le_mul_of_nonneg_left hlogBar (sub_nonneg.mpr hw1))
      _ = c - c * h * (O + L) := by
        dsimp [w, c]
        field_simp [hden.ne']
        ring
  calc
    N = Real.exp (Real.log N) := (Real.exp_log hN).symm
    _ ≤ Real.exp (c - c * h * (O + L)) := Real.exp_le_exp.mpr hlog
    _ = Real.exp c * Real.exp (-c * h * (O + L)) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Principal arbitrary-bottom version of genuine Lemma A.8.  The bottom row
may be any actual complex row with both coordinate moduli at most one. -/
theorem DownwardPath.norm_actualTransferRow_pair_le_A43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (P : DownwardPath R)
    (fL : ComplexRow) (hf0 : ‖fL.fst‖ ≤ 1) (hf1 : ‖fL.snd‖ ≤ 1) :
    ‖(P.actualTransferRow z hz θ).pair fL‖ ≤
      actualA43PrefactorConstant Z *
        Real.exp (-actualA43RateConstant Z * Real.sin (θ / 2) ^ 2 *
          (P.occupationMass R z + P.actualSideLogBarrierSum z)) := by
  exact (ComplexRow.norm_pair_le_normOne
    (P.actualTransferRow z hz θ) fL hf0 hf1).trans
      (P.actualTransferRow_normOne_le_A43 hG R Z z θ hz hzZ hθ)

/-- Genuine Lemma A.8 (A.43), specialized to the actual complex terminal
vector built from the terminal rooted hard-core laws. -/
theorem DownwardPath.norm_actualTransferAmplitude_le_A43
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (P : DownwardPath R) :
    ‖P.actualTransferAmplitude z hz θ‖ ≤
      actualA43PrefactorConstant Z *
        Real.exp (-actualA43RateConstant Z * Real.sin (θ / 2) ^ 2 *
          (P.occupationMass R z + P.actualSideLogBarrierSum z)) := by
  have hf := P.actualBottomVector_norms z hz θ
  exact P.norm_actualTransferRow_pair_le_A43 hG R Z z θ hz hzZ hθ
    (P.actualBottomVector z hz θ) hf.1 hf.2

end
end AppendixA
end Forest
end Erdos993
