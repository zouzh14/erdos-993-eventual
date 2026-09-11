import Erdos993.Forest.RecursiveDecompositionScale
import Erdos993.Forest.BoundedScaleCompactness

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section
open scoped BigOperators
open ActualRootedVariance
open ActualRootedVariance.ComponentRooting

universe u
variable {ι : Type u}

lemma boundedScaleH_eq_rpow_of_one_le {α x : ℝ}
    (hα : α ≤ 1) (hx : 1 ≤ x) : boundedScaleH α x = x ^ α := by
  unfold boundedScaleH
  rw [min_eq_right]
  simpa using Real.rpow_le_rpow_of_exponent_le hx hα

lemma boundedScaleH_chord {α x y : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hx0 : 0 ≤ x) (hy1 : 1 ≤ y) (hxy : x ≤ y) :
    (x / y) * boundedScaleH α y ≤ boundedScaleH α x := by
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
  let q := x / y
  have hq0 : 0 ≤ q := div_nonneg hx0 hy0.le
  have hq1 : q ≤ 1 := (div_le_one hy0).2 hxy
  have hqpow : q ≤ q ^ α := by
    by_cases hqz : q = 0
    · rw [hqz]
      exact Real.rpow_nonneg (by norm_num) α
    · have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      simpa using Real.rpow_le_rpow_of_exponent_ge hqp hq1 hα1.le
  have hyH : boundedScaleH α y = y ^ α :=
    boundedScaleH_eq_rpow_of_one_le hα1.le hy1
  have hqy : x = q * y := by
    dsimp [q]
    field_simp [hy0.ne']
  rw [hyH]
  apply le_min
  · have hypow : y ^ α ≤ y := by
      simpa using Real.rpow_le_rpow_of_exponent_le hy1 hα1.le
    have := mul_le_mul_of_nonneg_left hypow hq0
    change q * y ^ α ≤ x
    rw [hqy]
    exact this
  · have hm := mul_le_mul_of_nonneg_right hqpow (Real.rpow_nonneg hy0.le α)
    change q * y ^ α ≤ x ^ α
    rw [hqy, Real.mul_rpow hq0 hy0.le]
    exact hm

lemma boundedScaleH_pos_of_pos {α x : ℝ} (hα : 0 < α) (hx : 0 < x) :
    0 < boundedScaleH α x := by
  unfold boundedScaleH
  exact lt_min hx (Real.rpow_pos_of_pos hx α)

/-- Scalar form of Appendix A, (A.70).  Its hypotheses are precisely (A.68),
(A.69), and the two numerical choices made before the recursive construction. -/
theorem boundedScaleH_gain_A70
    [Fintype ι] {α ζ σ a0 X : ℝ} {x : ι → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hζ : 0 < ζ) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hσX : 1 ≤ σ * X)
    (hx0 : ∀ i, 0 ≤ x i)
    (hsum : a0 * X ≤ ∑ i, x i)
    (hdichotomy :
      (∀ i, x i ≤ σ * X) ∨
        ∃ i j, i ≠ j ∧ σ * X < x i ∧ σ * X < x j)
    (htwo : 1 + ζ < 2 * σ ^ α)
    (hmass : 1 + ζ < (a0 / σ) * σ ^ α) :
    (1 + ζ) * boundedScaleH α X < ∑ i, boundedScaleH α (x i) := by
  classical
  have hX1 : 1 ≤ X := by
    have hσXpos : 0 < σ * X := lt_of_lt_of_le zero_lt_one hσX
    have hXpos : 0 < X := pos_of_mul_pos_right hσXpos hσ0.le
    by_contra hn
    have hXlt : X < 1 := lt_of_not_ge hn
    have hσXlt : σ * X < X := mul_lt_of_lt_one_left hXpos hσ1
    linarith
  have hHX : boundedScaleH α X = X ^ α :=
    boundedScaleH_eq_rpow_of_one_le hα1.le hX1
  rw [hHX]
  rcases hdichotomy with hall | htwoRoots
  · have hchord : ∀ i,
        (x i / (σ * X)) * boundedScaleH α (σ * X) ≤
          boundedScaleH α (x i) := fun i =>
      boundedScaleH_chord hα0 hα1 (hx0 i) hσX (hall i)
    have hsumchord0 := Finset.sum_le_sum
      (fun i (_ : i ∈ Finset.univ) => hchord i)
    have hsumchord : ((∑ i, x i) / (σ * X)) *
        boundedScaleH α (σ * X) ≤ ∑ i, boundedScaleH α (x i) := by
      rw [Finset.sum_div, Finset.sum_mul]
      exact hsumchord0
    have hypos : 0 < σ * X := lt_of_lt_of_le zero_lt_one hσX
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hratio : a0 / σ ≤ (∑ i, x i) / (σ * X) := by
      apply (div_le_div_iff₀ hσ0 hypos).2
      have hm := mul_le_mul_of_nonneg_left hsum hσ0.le
      nlinarith
    have hHy : 0 < boundedScaleH α (σ * X) :=
      boundedScaleH_pos_of_pos hα0 hypos
    have hprod := mul_le_mul_of_nonneg_right hratio hHy.le
    have hyH : boundedScaleH α (σ * X) = (σ * X) ^ α :=
      boundedScaleH_eq_rpow_of_one_le hα1.le hσX
    rw [hyH, Real.mul_rpow hσ0.le hXpos.le] at hprod hsumchord
    have hmass' := mul_lt_mul_of_pos_right hmass (Real.rpow_pos_of_pos hXpos α)
    nlinarith
  · obtain ⟨i, j, hij, hi, hj⟩ := htwoRoots
    have hσX0 : 0 ≤ σ * X := hσX.trans' (by norm_num)
    have hiH : (σ * X) ^ α < boundedScaleH α (x i) := by
      rw [boundedScaleH_eq_rpow_of_one_le hα1.le
        (hσX.trans hi.le)]
      exact Real.rpow_lt_rpow hσX0 hi hα0
    have hjH : (σ * X) ^ α < boundedScaleH α (x j) := by
      rw [boundedScaleH_eq_rpow_of_one_le hα1.le
        (hσX.trans hj.le)]
      exact Real.rpow_lt_rpow hσX0 hj hα0
    have hle := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i, j} : Finset ι) ⊆ Finset.univ by simp)
      (fun k hk hkuniv => (le_min (hx0 k) (Real.rpow_nonneg (hx0 k) α)))
    have hpows : (σ * X) ^ α = σ ^ α * X ^ α :=
      Real.mul_rpow hσ0.le (hX1.trans' (by norm_num))
    have hsumtwo : boundedScaleH α (x i) + boundedScaleH α (x j) ≤
        ∑ k, boundedScaleH α (x k) := by
      simpa [Finset.sum_pair hij] using hle
    rw [hpows] at hiH hjH
    have htwo' := mul_lt_mul_of_pos_right htwo (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one hX1) α)
    nlinarith

/-- Fixed global heavy-component cutoff used by the A.10 recursion. -/
noncomputable def recursiveSigma (Z : ℝ) : ℝ :=
  1 / (32 * recursiveScaleConstant Z)

lemma recursiveScaleConstant_one_le {Z : ℝ} (hZ : 0 < Z) :
    1 ≤ recursiveScaleConstant Z := by
  have hM : 1 ≤ maximalModulusPathVarianceConstant Z := by
    unfold maximalModulusPathVarianceConstant
    exact le_max_left _ _
  have hD := recursiveDeletionScaleConstant_one_le hZ
  unfold recursiveScaleConstant
  nlinarith [mul_nonneg (sub_nonneg.mpr hM) (sub_nonneg.mpr hD)]

lemma recursiveSigma_pos {Z : ℝ} (hZ : 0 < Z) : 0 < recursiveSigma Z := by
  unfold recursiveSigma
  exact one_div_pos.mpr (mul_pos (by norm_num) (recursiveScaleConstant_pos hZ))

/-- Explicit exponent used in A.10.  It makes `σ ^ α = 3/4`. -/
noncomputable def recursiveAlpha (Z : ℝ) : ℝ :=
  Real.log (4 / 3 : ℝ) / (-Real.log (recursiveSigma Z))

/-- Explicit positive gain margin. -/
noncomputable def recursiveZeta (_Z : ℝ) : ℝ := 1 / 4

lemma recursiveSigma_lt_one {Z : ℝ} (hZ : 0 < Z) : recursiveSigma Z < 1 := by
  have hC := recursiveScaleConstant_one_le hZ
  unfold recursiveSigma
  apply (div_lt_one (mul_pos (by norm_num) (recursiveScaleConstant_pos hZ))).2
  nlinarith

lemma recursiveSigma_lt_three_quarters {Z : ℝ} (hZ : 0 < Z) :
    recursiveSigma Z < (3 / 4 : ℝ) := by
  have hC := recursiveScaleConstant_one_le hZ
  have hCp := recursiveScaleConstant_pos hZ
  unfold recursiveSigma
  apply (div_lt_iff₀ (mul_pos (by norm_num) hCp)).2
  nlinarith

lemma recursiveAlpha_pos {Z : ℝ} (hZ : 0 < Z) : 0 < recursiveAlpha Z := by
  unfold recursiveAlpha
  exact div_pos (Real.log_pos (by norm_num))
    (neg_pos.mpr (Real.log_neg (recursiveSigma_pos hZ)
      (recursiveSigma_lt_one hZ)))

lemma recursiveAlpha_lt_one {Z : ℝ} (hZ : 0 < Z) : recursiveAlpha Z < 1 := by
  have hs0 := recursiveSigma_pos hZ
  have hs34 := recursiveSigma_lt_three_quarters hZ
  have hloglt := Real.strictMonoOn_log (Set.mem_Ioi.mpr hs0)
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 3 / 4)) hs34
  have hinv := Real.log_inv (4 / 3 : ℝ)
  norm_num at hinv
  have hden : 0 < -Real.log (recursiveSigma Z) := by
    exact neg_pos.mpr (Real.log_neg hs0 (recursiveSigma_lt_one hZ))
  unfold recursiveAlpha
  apply (div_lt_one hden).2
  nlinarith

lemma recursiveSigma_rpow_recursiveAlpha {Z : ℝ} (hZ : 0 < Z) :
    recursiveSigma Z ^ recursiveAlpha Z = (3 / 4 : ℝ) := by
  have hs0 := recursiveSigma_pos hZ
  have hlogs : Real.log (recursiveSigma Z) ≠ 0 :=
    ne_of_lt (Real.log_neg hs0 (recursiveSigma_lt_one hZ))
  rw [Real.rpow_def_of_pos hs0]
  unfold recursiveAlpha
  have he : Real.log (recursiveSigma Z) *
      (Real.log (4 / 3 : ℝ) / -Real.log (recursiveSigma Z)) =
      -Real.log (4 / 3 : ℝ) := by
    field_simp [hlogs]
  rw [he, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
  norm_num

lemma recursiveA0_div_recursiveSigma {Z : ℝ} (hZ : 0 < Z) :
    recursiveA0 Z / recursiveSigma Z = 16 := by
  have hC := recursiveScaleConstant_pos hZ
  unfold recursiveA0 recursiveSigma
  field_simp [hC.ne']
  ring

lemma recursiveZeta_pos (Z : ℝ) : 0 < recursiveZeta Z := by
  unfold recursiveZeta
  norm_num

lemma recursive_two_gain {Z : ℝ} (hZ : 0 < Z) :
    1 + recursiveZeta Z <
      2 * recursiveSigma Z ^ recursiveAlpha Z := by
  rw [recursiveSigma_rpow_recursiveAlpha hZ]
  unfold recursiveZeta
  norm_num

lemma recursive_mass_gain {Z : ℝ} (hZ : 0 < Z) :
    1 + recursiveZeta Z <
      (recursiveA0 Z / recursiveSigma Z) *
        recursiveSigma Z ^ recursiveAlpha Z := by
  rw [recursiveA0_div_recursiveSigma hZ,
    recursiveSigma_rpow_recursiveAlpha hZ]
  unfold recursiveZeta
  norm_num

/-- Concrete family form of Appendix A, (A.70), obtained from the actual A.10
continuation, (A.67)--(A.69), and the explicit `α_Z, ζ_Z`. -/
theorem RecursiveDecomposition.boundedScaleH_family_gain_A70
    {V : Type u} [Fintype V] {G : SimpleGraph V} (hG : G.IsAcyclic)
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X X0 : ℝ} {u : V}
    (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (hcut : highScaleThreshold Z ≤ X0)
    (hX0σ : X0 ≤ recursiveSigma Z * X)
    (hroot : descendantScaleAt R z hz θ u = X)
    (hσX : 1 ≤ recursiveSigma Z * X)
    (D : RecursiveDecomposition R Z z hz θ X (recursiveSigma Z) X0 u)
    (hK : D.K < X / (2 * recursiveScaleConstant Z))
    (hnotNarrow : ¬
      (IsHighScaleNarrow R Z z hz θ D.toTrace.terminalRoot ∧
        recursiveSigma Z * X <
          descendantScaleAt R z hz θ D.toTrace.terminalRoot)) :
    (1 + recursiveZeta Z) * boundedScaleH (recursiveAlpha Z) X <
      ∑ v ∈ D.family,
        boundedScaleH (recursiveAlpha Z) (descendantScaleAt R z hz θ v) := by
  classical
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have h67 := D.scale_le_K_add_familyScale_A67 hG hzZ hθ hcut
  rw [hroot] at h67
  have h69 : recursiveA0 Z * X ≤ D.familyScale :=
    child_scale_sum_A69 hZ h67 hK
  have hd0 := D.family_scale_dichotomy_or_large_narrow_A68 hG hX0σ
  have hd : ScaleFamilyDichotomy R z hz θ (recursiveSigma Z) X D.family :=
    hd0.resolve_right hnotNarrow
  let x : ↥D.family → ℝ := fun i => descendantScaleAt R z hz θ i.1
  have hx0 : ∀ i, 0 ≤ x i := fun i =>
    mul_nonneg (sq_nonneg θ) (R.subtreeLawAt z hz i.1).variance_nonneg
  have hsum : recursiveA0 Z * X ≤ ∑ i, x i := by
    rw [← Finset.sum_subtype D.family (fun v => Iff.rfl)
      (fun v => descendantScaleAt R z hz θ v)]
    simpa [RecursiveDecomposition.familyScale, x] using h69
  have hd' :
      (∀ i, x i ≤ recursiveSigma Z * X) ∨
        ∃ i j, i ≠ j ∧ recursiveSigma Z * X < x i ∧
          recursiveSigma Z * X < x j := by
    rcases hd with hall | htwo
    · exact Or.inl (fun i => hall i.1 i.2)
    · obtain ⟨v, hv, w, hw, hvw, hvh, hwh⟩ := htwo
      exact Or.inr ⟨⟨v, hv⟩, ⟨w, hw⟩,
        (fun h => hvw (congrArg Subtype.val h)), hvh, hwh⟩
  have hgain := boundedScaleH_gain_A70
    (ι := ↥D.family) (x := x)
    (recursiveAlpha_pos hZ) (recursiveAlpha_lt_one hZ)
    (recursiveZeta_pos Z) (recursiveSigma_pos hZ)
    (recursiveSigma_lt_one hZ) hσX hx0 hsum hd'
    (recursive_two_gain hZ) (recursive_mass_gain hZ)
  rw [← Finset.sum_subtype D.family (fun v => Iff.rfl)
    (fun v => boundedScaleH (recursiveAlpha Z)
      (descendantScaleAt R z hz θ v))] at hgain
  simpa [x] using hgain

end
end AppendixA
end Forest
end Erdos993
