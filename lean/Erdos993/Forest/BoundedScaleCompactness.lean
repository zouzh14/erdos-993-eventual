import Erdos993.Forest.CharacteristicTransfer
import Erdos993.Forest.IndependentComponentFourier

/-!
# Bounded-scale compactness for Appendix A

This module proves the genuine finite-forest bounded-scale Fourier gap (Lemma
A.6) and its bounded-scale `H_α` consequence (A.39).  The proof is quantitative:
it combines the component and child factorisations, A.5, A.29/A.30, the
depth-free transfer A.33, and well-founded strict descent through child
subtrees.
-/

open scoped BigOperators

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open ActualRootedVariance
open ActualRootedVariance.ComponentRooting

universe u

noncomputable local instance finiteSubtypeBoundedScale
    {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x : α // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- On the interval `[1/2,1]`, logarithmic Fourier loss is at most twice
modulus defect.  This is the elementary reverse companion to
`one_sub_characteristicModulus_le_logarithmicLoss`. -/
theorem FiniteLatticeLaw.logarithmicLoss_le_two_mul_one_sub_characteristicModulus
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (θ : ℝ)
    (hhalf : (1 / 2 : ℝ) ≤ L.characteristicModulus θ) :
    L.logarithmicLoss θ ≤
      ((2 * (1 - L.characteristicModulus θ) : ℝ) : EReal) := by
  have hxpos : 0 < L.characteristicModulus θ :=
    lt_of_lt_of_le (by norm_num) hhalf
  rw [FiniteLatticeLaw.logarithmicLoss,
    ENNReal.log_ofReal_of_pos hxpos]
  norm_cast
  have hlog : -Real.log (L.characteristicModulus θ) ≤
      (L.characteristicModulus θ)⁻¹ - 1 := by
    linarith [Real.one_sub_inv_le_log_of_pos hxpos]
  have hinv : (L.characteristicModulus θ)⁻¹ ≤ (2 : ℝ) := by
    have hdiv : (1 : ℝ) / L.characteristicModulus θ ≤ 2 := by
      apply (div_le_iff₀ hxpos).2
      nlinarith [hhalf]
    simpa only [one_div] using hdiv
  have hgap0 : 0 ≤ 1 - L.characteristicModulus θ :=
    sub_nonneg.mpr (L.characteristicModulus_le_one θ)
  calc
    -Real.log (L.characteristicModulus θ) ≤
        (L.characteristicModulus θ)⁻¹ - 1 := hlog
    _ = (1 - L.characteristicModulus θ) *
        (L.characteristicModulus θ)⁻¹ := by
      field_simp [hxpos.ne']
    _ ≤ (1 - L.characteristicModulus θ) * 2 :=
      mul_le_mul_of_nonneg_left hinv hgap0
    _ = 2 * (1 - L.characteristicModulus θ) := by ring

/-- Child descent is well founded because every child subtree has strictly
smaller finite order. -/
theorem childRelation_wellFounded
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (R : ComponentRooting G) :
    WellFounded (fun v u => R.IsChild (G := G) u v) := by
  refine (measure (fun u => R.subtreeOrder (G := G) u)).wf.mono ?_
  intro v u huv
  exact R.subtreeOrder_child_lt (G := G) huv

/-- No predicate on vertices of a finite rooted forest can hold at one vertex
and supply a further child satisfying it at every such vertex. -/
theorem not_exists_of_child_closed
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (R : ComponentRooting G) (P : V → Prop)
    (hstep : ∀ u, P u → ∃ v, R.IsChild (G := G) u v ∧ P v) :
    ¬ ∃ u, P u := by
  rintro ⟨u, hu⟩
  induction u using (childRelation_wellFounded R).induction with
  | h u ih =>
      obtain ⟨v, huv, hv⟩ := hstep u hu
      exact ih v huv hv

/-- If a subtree has scaled variance above `ρ` while `θ² ≤ ρ/4`, then its
root-vacant child forest has scaled variance at least `ρ/(2 A_Z)`.  This is
the quantitative form of (A.37), obtained from A.29 and the root Bernoulli
variance bound. -/
theorem rootVacant_scaledVariance_gt
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ ρ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hρ : 0 < ρ) (hθsmall : θ ^ 2 ≤ ρ / 4)
    (u : V)
    (hu : ρ < subtreeVarianceAt R z hz u * θ ^ 2) :
    ρ / (2 * rootVarianceUpperConstant Z) <
      rootVacantVarianceAt R z hz u * θ ^ 2 := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hA : 0 < rootVarianceUpperConstant Z := by
    unfold rootVarianceUpperConstant
    linarith
  have hupper :=
    subtreeVarianceAt_le_rootVarianceUpperConstant_mul_add
      hG R Z z hz hzZ u
  have hθ0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hb1 : UniformFourthMoment.rootedOccupationProbabilityAt R z u ≤ 1 :=
    UniformFourthMoment.rootedOccupationProbabilityAt_le_one R z hz u
  have hb0 : 0 ≤ UniformFourthMoment.rootedOccupationProbabilityAt R z u :=
    (UniformFourthMoment.rootedOccupationProbabilityAt_pos R z hz u).le
  have hmul := mul_le_mul_of_nonneg_right hupper hθ0
  have hroot : 2 * UniformFourthMoment.rootedOccupationProbabilityAt R z u * θ ^ 2 ≤ ρ / 2 := by
    have hbθ : UniformFourthMoment.rootedOccupationProbabilityAt R z u * θ ^ 2 ≤ ρ / 4 :=
      (mul_le_of_le_one_left hθ0 hb1).trans hθsmall
    linarith
  have hmid : ρ / 2 < rootVarianceUpperConstant Z *
      (rootVacantVarianceAt R z hz u * θ ^ 2) := by
    nlinarith
  apply (div_lt_iff₀ (by positivity : 0 < 2 * rootVarianceUpperConstant Z)).2
  nlinarith

/-- If the root-vacant Fourier loss is smaller than the A.5 loss forced by
(A.37), a child subtree must retain scaled variance above `ρ`. -/
theorem exists_child_scaledVariance_gt_of_rootVacantLoss_lt
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ ρ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (hρ : 0 < ρ)
    (hρsmall : ρ ≤ smallFrequencyScale Z)
    (hθsmall : θ ^ 2 ≤ ρ / 4) (u : V)
    (hu : ρ < subtreeVarianceAt R z hz u * θ ^ 2)
    (hQloss :
      (hardCoreLaw
        (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
        z hz).logarithmicLoss θ <
          ((smallFrequencyConstant Z *
            (ρ / (2 * rootVarianceUpperConstant Z)) : ℝ) : EReal)) :
    ∃ v ∈ R.children (G := G) u,
      ρ < subtreeVarianceAt R z hz v * θ ^ 2 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hQvar := rootVacant_scaledVariance_gt hG R Z z θ ρ hz hzZ hρ
    hθsmall u hu
  have hterm : ∀ v ∈ R.children (G := G) u,
      ((smallFrequencyConstant Z *
        (subtreeVarianceAt R z hz v * θ ^ 2) : ℝ) : EReal) ≤
        (R.subtreeLawAt z hz v).logarithmicLoss θ := by
    intro v hv
    have hvsmall : subtreeVarianceAt R z hz v * θ ^ 2 ≤
        smallFrequencyScale Z := (hnone v hv).trans hρsmall
    simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
      uniformSmallFrequencyCurvature
        (R.Subtree (G := G) v) (R.subtree_isAcyclic (G := G) hG v)
        Z z θ hZ hz hzZ hθ hvsmall
  have hsum := Finset.sum_le_sum hterm
  have hvarsum := R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u
  have hleft :
      ((smallFrequencyConstant Z *
        (rootVacantVarianceAt R z hz u * θ ^ 2) : ℝ) : EReal) =
      ∑ v ∈ R.children (G := G) u,
        ((smallFrequencyConstant Z *
          (subtreeVarianceAt R z hz v * θ ^ 2) : ℝ) : EReal) := by
    have hsumcoe :
        (∑ v ∈ R.children (G := G) u,
          ((smallFrequencyConstant Z *
            (subtreeVarianceAt R z hz v * θ ^ 2) : ℝ) : EReal)) =
        ((∑ v ∈ R.children (G := G) u,
          smallFrequencyConstant Z *
            (subtreeVarianceAt R z hz v * θ ^ 2) : ℝ) : EReal) := by
      induction R.children (G := G) u using Finset.induction_on with
      | empty => simp
      | @insert v s hv ih =>
          rw [Finset.sum_insert hv, Finset.sum_insert hv, ih]
          norm_cast
    rw [hsumcoe]
    norm_cast
    rw [rootVacantVarianceAt, hvarsum, Finset.sum_mul, Finset.mul_sum]
  have hQdecomp :=
    hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
      hG R z θ hz u
  have hc : 0 < smallFrequencyConstant Z := smallFrequencyConstant_pos hZ
  have hlowerReal :
      smallFrequencyConstant Z *
          (ρ / (2 * rootVarianceUpperConstant Z)) <
        smallFrequencyConstant Z *
          (rootVacantVarianceAt R z hz u * θ ^ 2) :=
    mul_lt_mul_of_pos_left hQvar hc
  have hlowerE :
      ((smallFrequencyConstant Z *
        (ρ / (2 * rootVarianceUpperConstant Z)) : ℝ) : EReal) <
      ((smallFrequencyConstant Z *
        (rootVacantVarianceAt R z hz u * θ ^ 2) : ℝ) : EReal) :=
    EReal.coe_lt_coe_iff.mpr hlowerReal
  rw [hQdecomp] at hQloss
  exact (lt_irrefl _ ((hlowerE.trans_le (hleft.trans_le hsum)).trans hQloss))

/-- Conditioning a vertex to be vacant costs at most one further factor
`1+Z` in modulus defect. -/
theorem one_sub_deleteVertexCharacteristicModulus_le_one_add_ceiling_mul
    {V : Type*} [Fintype V] (G : SimpleGraph V) (p : V)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    1 - (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ ≤
      (1 + Z) * (1 - (hardCoreLaw G z hz).characteristicModulus θ) := by
  classical
  let q := independenceEval (deleteVertex G p) z / independenceEval G z
  let MG := (hardCoreLaw G z hz).characteristicModulus θ
  let MD := (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ
  have hmix := hardCoreLaw_characteristicModulus_vertexDeletion_le G p z θ hz
  have hweighted : q * (1 - MD) ≤ 1 - MG := by
    dsimp [q, MG, MD] at *
    linarith
  have hqz : 1 / (1 + z) ≤ q := by
    dsimp [q]
    exact one_div_one_add_le_deleteVertex_ratio G p z hz
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hzden : 0 < 1 + z := by linarith
  have hZden : 0 < 1 + Z := by linarith
  have hmono : 1 / (1 + Z) ≤ 1 / (1 + z) := by
    apply (div_le_div_iff₀ hZden hzden).2
    nlinarith
  have hq : 1 / (1 + Z) ≤ q := hmono.trans hqz
  have hMD : 0 ≤ 1 - MD := sub_nonneg.mpr
    (FiniteLatticeLaw.characteristicModulus_le_one _ _)
  have heta : (1 / (1 + Z)) * (1 - MD) ≤ 1 - MG :=
    (mul_le_mul_of_nonneg_right hq hMD).trans hweighted
  change 1 - MD ≤ (1 + Z) * (1 - MG)
  calc
    1 - MD = (1 + Z) * ((1 / (1 + Z)) * (1 - MD)) := by
      field_simp [hZden.ne']
    _ ≤ (1 + Z) * (1 - MG) :=
      mul_le_mul_of_nonneg_left heta hZden.le

/-- A small logarithmic loss for the whole forest uniformly forces a small
root-vacant modulus defect at every rooted descendant subtree.  Component
roots use exact component additivity; nonroots use A.33. -/
theorem rootVacantCharacteristicModulus_defect_lt_of_globalLoss_lt
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ ε : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hε : 0 < ε)
    (hglobal : (hardCoreLaw G z hz).logarithmicLoss θ < (ε : EReal))
    (u : V) :
    1 - (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).characteristicModulus θ < (1 + Z) ^ 2 * ε := by
  classical
  let μG := hardCoreLaw G z hz
  let μU := R.subtreeLawAt z hz u
  let μQ := hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z hz
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hB : 0 < 1 + Z := by linarith
  have hdefG : 1 - μG.characteristicModulus θ < ε := by
    have hE := (μG.one_sub_characteristicModulus_le_logarithmicLoss θ).trans_lt
      hglobal
    exact EReal.coe_lt_coe_iff.mp hE
  have hQU := one_sub_deleteVertexCharacteristicModulus_le_one_add_ceiling_mul
    (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) Z z θ hz hzZ
  change 1 - μQ.characteristicModulus θ < (1 + Z) ^ 2 * ε
  by_cases hroot : u = R.rootOf (G := G) u
  · have huRoots : u ∈ R.componentRoots (G := G) :=
      (R.mem_componentRoots (G := G) u).2 hroot
    have hnonneg : ∀ v ∈ R.componentRoots (G := G),
        (0 : EReal) ≤ (R.subtreeLawAt z hz v).logarithmicLoss θ := by
      intro v hv
      have hdef0 : 0 ≤ 1 - (R.subtreeLawAt z hz v).characteristicModulus θ :=
        sub_nonneg.mpr ((R.subtreeLawAt z hz v).characteristicModulus_le_one θ)
      exact (EReal.coe_nonneg.mpr hdef0).trans
        ((R.subtreeLawAt z hz v).one_sub_characteristicModulus_le_logarithmicLoss θ)
    have htermle : (R.subtreeLawAt z hz u).logarithmicLoss θ ≤
        ∑ v ∈ R.componentRoots (G := G),
          (R.subtreeLawAt z hz v).logarithmicLoss θ := by
      exact Finset.single_le_sum hnonneg huRoots
    have hdecomp := hardCoreLaw_logarithmicLoss_eq_sum_componentRoots
      G R z θ hz
    have hdecomp' : (hardCoreLaw G z hz).logarithmicLoss θ =
        ∑ v ∈ R.componentRoots (G := G),
          (R.subtreeLawAt z hz v).logarithmicLoss θ := by
      simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using hdecomp
    have hUloss : μU.logarithmicLoss θ < (ε : EReal) := by
      dsimp [μU]
      rw [← hdecomp'] at htermle
      exact htermle.trans_lt hglobal
    have hdefU : 1 - μU.characteristicModulus θ < ε := by
      have hE := (μU.one_sub_characteristicModulus_le_logarithmicLoss θ).trans_lt
        hUloss
      exact EReal.coe_lt_coe_iff.mp hE
    have hQsmall : 1 - μQ.characteristicModulus θ < (1 + Z) * ε := by
      dsimp [μQ, μU] at hQU ⊢
      exact hQU.trans_lt (mul_lt_mul_of_pos_left hdefU hB)
    have hB1 : 1 ≤ 1 + Z := by linarith
    have hBε0 : 0 ≤ (1 + Z) * ε := (mul_pos hB hε).le
    calc
      1 - μQ.characteristicModulus θ < (1 + Z) * ε := hQsmall
      _ ≤ (1 + Z) ^ 2 * ε := by nlinarith
  · obtain ⟨p, hpu⟩ := R.exists_isChild_of_ne_root (G := G) hroot
    have hUG := one_sub_subtreeCharacteristicModulus_le_one_add_ceiling_mul
      hG R Z z θ hz hzZ hpu
    have hUsmall : 1 - μU.characteristicModulus θ < (1 + Z) * ε := by
      dsimp [μU] at hUG ⊢
      exact hUG.trans_lt (mul_lt_mul_of_pos_left hdefG hB)
    have hQsmall : 1 - μQ.characteristicModulus θ <
        (1 + Z) * ((1 + Z) * ε) := by
      dsimp [μQ, μU] at hQU ⊢
      exact hQU.trans_lt (mul_lt_mul_of_pos_left hUsmall hB)
    nlinarith

/-- If the global loss is below the A.5 amount `c_Z a`, at least one connected
component lies above the small-frequency scale.  This is the finite,
pointwise component-selection step behind (A.35). -/
theorem exists_componentRoot_scaledVariance_gt_of_globalLoss_lt
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ a ε : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi)
    (ha : a ≤ (hardCoreLaw G z hz).variance * θ ^ 2)
    (hεcomp : ε ≤ smallFrequencyConstant Z * a)
    (hglobal : (hardCoreLaw G z hz).logarithmicLoss θ < (ε : EReal)) :
    ∃ r ∈ R.componentRoots (G := G),
      smallFrequencyScale Z < subtreeVarianceAt R z hz r * θ ^ 2 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hterm : ∀ r ∈ R.componentRoots (G := G),
      ((smallFrequencyConstant Z *
        (subtreeVarianceAt R z hz r * θ ^ 2) : ℝ) : EReal) ≤
        (R.subtreeLawAt z hz r).logarithmicLoss θ := by
    intro r hr
    simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
      uniformSmallFrequencyCurvature
        (R.Subtree (G := G) r) (R.subtree_isAcyclic (G := G) hG r)
        Z z θ hZ hz hzZ hθ (hnone r hr)
  have hsum := Finset.sum_le_sum hterm
  have hvarsum := R.variance_eq_sum_componentRoot_subtreeVarianceAt z hz
  have hleft :
      ((smallFrequencyConstant Z *
        ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) =
      ∑ r ∈ R.componentRoots (G := G),
        ((smallFrequencyConstant Z *
          (subtreeVarianceAt R z hz r * θ ^ 2) : ℝ) : EReal) := by
    have hsumcoe :
        (∑ r ∈ R.componentRoots (G := G),
          ((smallFrequencyConstant Z *
            (subtreeVarianceAt R z hz r * θ ^ 2) : ℝ) : EReal)) =
        ((∑ r ∈ R.componentRoots (G := G),
          smallFrequencyConstant Z *
            (subtreeVarianceAt R z hz r * θ ^ 2) : ℝ) : EReal) := by
      induction R.componentRoots (G := G) using Finset.induction_on with
      | empty => simp
      | @insert r s hr ih =>
          rw [Finset.sum_insert hr, Finset.sum_insert hr, ih]
          norm_cast
    rw [hsumcoe]
    norm_cast
    rw [hvarsum, Finset.sum_mul, Finset.mul_sum]
  have hdecomp : (hardCoreLaw G z hz).logarithmicLoss θ =
      ∑ r ∈ R.componentRoots (G := G),
        (R.subtreeLawAt z hz r).logarithmicLoss θ := by
    simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
      hardCoreLaw_logarithmicLoss_eq_sum_componentRoots G R z θ hz
  have hca : smallFrequencyConstant Z * a ≤
      smallFrequencyConstant Z * ((hardCoreLaw G z hz).variance * θ ^ 2) :=
    mul_le_mul_of_nonneg_left ha (smallFrequencyConstant_pos hZ).le
  have hchain : (ε : EReal) ≤ (hardCoreLaw G z hz).logarithmicLoss θ := by
    calc
      (ε : EReal) ≤ ((smallFrequencyConstant Z * a : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hεcomp
      _ ≤ ((smallFrequencyConstant Z *
          ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hca
      _ = ∑ r ∈ R.componentRoots (G := G),
          ((smallFrequencyConstant Z *
            (subtreeVarianceAt R z hz r * θ ^ 2) : ℝ) : EReal) := hleft
      _ ≤ ∑ r ∈ R.componentRoots (G := G),
          (R.subtreeLawAt z hz r).logarithmicLoss θ := hsum
      _ = (hardCoreLaw G z hz).logarithmicLoss θ := hdecomp.symm
  exact (not_lt_of_ge hchain) hglobal

/-- Fixed positive scaled-variance threshold used in the descendant descent. -/
def boundedScaleDescentThreshold (Z : ℝ) : ℝ :=
  smallFrequencyScale Z / 2

/-- Explicit low-frequency compactness constant. -/
def boundedScaleLowEpsilon (Z a : ℝ) : ℝ :=
  let ρ := boundedScaleDescentThreshold Z
  let B := 1 + Z
  let K := smallFrequencyConstant Z *
    (ρ / (2 * rootVarianceUpperConstant Z))
  min (smallFrequencyConstant Z * a)
    (min (1 / (8 * B ^ 2)) (K / (4 * B ^ 2)))

 theorem boundedScaleLowEpsilon_pos {Z a : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    0 < boundedScaleLowEpsilon Z a := by
  have hs : 0 < smallFrequencyScale Z := smallFrequencyScale_pos hZ
  have hc : 0 < smallFrequencyConstant Z := smallFrequencyConstant_pos hZ
  have hA : 0 < rootVarianceUpperConstant Z := by
    unfold rootVarianceUpperConstant
    linarith
  have hB : 0 < 1 + Z := by linarith
  unfold boundedScaleLowEpsilon boundedScaleDescentThreshold
  dsimp only
  apply lt_min
  · exact mul_pos hc ha
  · apply lt_min
    · positivity
    · positivity

/-- Quantitative bounded-scale compactness in the small-`θ` branch.  The
strict descendant contradiction is packaged by `not_exists_of_child_closed`;
there is no depth parameter. -/
theorem boundedScaleCompactness_smallTheta
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ a : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (ha : 0 < a) (hθ : |θ| ≤ Real.pi)
    (hscale : a ≤ (hardCoreLaw G z hz).variance * θ ^ 2)
    (hθsmall : θ ^ 2 ≤ boundedScaleDescentThreshold Z / 4) :
    ((boundedScaleLowEpsilon Z a : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  classical
  let R : ComponentRooting G := Classical.choice (nonempty_componentRooting G)
  let ρ := boundedScaleDescentThreshold Z
  let ε := boundedScaleLowEpsilon Z a
  let B := 1 + Z
  let K := smallFrequencyConstant Z *
    (ρ / (2 * rootVarianceUpperConstant Z))
  have hs : 0 < smallFrequencyScale Z := smallFrequencyScale_pos hZ
  have hρ : 0 < ρ := by
    dsimp [ρ, boundedScaleDescentThreshold]
    positivity
  have hρsmall : ρ ≤ smallFrequencyScale Z := by
    dsimp [ρ, boundedScaleDescentThreshold]
    linarith
  have hA : 0 < rootVarianceUpperConstant Z := by
    unfold rootVarianceUpperConstant
    linarith
  have hB : 0 < B := by dsimp [B]; linarith
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (smallFrequencyConstant_pos hZ)
      (div_pos hρ (mul_pos (by norm_num) hA))
  have hε : 0 < ε := by
    dsimp [ε]
    exact boundedScaleLowEpsilon_pos hZ ha
  have hεcomp : ε ≤ smallFrequencyConstant Z * a := by
    dsimp [ε, boundedScaleLowEpsilon]
    exact min_le_left _ _
  have hεhalf : ε ≤ 1 / (8 * B ^ 2) := by
    dsimp [ε, boundedScaleLowEpsilon, B]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hεK : ε ≤ K / (4 * B ^ 2) := by
    dsimp [ε, boundedScaleLowEpsilon, K, B, ρ]
    exact (min_le_right _ _).trans (min_le_right _ _)
  by_contra hnot
  have hglobal : (hardCoreLaw G z hz).logarithmicLoss θ < (ε : EReal) := by
    exact lt_of_not_ge hnot
  obtain ⟨r, hrRoots, hrlarge⟩ :=
    exists_componentRoot_scaledVariance_gt_of_globalLoss_lt
      hG R Z z θ a ε hZ hz hzZ hθ hscale hεcomp hglobal
  have hrρ : ρ < subtreeVarianceAt R z hz r * θ ^ 2 :=
    (show ρ < smallFrequencyScale Z by
      dsimp [ρ, boundedScaleDescentThreshold]
      linarith).trans hrlarge
  have hclosed : ∀ u,
      ρ < subtreeVarianceAt R z hz u * θ ^ 2 →
      ∃ v, R.IsChild (G := G) u v ∧
        ρ < subtreeVarianceAt R z hz v * θ ^ 2 := by
    intro u hu
    have hQdef := rootVacantCharacteristicModulus_defect_lt_of_globalLoss_lt
      hG R Z z θ ε hz hzZ hε hglobal u
    let μQ := hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z hz
    have hQdef' : 1 - μQ.characteristicModulus θ < B ^ 2 * ε := by
      simpa only [B, μQ] using hQdef
    have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
    have hsmallDef : B ^ 2 * ε ≤ (1 / 8 : ℝ) := by
      have := mul_le_mul_of_nonneg_left hεhalf hB2.le
      field_simp [hB.ne'] at this ⊢
      nlinarith
    have hhalf : (1 / 2 : ℝ) ≤ μQ.characteristicModulus θ := by
      nlinarith
    have hlogupper :=
      Erdos993.Forest.AppendixA.FiniteLatticeLaw.logarithmicLoss_le_two_mul_one_sub_characteristicModulus
        μQ θ hhalf
    have hrealK : 2 * (1 - μQ.characteristicModulus θ) < K := by
      have hmul : 2 * (1 - μQ.characteristicModulus θ) <
          2 * (B ^ 2 * ε) := by nlinarith
      have heK : 2 * (B ^ 2 * ε) ≤ K / 2 := by
        have := mul_le_mul_of_nonneg_left hεK
          (by positivity : 0 ≤ 2 * B ^ 2)
        field_simp [hB.ne'] at this
        nlinarith
      exact hmul.trans_le (heK.trans (by nlinarith [hK] : K / 2 < K).le)
    have hQloss : μQ.logarithmicLoss θ < (K : EReal) :=
      hlogupper.trans_lt (EReal.coe_lt_coe_iff.mpr hrealK)
    obtain ⟨v, hv, hvρ⟩ :=
      exists_child_scaledVariance_gt_of_rootVacantLoss_lt
        hG R Z z θ ρ hZ hz hzZ hθ hρ hρsmall hθsmall u hu (by
          simpa only [K, μQ] using hQloss)
    exact ⟨v, (R.mem_children (G := G) u v).mp hv, hvρ⟩
  exact not_exists_of_child_closed R
    (fun u => ρ < subtreeVarianceAt R z hz u * θ ^ 2) hclosed ⟨r, hrρ⟩

/-- Explicit A.4 constant for the complementary, non-small `θ` branch. -/
def boundedScaleHighEpsilon (Z a : ℝ) : ℝ :=
  uniformGapConstant Z * min (a / Real.pi ^ 2) 1 *
    (boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2))

 theorem boundedScaleHighEpsilon_pos {Z a : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    0 < boundedScaleHighEpsilon Z a := by
  unfold boundedScaleHighEpsilon
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hm : 0 < min (a / Real.pi ^ 2) 1 :=
    lt_min (div_pos ha hpi) (by norm_num)
  have hρ : 0 < boundedScaleDescentThreshold Z := by
    unfold boundedScaleDescentThreshold
    exact div_pos (smallFrequencyScale_pos hZ) (by norm_num)
  exact mul_pos
    (mul_pos (uniformGapConstant_pos hZ) hm)
    (div_pos hρ (mul_pos (by norm_num) hpi))

/-- The concrete positive constant used by Lemma A.6.  The argument actually
does not need the upper endpoint `b`, but it is retained in the signature to
match the bounded-scale statement and make the permitted dependence explicit. -/
def boundedScaleEpsilon (Z a b : ℝ) : ℝ :=
  min (boundedScaleLowEpsilon Z a) (boundedScaleHighEpsilon Z a)

 theorem boundedScaleEpsilon_pos {Z a b : ℝ} (hZ : 0 < Z) (ha : 0 < a) :
    0 < boundedScaleEpsilon Z a b := by
  unfold boundedScaleEpsilon
  exact lt_min (boundedScaleLowEpsilon_pos hZ ha)
    (boundedScaleHighEpsilon_pos hZ ha)

/-- The A.4 lower bound is uniformly positive once `θ²` is outside the small
window and the scaled variance is at least `a`. -/
theorem boundedScaleCompactness_largeTheta
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ a : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (ha : 0 < a) (hθ : |θ| ≤ Real.pi)
    (hscale : a ≤ (hardCoreLaw G z hz).variance * θ ^ 2)
    (hθlarge : boundedScaleDescentThreshold Z / 4 < θ ^ 2) :
    ((boundedScaleHighEpsilon Z a : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  let μ := hardCoreLaw G z hz
  have hV0 : 0 ≤ μ.variance := μ.variance_nonneg
  have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hθpi : θ ^ 2 ≤ Real.pi ^ 2 := by
    have habs : |θ| ^ 2 ≤ Real.pi ^ 2 :=
      (sq_le_sq₀ (abs_nonneg θ) Real.pi_pos.le).2 hθ
    simpa only [sq_abs] using habs
  have hVa : a / Real.pi ^ 2 ≤ μ.variance := by
    apply (div_le_iff₀ hpi).2
    calc
      a ≤ μ.variance * θ ^ 2 := hscale
      _ ≤ μ.variance * Real.pi ^ 2 :=
        mul_le_mul_of_nonneg_left hθpi hV0
  have hmin : min (a / Real.pi ^ 2) 1 ≤ min μ.variance 1 :=
    min_le_min hVa le_rfl
  have hsin := sq_div_pi_sq_le_sin_half_sq hθ
  have hfreq : boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2) ≤
      θ ^ 2 / Real.pi ^ 2 := by
    calc
      boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2) =
          (boundedScaleDescentThreshold Z / 4) / Real.pi ^ 2 := by ring
      _ ≤ θ ^ 2 / Real.pi ^ 2 :=
        (div_le_div_iff_of_pos_right hpi).2 hθlarge.le
  have hsine : boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2) ≤
      Real.sin (θ / 2) ^ 2 := hfreq.trans hsin
  have hk0 : 0 ≤ uniformGapConstant Z := uniformGapConstant_nonneg hZ.le
  have hm0 : 0 ≤ min (a / Real.pi ^ 2) 1 :=
    (lt_min (div_pos ha hpi) (by norm_num)).le
  have hsin0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
  have hthreshold0 : 0 ≤ boundedScaleDescentThreshold Z /
      (4 * Real.pi ^ 2) := by
    have hρpos : 0 < boundedScaleDescentThreshold Z := by
      unfold boundedScaleDescentThreshold
      exact div_pos (smallFrequencyScale_pos hZ) (by norm_num)
    exact (div_pos hρpos (mul_pos (by norm_num) hpi)).le
  have hreal : boundedScaleHighEpsilon Z a ≤
      uniformGapConstant Z * min μ.variance 1 * Real.sin (θ / 2) ^ 2 := by
    unfold boundedScaleHighEpsilon
    have hmin0 : 0 ≤ min μ.variance 1 := le_min hV0 (by norm_num)
    calc
      uniformGapConstant Z * min (a / Real.pi ^ 2) 1 *
          (boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2)) ≤
        uniformGapConstant Z * min μ.variance 1 *
          (boundedScaleDescentThreshold Z / (4 * Real.pi ^ 2)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hmin hk0) hthreshold0
      _ ≤ uniformGapConstant Z * min μ.variance 1 *
          Real.sin (θ / 2) ^ 2 :=
            mul_le_mul_of_nonneg_left hsine (mul_nonneg hk0 hmin0)
  exact (EReal.coe_le_coe_iff.mpr hreal).trans
    (SimpleGraph.IsAcyclic.uniformCharacteristicFunctionGap
      G hG Z z θ hZ hz hzZ hθ)

/-- **Lemma A.6 (bounded-scale compactness), genuine finite form.**  The
constant is independent of the finite acyclic graph, activity, and frequency;
it depends only on `Z,a,b`. -/
theorem boundedScaleCompactness
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ a b : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (ha : 0 < a) (hab : a ≤ b) (hθ : |θ| ≤ Real.pi)
    (hlower : a ≤ (hardCoreLaw G z hz).variance * θ ^ 2)
    (hupper : (hardCoreLaw G z hz).variance * θ ^ 2 ≤ b) :
    ((boundedScaleEpsilon Z a b : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  by_cases hsmall : θ ^ 2 ≤ boundedScaleDescentThreshold Z / 4
  · exact (EReal.coe_le_coe_iff.mpr (min_le_left _ _)).trans
      (boundedScaleCompactness_smallTheta G hG Z z θ a hZ hz hzZ ha hθ
        hlower hsmall)
  · have hlarge : boundedScaleDescentThreshold Z / 4 < θ ^ 2 :=
      lt_of_not_ge hsmall
    exact (EReal.coe_le_coe_iff.mpr (min_le_right _ _)).trans
      (boundedScaleCompactness_largeTheta G hG Z z θ a hZ hz hzZ ha hθ
        hlower hlarge)

/-- Existential packaging of A.6, displaying exactly that the positive
constant depends only on the prescribed scale parameters. -/
theorem exists_boundedScaleCompactness
    (Z a b : ℝ) (hZ : 0 < Z) (ha : 0 < a) (hab : a ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.IsAcyclic →
      ∀ z θ : ℝ, ∀ hz : 0 < z, z ≤ Z → |θ| ≤ Real.pi →
      a ≤ (hardCoreLaw G z hz).variance * θ ^ 2 →
      (hardCoreLaw G z hz).variance * θ ^ 2 ≤ b →
      (ε : EReal) ≤ (hardCoreLaw G z hz).logarithmicLoss θ := by
  refine ⟨boundedScaleEpsilon Z a b, boundedScaleEpsilon_pos hZ ha, ?_⟩
  intro V _ G hG z θ hz hzZ hθ hlower hupper
  exact boundedScaleCompactness G hG Z z θ a b hZ hz hzZ ha hab hθ
    hlower hupper

/-- The manuscript envelope `H_α(x)=min{x,x^α}`. -/
def boundedScaleH (α x : ℝ) : ℝ := min x (x ^ α)

/-- Explicit constant for the bounded-scale `H_α` corollary. -/
def boundedScaleHAlphaConstant (Z X0 α : ℝ) : ℝ :=
  min (smallFrequencyConstant Z)
    (boundedScaleEpsilon Z (smallFrequencyScale Z) X0 / X0)

 theorem boundedScaleHAlphaConstant_pos
    {Z X0 α : ℝ} (hZ : 0 < Z) (hX0 : 0 < X0) :
    0 < boundedScaleHAlphaConstant Z X0 α := by
  unfold boundedScaleHAlphaConstant
  apply lt_min
  · exact smallFrequencyConstant_pos hZ
  · exact div_pos
      (boundedScaleEpsilon_pos hZ (smallFrequencyScale_pos hZ)) hX0

/-- **Equation A.39 (bounded-scale `H_α` envelope).**  This is obtained only
from genuine A.5 and A.6.  The hypotheses on `α` record the manuscript's
range; the elementary estimate `H_α(x) ≤ x` is all that is needed on a fixed
bounded scale. -/
theorem boundedScaleHAlpha
    {V : Type u} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ X0 α : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hX0 : 0 < X0) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ : |θ| ≤ Real.pi)
    (hupper : (hardCoreLaw G z hz).variance * θ ^ 2 ≤ X0) :
    ((boundedScaleHAlphaConstant Z X0 α *
      boundedScaleH α ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) ≤
      (hardCoreLaw G z hz).logarithmicLoss θ := by
  let μ := hardCoreLaw G z hz
  let x := μ.variance * θ ^ 2
  let c := boundedScaleHAlphaConstant Z X0 α
  have hx0 : 0 ≤ x := mul_nonneg μ.variance_nonneg (sq_nonneg θ)
  have hxpow0 : 0 ≤ x ^ α := Real.rpow_nonneg hx0 α
  have hH0 : 0 ≤ boundedScaleH α x := le_min hx0 hxpow0
  have hHx : boundedScaleH α x ≤ x := min_le_left _ _
  have hcpos : 0 < c := by
    dsimp [c]
    exact boundedScaleHAlphaConstant_pos hZ hX0
  have hcle : c ≤ smallFrequencyConstant Z := by
    dsimp [c, boundedScaleHAlphaConstant]
    exact min_le_left _ _
  by_cases hsmall : x ≤ smallFrequencyScale Z
  · have hA5 := uniformSmallFrequencyCurvature G hG Z z θ
      hZ hz hzZ hθ hsmall
    have hreal : c * boundedScaleH α x ≤ smallFrequencyConstant Z * x := by
      calc
        c * boundedScaleH α x ≤
            smallFrequencyConstant Z * boundedScaleH α x :=
          mul_le_mul_of_nonneg_right hcle hH0
        _ ≤ smallFrequencyConstant Z * x :=
          mul_le_mul_of_nonneg_left hHx (smallFrequencyConstant_pos hZ).le
    exact (EReal.coe_le_coe_iff.mpr (by simpa [c, x] using hreal)).trans hA5
  · have hlarge : smallFrequencyScale Z < x := lt_of_not_ge hsmall
    have hsX : smallFrequencyScale Z ≤ X0 :=
      hlarge.le.trans (by simpa [x, μ] using hupper)
    have hA6 := boundedScaleCompactness G hG Z z θ
      (smallFrequencyScale Z) X0 hZ hz hzZ (smallFrequencyScale_pos hZ)
      hsX hθ hlarge.le (by simpa [x, μ] using hupper)
    have hcquot : c ≤ boundedScaleEpsilon Z (smallFrequencyScale Z) X0 / X0 := by
      dsimp [c, boundedScaleHAlphaConstant]
      exact min_le_right _ _
    have hHX0 : boundedScaleH α x ≤ X0 :=
      hHx.trans (by simpa [x, μ] using hupper)
    have hreal : c * boundedScaleH α x ≤
        boundedScaleEpsilon Z (smallFrequencyScale Z) X0 := by
      calc
        c * boundedScaleH α x ≤
            (boundedScaleEpsilon Z (smallFrequencyScale Z) X0 / X0) *
              boundedScaleH α x :=
          mul_le_mul_of_nonneg_right hcquot hH0
        _ ≤ (boundedScaleEpsilon Z (smallFrequencyScale Z) X0 / X0) * X0 :=
          mul_le_mul_of_nonneg_left hHX0
            (div_nonneg (boundedScaleEpsilon_pos hZ
              (smallFrequencyScale_pos hZ)).le hX0.le)
        _ = boundedScaleEpsilon Z (smallFrequencyScale Z) X0 := by
          field_simp [hX0.ne']
    exact (EReal.coe_le_coe_iff.mpr (by simpa [c, x] using hreal)).trans hA6

/-- Existential form of A.39, making the dependence on `Z,X0,α` explicit. -/
theorem exists_boundedScaleHAlpha
    (Z X0 α : ℝ) (hZ : 0 < Z) (hX0 : 0 < X0)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type u) [Fintype V] (G : SimpleGraph V), G.IsAcyclic →
      ∀ z θ : ℝ, ∀ hz : 0 < z, z ≤ Z → |θ| ≤ Real.pi →
      (hardCoreLaw G z hz).variance * θ ^ 2 ≤ X0 →
      ((c * boundedScaleH α
        ((hardCoreLaw G z hz).variance * θ ^ 2) : ℝ) : EReal) ≤
        (hardCoreLaw G z hz).logarithmicLoss θ := by
  refine ⟨boundedScaleHAlphaConstant Z X0 α,
    boundedScaleHAlphaConstant_pos hZ hX0, ?_⟩
  intro V _ G hG z θ hz hzZ hθ hupper
  exact boundedScaleHAlpha G hG Z z θ X0 α hZ hz hzZ hX0 hα0 hα1
    hθ hupper

end
end AppendixA
end Forest
end Erdos993
