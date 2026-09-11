import Erdos993.Forest.MaximalModulusPathLoss
import Erdos993.Forest.NarrowSubtreeLoss

/-!
# Unified concrete maximal-modulus path lemma (Appendix A.9)
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

noncomputable local instance classicalDecidableEqA9Final (α : Type*) : DecidableEq α :=
  Classical.decEq α

lemma descendants_subset_of_isDescendant
    (R : ComponentRooting G) {u v : V}
    (huv : R.IsDescendant (G := G) u v) :
    R.descendants (G := G) v ⊆ R.descendants (G := G) u := by
  intro x hx
  rw [R.mem_descendants] at hx ⊢
  exact Relation.ReflTransGen.trans huv hx

/-- Grandchild descendant subtrees are pairwise disjoint. -/
theorem grandchildren_pairwiseDisjoint_descendants
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    (↑(grandchildrenAt R u) : Set V).PairwiseDisjoint
      (fun v => R.descendants (G := G) v) := by
  intro x hx y hy hxy
  change x ∈ grandchildrenAt R u at hx
  change y ∈ grandchildrenAt R u at hy
  rw [grandchildrenAt, Finset.mem_biUnion] at hx hy
  obtain ⟨cx, hcx, hxx⟩ := hx
  obtain ⟨cy, hcy, hyy⟩ := hy
  have hucx := (R.mem_children (G := G) u cx).mp hcx
  have hucy := (R.mem_children (G := G) u cy).mp hcy
  have hcxx := (R.mem_children (G := G) cx x).mp hxx
  have hcyy := (R.mem_children (G := G) cy y).mp hyy
  by_cases hc : cx = cy
  · subst cy
    exact R.disjoint_descendants_of_ne_children (G := G) hG hcxx hcyy hxy
  · have hd := R.disjoint_descendants_of_ne_children (G := G) hG hucx hucy hc
    exact hd.mono
      (descendants_subset_of_isDescendant R (Relation.ReflTransGen.single hcxx))
      (descendants_subset_of_isDescendant R (Relation.ReflTransGen.single hcyy))

namespace MaximalModulusTrace

/-- The roots of the final subtree and every actually discarded component. -/
noncomputable def decompositionRoots
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → Finset V
  | .stop u => {u}
  | .qStep (u := u) (v := v) _ _ tail =>
      qDiscardedRoots R u v ∪ tail.decompositionRoots
  | .rStep (u := u) (c := c) (v := v) _ _ _ tail =>
      rDiscardedRoots R u c v ∪ tail.decompositionRoots

/-- These roots are exactly the terminal root together with the recorded
finite discarded family. -/
theorem decompositionRoots_eq_insert_terminal_discarded
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.decompositionRoots = insert τ.terminalRoot τ.discardedRoots := by
  induction τ with
  | stop u => simp [decompositionRoots, terminalRoot, discardedRoots]
  | qStep huv hmax tail ih =>
      simp only [decompositionRoots, terminalRoot, discardedRoots, ih]
      ext x
      simp [or_assoc, or_left_comm, or_comm]
  | rStep huc hcv hmax tail ih =>
      simp only [decompositionRoots, terminalRoot, discardedRoots, ih]
      ext x
      simp [or_assoc, or_left_comm, or_comm]

private lemma qDiscardedRoots_mem_child_ne
    (R : ComponentRooting G) {u v x : V}
    (hx : x ∈ qDiscardedRoots R u v) :
    R.IsChild (G := G) u x ∧ x ≠ v := by
  exact ⟨(R.mem_children (G := G) u x).mp (Finset.mem_erase.mp hx).2,
    (Finset.mem_erase.mp hx).1⟩

private lemma rDiscardedRoots_mem_grandchild_ne
    (hG : G.IsAcyclic) (R : ComponentRooting G) {u c v x : V}
    (huc : R.IsChild (G := G) u c) (hcv : R.IsChild (G := G) c v)
    (hx : x ∈ rDiscardedRoots R u c v) :
    x ∈ grandchildrenAt R u ∧ x ≠ v := by
  unfold rDiscardedRoots at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · have hxe := Finset.mem_erase.mp hx
    constructor
    · rw [grandchildrenAt, Finset.mem_biUnion]
      exact ⟨c, (R.mem_children (G := G) u c).mpr huc, hxe.2⟩
    · exact hxe.1
  · rw [Finset.mem_biUnion] at hx
    obtain ⟨d, hd, hxd⟩ := hx
    have hde := Finset.mem_erase.mp hd
    have hud := (R.mem_children (G := G) u d).mp hde.2
    have hdx := (R.mem_children (G := G) d x).mp hxd
    constructor
    · rw [grandchildrenAt, Finset.mem_biUnion]
      exact ⟨d, hde.2, hxd⟩
    · intro hxv
      subst x
      exact hde.1 (R.isChild_unique (G := G) hG hdx hcv)

/-- Every final/discarded component remains a descendant of the input root. -/
theorem decompositionRoot_isDescendant
    (hG : G.IsAcyclic) {R : ComponentRooting G} {z : ℝ} {hz : 0 < z}
    {θ : ℝ} {u : V} (τ : MaximalModulusTrace R z hz θ u) :
    ∀ x ∈ τ.decompositionRoots, R.IsDescendant (G := G) u x := by
  induction τ with
  | stop u =>
      intro x hx
      simp only [decompositionRoots, Finset.mem_singleton] at hx
      subst x
      exact Relation.ReflTransGen.refl
  | @qStep u v huv hmax tail ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Relation.ReflTransGen.single (qDiscardedRoots_mem_child_ne R hx).1
      · exact (Relation.ReflTransGen.single huv).trans (ih x hx)
  | @rStep u c v huc hcv hmax tail ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxg, _⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
        rw [grandchildrenAt, Finset.mem_biUnion] at hxg
        obtain ⟨d, hd, hdx⟩ := hxg
        exact (Relation.ReflTransGen.single
          ((R.mem_children (G := G) u d).mp hd)).trans
            (Relation.ReflTransGen.single
              ((R.mem_children (G := G) d x).mp hdx))
      · exact (Relation.ReflTransGen.single huc).trans
          ((Relation.ReflTransGen.single hcv).trans (ih x hx))

/-- The final subtree and the actual finite discarded family are pairwise
disjoint descendant subtrees. -/
theorem decompositionRoots_pairwiseDisjoint_descendants
    (hG : G.IsAcyclic) {R : ComponentRooting G} {z : ℝ} {hz : 0 < z}
    {θ : ℝ} {u : V} (τ : MaximalModulusTrace R z hz θ u) :
    (↑τ.decompositionRoots : Set V).PairwiseDisjoint
      (fun v => R.descendants (G := G) v) := by
  induction τ with
  | stop u =>
      intro x hx y hy hxy
      have hx' : x = u := by simpa [decompositionRoots] using hx
      have hy' : y = u := by simpa [decompositionRoots] using hy
      exact (hxy (hx'.trans hy'.symm)).elim
  | @qStep u v huv hmax tail ih =>
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hx | hx <;>
        rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hux, _⟩ := qDiscardedRoots_mem_child_ne R hx
        obtain ⟨huy, _⟩ := qDiscardedRoots_mem_child_ne R hy
        exact R.disjoint_descendants_of_ne_children (G := G) hG hux huy hxy
      · obtain ⟨hux, hxv⟩ := qDiscardedRoots_mem_child_ne R hx
        have hvy := tail.decompositionRoot_isDescendant hG y hy
        exact (R.disjoint_descendants_of_ne_children (G := G) hG hux huv hxv).mono_right
          (descendants_subset_of_isDescendant R hvy)
      · obtain ⟨huy, hyv⟩ := qDiscardedRoots_mem_child_ne R hy
        have hvx := tail.decompositionRoot_isDescendant hG x hx
        exact ((R.disjoint_descendants_of_ne_children (G := G) hG huy huv hyv).mono_right
          (descendants_subset_of_isDescendant R hvx)).symm
      · exact ih hx hy hxy
  | @rStep u c v huc hcv hmax tail ih =>
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hx | hx <;>
        rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hxg, _⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
        obtain ⟨hyg, _⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hy
        exact grandchildren_pairwiseDisjoint_descendants hG R u hxg hyg hxy
      · obtain ⟨hxg, hxv⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
        have hvg : v ∈ grandchildrenAt R u := by
          rw [grandchildrenAt, Finset.mem_biUnion]
          exact ⟨c, (R.mem_children (G := G) u c).mpr huc,
            (R.mem_children (G := G) c v).mpr hcv⟩
        have hvy := tail.decompositionRoot_isDescendant hG y hy
        exact (grandchildren_pairwiseDisjoint_descendants hG R u hxg hvg hxv).mono_right
          (descendants_subset_of_isDescendant R hvy)
      · obtain ⟨hyg, hyv⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hy
        have hvg : v ∈ grandchildrenAt R u := by
          rw [grandchildrenAt, Finset.mem_biUnion]
          exact ⟨c, (R.mem_children (G := G) u c).mpr huc,
            (R.mem_children (G := G) c v).mpr hcv⟩
        have hvx := tail.decompositionRoot_isDescendant hG x hx
        exact ((grandchildren_pairwiseDisjoint_descendants hG R u hyg hvg hyv).mono_right
          (descendants_subset_of_isDescendant R hvx)).symm
      · exact ih hx hy hxy

end MaximalModulusTrace

/-- Appendix A, Lemma A.9: the canonical finite maximal-modulus construction,
with its actual Q/R trace, filled child-chain, terminal subtree, pairwise-disjoint
discarded descendant components, scale accounting (A.63), exact iterated
factorization (A.64), and transfer decay (A.65). -/
theorem exists_maximalModulusTrace_A9
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) (u : V) :
    ∃ τ : MaximalModulusTrace R z hz θ u,
      τ = MaximalModulusTrace.canonical R z hz θ (Fintype.card V) u ∧
      τ.vertices.IsChain (fun x y => R.IsChild (G := G) x y) ∧
      τ.vertices ≠ [] ∧
      τ.decompositionRoots = insert τ.terminalRoot τ.discardedRoots ∧
      (∀ x ∈ τ.decompositionRoots,
        R.IsDescendant (G := G) u x) ∧
      (↑τ.decompositionRoots : Set V).PairwiseDisjoint
        (fun x => R.descendants (G := G) x) ∧
      descendantScaleAt R z hz θ u ≤
        maximalModulusPathVarianceConstant Z *
          (τ.K + τ.terminalScale + τ.discardedScale) ∧
      τ.accountedLoss ≤ (R.subtreeLawAt z hz u).logarithmicLoss θ ∧
      ((maximalModulusPathLossRateConstant Z * τ.K -
          maximalModulusPathLossOffsetConstant Z : ℝ) : EReal) ≤
        (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  let τ := MaximalModulusTrace.canonical R z hz θ (Fintype.card V) u
  refine ⟨τ, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact τ.vertices_isChain
  · intro h
    have hv := τ.vertices_eq_cons_tail
    rw [h] at hv
    simp at hv
  · exact τ.decompositionRoots_eq_insert_terminal_discarded
  · exact τ.decompositionRoot_isDescendant hG
  · exact τ.decompositionRoots_pairwiseDisjoint_descendants hG
  · exact τ.scale_le_K_terminal_discarded_A63 hG R Z z θ hz hzZ
  · exact τ.accountedLoss_le_subtreeLoss_A64 hG R z θ hz
  · exact τ.logarithmicLoss_ge_K_A65 hG R Z z θ hz hzZ hθ

end
end AppendixA
end Forest
end Erdos993
