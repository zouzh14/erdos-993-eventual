import Erdos993.Forest.RecursiveDecompositionData

set_option maxHeartbeats 5000000

/-!
# Geometry and exact loss bookkeeping for the A.10 recursive family
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

noncomputable local instance classicalDecidableEqA10Geometry (α : Type*) : DecidableEq α :=
  Classical.decEq α

namespace RecursiveDecomposition

private lemma qDiscardedRoots_mem_child_ne
    (R : ComponentRooting G) {u v x : V}
    (hx : x ∈ MaximalModulusTrace.qDiscardedRoots R u v) :
    R.IsChild (G := G) u x ∧ x ≠ v := by
  exact ⟨(R.mem_children (G := G) u x).mp (Finset.mem_erase.mp hx).2,
    (Finset.mem_erase.mp hx).1⟩

private lemma rDiscardedRoots_mem_grandchild_ne
    (hG : G.IsAcyclic) (R : ComponentRooting G) {u c v x : V}
    (huc : R.IsChild (G := G) u c) (hcv : R.IsChild (G := G) c v)
    (hx : x ∈ MaximalModulusTrace.rDiscardedRoots R u c v) :
    x ∈ grandchildrenAt R u ∧ x ≠ v := by
  unfold MaximalModulusTrace.rDiscardedRoots at hx
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

private theorem children_pairwiseDisjoint_children
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    (↑(R.children (G := G) u) : Set V).PairwiseDisjoint
      (fun d => R.children (G := G) d) := by
  intro d hd e he hde
  have hdisj := R.children_pairwiseDisjoint_descendants (G := G) hG u hd he hde
  exact hdisj.mono
    (fun x hx => (R.mem_descendants (G := G) d x).mpr
      (Relation.ReflTransGen.single
        ((R.mem_children (G := G) d x).mp hx)))
    (fun x hx => (R.mem_descendants (G := G) e x).mpr
      (Relation.ReflTransGen.single
        ((R.mem_children (G := G) e x).mp hx)))

/-- Flattening a grandchild sum over the pairwise-disjoint child families. -/
theorem sum_grandchildrenAt_eq_sum_children
    {M : Type*} [AddCommMonoid M]
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) (f : V → M) :
    (∑ v ∈ grandchildrenAt R u, f v) =
      ∑ c ∈ R.children (G := G) u,
        ∑ v ∈ R.children (G := G) c, f v := by
  rw [grandchildrenAt, Finset.sum_biUnion
    (children_pairwiseDisjoint_children hG R u)]

/-- The explicit R-discarded root union has exactly the two sums appearing in
A.9, with no duplication. -/
theorem sum_rDiscardedRoots_eq
    {M : Type*} [AddCommMonoid M]
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u c v : V} (huc : R.IsChild (G := G) u c)
    (hcv : R.IsChild (G := G) c v) (f : V → M) :
    (∑ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v, f w) =
      (∑ w ∈ (R.children (G := G) c).erase v, f w) +
        ∑ d ∈ (R.children (G := G) u).erase c,
          ∑ w ∈ R.children (G := G) d, f w := by
  have hpair :
      (↑((R.children (G := G) u).erase c) : Set V).PairwiseDisjoint
        (fun d => R.children (G := G) d) := by
    intro d hd e he hde
    exact children_pairwiseDisjoint_children hG R u
      (Finset.mem_erase.mp hd).2 (Finset.mem_erase.mp he).2 hde
  have hdisj : Disjoint ((R.children (G := G) c).erase v)
      (((R.children (G := G) u).erase c).biUnion
        (fun d => R.children (G := G) d)) := by
    rw [Finset.disjoint_left]
    intro x hx hxunion
    obtain ⟨d, hd, hdx⟩ := Finset.mem_biUnion.mp hxunion
    have hdc := (Finset.mem_erase.mp hd).1
    have hcx := (R.mem_children (G := G) c x).mp
      (Finset.mem_erase.mp hx).2
    have hdx' := (R.mem_children (G := G) d x).mp hdx
    exact hdc (R.isChild_unique (G := G) hG hdx' hcx)
  unfold MaximalModulusTrace.rDiscardedRoots
  rw [Finset.sum_union hdisj, Finset.sum_biUnion hpair]

/-- Every member of `C(T)` is a (possibly reflexive, only in the retained
one-point base case) descendant of the input subtree root. -/
theorem familyRoot_isDescendant
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    ∀ x ∈ D.family, R.IsDescendant (G := G) u x := by
  induction D with
  | retained u hretain =>
      intro x hx
      simp only [family, Finset.mem_singleton] at hx
      subst x
      exact Relation.ReflTransGen.refl
  | splitQ u hretain hmax hsplit =>
      intro x hx
      exact Relation.ReflTransGen.single
        ((R.mem_children (G := G) u x).mp hx)
  | splitR u hretain hmax hsplit =>
      intro x hx
      change x ∈ grandchildrenAt R u at hx
      rw [grandchildrenAt, Finset.mem_biUnion] at hx
      obtain ⟨c, huc, hcx⟩ := hx
      exact (Relation.ReflTransGen.single
        ((R.mem_children (G := G) u c).mp huc)).trans
          (Relation.ReflTransGen.single
            ((R.mem_children (G := G) c x).mp hcx))
  | @qStep u v hretain hmax hone huv tail ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Relation.ReflTransGen.single
          (qDiscardedRoots_mem_child_ne R hx).1
      · exact (Relation.ReflTransGen.single huv).trans (ih x hx)
  | @rStep u c v hretain hmax hone huc hcv tail ih =>
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxg, _⟩ :=
          rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
        rw [grandchildrenAt, Finset.mem_biUnion] at hxg
        obtain ⟨d, hd, hdx⟩ := hxg
        exact (Relation.ReflTransGen.single
          ((R.mem_children (G := G) u d).mp hd)).trans
            (Relation.ReflTransGen.single
              ((R.mem_children (G := G) d x).mp hdx))
      · exact (Relation.ReflTransGen.single huc).trans
          ((Relation.ReflTransGen.single hcv).trans (ih x hx))

/-- The subtrees rooted at the actual recursive family are pairwise disjoint. -/
theorem family_pairwiseDisjoint_descendants
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    (↑D.family : Set V).PairwiseDisjoint
      (fun v => R.descendants (G := G) v) := by
  induction D with
  | retained u hretain =>
      intro x hx y hy hxy
      have hx' : x = u := by simpa [family] using hx
      have hy' : y = u := by simpa [family] using hy
      exact (hxy (hx'.trans hy'.symm)).elim
  | splitQ u hretain hmax hsplit =>
      exact R.children_pairwiseDisjoint_descendants (G := G) hG u
  | splitR u hretain hmax hsplit =>
      exact grandchildren_pairwiseDisjoint_descendants hG R u
  | @qStep u v hretain hmax hone huv tail ih =>
      intro x hx y hy hxy
      rcases Finset.mem_union.mp hx with hx | hx <;>
        rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨hux, _⟩ := qDiscardedRoots_mem_child_ne R hx
        obtain ⟨huy, _⟩ := qDiscardedRoots_mem_child_ne R hy
        exact R.disjoint_descendants_of_ne_children (G := G) hG hux huy hxy
      · obtain ⟨hux, hxv⟩ := qDiscardedRoots_mem_child_ne R hx
        have hvy := tail.familyRoot_isDescendant hG y hy
        exact (R.disjoint_descendants_of_ne_children (G := G) hG hux huv hxv).mono_right
          (descendants_subset_of_isDescendant R hvy)
      · obtain ⟨huy, hyv⟩ := qDiscardedRoots_mem_child_ne R hy
        have hvx := tail.familyRoot_isDescendant hG x hx
        exact ((R.disjoint_descendants_of_ne_children (G := G) hG huy huv hyv).mono_right
          (descendants_subset_of_isDescendant R hvx)).symm
      · exact ih hx hy hxy
  | @rStep u c v hretain hmax hone huc hcv tail ih =>
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
        have hvy := tail.familyRoot_isDescendant hG y hy
        exact (grandchildren_pairwiseDisjoint_descendants hG R u hxg hvg hxv).mono_right
          (descendants_subset_of_isDescendant R hvy)
      · obtain ⟨hyg, hyv⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hy
        have hvg : v ∈ grandchildrenAt R u := by
          rw [grandchildrenAt, Finset.mem_biUnion]
          exact ⟨c, (R.mem_children (G := G) u c).mpr huc,
            (R.mem_children (G := G) c v).mpr hcv⟩
        have hvx := tail.familyRoot_isDescendant hG x hx
        exact ((grandchildren_pairwiseDisjoint_descendants hG R u hyg hvg hyv).mono_right
          (descendants_subset_of_isDescendant R hvx)).symm
      · exact ih hx hy hxy

/-- At a non-retained input, every member of the recursive family is a strict
descendant subtree. -/
theorem familyRoot_isStrictDescendant
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u)
    (hnot : ¬ IsA10Retained R Z z hz θ X0 u) :
    ∀ x ∈ D.family,
      R.IsDescendant (G := G) u x ∧ x ≠ u := by
  intro x hx
  refine ⟨D.familyRoot_isDescendant hG x hx, ?_⟩
  cases D with
  | retained u hretain => exact False.elim (hnot hretain)
  | splitQ u hretain hmax hsplit =>
      have hux := (R.mem_children (G := G) u x).mp hx
      intro hxu
      subst x
      exact R.not_mem_descendants_child (G := G) hux
        (R.self_mem_descendants (G := G) u)
  | splitR u hretain hmax hsplit =>
      change x ∈ grandchildrenAt R u at hx
      rw [grandchildrenAt, Finset.mem_biUnion] at hx
      obtain ⟨c, huc, hcx⟩ := hx
      have huc' := (R.mem_children (G := G) u c).mp huc
      intro hxu
      subst x
      exact R.not_mem_descendants_child (G := G) huc'
        ((R.mem_descendants (G := G) c u).mpr
          (Relation.ReflTransGen.single
            ((R.mem_children (G := G) c u).mp hcx)))
  | @qStep u v hretain hmax hone huv tail =>
      rcases Finset.mem_union.mp hx with hx | hx
      · have hux := (qDiscardedRoots_mem_child_ne R hx).1
        intro hxu
        subst x
        exact R.not_mem_descendants_child (G := G) hux
          (R.self_mem_descendants (G := G) u)
      · have hvx := tail.familyRoot_isDescendant hG x hx
        intro hxu
        subst x
        exact R.not_mem_descendants_child (G := G) huv
          ((R.mem_descendants (G := G) v u).mpr hvx)
  | @rStep u c v hretain hmax hone huc hcv tail =>
      have hcvDesc : R.IsDescendant (G := G) c v :=
        Relation.ReflTransGen.single hcv
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxg, _⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
        rw [grandchildrenAt, Finset.mem_biUnion] at hxg
        obtain ⟨d, hud, hdx⟩ := hxg
        have hud' := (R.mem_children (G := G) u d).mp hud
        intro hxu
        subst x
        exact R.not_mem_descendants_child (G := G) hud'
          ((R.mem_descendants (G := G) d u).mpr
            (Relation.ReflTransGen.single
              ((R.mem_children (G := G) d u).mp hdx)))
      · have hvx := tail.familyRoot_isDescendant hG x hx
        intro hxu
        subst x
        have hcu : R.IsDescendant (G := G) c u :=
          Relation.ReflTransGen.trans hcvDesc hvx
        exact R.not_mem_descendants_child (G := G) huc
          ((R.mem_descendants (G := G) c u).mpr hcu)

/-- Sum of logarithmic losses of the concrete recursive family. -/
noncomputable def familyLoss
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) : EReal :=
  ∑ v ∈ D.family, (R.subtreeLawAt z hz v).logarithmicLoss θ

theorem disjoint_qDiscardedRoots_family
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u v : V}
    (huv : R.IsChild (G := G) u v)
    (tail : RecursiveDecomposition R Z z hz θ X σ X0 v) :
    Disjoint (MaximalModulusTrace.qDiscardedRoots R u v) tail.family := by
  rw [Finset.disjoint_left]
  intro x hx hxTail
  obtain ⟨hux, hxv⟩ := qDiscardedRoots_mem_child_ne R hx
  have hvx := tail.familyRoot_isDescendant hG x hxTail
  have hd := R.disjoint_descendants_of_ne_children (G := G) hG hux huv hxv
  have hxx := R.self_mem_descendants (G := G) x
  exact Finset.disjoint_left.mp hd hxx
    ((R.mem_descendants (G := G) v x).mpr hvx)

theorem disjoint_rDiscardedRoots_family
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u c v : V}
    (huc : R.IsChild (G := G) u c) (hcv : R.IsChild (G := G) c v)
    (tail : RecursiveDecomposition R Z z hz θ X σ X0 v) :
    Disjoint (MaximalModulusTrace.rDiscardedRoots R u c v) tail.family := by
  rw [Finset.disjoint_left]
  intro x hx hxTail
  obtain ⟨hxg, hxv⟩ := rDiscardedRoots_mem_grandchild_ne hG R huc hcv hx
  have hvg : v ∈ grandchildrenAt R u := by
    rw [grandchildrenAt, Finset.mem_biUnion]
    exact ⟨c, (R.mem_children (G := G) u c).mpr huc,
      (R.mem_children (G := G) c v).mpr hcv⟩
  have hvx := tail.familyRoot_isDescendant hG x hxTail
  have hd := grandchildren_pairwiseDisjoint_descendants hG R u hxg hvg hxv
  have hxx := R.self_mem_descendants (G := G) x
  exact Finset.disjoint_left.mp hd hxx
    ((R.mem_descendants (G := G) v x).mpr hvx)

private theorem splitQ_familyLoss_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V)
    (hmax : occupiedCharacteristicModulusAt R z hz θ u ≤
      vacantCharacteristicModulusAt R z hz θ u) :
    (∑ v ∈ R.children (G := G) u,
      (R.subtreeLawAt z hz v).logarithmicLoss θ) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hroot := vacantDeletionLoss_le_subtreeLoss_of_max R z θ hz u hmax
  rw [hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
    hG R z θ hz u] at hroot
  exact hroot

private theorem splitR_familyLoss_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V)
    (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
      occupiedCharacteristicModulusAt R z hz θ u) :
    (∑ v ∈ grandchildrenAt R u,
      (R.subtreeLawAt z hz v).logarithmicLoss θ) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hroot := occupiedDeletionLoss_le_subtreeLoss_of_max R z θ hz u hmax
  rw [hardCoreLaw_logarithmicLoss_deleteClosedSubtreeRoot_eq_sum_childVacant
    hG R z θ hz u] at hroot
  simp_rw [hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
    hG R z θ hz] at hroot
  rw [sum_grandchildrenAt_eq_sum_children hG R u
    (fun v => (R.subtreeLawAt z hz v).logarithmicLoss θ)]
  exact hroot

/-- Exact no-double-counting comparison: the sum over the concrete recursive
family is bounded by the A.9 repeated-substitution account. -/
theorem familyLoss_le_accountedLoss
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    D.familyLoss ≤ D.toTrace.accountedLoss := by
  induction D with
  | retained u hretain =>
      simp [familyLoss, family, toTrace,
        MaximalModulusTrace.accountedLoss]
  | splitQ u hretain hmax hsplit =>
      exact splitQ_familyLoss_le hG R z θ hz u hmax
  | splitR u hretain hmax hsplit =>
      exact splitR_familyLoss_le hG R z θ hz u hmax
  | @qStep u v hretain hmax hone huv tail ih =>
      rw [familyLoss, family, Finset.sum_union
        (disjoint_qDiscardedRoots_family hG huv tail)]
      change MaximalModulusTrace.qDiscardedLoss R z θ hz u v +
          tail.familyLoss ≤
        MaximalModulusTrace.qDiscardedLoss R z θ hz u v +
          tail.toTrace.accountedLoss
      simpa [add_comm] using
        (add_le_add_right ih
          (MaximalModulusTrace.qDiscardedLoss R z θ hz u v))
  | @rStep u c v hretain hmax hone huc hcv tail ih =>
      rw [familyLoss, family, Finset.sum_union
        (disjoint_rDiscardedRoots_family hG huc hcv tail)]
      change (∑ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v,
          (R.subtreeLawAt z hz w).logarithmicLoss θ) + tail.familyLoss ≤
        MaximalModulusTrace.rDiscardedLoss R z θ hz u c v +
          tail.toTrace.accountedLoss
      have hr : (∑ w ∈ MaximalModulusTrace.rDiscardedRoots R u c v,
          (R.subtreeLawAt z hz w).logarithmicLoss θ) =
          MaximalModulusTrace.rDiscardedLoss R z θ hz u c v := by
        have hpair :
            (↑((R.children (G := G) u).erase c) : Set V).PairwiseDisjoint
              (fun d => R.children (G := G) d) := by
          intro d hd e he hde
          exact children_pairwiseDisjoint_children hG R u
            (Finset.mem_erase.mp hd).2 (Finset.mem_erase.mp he).2 hde
        have hdisj : Disjoint ((R.children (G := G) c).erase v)
            (((R.children (G := G) u).erase c).biUnion
              (fun d => R.children (G := G) d)) := by
          rw [Finset.disjoint_left]
          intro x hx hxunion
          obtain ⟨d, hd, hdx⟩ := Finset.mem_biUnion.mp hxunion
          have hdc := (Finset.mem_erase.mp hd).1
          have hcx := (R.mem_children (G := G) c x).mp
            (Finset.mem_erase.mp hx).2
          have hdx' := (R.mem_children (G := G) d x).mp hdx
          exact hdc (R.isChild_unique (G := G) hG hdx' hcx)
        unfold MaximalModulusTrace.rDiscardedRoots
          MaximalModulusTrace.rDiscardedLoss
        rw [Finset.sum_union hdisj, Finset.sum_biUnion hpair]
      rw [hr]
      simpa [add_comm] using
        (add_le_add_right ih
          (MaximalModulusTrace.rDiscardedLoss R z θ hz u c v))

/-- Lemma A.10 loss inequality for the actual recursive family. -/
theorem familyLoss_le_subtreeLoss_A10
    (hG : G.IsAcyclic) {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    D.familyLoss ≤ (R.subtreeLawAt z hz u).logarithmicLoss θ :=
  D.familyLoss_le_accountedLoss hG |>.trans
    (D.toTrace.accountedLoss_le_subtreeLoss_A64 hG R z θ hz)

end RecursiveDecomposition

end
end AppendixA
end Forest
end Erdos993
