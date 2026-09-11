import Erdos993.Forest.TransferMatrixTwoRow
import Erdos993.Forest.TransferMatrixBarrier

/-!
# The concrete artificial side root and actual-path contraction

This module constructs the genuine side-root forest used in the chordal form of
Appendix A, equation (A.48).  No abstract transfer interface is introduced:
all factors and probabilities are those of the hard-core model on induced
subforests of the original finite forest.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section
set_option maxHeartbeats 1200000

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment

universe u

noncomputable local instance classicalDecidableEqSide (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtypeSide {α : Type*} [Fintype α]
    (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Children retained after removing the distinguished downward edge. -/
noncomputable def retainedSideChildren
    (R : ComponentRooting G) (u v : V) : Finset V :=
  (R.children (G := G) u).erase v

/-- The union of all retained side-child descendant subtrees. -/
noncomputable def sideForestVertices
    (R : ComponentRooting G) (u v : V) : Finset V :=
  (retainedSideChildren (G := G) R u v).biUnion
    (fun w => R.descendants (G := G) w)

/-- The side forest with each retained child root removed. -/
noncomputable def sideProperForestVertices
    (R : ComponentRooting G) (u v : V) : Finset V :=
  (retainedSideChildren (G := G) R u v).biUnion
    (fun w => (R.descendants (G := G) w).erase w)

/-- Vertices of the artificial side-root tree: the actual parent `u` plus all
retained side branches. -/
noncomputable def sideRootVertices
    (R : ComponentRooting G) (u v : V) : Finset V :=
  insert u (sideForestVertices (G := G) R u v)

abbrev SideRootVertex (R : ComponentRooting G) (u v : V) :=
  {x : V // x ∈ sideRootVertices (G := G) R u v}

abbrev sideRootGraph (R : ComponentRooting G) (u v : V) :
    SimpleGraph (SideRootVertex (G := G) R u v) :=
  G.induce {x | x ∈ sideRootVertices (G := G) R u v}

/-- The actual vertex `u`, regarded as the new side root. -/
def artificialSideRoot (R : ComponentRooting G) (u v : V) :
    SideRootVertex (G := G) R u v :=
  ⟨u, by simp [sideRootVertices]⟩

/-- Membership in one retained descendant branch implies membership in the
artificial side-root vertex set. -/
theorem mem_sideRootVertices_of_descendant
    (R : ComponentRooting G) {u v w x : V}
    (hw : w ∈ retainedSideChildren (G := G) R u v)
    (hx : R.IsDescendant (G := G) w x) :
    x ∈ sideRootVertices (G := G) R u v := by
  apply Finset.mem_insert_of_mem
  rw [sideForestVertices, Finset.mem_biUnion]
  exact ⟨w, hw, (R.mem_descendants (G := G) w x).mpr hx⟩

/-- Every vertex of the concrete artificial side-root graph is reachable from
its root.  The proof follows the actual parent-child chain inside its retained
branch. -/
theorem artificialSideRoot_reachable
    (R : ComponentRooting G) (u v : V)
    (x : SideRootVertex (G := G) R u v) :
    (sideRootGraph (G := G) R u v).Reachable
      (artificialSideRoot (G := G) R u v) x := by
  let H := sideRootGraph (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  by_cases hxu : x.1 = u
  · have hx : x = r := Subtype.ext hxu
    subst x
    simpa [r] using
      (SimpleGraph.Reachable.refl (G := H) r)
  have hxside : x.1 ∈ sideForestVertices (G := G) R u v := by
    have hxmem : x.1 ∈ insert u (sideForestVertices (G := G) R u v) := by
      exact x.2
    exact (Finset.mem_insert.mp hxmem).resolve_left hxu
  rw [sideForestVertices, Finset.mem_biUnion] at hxside
  obtain ⟨w, hw, hxw⟩ := hxside
  have hwchild : R.IsChild (G := G) u w :=
    (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw)
  have hwdesc : R.IsDescendant (G := G) w x.1 :=
    (R.mem_descendants (G := G) w x.1).mp hxw
  have aux : ∀ n : ℕ, ∀ y : V,
      R.depth (G := G) y = n →
      R.IsDescendant (G := G) w y →
      ∃ yH : SideRootVertex (G := G) R u v,
        yH.1 = y ∧ H.Reachable r yH := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hdepth hwy
        by_cases hyw : y = w
        · subst y
          let wH : SideRootVertex (G := G) R u v :=
            ⟨w, mem_sideRootVertices_of_descendant (G := G) R hw
              Relation.ReflTransGen.refl⟩
          refine ⟨wH, rfl, ?_⟩
          apply SimpleGraph.Adj.reachable
          change G.Adj u w
          exact hwchild.1
        · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hwy with hEq | htail
          · exact (hyw hEq).elim
          · obtain ⟨p, hwp, hpy⟩ := htail
            have hpdepth : R.depth (G := G) p < n := by
              have hd := R.depth_child (G := G) hpy
              omega
            obtain ⟨pH, hpval, hreach⟩ :=
              ih (R.depth (G := G) p) hpdepth p rfl hwp
            let yH : SideRootVertex (G := G) R u v :=
              ⟨y, mem_sideRootVertices_of_descendant (G := G) R hw hwy⟩
            refine ⟨yH, rfl, hreach.trans ?_⟩
            apply SimpleGraph.Adj.reachable
            change G.Adj pH.1 y
            rw [hpval]
            exact hpy.1
  obtain ⟨xH, hxval, hreach⟩ :=
    aux (R.depth (G := G) x.1) x.1 rfl hwdesc
  have heq : xH = x := Subtype.ext hxval
  simpa [H, r] using heq ▸ hreach

/-- The concrete artificial side-root graph is connected, including the empty
side-branch case (where it is a singleton). -/
theorem sideRootGraph_connected
    (R : ComponentRooting G) (u v : V) :
    (sideRootGraph (G := G) R u v).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · intro x y
    exact (artificialSideRoot_reachable (G := G) R u v x).symm.trans
      (artificialSideRoot_reachable (G := G) R u v y)
  · exact ⟨artificialSideRoot (G := G) R u v⟩

/-- Inducing the artificial side-root graph preserves acyclicity. -/
theorem sideRootGraph_isAcyclic
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u v : V) :
    (sideRootGraph (G := G) R u v).IsAcyclic :=
  hG.induce _

/-- Root the connected artificial graph at its distinguished side-root vertex.
The fallback branch makes the construction valid definitionally even before
connectivity is used. -/
noncomputable def sideComponentRooting
    (R : ComponentRooting G) (u v : V) :
    ComponentRooting (sideRootGraph (G := G) R u v) := by
  let H := sideRootGraph (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let R₀ := defaultComponentRooting H
  exact
    { root := fun c => if c = H.connectedComponentMk r then r else R₀.root c
      root_mem := by
        intro c
        split_ifs with hc
        · subst c
          exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem
        · exact R₀.root_mem c }

/-- Every artificial side vertex has the distinguished root under the chosen
component rooting. -/
@[simp] theorem sideComponentRooting_rootOf
    (R : ComponentRooting G) (u v : V)
    (x : SideRootVertex (G := G) R u v) :
    (sideComponentRooting (G := G) R u v).rootOf
        (G := sideRootGraph (G := G) R u v) x =
      artificialSideRoot (G := G) R u v := by
  let H := sideRootGraph (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  have hreach : H.Reachable x r :=
    (artificialSideRoot_reachable (G := G) R u v x).symm
  have hcomp : H.connectedComponentMk x = H.connectedComponentMk r :=
    SimpleGraph.ConnectedComponent.sound hreach
  unfold ComponentRooting.rootOf
  change (if _ : H.connectedComponentMk x = H.connectedComponentMk r then r
    else (defaultComponentRooting H).root (H.connectedComponentMk x)) = r
  exact if_pos hcomp

/-- The descendants of the artificial root are all vertices of the connected
side-root graph. -/
theorem sideComponentRooting_descendants_eq_univ
    (R : ComponentRooting G) (u v : V) :
    (sideComponentRooting (G := G) R u v).descendants
        (G := sideRootGraph (G := G) R u v)
        (artificialSideRoot (G := G) R u v) = Finset.univ := by
  classical
  ext x
  simp only [Finset.mem_univ, iff_true, ComponentRooting.mem_descendants]
  have h := ComponentRooting.root_isDescendant
    (G := sideRootGraph (G := G) R u v)
    (sideComponentRooting (G := G) R u v) x
  simpa using h

/-- The rooted subtree at the artificial side root is graph-isomorphic to the
whole concrete side-root graph. -/
noncomputable def artificialSideRootSubtreeIso
    (R : ComponentRooting G) (u v : V) :
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    Rs.Subtree (G := sideRootGraph (G := G) R u v) r ≃g
      sideRootGraph (G := G) R u v := by
  classical
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let e :
      {x : SideRootVertex (G := G) R u v // x ∈ Rs.descendants (G := H) r} ≃
        SideRootVertex (G := G) R u v :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, by
        rw [sideComponentRooting_descendants_eq_univ]
        exact Finset.mem_univ x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- The artificial root is not contained in any retained child branch. -/
theorem artificialSideRoot_not_mem_sideForest
    (R : ComponentRooting G) (u v : V) :
    u ∉ sideForestVertices (G := G) R u v := by
  intro hu
  rw [sideForestVertices, Finset.mem_biUnion] at hu
  obtain ⟨w, hw, huw⟩ := hu
  have hchild : R.IsChild (G := G) u w :=
    (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw)
  exact (R.not_mem_descendants_child (G := G) hchild) huw

/-- Deleting the artificial side root leaves exactly the disjoint retained
side-child descendant subtrees. -/
noncomputable def deleteArtificialSideRootIsoSideForest
    (R : ComponentRooting G) (u v : V) :
    deleteVertex (sideRootGraph (G := G) R u v)
        (artificialSideRoot (G := G) R u v) ≃g
      G.induce {x | x ∈ sideForestVertices (G := G) R u v} := by
  classical
  let e :
      {x : SideRootVertex (G := G) R u v //
        x ≠ artificialSideRoot (G := G) R u v} ≃
      {x : V // x ∈ sideForestVertices (G := G) R u v} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          have hx : x.1.1 ∈ insert u (sideForestVertices (G := G) R u v) := x.1.2
          rcases Finset.mem_insert.mp hx with hxu | hxside
          · exfalso
            apply x.2
            apply Subtype.ext
            exact hxu
          · exact hxside⟩
      invFun := fun y =>
        ⟨⟨y.1, Finset.mem_insert_of_mem y.2⟩, by
          intro hroot
          have hyu : y.1 = u := congrArg Subtype.val hroot
          apply artificialSideRoot_not_mem_sideForest (G := G) R u v
          simpa only [hyu] using y.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- Deleting the closed neighborhood of the artificial root leaves exactly
the proper descendants in every retained side branch. -/
noncomputable def deleteClosedArtificialSideRootIsoProperSideForest
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u v : V) :
    deleteClosedNeighborhood (sideRootGraph (G := G) R u v)
        (artificialSideRoot (G := G) R u v) ≃g
      G.induce {x | x ∈ sideProperForestVertices (G := G) R u v} := by
  classical
  let e :
      {x : SideRootVertex (G := G) R u v //
        x ≠ artificialSideRoot (G := G) R u v ∧
          ¬ (sideRootGraph (G := G) R u v).Adj
            (artificialSideRoot (G := G) R u v) x} ≃
      {x : V // x ∈ sideProperForestVertices (G := G) R u v} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          have hxroot : x.1.1 ≠ u := by
            intro hxu
            apply x.2.1
            apply Subtype.ext
            exact hxu
          have hxside : x.1.1 ∈ sideForestVertices (G := G) R u v := by
            have hx : x.1.1 ∈ insert u (sideForestVertices (G := G) R u v) := x.1.2
            exact (Finset.mem_insert.mp hx).resolve_left hxroot
          rw [sideForestVertices, Finset.mem_biUnion] at hxside
          obtain ⟨w, hw, hxw⟩ := hxside
          rw [sideProperForestVertices, Finset.mem_biUnion]
          refine ⟨w, hw, Finset.mem_erase.mpr ⟨?_, hxw⟩⟩
          intro hxweq
          apply x.2.2
          change G.Adj u x.1.1
          have hchild : R.IsChild (G := G) u w :=
            (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw)
          simpa [hxweq] using hchild.1⟩
      invFun := fun y =>
        have hyprop := y.2
        have hybranch : ∃ w ∈ retainedSideChildren (G := G) R u v,
            y.1 ∈ (R.descendants (G := G) w).erase w := by
          simpa only [sideProperForestVertices, Finset.mem_biUnion] using hyprop
        let w := Classical.choose hybranch
        have hw := Classical.choose_spec hybranch
        have hwside : w ∈ retainedSideChildren (G := G) R u v := hw.1
        have hyproper : y.1 ∈ (R.descendants (G := G) w).erase w := hw.2
        have hchild : R.IsChild (G := G) u w :=
          (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hwside)
        have hydesc : R.IsDescendant (G := G) w y.1 :=
          (R.mem_descendants (G := G) w y.1).mp (Finset.mem_erase.mp hyproper).2
        ⟨⟨y.1, Finset.mem_insert_of_mem (by
            rw [sideForestVertices, Finset.mem_biUnion]
            exact ⟨w, hwside, (Finset.mem_erase.mp hyproper).2⟩)⟩, by
          constructor
          · intro hyroot
            have hyu : y.1 = u := congrArg Subtype.val hyroot
            exact (R.not_mem_descendants_child (G := G) hchild)
              (hyu ▸ (Finset.mem_erase.mp hyproper).2)
          · intro hadj
            change G.Adj u y.1 at hadj
            have huy : R.IsChild (G := G) u y.1 :=
              (ComponentRooting.adj_of_descendant_iff_isChild (G := G) hG R
                (R.child_descendant (G := G) hchild hydesc)).mp hadj
            have heq : w = y.1 :=
              ComponentRooting.child_eq_of_common_descendant (G := G) hG R
                hchild huy hydesc Relation.ReflTransGen.refl
            exact (Finset.mem_erase.mp hyproper).1 heq.symm⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- Partition function of the concrete retained side forest. -/
theorem independenceEval_sideForest_eq_prod_rootedPAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u v : V) :
    independenceEval
        (G.induce {x | x ∈ sideForestVertices (G := G) R u v}) z =
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        UniformFourthMoment.rootedPAt R z w := by
  classical
  unfold sideForestVertices UniformFourthMoment.rootedPAt
  apply independenceEval_induceFinset_biUnion G
    (retainedSideChildren (G := G) R u v)
    (fun w => R.descendants (G := G) w)
  · intro w hw y hy hwy
    exact R.children_pairwiseDisjoint_descendants (G := G) hG u
      (Finset.mem_of_mem_erase hw) (Finset.mem_of_mem_erase hy) hwy
  · intro w hw y hy hwy x t hx ht
    exact R.not_adj_of_distinct_child_descendants (G := G) hG
      ((R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw))
      ((R.mem_children (G := G) u y).mp (Finset.mem_of_mem_erase hy))
      hwy
      ((R.mem_descendants (G := G) w x).mp hx)
      ((R.mem_descendants (G := G) y t).mp ht)

/-- Partition function of the retained side forest after all retained child
roots are deleted. -/
theorem independenceEval_sideProperForest_eq_prod_rootedQAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u v : V) :
    independenceEval
        (G.induce {x | x ∈ sideProperForestVertices (G := G) R u v}) z =
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        UniformFourthMoment.rootedQAt R z w := by
  classical
  unfold sideProperForestVertices
  calc
    independenceEval
        (G.induce {x | x ∈ (retainedSideChildren (G := G) R u v).biUnion
          (fun w => (R.descendants (G := G) w).erase w)}) z =
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        independenceEval
          (G.induce {x | x ∈ (R.descendants (G := G) w).erase w}) z := by
      apply independenceEval_induceFinset_biUnion G
        (retainedSideChildren (G := G) R u v)
        (fun w => (R.descendants (G := G) w).erase w)
      · intro w hw y hy hwy
        change Disjoint ((R.descendants (G := G) w).erase w)
          ((R.descendants (G := G) y).erase y)
        rw [Finset.disjoint_left]
        intro x hxw hxy
        exact (Finset.disjoint_left.mp
          (R.children_pairwiseDisjoint_descendants (G := G) hG u
            (Finset.mem_of_mem_erase hw) (Finset.mem_of_mem_erase hy) hwy))
          (Finset.mem_of_mem_erase hxw) (Finset.mem_of_mem_erase hxy)
      · intro w hw y hy hwy x t hx ht
        exact R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw))
          ((R.mem_children (G := G) u y).mp (Finset.mem_of_mem_erase hy))
          hwy
          ((R.mem_descendants (G := G) w x).mp (Finset.mem_of_mem_erase hx))
          ((R.mem_descendants (G := G) y t).mp (Finset.mem_of_mem_erase ht))
    _ = ∏ w ∈ retainedSideChildren (G := G) R u v,
        UniformFourthMoment.rootedQAt R z w := by
      apply Finset.prod_congr rfl
      intro w hw
      unfold UniformFourthMoment.rootedQAt
      exact (independenceEval_graphIso
        (ActualRootedVariance.ComponentRooting.deleteSubtreeRootIsoProperDescendants
          (G := G) R w) z).symm

/-- Deleting the root from the rooted-subtree presentation of the artificial
side graph gives the concrete retained side forest. -/
noncomputable def deleteArtificialSideRootSubtreeIsoSideForest
    (R : ComponentRooting G) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    deleteVertex (Rs.Subtree (G := H) r) (Rs.subtreeRoot (G := H) r) ≃g
      G.induce {x | x ∈ sideForestVertices (G := G) R u v} := by
  classical
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let e :
      {x : {y : SideRootVertex (G := G) R u v //
          y ∈ Rs.descendants (G := H) r} //
        x ≠ Rs.subtreeRoot (G := H) r} ≃
      {x : V // x ∈ sideForestVertices (G := G) R u v} :=
    { toFun := fun x =>
        ⟨x.1.1.1, by
          have hx : x.1.1.1 ∈ insert u (sideForestVertices (G := G) R u v) :=
            x.1.1.2
          rcases Finset.mem_insert.mp hx with hxu | hxside
          · exfalso
            apply x.2
            apply Subtype.ext
            apply Subtype.ext
            exact hxu
          · exact hxside⟩
      invFun := fun y =>
        let sy : SideRootVertex (G := G) R u v :=
          ⟨y.1, Finset.mem_insert_of_mem y.2⟩
        ⟨⟨sy, by
            rw [sideComponentRooting_descendants_eq_univ]
            exact Finset.mem_univ sy⟩, by
          intro hroot
          have hyu : y.1 = u := by
            have := congrArg (fun t => t.1.1) hroot
            exact this
          apply artificialSideRoot_not_mem_sideForest (G := G) R u v
          simpa only [hyu] using y.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- Deleting the closed root neighborhood from the rooted-subtree
presentation gives the retained proper-side forest. -/
noncomputable def deleteClosedArtificialSideRootSubtreeIsoProperSideForest
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    deleteClosedNeighborhood (Rs.Subtree (G := H) r)
        (Rs.subtreeRoot (G := H) r) ≃g
      G.induce {x | x ∈ sideProperForestVertices (G := G) R u v} := by
  classical
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let e :
      {x : {y : SideRootVertex (G := G) R u v //
          y ∈ Rs.descendants (G := H) r} //
        x ≠ Rs.subtreeRoot (G := H) r ∧
          ¬ (Rs.Subtree (G := H) r).Adj (Rs.subtreeRoot (G := H) r) x} ≃
      {x : V // x ∈ sideProperForestVertices (G := G) R u v} :=
    { toFun := fun x =>
        ⟨x.1.1.1, by
          have hxroot : x.1.1.1 ≠ u := by
            intro hxu
            apply x.2.1
            apply Subtype.ext
            apply Subtype.ext
            exact hxu
          have hxside : x.1.1.1 ∈ sideForestVertices (G := G) R u v := by
            have hx : x.1.1.1 ∈ insert u (sideForestVertices (G := G) R u v) :=
              x.1.1.2
            exact (Finset.mem_insert.mp hx).resolve_left hxroot
          rw [sideForestVertices, Finset.mem_biUnion] at hxside
          obtain ⟨w, hw, hxw⟩ := hxside
          rw [sideProperForestVertices, Finset.mem_biUnion]
          refine ⟨w, hw, Finset.mem_erase.mpr ⟨?_, hxw⟩⟩
          intro hxweq
          apply x.2.2
          change G.Adj u x.1.1.1
          have hchild : R.IsChild (G := G) u w :=
            (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw)
          simpa [hxweq] using hchild.1⟩
      invFun := fun y =>
        have hyprop := y.2
        have hybranch : ∃ w ∈ retainedSideChildren (G := G) R u v,
            y.1 ∈ (R.descendants (G := G) w).erase w := by
          simpa only [sideProperForestVertices, Finset.mem_biUnion] using hyprop
        let w := Classical.choose hybranch
        have hw := Classical.choose_spec hybranch
        have hwside : w ∈ retainedSideChildren (G := G) R u v := hw.1
        have hyproper : y.1 ∈ (R.descendants (G := G) w).erase w := hw.2
        have hchild : R.IsChild (G := G) u w :=
          (R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hwside)
        have hydesc : R.IsDescendant (G := G) w y.1 :=
          (R.mem_descendants (G := G) w y.1).mp (Finset.mem_erase.mp hyproper).2
        let sy : SideRootVertex (G := G) R u v :=
          ⟨y.1, Finset.mem_insert_of_mem (by
            rw [sideForestVertices, Finset.mem_biUnion]
            exact ⟨w, hwside, (Finset.mem_erase.mp hyproper).2⟩)⟩
        ⟨⟨sy, by
            rw [sideComponentRooting_descendants_eq_univ]
            exact Finset.mem_univ sy⟩, by
          constructor
          · intro hroot
            have hyu : y.1 = u := congrArg (fun t => t.1.1) hroot
            exact (R.not_mem_descendants_child (G := G) hchild)
              (by simpa only [hyu] using (Finset.mem_erase.mp hyproper).2)
          · intro hadj
            change G.Adj u y.1 at hadj
            have huy : R.IsChild (G := G) u y.1 :=
              (ComponentRooting.adj_of_descendant_iff_isChild (G := G) hG R
                (R.child_descendant (G := G) hchild hydesc)).mp hadj
            have heq : w = y.1 :=
              ComponentRooting.child_eq_of_common_descendant (G := G) hG R
                hchild huy hydesc Relation.ReflTransGen.refl
            exact (Finset.mem_erase.mp hyproper).1 heq.symm⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- Root-vacant partition contribution of the artificial side-root tree. -/
theorem artificialSideRoot_rootedQAt_eq_prod_sideP
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    UniformFourthMoment.rootedQAt Rs z r =
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        UniformFourthMoment.rootedPAt R z w := by
  classical
  dsimp
  unfold UniformFourthMoment.rootedQAt
  calc
    independenceEval
        (deleteVertex
          ((sideComponentRooting (G := G) R u v).Subtree
            (G := sideRootGraph (G := G) R u v)
            (artificialSideRoot (G := G) R u v))
          ((sideComponentRooting (G := G) R u v).subtreeRoot
            (G := sideRootGraph (G := G) R u v)
            (artificialSideRoot (G := G) R u v))) z =
      independenceEval
        (G.induce {x | x ∈ sideForestVertices (G := G) R u v}) z :=
          UniformFourthMoment.independenceEval_graphIso
            (deleteArtificialSideRootSubtreeIsoSideForest (G := G) R u v) z
    _ = _ := independenceEval_sideForest_eq_prod_rootedPAt hG R z u v

/-- Root-occupied partition contribution of the artificial side-root tree. -/
theorem artificialSideRoot_rootedAAt_eq_z_mul_prod_sideQ
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    UniformFourthMoment.rootedAAt Rs z r = z *
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        UniformFourthMoment.rootedQAt R z w := by
  classical
  dsimp
  unfold UniformFourthMoment.rootedAAt
  congr 1
  calc
    independenceEval
        (deleteClosedNeighborhood
          ((sideComponentRooting (G := G) R u v).Subtree
            (G := sideRootGraph (G := G) R u v)
            (artificialSideRoot (G := G) R u v))
          ((sideComponentRooting (G := G) R u v).subtreeRoot
            (G := sideRootGraph (G := G) R u v)
            (artificialSideRoot (G := G) R u v))) z =
      independenceEval
        (G.induce {x | x ∈ sideProperForestVertices (G := G) R u v}) z :=
          UniformFourthMoment.independenceEval_graphIso
            (deleteClosedArtificialSideRootSubtreeIsoProperSideForest
              (G := G) hG R u v) z
    _ = _ := independenceEval_sideProperForest_eq_prod_rootedQAt hG R z u v

/-- The concrete side-vacancy product is exactly the ratio between the
proper-side and full-side partition products. -/
theorem sideVacancyProduct_eq_prodQ_div_prodP
    (R : ComponentRooting G) (z : ℝ) (u v : V) :
    sideVacancyProduct R z u v =
      (∏ w ∈ retainedSideChildren (G := G) R u v,
          UniformFourthMoment.rootedQAt R z w) /
        (∏ w ∈ retainedSideChildren (G := G) R u v,
          UniformFourthMoment.rootedPAt R z w) := by
  classical
  unfold sideVacancyProduct rootedVacancyProbabilityAt retainedSideChildren
  rw [Finset.prod_div_distrib]

/-- Exact artificial-side-root occupation probability. -/
theorem artificialSideRoot_occupation_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    rootedOccupationProbabilityAt Rs z r =
      (z * sideVacancyProduct R z u v) /
        (1 + z * sideVacancyProduct R z u v) := by
  classical
  dsimp
  let P : ℝ := ∏ w ∈ retainedSideChildren (G := G) R u v,
    UniformFourthMoment.rootedPAt R z w
  let Q : ℝ := ∏ w ∈ retainedSideChildren (G := G) R u v,
    UniformFourthMoment.rootedQAt R z w
  have hPpos : 0 < P := by
    dsimp [P]
    exact Finset.prod_pos fun w hw => by
      rw [UniformFourthMoment.rootedPAt_eq_rootedQAt_add_rootedAAt]
      exact add_pos
        (UniformFourthMoment.rootedQAt_pos R z hz w)
        (UniformFourthMoment.rootedAAt_pos R z hz w)
  have hratio : sideVacancyProduct R z u v = Q / P := by
    simpa [P, Q] using sideVacancyProduct_eq_prodQ_div_prodP R z u v
  unfold rootedOccupationProbabilityAt
  rw [UniformFourthMoment.rootedPAt_eq_rootedQAt_add_rootedAAt,
    artificialSideRoot_rootedQAt_eq_prod_sideP hG,
    artificialSideRoot_rootedAAt_eq_z_mul_prod_sideQ hG]
  change z * Q / (P + z * Q) =
    z * sideVacancyProduct R z u v /
      (1 + z * sideVacancyProduct R z u v)
  rw [hratio]
  field_simp [hPpos.ne']
  <;> ring

/-- Exact artificial-side-root vacancy probability. -/
theorem artificialSideRoot_vacancy_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    rootedVacancyProbabilityAt Rs z r =
      1 / (1 + z * sideVacancyProduct R z u v) := by
  dsimp
  have hsum := rootedOccupationProbabilityAt_add_vacancy
    (sideComponentRooting (G := G) R u v) z hz
    (artificialSideRoot (G := G) R u v)
  rw [artificialSideRoot_occupation_eq hG R z hz u v] at hsum
  have hden : 1 + z * sideVacancyProduct R z u v ≠ 0 := by
    have hQ := sideVacancyProduct_pos R z hz u v
    positivity
  field_simp [hden] at hsum ⊢
  linarith

/-- The full retained-side characteristic function is exactly `a`. -/
theorem hardCoreLaw_characteristic_sideForest_eq_sideCharacteristicA
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (u v : V) :
    (hardCoreLaw
      (G.induce {x | x ∈ sideForestVertices (G := G) R u v}) z hz).characteristic θ =
      sideCharacteristicA R z hz θ u v := by
  classical
  unfold sideForestVertices sideCharacteristicA retainedSideChildren
  unfold ActualRootedVariance.ComponentRooting.subtreeLawAt
  refine hardCoreLaw_characteristic_induceFinset_biUnion G
    ((R.children (G := G) u).erase v)
    (fun w => R.descendants (G := G) w) ?_ ?_ z θ hz
  · intro w hw y hy hwy
    exact R.children_pairwiseDisjoint_descendants (G := G) hG u
      (Finset.mem_of_mem_erase hw) (Finset.mem_of_mem_erase hy) hwy
  · intro w hw y hy hwy x t hx ht
    exact R.not_adj_of_distinct_child_descendants (G := G) hG
      ((R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw))
      ((R.mem_children (G := G) u y).mp (Finset.mem_of_mem_erase hy))
      hwy
      ((R.mem_descendants (G := G) w x).mp hx)
      ((R.mem_descendants (G := G) y t).mp ht)

/-- The retained-side characteristic after deleting every retained child root
is exactly `c`. -/
theorem hardCoreLaw_characteristic_sideProperForest_eq_sideCharacteristicC
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (u v : V) :
    (hardCoreLaw
      (G.induce {x | x ∈ sideProperForestVertices (G := G) R u v}) z hz).characteristic θ =
      sideCharacteristicC R z hz θ u v := by
  classical
  unfold sideProperForestVertices
  calc
    (hardCoreLaw
      (G.induce {x | x ∈ (retainedSideChildren (G := G) R u v).biUnion
        (fun w => (R.descendants (G := G) w).erase w)}) z hz).characteristic θ =
      ∏ w ∈ retainedSideChildren (G := G) R u v,
        (hardCoreLaw
          (G.induce {x | x ∈ (R.descendants (G := G) w).erase w})
          z hz).characteristic θ := by
      refine hardCoreLaw_characteristic_induceFinset_biUnion G
        (retainedSideChildren (G := G) R u v)
        (fun w => (R.descendants (G := G) w).erase w) ?_ ?_ z θ hz
      · intro w hw y hy hwy
        change Disjoint ((R.descendants (G := G) w).erase w)
          ((R.descendants (G := G) y).erase y)
        rw [Finset.disjoint_left]
        intro x hxw hxy
        exact (Finset.disjoint_left.mp
          (R.children_pairwiseDisjoint_descendants (G := G) hG u
            (Finset.mem_of_mem_erase hw) (Finset.mem_of_mem_erase hy) hwy))
          (Finset.mem_of_mem_erase hxw) (Finset.mem_of_mem_erase hxy)
      · intro w hw y hy hwy x t hx ht
        exact R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u w).mp (Finset.mem_of_mem_erase hw))
          ((R.mem_children (G := G) u y).mp (Finset.mem_of_mem_erase hy))
          hwy
          ((R.mem_descendants (G := G) w x).mp (Finset.mem_of_mem_erase hx))
          ((R.mem_descendants (G := G) y t).mp (Finset.mem_of_mem_erase ht))
    _ = ∏ w ∈ retainedSideChildren (G := G) R u v,
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) w) (R.subtreeRoot (G := G) w))
          z hz).characteristic θ := by
      apply Finset.prod_congr rfl
      intro w hw
      exact (hardCoreLaw_characteristic_iso
        (ActualRootedVariance.ComponentRooting.deleteSubtreeRootIsoProperDescendants
          (G := G) R w) z θ hz).symm
    _ = sideCharacteristicC R z hz θ u v := by
      rfl

/-- Exact root-deletion mixture for the artificial side-root subtree, with
both deleted factors identified with the concrete transfer factors `a` and
`c`. -/
theorem artificialSideRoot_characteristic_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    (Rs.subtreeLawAt z hz r).characteristic θ =
      (rootedVacancyProbabilityAt Rs z r : ℂ) *
          sideCharacteristicA R z hz θ u v +
        (rootedOccupationProbabilityAt Rs z r : ℂ) *
          (FiniteLatticeLaw.phase θ 1 * sideCharacteristicC R z hz θ u v) := by
  classical
  dsimp
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let T := Rs.Subtree (G := H) r
  let tr := Rs.subtreeRoot (G := H) r
  have hmix := hardCoreLaw_characteristic_vertexDeletion T tr z θ hz
  rw [hardCoreLaw_characteristic_iso
      (deleteArtificialSideRootSubtreeIsoSideForest (G := G) R u v) z θ hz,
    hardCoreLaw_characteristic_sideForest_eq_sideCharacteristicA hG R z hz θ u v,
    hardCoreLaw_characteristic_iso
      (deleteClosedArtificialSideRootSubtreeIsoProperSideForest
        (G := G) hG R u v) z θ hz,
    hardCoreLaw_characteristic_sideProperForest_eq_sideCharacteristicC
      hG R z hz θ u v] at hmix
  simpa [T, tr, H, Rs, r,
    ActualRootedVariance.ComponentRooting.subtreeLawAt,
    rootedVacancyProbabilityAt, rootedOccupationProbabilityAt,
    UniformFourthMoment.rootedQAt, UniformFourthMoment.rootedAAt,
    UniformFourthMoment.rootedPAt] using hmix

/-- Concrete chordal A.48 on the artificial side-root tree.  This is
zero-safe: no argument of `a` or `c` is selected. -/
theorem artificialSideRoot_chordal_coercivity
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (u v : V) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    let q := rootedVacancyProbabilityAt Rs z r
    let b := rootedOccupationProbabilityAt Rs z r
    let a := sideCharacteristicA R z hz θ u v
    let c := sideCharacteristicC R z hz θ u v
    let phase := FiniteLatticeLaw.phase θ 1
    sideRootGapConstant Z * b * Real.sin (θ / 2) ^ 2 ≤
      q * (1 - ‖a‖ ^ 2) + b * (1 - ‖c‖ ^ 2) +
        q * b * ‖a - phase * c‖ ^ 2 := by
  classical
  dsimp
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let q := rootedVacancyProbabilityAt Rs z r
  let b := rootedOccupationProbabilityAt Rs z r
  let a := sideCharacteristicA R z hz θ u v
  let c := sideCharacteristicC R z hz θ u v
  let phase := FiniteLatticeLaw.phase θ 1
  let m := ‖(q : ℂ) * a + (b : ℂ) * (phase * c)‖
  have hHacyc : H.IsAcyclic := by
    dsimp [H, sideRootGraph]
    exact hG.induce _
  have hgap := occupation_mul_sin_sq_le_rootedCharacteristic_defect
    hHacyc Rs Z z θ hz hzZ hθ r
  have hmix := artificialSideRoot_characteristic_eq hG R z hz θ u v
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (rootedVacancyProbabilityAt_pos Rs z hz r).le
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos Rs z hz r).le
  have hqb : q + b = 1 := by
    dsimp [q, b]
    linarith [rootedOccupationProbabilityAt_add_vacancy Rs z hz r]
  have ha1 : ‖a‖ ≤ 1 := by
    dsimp [a]
    exact norm_sideCharacteristicA_le_one R z hz θ u v
  have hc1 : ‖c‖ ≤ 1 := by
    dsimp [c]
    exact norm_sideCharacteristicC_le_one R z hz θ u v
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase]
    exact FiniteLatticeLaw.norm_phase θ 1
  have hm0 : 0 ≤ m := norm_nonneg _
  have hm1 : m ≤ 1 := by
    dsimp [m]
    calc
      ‖(q : ℂ) * a + (b : ℂ) * (phase * c)‖ ≤
          ‖(q : ℂ) * a‖ + ‖(b : ℂ) * (phase * c)‖ := norm_add_le _ _
      _ = q * ‖a‖ + b * ‖c‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0,
          norm_mul, hphase, one_mul]
      _ ≤ q * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left ha1 hq0)
        (mul_le_mul_of_nonneg_left hc1 hb0)
      _ = 1 := by linarith
  have hid := weighted_norm_sq_identity q b a (phase * c) hq0 hb0 hqb
  rw [norm_mul, hphase, one_mul] at hid
  have henergy :
      q * (1 - ‖a‖ ^ 2) + b * (1 - ‖c‖ ^ 2) +
          q * b * ‖a - phase * c‖ ^ 2 = 1 - m ^ 2 := by
    dsimp [m]
    rw [hid]
    nlinarith [hqb]
  have hlinear_sq : 1 - m ≤ 1 - m ^ 2 := by
    nlinarith [hm0, hm1]
  change sideRootGapConstant Z * b * Real.sin (θ / 2) ^ 2 ≤ _
  calc
    sideRootGapConstant Z * b * Real.sin (θ / 2) ^ 2 ≤ 1 - m := by
      dsimp [m]
      rw [← hmix]
      simpa [H, Rs, r, b] using hgap
    _ ≤ 1 - m ^ 2 := hlinear_sq
    _ = q * (1 - ‖a‖ ^ 2) + b * (1 - ‖c‖ ^ 2) +
          q * b * ‖a - phase * c‖ ^ 2 := henergy.symm

/-- Comparison between the artificial side-root Bernoulli weights and the
actual weight at `u`.  The comparison loses only the uniform vacancy floor. -/
theorem artificialSideRoot_weights_compare_actual
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    {u v : V} (huv : R.IsChild (G := G) u v) :
    let H := sideRootGraph (G := G) R u v
    let Rs := sideComponentRooting (G := G) R u v
    let r := artificialSideRoot (G := G) R u v
    let qS := rootedVacancyProbabilityAt Rs z r
    let bS := rootedOccupationProbabilityAt Rs z r
    let q := rootedVacancyProbabilityAt R z u
    let b := rootedOccupationProbabilityAt R z u
    (1 / (1 + Z)) * bS ≤ b ∧ b ≤ bS ∧ qS ≤ q := by
  classical
  dsimp
  let η : ℝ := 1 / (1 + Z)
  let Q := sideVacancyProduct R z u v
  let x := z * Q
  let qv := rootedVacancyProbabilityAt R z v
  let y := x * qv
  let q := rootedVacancyProbabilityAt R z u
  let b := rootedOccupationProbabilityAt R z u
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let qS := rootedVacancyProbabilityAt Rs z r
  let bS := rootedOccupationProbabilityAt Rs z r
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hη : 0 < η := by dsimp [η]; positivity
  have hQ : 0 < Q := sideVacancyProduct_pos R z hz u v
  have hx : 0 < x := mul_pos hz hQ
  have hqvη : η ≤ qv := by
    dsimp [η, qv]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ v
  have hqv1 : qv ≤ 1 := rootedVacancyProbabilityAt_le_one R z hz v
  have hq0 : 0 < q := rootedVacancyProbabilityAt_pos R z hz u
  have hfull : b = q * x * qv := by
    calc
      b = q * z * qv * Q := by
        dsimp [b, q, qv, Q]
        exact rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_child_vacancy_mul_side
          hG R z hz huv
      _ = q * x * qv := by dsimp [x]; ring
  have hsum : q + b = 1 := by
    dsimp [q, b]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u]
  have hsideB : bS = x / (1 + x) := by
    dsimp [bS, x, Q, Rs, r, H]
    exact artificialSideRoot_occupation_eq hG R z hz u v
  have hsideQ : qS = 1 / (1 + x) := by
    dsimp [qS, x, Q, Rs, r, H]
    exact artificialSideRoot_vacancy_eq hG R z hz u v
  have hsideSum : qS + bS = 1 := by
    dsimp [qS, bS]
    linarith [rootedOccupationProbabilityAt_add_vacancy Rs z hz r]
  have hyx : y ≤ x := by
    dsimp [y]
    nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hqv1)]
  have hqy : q * (1 + y) = 1 := by
    dsimp [y]
    rw [hfull] at hsum
    nlinarith
  have hqSideLe : qS ≤ q := by
    rw [hsideQ]
    apply (div_le_iff₀ (by linarith [hx])).2
    have hmul := mul_le_mul_of_nonneg_left hyx hq0.le
    nlinarith [hqy]
  have hbLe : b ≤ bS := by linarith [hsum, hsideSum, hqSideLe]
  have hbSideProd : bS = qS * x := by
    rw [hsideB, hsideQ]
    have hden : 1 + x ≠ 0 := (by linarith [hx] : 0 < 1 + x).ne'
    field_simp [hden]
  have hbLower : η * bS ≤ b := by
    calc
      η * bS = η * (qS * x) := by rw [hbSideProd]
      _ ≤ qv * (qS * x) :=
        mul_le_mul_of_nonneg_right hqvη (mul_nonneg
          (by exact (rootedVacancyProbabilityAt_pos Rs z hz r).le) hx.le)
      _ ≤ qv * (q * x) := by
        apply mul_le_mul_of_nonneg_left _ (le_trans hη.le hqvη)
        exact mul_le_mul_of_nonneg_right hqSideLe hx.le
      _ = b := by rw [hfull]; ring
  exact ⟨by simpa [η] using hbLower, hbLe, hqSideLe⟩

/-- Concrete A.48 for the genuine transfer coefficient on `u → v`.
The coefficient is uniform in the forest and loses only one additional vacancy
floor when the artificial side-root weights are compared with the actual root
weights. -/
theorem actualTransferCoefficient_chordal_coercivity
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    {u v : V} (huv : R.IsChild (G := G) u v) :
    sideRootGapConstant Z * (1 / (1 + Z)) *
        rootedOccupationProbabilityAt R z u * Real.sin (θ / 2) ^ 2 ≤
      let K := actualTransferCoefficient R z hz θ u v
      K.q * (1 - ‖K.a‖ ^ 2) + K.b * (1 - ‖K.c‖ ^ 2) +
        K.q * K.b * ‖K.a - K.phase * K.c‖ ^ 2 := by
  classical
  let η : ℝ := 1 / (1 + Z)
  let H := sideRootGraph (G := G) R u v
  let Rs := sideComponentRooting (G := G) R u v
  let r := artificialSideRoot (G := G) R u v
  let qS := rootedVacancyProbabilityAt Rs z r
  let bS := rootedOccupationProbabilityAt Rs z r
  let q := rootedVacancyProbabilityAt R z u
  let b := rootedOccupationProbabilityAt R z u
  let a := sideCharacteristicA R z hz θ u v
  let c := sideCharacteristicC R z hz θ u v
  let phase := FiniteLatticeLaw.phase θ 1
  let ra := 1 - ‖a‖ ^ 2
  let rc := 1 - ‖c‖ ^ 2
  let d := ‖a - phase * c‖ ^ 2
  let Eside := qS * ra + bS * rc + qS * bS * d
  let E := q * ra + b * rc + q * b * d
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact (div_le_one (by linarith)).2 (by linarith)
  have hκ0 : 0 ≤ sideRootGapConstant Z := by
    unfold sideRootGapConstant
    exact mul_nonneg (uniformGapConstant_nonneg hZ.le) (sq_nonneg _)
  have hh0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
  have hqS0 : 0 ≤ qS := by
    dsimp [qS]
    exact (rootedVacancyProbabilityAt_pos Rs z hz r).le
  have hbS0 : 0 ≤ bS := by
    dsimp [bS]
    exact (rootedOccupationProbabilityAt_pos Rs z hz r).le
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (rootedVacancyProbabilityAt_pos R z hz u).le
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hra0 : 0 ≤ ra := by
    dsimp [ra, a]
    have ha := norm_sideCharacteristicA_le_one R z hz θ u v
    nlinarith [norm_nonneg (sideCharacteristicA R z hz θ u v)]
  have hrc0 : 0 ≤ rc := by
    dsimp [rc, c]
    have hc := norm_sideCharacteristicC_le_one R z hz θ u v
    nlinarith [norm_nonneg (sideCharacteristicC R z hz θ u v)]
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hcomp := artificialSideRoot_weights_compare_actual
    hG R Z z hz hzZ huv
  have hbLower : η * bS ≤ b := by
    simpa [η, H, Rs, r, qS, bS, q, b] using hcomp.1
  have hbUpper : b ≤ bS := by
    simpa [H, Rs, r, qS, bS, q, b] using hcomp.2.1
  have hqLower : qS ≤ q := by
    simpa [H, Rs, r, qS, bS, q, b] using hcomp.2.2
  have hηqS : η * qS ≤ q := by
    calc
      η * qS ≤ 1 * qS := mul_le_mul_of_nonneg_right hη1 hqS0
      _ = qS := one_mul qS
      _ ≤ q := hqLower
  have hqa : η * (qS * ra) ≤ q * ra := by
    nlinarith [mul_le_mul_of_nonneg_right hηqS hra0]
  have hbc : η * (bS * rc) ≤ b * rc := by
    nlinarith [mul_le_mul_of_nonneg_right hbLower hrc0]
  have hqb : η * (qS * bS * d) ≤ q * b * d := by
    have h1 : η * (qS * bS) ≤ qS * b := by
      have := mul_le_mul_of_nonneg_left hbLower hqS0
      nlinarith
    have h2 : qS * b ≤ q * b := mul_le_mul_of_nonneg_right hqLower hb0
    have h3 : η * (qS * bS) ≤ q * b := h1.trans h2
    nlinarith [mul_le_mul_of_nonneg_right h3 hd0]
  have henergyScale : η * Eside ≤ E := by
    dsimp [Eside, E]
    nlinarith [hqa, hbc, hqb]
  have hside : sideRootGapConstant Z * bS * Real.sin (θ / 2) ^ 2 ≤ Eside := by
    dsimp [Eside, qS, bS, a, c, phase, ra, rc, d, H, Rs, r]
    exact artificialSideRoot_chordal_coercivity hG R Z z θ hz hzZ hθ u v
  have hleft :
      sideRootGapConstant Z * η * b * Real.sin (θ / 2) ^ 2 ≤
        η * (sideRootGapConstant Z * bS * Real.sin (θ / 2) ^ 2) := by
    have hm := mul_le_mul_of_nonneg_left hbUpper
      (mul_nonneg (mul_nonneg hκ0 hη0) hh0)
    nlinarith
  have hscaledSide :
      η * (sideRootGapConstant Z * bS * Real.sin (θ / 2) ^ 2) ≤
        η * Eside := mul_le_mul_of_nonneg_left hside hη0
  change sideRootGapConstant Z * η * b * Real.sin (θ / 2) ^ 2 ≤ E
  exact hleft.trans (hscaledSide.trans henergyScale)

/-- Explicit uniform constant in the concrete two-row occupation payment. -/
noncomputable def occupationTwoRowConstant (Z : ℝ) : ℝ :=
  let η := 1 / (1 + Z)
  (64 / η ^ 2) / (sideRootGapConstant Z * η)

/-- Concrete A.52 before relative-decrement normalization. -/
theorem actualTransferCoefficient_two_row_occupation_payment
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    {u v s t : V} (huv : R.IsChild (G := G) u v)
    (hst : R.IsChild (G := G) s t) (row : ComplexRow) :
    ‖row.fst‖ * rootedOccupationProbabilityAt R z u * Real.sin (θ / 2) ^ 2 ≤
      occupationTwoRowConstant Z *
        ((row.normOne -
            ((actualTransferCoefficient R z hz θ u v).applyRow row).normOne) +
          (((actualTransferCoefficient R z hz θ u v).applyRow row).normOne -
            ((actualTransferCoefficient R z hz θ s t).applyRow
              ((actualTransferCoefficient R z hz θ u v).applyRow row)).normOne)) := by
  let η : ℝ := 1 / (1 + Z)
  let κ := sideRootGapConstant Z
  let K := actualTransferCoefficient R z hz θ u v
  let J := actualTransferCoefficient R z hz θ s t
  let X := ‖row.fst‖
  let b := rootedOccupationProbabilityAt R z u
  let h := Real.sin (θ / 2) ^ 2
  let D := (row.normOne - (K.applyRow row).normOne) +
    ((K.applyRow row).normOne - (J.applyRow (K.applyRow row)).normOne)
  let E := K.q * (1 - ‖K.a‖ ^ 2) + K.b * (1 - ‖K.c‖ ^ 2) +
    K.q * K.b * ‖K.a - K.phase * K.c‖ ^ 2
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < κ := by
    dsimp [κ, sideRootGapConstant]
    exact mul_pos (uniformGapConstant_pos hZ) (sq_pos_of_pos hη)
  have hden : 0 < κ * η := mul_pos hκ hη
  have hK : K.Admissible := actualTransferCoefficient_admissible R z hz θ u v
  have hJ : J.Admissible := actualTransferCoefficient_admissible R z hz θ s t
  have hqK : η ≤ K.q := by
    dsimp [η, K, actualTransferCoefficient]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ u
  have hqJ : η ≤ J.q := by
    dsimp [η, J, actualTransferCoefficient]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ s
  have hA48 : κ * η * b * h ≤ E := by
    dsimp [κ, η, b, h, E, K]
    exact actualTransferCoefficient_chordal_coercivity hG R Z z θ hz hzZ hθ huv
  have htwo : X * E ≤ (64 / η ^ 2) * D := by
    dsimp [X, E, D, K, J]
    exact two_row_chordal_payment _ _ row η hK hJ hη hqK hqJ
  have hchain : (κ * η) * (X * b * h) ≤ (64 / η ^ 2) * D := by
    calc
      (κ * η) * (X * b * h) = X * (κ * η * b * h) := by ring
      _ ≤ X * E := mul_le_mul_of_nonneg_left hA48 (norm_nonneg _)
      _ ≤ (64 / η ^ 2) * D := htwo
  change X * b * h ≤ occupationTwoRowConstant Z * D
  calc
    X * b * h ≤ ((64 / η ^ 2) * D) / (κ * η) :=
      (le_div_iff₀ hden).2 (by simpa [mul_comm] using hchain)
    _ = occupationTwoRowConstant Z * D := by
      dsimp [occupationTwoRowConstant, η, κ]
      field_simp
      <;> ring

/-- Uniform comparison constant for occupations at two consecutive path
vertices, with the intervening side logarithmic barrier as slack. -/
noncomputable def actualOccupationShiftConstant (Z : ℝ) : ℝ :=
  Real.exp 1 * (1 + Z) ^ 2 + 1

/-- A barrier-assisted version of (A.53): the occupation at the child is
controlled by the occupation at the parent plus the side barrier at the
parent.  This form avoids any phase case split later. -/
theorem child_occupation_le_parent_add_sideBarrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    {u v : V} (huv : R.IsChild (G := G) u v) :
    rootedOccupationProbabilityAt R z v ≤
      actualOccupationShiftConstant Z *
        (rootedOccupationProbabilityAt R z u + sideLogBarrier R z u v) := by
  let η : ℝ := 1 / (1 + Z)
  let q := rootedVacancyProbabilityAt R z u
  let qv := rootedVacancyProbabilityAt R z v
  let b := rootedOccupationProbabilityAt R z u
  let bv := rootedOccupationProbabilityAt R z v
  let Q := sideVacancyProduct R z u v
  let Λ := sideLogBarrier R z u v
  let A := Real.exp 1 * (1 + Z) ^ 2
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hη : 0 < η := by dsimp [η]; positivity
  have hqη : η ≤ q := by
    dsimp [η, q]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ u
  have hqvη : η ≤ qv := by
    dsimp [η, qv]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt hG R z Z hz hzZ v
  have hQ0 : 0 < Q := sideVacancyProduct_pos R z hz u v
  have hΛ0 : 0 ≤ Λ := by
    dsimp [Λ]
    exact sideLogBarrier_nonneg R z hz u v
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hbv0 : 0 ≤ bv := by
    dsimp [bv]
    exact (rootedOccupationProbabilityAt_pos R z hz v).le
  have hbv1 : bv ≤ 1 := by
    dsimp [bv]
    exact rootedOccupationProbabilityAt_le_one R z hz v
  have hbvz : bv ≤ z := by
    have h := rootedOccupationProbabilityAt_le_z_mul_prod_child_vacancy
      hG R z hz v
    have hp :
        (∏ w ∈ R.children (G := G) v,
          rootedVacancyProbabilityAt R z w) ≤ 1 := by
      apply Finset.prod_le_one
      · intro w hw
        exact (rootedVacancyProbabilityAt_pos R z hz w).le
      · intro w hw
        exact rootedVacancyProbabilityAt_le_one R z hz w
    calc
      bv ≤ z * ∏ w ∈ R.children (G := G) v,
          rootedVacancyProbabilityAt R z w := by simpa [bv] using h
      _ ≤ z * 1 := mul_le_mul_of_nonneg_left hp hz.le
      _ = z := mul_one z
  have hrec : b = q * z * qv * Q := by
    dsimp [b, q, qv, Q]
    exact rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_child_vacancy_mul_side
      hG R z hz huv
  have hlower : η ^ 2 * z * Q ≤ b := by
    rw [hrec]
    have hq0 : 0 ≤ q := le_trans hη.le hqη
    have hqq : η ^ 2 ≤ q * qv := by
      simpa [pow_two] using mul_le_mul hqη hqvη hη.le hq0
    nlinarith [mul_le_mul_of_nonneg_right hqq (mul_nonneg hz.le hQ0.le)]
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    have he : 1 ≤ Real.exp 1 := (Real.one_le_exp_iff).2 (by norm_num)
    have hs : 1 ≤ (1 + Z) ^ 2 := by nlinarith
    nlinarith [mul_le_mul he hs (by norm_num : (0 : ℝ) ≤ 1) (Real.exp_pos 1).le]
  by_cases hsmall : Λ ≤ 1
  · have hQexp : Real.exp (-Λ) = Q := by
      dsimp [Λ, Q]
      exact exp_neg_sideLogBarrier_eq_sideVacancyProduct R z hz u v
    have hexp : Real.exp (-1) ≤ Q := by
      rw [← hQexp]
      exact Real.exp_le_exp.mpr (by linarith)
    have hlower' : η ^ 2 * z * Real.exp (-1) ≤ b := by
      calc
        η ^ 2 * z * Real.exp (-1) ≤ η ^ 2 * z * Q :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg (sq_nonneg _) hz.le)
        _ ≤ b := hlower
    have hAz : z ≤ A * b := by
      have hm := mul_le_mul_of_nonneg_left hlower' hA0
      have hid : A * (η ^ 2 * z * Real.exp (-1)) = z := by
        dsimp [A, η]
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero, (by linarith : 1 + Z ≠ 0)]
        <;> ring
      calc
        z = A * (η ^ 2 * z * Real.exp (-1)) := hid.symm
        _ ≤ A * b := hm
    change bv ≤ (A + 1) * (b + Λ)
    calc
      bv ≤ z := hbvz
      _ ≤ A * b := hAz
      _ ≤ (A + 1) * (b + Λ) := by nlinarith [mul_nonneg hA0 hΛ0]
      _ = actualOccupationShiftConstant Z * (b + Λ) := by
        rfl
  · have hΛ1 : 1 ≤ Λ := le_of_not_ge hsmall
    change bv ≤ (A + 1) * (b + Λ)
    calc
      bv ≤ 1 := hbv1
      _ ≤ Λ := hΛ1
      _ ≤ (A + 1) * (b + Λ) := by
        have hsum : Λ ≤ b + Λ := by linarith
        exact hsum.trans (by
          have := mul_le_mul_of_nonneg_right hA1 (add_nonneg hb0 hΛ0)
          nlinarith)
      _ = actualOccupationShiftConstant Z * (b + Λ) := by rfl

end
end AppendixA
end Forest
end Erdos993
