import Erdos993.Forest.TransferMatrixContraction
import Erdos993.Forest.IndependentComponentFourier

/-!
# Exact characteristic identities for actual transfer paths

This module supplies the exact rooted Q/R factorization and identifies the
concrete transfer amplitude of Appendix A with the characteristic function of
the starting descendant subtree.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA9 (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtypeA9 {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Public structural realization of the closed-root deletion of an actual
rooted descendant subtree.  It is the disjoint union of the proper-descendant
forests of the root's children. -/
noncomputable def _root_.Erdos993.ActualRootedVariance.ComponentRooting.deleteClosedSubtreeRootIsoProperChildUnion
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ (R.children (G := G) u).biUnion
        (fun v => R.properDescendants (G := G) v)} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u ∧
          ¬ (R.Subtree (G := G) u).Adj (R.subtreeRoot (G := G) u) x} ≃
      {x : V // x ∈ (R.children (G := G) u).biUnion
        (fun v => R.properDescendants (G := G) v)} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          rw [Finset.mem_biUnion]
          have hxdesc := (R.mem_descendants (G := G) u x.1.1).mp x.1.2
          rcases (R.isDescendant_iff_eq_or_child_descendant (G := G) u x.1.1).mp hxdesc with
            hxu | ⟨v, huv, hvx⟩
          · exact (x.2.1 (Subtype.ext hxu.symm)).elim
          · refine ⟨v, (R.mem_children (G := G) _ _).mpr huv,
              Finset.mem_erase.mpr ⟨?_,
                (R.mem_descendants (G := G) _ _).mpr hvx⟩⟩
            intro hxv
            exact x.2.2 (by
              change G.Adj u x.1.1
              simpa [hxv] using huv.1)⟩
      invFun := fun y =>
        ⟨⟨y.1, by
            have hyprop := y.property
            rw [Finset.mem_biUnion] at hyprop
            obtain ⟨v, hv, hy⟩ := hyprop
            exact (R.mem_descendants (G := G) _ _).mpr
              (R.child_descendant (G := G) ((R.mem_children (G := G) _ _).mp hv)
                ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2))⟩,
          by
            have hyprop := y.property
            rw [Finset.mem_biUnion] at hyprop
            obtain ⟨v, hv, hy⟩ := hyprop
            have huv := (R.mem_children (G := G) _ _).mp hv
            have hyv := (R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2
            have hyvne : y.1 ≠ v := (Finset.mem_erase.mp hy).1
            constructor
            · intro hyu
              have : y.1 = u := congrArg Subtype.val hyu
              exact (R.not_mem_descendants_child (G := G) huv)
                (this ▸ (Finset.mem_erase.mp hy).2)
            · intro hadj
              change G.Adj u y.1 at hadj
              have huy : R.IsChild (G := G) u y.1 :=
                (ComponentRooting.adj_of_descendant_iff_isChild (G := G) hG R
                  (R.child_descendant (G := G) huv hyv)).mp hadj
              have heq : v = y.1 :=
                ComponentRooting.child_eq_of_common_descendant (G := G) hG R
                  huv huy hyv Relation.ReflTransGen.refl
              exact hyvne heq.symm⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  rfl

/-- Exact complex characteristic factorization of the root-vacant forest over
actual child descendant subtrees. -/
theorem hardCoreLaw_characteristic_deleteSubtreeRoot_eq_prod_children
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).characteristic θ =
      ∏ v ∈ R.children (G := G) u,
        (R.subtreeLawAt z hz v).characteristic θ := by
  classical
  rw [hardCoreLaw_characteristic_iso
    (R.deleteSubtreeRootIsoChildren (G := G) u) z θ hz]
  simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
    hardCoreLaw_characteristic_induceFinset_biUnion
      G (R.children (G := G) u)
      (fun v => R.descendants (G := G) v)
      (R.children_pairwiseDisjoint_descendants (G := G) hG u)
      (fun i hi j hj hij x y hx hy =>
        R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u i).mp hi)
          ((R.mem_children (G := G) u j).mp hj) hij
          ((R.mem_descendants (G := G) i x).mp hx)
          ((R.mem_descendants (G := G) j y).mp hy)) z θ hz

/-- Exact complex characteristic factorization of the closed-root deletion over
the root-vacant forests of the children. -/
theorem hardCoreLaw_characteristic_deleteClosedSubtreeRoot_eq_prod_childVacant
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (hardCoreLaw
      (deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u)) z hz).characteristic θ =
      ∏ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z hz).characteristic θ := by
  classical
  rw [hardCoreLaw_characteristic_iso
    (R.deleteClosedSubtreeRootIsoProperChildUnion (G := G) hG u) z θ hz]
  have hfac := hardCoreLaw_characteristic_induceFinset_biUnion
    G (R.children (G := G) u)
      (fun v => R.properDescendants (G := G) v)
      (fun i hi j hj hij =>
        (R.children_pairwiseDisjoint_descendants (G := G) hG u hi hj hij).mono
          (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      (fun i hi j hj hij x y hx hy =>
        R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u i).mp hi)
          ((R.mem_children (G := G) u j).mp hj) hij
          ((R.mem_descendants (G := G) i x).mp (Finset.mem_erase.mp hx).2)
          ((R.mem_descendants (G := G) j y).mp (Finset.mem_erase.mp hy).2)) z θ hz
  calc
    (hardCoreLaw
        (G.induce {x | x ∈ (R.children (G := G) u).biUnion
          (fun v => R.properDescendants (G := G) v)}) z hz).characteristic θ =
      ∏ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (G.induce (↑(R.properDescendants (G := G) v) : Set V))
          z hz).characteristic θ := by
            simpa only [Set.mem_setOf_eq] using hfac
    _ = ∏ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z hz).characteristic θ := by
      apply Finset.prod_congr rfl
      intro v hv
      exact (hardCoreLaw_characteristic_iso
        (R.deleteSubtreeRootIsoProperDescendants (G := G) v) z θ hz).symm

/-- The vacant characteristic at a parent splits into the distinguished child
and its side-child product. -/
theorem vacantCharacteristic_eq_side_mul_child
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).characteristic θ =
      sideCharacteristicA R z hz θ u v *
        (R.subtreeLawAt z hz v).characteristic θ := by
  classical
  rw [hardCoreLaw_characteristic_deleteSubtreeRoot_eq_prod_children hG R z θ hz u]
  have hv : v ∈ R.children (G := G) u := (R.mem_children (G := G) u v).mpr huv
  rw [← Finset.prod_erase_mul _ _ hv]
  rfl

/-- The occupied-root remainder characteristic at a parent splits into the
vacant characteristic of the distinguished child and its side-child product. -/
theorem occupiedCharacteristic_eq_side_mul_childVacant
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    (hardCoreLaw
      (deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u)) z hz).characteristic θ =
      sideCharacteristicC R z hz θ u v *
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z hz).characteristic θ := by
  classical
  rw [hardCoreLaw_characteristic_deleteClosedSubtreeRoot_eq_prod_childVacant
    hG R z θ hz u]
  have hv : v ∈ R.children (G := G) u := (R.mem_children (G := G) u v).mpr huv
  rw [← Finset.prod_erase_mul _ _ hv]
  rfl

/-- Exact probability-normalized root characteristic recursion on every actual
descendant subtree. -/
theorem subtreeCharacteristic_eq_vacant_add_occupied
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u : V) :
    (R.subtreeLawAt z hz u).characteristic θ =
      (rootedVacancyProbabilityAt R z u : ℂ) *
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) z hz).characteristic θ +
      (rootedOccupationProbabilityAt R z u : ℂ) *
        (FiniteLatticeLaw.phase θ 1 *
          (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).characteristic θ) := by
  simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt,
    rootedVacancyProbabilityAt, rootedOccupationProbabilityAt,
    UniformFourthMoment.rootedQAt, UniformFourthMoment.rootedAAt,
    mul_div_assoc] using
    hardCoreLaw_characteristic_vertexDeletion
      (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) z θ hz

/-- The two actual rooted characteristics propagated by the transfer matrix. -/
noncomputable def rootedCharacteristicVector
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u : V) : ComplexRow :=
  ⟨(R.subtreeLawAt z hz u).characteristic θ,
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u)) z hz).characteristic θ⟩

/-- One actual transfer step preserves pairing with the two rooted
characteristics. -/
theorem actualTransferCoefficient_pair_characteristics
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) {u v : V}
    (huv : R.IsChild (G := G) u v) (r : ComplexRow) :
    ((actualTransferCoefficient R z hz θ u v).applyRow r).pair
        (rootedCharacteristicVector R z hz θ v) =
      r.pair (rootedCharacteristicVector R z hz θ u) := by
  unfold rootedCharacteristicVector
  rw [subtreeCharacteristic_eq_vacant_add_occupied R z θ hz u,
    vacantCharacteristic_eq_side_mul_child hG R z θ hz huv,
    occupiedCharacteristic_eq_side_mul_childVacant hG R z θ hz huv]
  simp only [rootedCharacteristicVector, TransferCoefficient.applyRow, ComplexRow.pair,
    actualTransferCoefficient]
  ring

/-- Last element of `u :: rest`, in a proof-independent recursive form. -/
def terminalFrom (u : V) : List V → V
  | [] => u
  | v :: rest => terminalFrom v rest

/-- The recursive terminal agrees with `List.getLast`. -/
theorem terminalFrom_eq_getLast (u : V) : ∀ rest : List V,
    terminalFrom u rest = (u :: rest).getLast (by simp)
  | [] => rfl
  | v :: rest => by
      simpa [terminalFrom] using terminalFrom_eq_getLast v rest

/-- Applying all concrete transfer matrices along a nonempty child chain
preserves the pairing with the terminal and initial rooted characteristic
vectors. -/
theorem applyTransferList_pair_characteristics
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) :
    ∀ (u : V) (rest : List V),
      (u :: rest).IsChain (R.IsChild (G := G)) → ∀ r : ComplexRow,
      (applyTransferList r
          (actualTransferCoefficients R z hz θ (u :: rest))).pair
          (rootedCharacteristicVector R z hz θ (terminalFrom u rest)) =
        r.pair (rootedCharacteristicVector R z hz θ u)
  | u, [], _, r => rfl
  | u, v :: rest, hchain, r => by
      simp only [actualTransferCoefficients, applyTransferList_cons, terminalFrom]
      have hchain' : R.IsChild (G := G) u v ∧
          (v :: rest).IsChain (R.IsChild (G := G)) := by
        simpa only [List.isChain_cons_cons] using hchain
      calc
        (applyTransferList
            ((actualTransferCoefficient R z hz θ u v).applyRow r)
            (actualTransferCoefficients R z hz θ (v :: rest))).pair
            (rootedCharacteristicVector R z hz θ (terminalFrom v rest)) =
          ((actualTransferCoefficient R z hz θ u v).applyRow r).pair
            (rootedCharacteristicVector R z hz θ v) :=
          applyTransferList_pair_characteristics hG R z θ hz
            v rest hchain'.2
            ((actualTransferCoefficient R z hz θ u v).applyRow r)
        _ = r.pair (rootedCharacteristicVector R z hz θ u) :=
          actualTransferCoefficient_pair_characteristics hG R z θ hz hchain'.1 r

/-- The concrete transfer amplitude is exactly the hard-core characteristic
function of the starting descendant subtree. -/
theorem DownwardPath.actualTransferAmplitude_eq_startCharacteristic
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (P : DownwardPath R) :
    P.actualTransferAmplitude z hz θ =
      (R.subtreeLawAt z hz P.start).characteristic θ := by
  have h := applyTransferList_pair_characteristics hG R z θ hz
    P.start (P.next :: P.tail) P.isChain (⟨1, 0⟩ : ComplexRow)
  rw [terminalFrom_eq_getLast P.start (P.next :: P.tail)] at h
  simpa [DownwardPath.actualTransferAmplitude, DownwardPath.actualTransferRow,
    DownwardPath.actualBottomVector, DownwardPath.terminalVertex,
    DownwardPath.vertices, rootedCharacteristicVector, ComplexRow.pair] using h

end
end AppendixA
end Forest
end Erdos993
