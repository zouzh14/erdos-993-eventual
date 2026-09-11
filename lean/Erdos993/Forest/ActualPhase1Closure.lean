import Erdos993.Forest.ActualRootedVariance
import Erdos993.Forest.ActualSublinearDisplacement
import Erdos993.Forest.SublinearConditionalMeanAdapter
import Erdos993.Forest.ActualLocalizationAssembly
import Erdos993.Forest.FinalClosure

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators
open Filter
open ActualRootedVariance

universe u

namespace LocalRootedTree

private def listToForest : List LocalRootedTree → LocalRootedForest
  | [] => .nil
  | t :: ts => .cons t (listToForest ts)

/-- The local rooted tree obtained by retaining the actual descendant relation
of a component rooting and listing each finite child set in its canonical
order. -/
noncomputable def actualLocalTree
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (R : ComponentRooting G) (u : V) : LocalRootedTree :=
  .node (listToForest ((R.children (G := G) u).attach.toList.map
    (fun v => actualLocalTree R v.1)))
termination_by R.subtreeOrder (G := G) u
decreasing_by
  exact R.subtreeOrder_child_lt (G := G)
    ((R.mem_children (G := G) _ _).mp v.property)

private theorem forestToList_listToForest : ∀ l : List LocalRootedTree,
    forestToList (listToForest l) = l
  | [] => rfl
  | t :: ts => by simp [listToForest, forestToList, forestToList_listToForest ts]

private theorem forestOrder_listToForest (l : List LocalRootedTree) :
    forestOrder (listToForest l) = (l.map order).sum := by
  rw [forestOrder_eq_sum, forestToList_listToForest]

private theorem list_sum_toList {α : Type u}
    (s : Finset α) (f : α → ℕ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha]

private theorem list_real_sum_toList {α : Type u}
    (s : Finset α) (f : α → ℝ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha]

private theorem list_prod_toList {α : Type u}
    (s : Finset α) (f : α → ℝ) :
    (s.toList.map f).prod = ∏ x ∈ s, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha]

private theorem vacancyProduct_listToForest (z : ℝ) :
    ∀ l : List LocalRootedTree,
      vacancyProduct z (listToForest l) =
        (l.map (fun t => (1 : ℝ) - occupation z t)).prod
  | [] => by simp [listToForest, vacancyProduct]
  | t :: ts => by
      simp [listToForest, vacancyProduct, occupation,
        vacancyProduct_listToForest z ts]

private theorem actualLocalTree_order
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    order (actualLocalTree R u) = R.subtreeOrder (G := G) u := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [actualLocalTree]
      simp only [order, forestOrder_listToForest, List.map_map]
      change 1 + ((R.children (G := G) u).attach.toList.map
        (fun v => order (actualLocalTree R v.1))).sum = n
      rw [show ((R.children (G := G) u).attach.toList.map
          (fun v => order (actualLocalTree R v.1))).sum =
          ∑ v ∈ R.children (G := G) u,
            R.subtreeOrder (G := G) v by
        classical
        calc
          ((R.children (G := G) u).attach.toList.map
              (fun v => order (actualLocalTree R v.1))).sum =
              ∑ v ∈ (R.children (G := G) u).attach,
                order (actualLocalTree R v.1) :=
            list_sum_toList _ _
          _ = ∑ v ∈ R.children (G := G) u,
                order (actualLocalTree R v) := by
            simpa only using
              (Finset.sum_attach (R.children (G := G) u)
                (fun v => order (actualLocalTree R v)))
          _ = ∑ v ∈ R.children (G := G) u,
                R.subtreeOrder (G := G) v := by
            apply Finset.sum_congr rfl
            intro v hv
            have hlt : R.subtreeOrder (G := G) v < n := by
              rw [← horder]
              exact R.subtreeOrder_child_lt (G := G)
                ((R.mem_children (G := G) _ _).mp hv)
            have hlocal : order (actualLocalTree R v) =
                R.subtreeOrder (G := G) v := ih _ hlt v rfl
            rw [hlocal] ]
      have hdesc := R.descendants_eq_insert_biUnion_children (G := G) u
      have hnot : u ∉ (R.children (G := G) u).biUnion
          (fun v => R.descendants (G := G) v) := by
        intro hu
        obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
        exact R.not_mem_descendants_child (G := G)
          ((R.mem_children (G := G) _ _).mp hv) huv
      have hsub : R.subtreeOrder (G := G) u =
          1 + ∑ v ∈ R.children (G := G) u,
            R.subtreeOrder (G := G) v := by
        unfold ComponentRooting.subtreeOrder
        rw [hdesc, Finset.card_eq_sum_ones, Finset.sum_insert hnot,
          Finset.sum_biUnion
            (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u)]
        simp only [Finset.card_eq_sum_ones]
      rw [← horder, hsub]

private theorem actualLocalTree_occupation
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupationProbability (G := G) C u =
      occupation C.activity (actualLocalTree R u) := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      have hprod :
          ((R.children (G := G) u).attach.toList.map (fun v =>
            (1 : ℝ) - occupation C.activity (actualLocalTree R v.1))).prod =
            Finset.prod (R.children (G := G) u) (fun v =>
              (1 : ℝ) - R.occupationProbability (G := G) C v) := by
        calc
          ((R.children (G := G) u).attach.toList.map (fun v =>
              (1 : ℝ) - occupation C.activity (actualLocalTree R v.1))).prod =
              Finset.prod (R.children (G := G) u).attach (fun v =>
                (1 : ℝ) - occupation C.activity (actualLocalTree R v.1)) :=
            list_prod_toList _ _
          _ = Finset.prod (R.children (G := G) u) (fun v =>
                (1 : ℝ) - occupation C.activity (actualLocalTree R v)) := by
            simpa only using
              (Finset.prod_attach (R.children (G := G) u)
                (fun v => (1 : ℝ) - occupation C.activity (actualLocalTree R v)))
          _ = Finset.prod (R.children (G := G) u) (fun v =>
                (1 : ℝ) - R.occupationProbability (G := G) C v) := by
            apply Finset.prod_congr rfl
            intro v hv
            have hlt : R.subtreeOrder (G := G) v < n := by
              rw [← horder]
              exact R.subtreeOrder_child_lt (G := G)
                ((R.mem_children (G := G) _ _).mp hv)
            have hlocal : R.occupationProbability (G := G) C v =
                occupation C.activity (actualLocalTree R v) :=
              ih _ hlt v rfl
            rw [hlocal]
      rw [actualLocalTree]
      change R.occupationProbability (G := G) C u =
        C.activity * vacancyProduct C.activity
          (listToForest ((R.children (G := G) u).attach.toList.map
            (fun v => actualLocalTree R v.1))) /
          (1 + C.activity * vacancyProduct C.activity
            (listToForest ((R.children (G := G) u).attach.toList.map
              (fun v => actualLocalTree R v.1))))
      rw [vacancyProduct_listToForest]
      simp only [List.map_map]
      change R.occupationProbability (G := G) C u =
        C.activity *
          ((R.children (G := G) u).attach.toList.map (fun v =>
            (1 : ℝ) - occupation C.activity (actualLocalTree R v.1))).prod /
          (1 + C.activity *
            ((R.children (G := G) u).attach.toList.map (fun v =>
              (1 : ℝ) - occupation C.activity (actualLocalTree R v.1))).prod)
      rw [hprod]
      have hprodP : 0 < Finset.prod (R.children (G := G) u) (fun v =>
          R.rootedP (G := G) C v) :=
        Finset.prod_pos (fun v hv => R.rootedP_pos (G := G) C v)
      have hprodQ : 0 < Finset.prod (R.children (G := G) u) (fun v =>
          R.rootedQ (G := G) C v) :=
        Finset.prod_pos (fun v hv => R.rootedQ_pos (G := G) C v)
      have hvac :
          Finset.prod (R.children (G := G) u) (fun v =>
              (1 : ℝ) - R.occupationProbability (G := G) C v) =
            Finset.prod (R.children (G := G) u) (fun v =>
              R.rootedQ (G := G) C v) /
            Finset.prod (R.children (G := G) u) (fun v =>
              R.rootedP (G := G) C v) := by
        calc
          Finset.prod (R.children (G := G) u) (fun v =>
              (1 : ℝ) - R.occupationProbability (G := G) C v) =
            Finset.prod (R.children (G := G) u) (fun v =>
              R.vacancyProbability (G := G) C v) := by
                apply Finset.prod_congr rfl
                intro v hv
                have hsum := R.occupationProbability_add_vacancyProbability
                  (G := G) C v
                linarith
          _ = Finset.prod (R.children (G := G) u) (fun v =>
              R.rootedQ (G := G) C v) /
            Finset.prod (R.children (G := G) u) (fun v =>
              R.rootedP (G := G) C v) := by
                rw [← Finset.prod_div_distrib]
                rfl
      rw [hvac]
      unfold ComponentRooting.occupationProbability
      rw [R.rootedP_eq_rootedQ_add_rootedA (G := G) C u,
        R.rootedA_eq_activity_mul_prod_rootedQ (G := G) C u,
        R.rootedQ_eq_prod_rootedP (G := G) C u]
      field_simp [ne_of_gt hprodP]

private theorem displacementSum_listToForest (z : ℝ) :
    ∀ l : List LocalRootedTree,
      displacementSum z (listToForest l) =
        (l.map (fun t => occupation z t * displacement z t)).sum
  | [] => by rfl
  | t :: ts => by
      simp [listToForest, displacementSum, displacementSum_listToForest z ts]

private theorem actualLocalTree_displacement
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.conditionalMeanDifference (G := G) C u =
      displacement C.activity (actualLocalTree R u) := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [R.conditionalMeanDifference_eq_one_sub_sum (G := G) C u,
        actualLocalTree, displacement_recursion,
        displacementSum_listToForest]
      simp only [List.map_map]
      change 1 - Finset.sum (R.children (G := G) u) (fun v =>
          R.occupationProbability (G := G) C v *
            R.conditionalMeanDifference (G := G) C v) =
        1 - (((R.children (G := G) u).attach.toList.map (fun v =>
          occupation C.activity (actualLocalTree R v.1) *
            displacement C.activity (actualLocalTree R v.1))).sum)
      congr 1
      calc
        Finset.sum (R.children (G := G) u) (fun v =>
            R.occupationProbability (G := G) C v *
              R.conditionalMeanDifference (G := G) C v) =
          Finset.sum (R.children (G := G) u) (fun v =>
            occupation C.activity (actualLocalTree R v) *
              displacement C.activity (actualLocalTree R v)) := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [actualLocalTree_occupation C R v]
                have hlt : R.subtreeOrder (G := G) v < n := by
                  rw [← horder]
                  exact R.subtreeOrder_child_lt (G := G)
                    ((R.mem_children (G := G) _ _).mp hv)
                rw [ih _ hlt v rfl]
        _ = Finset.sum (R.children (G := G) u).attach (fun v =>
            occupation C.activity (actualLocalTree R v.1) *
              displacement C.activity (actualLocalTree R v.1)) := by
                symm
                simpa only using
                  (Finset.sum_attach (R.children (G := G) u)
                    (fun v => occupation C.activity (actualLocalTree R v) *
                      displacement C.activity (actualLocalTree R v)))
        _ = ((R.children (G := G) u).attach.toList.map (fun v =>
            occupation C.activity (actualLocalTree R v.1) *
              displacement C.activity (actualLocalTree R v.1))).sum := by
                symm
                exact list_real_sum_toList _ _

/-- The actual component-rooting observables, transported field by field to the
local rooted-tree representation used by the proved sublinear estimate. -/
noncomputable def actualSublinearConditionalMeanFieldwiseAdapterSpec :
    SublinearConditionalMeanFieldwiseAdapterSpec actualRootedForestFamily.{u} where
  localTree := fun {_V} [_] {_G} _C R v => actualLocalTree R v
  occupationProbability_eq := by
    intro V _ G C R v
    exact actualLocalTree_occupation C R v
  conditionalMeanDifference_eq := by
    intro V _ G C R v
    exact actualLocalTree_displacement C R v
  subtreeOrder_eq := by
    intro V _ G C R v
    exact (actualLocalTree_order C R v).symm

/-- The unconditional Lemma 5.1 interface for the actual componentwise-rooted
forest family. -/
noncomputable def actualSublinearConditionalMeanInterface :
    SublinearConditionalMeanInterface actualRootedForestFamily.{u} :=
  actualSublinearConditionalMeanFieldwiseAdapterSpec.toInterface

end LocalRootedTree

/-- Package the three remaining manuscript interfaces with the proved actual
rooting, actual localization, and actual sublinear conditional-mean interface. -/
noncomputable def actualVerticalClosureAssumptions
    (M : MacroscopicContributionInterface actualRootedForestFamily.{u})
    (B : OccupationBalanceInterface actualRootedForestFamily.{u})
    (S : FirstRecoveryScaleInterface.{u}) :
    VerticalClosureAssumptions.{u} where
  rootedFamily := actualRootedForestFamily.{u}
  localization := actualLocalizationInterface
  macroscopicContribution := M
  occupationBalance := B
  firstRecoveryScale := S
  sublinearConditionalMean :=
    LocalRootedTree.actualSublinearConditionalMeanInterface

/-- Eventual weak unimodality for finite forests from exactly the three
remaining Phase 1 manuscript interfaces.  Canonical activity existence,
componentwise rooting, localization, and the sublinear bound are all discharged
by compiled actual theorems. -/
theorem eventually_weaklyUnimodal_of_actualPhase1Closure
    (M : MacroscopicContributionInterface actualRootedForestFamily.{u})
    (B : OccupationBalanceInterface actualRootedForestFamily.{u})
    (S : FirstRecoveryScaleInterface.{u}) :
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        G.IsAcyclic → orderThreshold ≤ Fintype.card V →
          WeaklyUnimodal (independenceCoefficients G) := by
  apply eventually_weaklyUnimodal_of_verticalClosureAssumptions
    (actualVerticalClosureAssumptions M B S)
  · intro V _ G s hs
    obtain ⟨z, hz, _hunique⟩ :=
      existsUnique_pos_hardCoreLaw_mean_eq_firstRecovery G hs
    exact ⟨z, hz⟩
  · intro V _ G C
    exact actualRootedForestFamily_nonempty C

end
end Forest
end Erdos993
