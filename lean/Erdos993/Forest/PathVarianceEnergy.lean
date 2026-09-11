import Erdos993.Forest.RootVarianceComparison

/-!
# Descendant energy and downward paths for Appendix A

This module develops the finite rooted-path bookkeeping used in Lemma A.7.
The local energy is the genuine arbitrary-activity Bernoulli energy from
`UniformFourthMoment`; no path estimate is assumed.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance
open UniformFourthMoment

universe u

noncomputable local instance pathDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
noncomputable local instance pathFiniteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- The sum of the arbitrary-activity rooted energies in the descendant subtree
of `u`. -/
noncomputable def descendantEnergyAt (R : ComponentRooting G) (z : ℝ)
    (hz : 0 < z) (u : V) : ℝ :=
  ∑ x ∈ R.descendants (G := G) u, rootedEnergyAt R z hz x

/-- Descendant energy splits into the root energy and the energies of the
pairwise disjoint child descendant subtrees. -/
theorem descendantEnergyAt_eq_root_add_sum_children
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) :
    descendantEnergyAt R z hz u =
      rootedEnergyAt R z hz u +
        ∑ v ∈ R.children (G := G) u, descendantEnergyAt R z hz v := by
  classical
  unfold descendantEnergyAt
  rw [R.descendants_eq_insert_biUnion_children (G := G) u]
  have hrootnot : u ∉ Finset.biUnion (R.children (G := G) u)
      (R.descendants (G := G)) := by
    rw [Finset.mem_biUnion]
    push_neg
    intro v hv
    exact R.not_mem_descendants_child (G := G)
      ((R.mem_children (G := G) u v).mp hv)
  rw [Finset.sum_insert hrootnot]
  rw [Finset.sum_biUnion
    (R.children_pairwiseDisjoint_descendants (G := G) hG u)]

/-- Descendant energy is nonnegative. -/
theorem descendantEnergyAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 ≤ descendantEnergyAt R z hz u := by
  unfold descendantEnergyAt
  exact Finset.sum_nonneg fun x hx => rootedEnergyAt_nonneg R z hz x

/-- The variance mass when the subtree root is available with probability `a`.
This is the arbitrary-activity version of the mass used in the A.13 telescope. -/
noncomputable def rootedVarianceMassAt (a : ℝ) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) : ℝ :=
  a * subtreeVarianceAt R z hz u +
    (1 - a) * rootVacantVarianceAt R z hz u

/-- Exact mass recursion.  If `u` is available with probability `a`, then a
child is available with probability `1-a*b_u`. -/
theorem rootedVarianceMassAt_eq_root_add_sum_children
    (hG : G.IsAcyclic) (a : ℝ) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedVarianceMassAt a R z hz u =
      a * rootedEnergyAt R z hz u +
        ∑ v ∈ R.children (G := G) u,
          rootedVarianceMassAt
            (1 - a * rootedOccupationProbabilityAt R z u) R z hz v := by
  classical
  let p := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let vp := subtreeVarianceAt R z hz u
  let vq := rootVacantVarianceAt R z hz u
  let vr := rootOccupiedVarianceAt R z hz u
  let e := rootedEnergyAt R z hz u
  have hvp : vp = q * vq + p * vr + e := by
    change (R.subtreeLawAt z hz u).variance = _
    rw [R.subtreeVarianceAt_law_total_variance z hz u]
    simp only [occupationProbabilityAt_eq_rooted, vacancyProbabilityAt_eq_rooted]
    rfl
  have hvq : vq = ∑ v ∈ R.children (G := G) u,
      subtreeVarianceAt R z hz v := by
    exact R.vacantVarianceAt_eq_sum_subtreeVarianceAt hG z hz u
  have hvr : vr = ∑ v ∈ R.children (G := G) u,
      rootVacantVarianceAt R z hz v := by
    exact R.occupiedVarianceAt_eq_sum_vacantVarianceAt hG z hz u
  have hchild : (∑ v ∈ R.children (G := G) u,
      rootedVarianceMassAt (1 - a * p) R z hz v) =
      (1 - a * p) * vq + (a * p) * vr := by
    rw [hvq, hvr, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    unfold rootedVarianceMassAt
    dsimp only [p]
    ring
  change a * vp + (1 - a) * vq =
    a * e + ∑ v ∈ R.children (G := G) u,
      rootedVarianceMassAt (1 - a * p) R z hz v
  rw [hchild, hvp]
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hq : q = 1 - p := by
    change p + q = 1 at hpq
    linarith
  rw [hq]
  ring

/-- A variance mass with availability in `[0,1]` is bounded by raw descendant
energy. -/
theorem rootedVarianceMassAt_le_descendantEnergyAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (u : V) :
    rootedVarianceMassAt a R z hz u ≤ descendantEnergyAt R z hz u := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on
      generalizing u a with
  | h n ih =>
      let p := rootedOccupationProbabilityAt R z u
      let a' := 1 - a * p
      have hp0 : 0 ≤ p := by
        dsimp [p]
        exact (rootedOccupationProbabilityAt_pos R z hz u).le
      have hp1 : p ≤ 1 := rootedOccupationProbabilityAt_le_one R z hz u
      have hap1 : a * p ≤ 1 := by
        calc
          a * p ≤ 1 * p := mul_le_mul_of_nonneg_right ha1 hp0
          _ = p := one_mul p
          _ ≤ 1 := hp1
      have ha'0 : 0 ≤ a' := by dsimp [a']; linarith
      have ha'1 : a' ≤ 1 := by
        dsimp [a']
        exact sub_le_self _ (mul_nonneg ha0 hp0)
      have hchild : (∑ v ∈ R.children (G := G) u,
          rootedVarianceMassAt a' R z hz v) ≤
          ∑ v ∈ R.children (G := G) u, descendantEnergyAt R z hz v := by
        apply Finset.sum_le_sum
        intro v hv
        exact ih (R.subtreeOrder (G := G) v) (by
          rw [← horder]
          exact R.subtreeOrder_child_lt (G := G)
            ((R.mem_children (G := G) u v).mp hv))
          a' ha'0 ha'1 v rfl
      have he0 := rootedEnergyAt_nonneg R z hz u
      rw [rootedVarianceMassAt_eq_root_add_sum_children hG a R z hz u]
      rw [descendantEnergyAt_eq_root_add_sum_children hG R z hz u]
      change a * rootedEnergyAt R z hz u +
          (∑ v ∈ R.children (G := G) u,
            rootedVarianceMassAt a' R z hz v) ≤ _
      exact add_le_add (mul_le_of_le_one_left he0 ha1) hchild

/-- The free subtree variance is bounded by raw descendant energy. -/
theorem subtreeVarianceAt_le_descendantEnergyAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) :
    subtreeVarianceAt R z hz u ≤ descendantEnergyAt R z hz u := by
  simpa [rootedVarianceMassAt] using
    rootedVarianceMassAt_le_descendantEnergyAt hG R z hz 1 (by norm_num) (by norm_num) u

/-- If availability is at least `(1+Z)⁻¹`, raw descendant energy is at most
`(1+Z)` times the corresponding variance mass. -/
theorem descendantEnergyAt_le_one_add_Z_mul_rootedVarianceMassAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (a : ℝ) (ha : 1 / (1 + Z) ≤ a) (ha1 : a ≤ 1) (u : V) :
    descendantEnergyAt R z hz u ≤
      (1 + Z) * rootedVarianceMassAt a R z hz u := by
  classical
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hZ1 : 0 < 1 + Z := by linarith
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on
      generalizing u a with
  | h n ih =>
      let p := rootedOccupationProbabilityAt R z u
      let a' := 1 - a * p
      have ha0 : 0 ≤ a := le_trans (by positivity : 0 ≤ 1 / (1 + Z)) ha
      have hp0 : 0 ≤ p := by
        dsimp [p]
        exact (rootedOccupationProbabilityAt_pos R z hz u).le
      have hpρ : p ≤ Z / (1 + Z) := by
        dsimp [p]
        exact rootedOccupationProbabilityAt_le_ceiling_ratio hG R z Z hz hzZ u
      have hap : a * p ≤ Z / (1 + Z) := by
        calc
          a * p ≤ 1 * p := mul_le_mul_of_nonneg_right ha1 hp0
          _ = p := one_mul p
          _ ≤ Z / (1 + Z) := hpρ
      have heta : 1 - Z / (1 + Z) = 1 / (1 + Z) := by
        field_simp
        ring
      have ha' : 1 / (1 + Z) ≤ a' := by
        dsimp [a']
        rw [← heta]
        linarith
      have ha'1 : a' ≤ 1 := by
        dsimp [a']
        exact sub_le_self _ (mul_nonneg ha0 hp0)
      have hchild : (∑ v ∈ R.children (G := G) u,
          descendantEnergyAt R z hz v) ≤
          (1 + Z) * ∑ v ∈ R.children (G := G) u,
            rootedVarianceMassAt a' R z hz v := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro v hv
        exact ih (R.subtreeOrder (G := G) v) (by
          rw [← horder]
          exact R.subtreeOrder_child_lt (G := G)
            ((R.mem_children (G := G) u v).mp hv))
          a' ha' ha'1 v rfl
      have he0 := rootedEnergyAt_nonneg R z hz u
      have hcoef : 1 ≤ (1 + Z) * a := by
        have hmul := mul_le_mul_of_nonneg_left ha hZ1.le
        calc
          1 = (1 + Z) * (1 / (1 + Z)) := by field_simp
          _ ≤ (1 + Z) * a := hmul
      have he : rootedEnergyAt R z hz u ≤
          (1 + Z) * (a * rootedEnergyAt R z hz u) := by
        have := mul_le_mul_of_nonneg_right hcoef he0
        nlinarith
      rw [descendantEnergyAt_eq_root_add_sum_children hG R z hz u]
      rw [rootedVarianceMassAt_eq_root_add_sum_children hG a R z hz u]
      change rootedEnergyAt R z hz u +
          (∑ v ∈ R.children (G := G) u, descendantEnergyAt R z hz v) ≤
        (1 + Z) * (a * rootedEnergyAt R z hz u +
          ∑ v ∈ R.children (G := G) u,
            rootedVarianceMassAt a' R z hz v)
      rw [mul_add]
      exact add_le_add he hchild

/-- Uniform comparison of descendant energy with free subtree variance. -/
theorem descendantEnergyAt_le_one_add_Z_mul_subtreeVarianceAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    descendantEnergyAt R z hz u ≤
      (1 + Z) * subtreeVarianceAt R z hz u := by
  simpa [rootedVarianceMassAt] using
    descendantEnergyAt_le_one_add_Z_mul_rootedVarianceMassAt
      hG R Z z hz hzZ 1 (by
        have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
        have hZ1 : 0 < 1 + Z := by linarith
        exact (div_le_one hZ1).2 (by linarith)) (by norm_num) u

/-- A finite nontrivial downward path.  Its vertex list is
`start :: next :: tail`, so positive length is structural, and every adjacent
pair is parent-to-child. -/
structure DownwardPath (R : ComponentRooting G) where
  start : V
  next : V
  tail : List V
  isChain : (start :: next :: tail).IsChain (R.IsChild (G := G))

namespace DownwardPath

variable {R : ComponentRooting G}

/-- The full vertex list of a downward path. -/
def vertices (P : DownwardPath R) : List V := P.start :: P.next :: P.tail

@[simp] theorem vertices_ne_nil (P : DownwardPath R) : P.vertices ≠ [] := by
  simp [vertices]

@[simp] theorem vertices_length (P : DownwardPath R) :
    P.vertices.length = P.tail.length + 2 := by
  simp [vertices]

/-- Sum a function over all path vertices except the final vertex. -/
def initialSum (f : V → ℝ) : List V → ℝ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => f u + initialSum f (v :: rest)

/-- Evaluate a function at the final vertex (and return zero on the unused
empty-list case). -/
def terminalValue (f : V → ℝ) : List V → ℝ
  | [] => 0
  | [u] => f u
  | _ :: v :: rest => terminalValue f (v :: rest)

/-- Sum a child-root quantity over all side children along a vertex list. -/
noncomputable def sideSum (R : ComponentRooting G)
    (f : V → ℝ) : List V → ℝ
  | [] => 0
  | [_] => 0
  | u :: v :: rest =>
      (∑ w ∈ (R.children (G := G) u).erase v, f w) +
        sideSum R f (v :: rest)

/-- The initial sum plus the terminal value is the total list sum. -/
theorem initialSum_add_terminalValue_eq_sum
    (f : V → ℝ) : ∀ l : List V, l ≠ [] →
    initialSum f l + terminalValue f l = (l.map f).sum
  | [], h => (h rfl).elim
  | [u], _ => by simp [initialSum, terminalValue]
  | u :: v :: rest, _ => by
      simp only [initialSum, terminalValue, List.map_cons, List.sum_cons]
      calc
        f u + initialSum f (v :: rest) + terminalValue f (v :: rest) =
            f u + (initialSum f (v :: rest) + terminalValue f (v :: rest)) := by ring
        _ = f u + (List.map f (v :: rest)).sum := by
          rw [initialSum_add_terminalValue_eq_sum f (v :: rest) (by simp)]

/-- The sum over the tail is bounded by initial-plus-terminal whenever the
summands are nonnegative. -/
theorem sum_tail_le_initial_add_terminal
    (f : V → ℝ) (hf : ∀ u, 0 ≤ f u) : ∀ l : List V,
    (l.tail.map f).sum ≤ initialSum f l + terminalValue f l
  | [] => by simp [initialSum, terminalValue]
  | u :: rest => by
      rw [initialSum_add_terminalValue_eq_sum f (u :: rest) (by simp)]
      simp only [List.tail_cons, List.map_cons, List.sum_cons]
      exact le_add_of_nonneg_left (hf u)

end DownwardPath

end
end AppendixA
end Forest
end Erdos993
