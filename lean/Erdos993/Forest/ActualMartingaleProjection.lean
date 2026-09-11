import Erdos993.Forest.ActualRootedVariance
import Erdos993.Forest.CanonicalLaw

/-!
# Actual finite-law martingale projection for rooted forests

This module starts the W2.3 construction directly on the finite configuration
space `IndepFinset G`.  Every weight is the probability from the original
canonical law `C.law`; in particular no local canonical state and no changed
activity is introduced.
-/

open scoped BigOperators

namespace Erdos993

open Forest ActualRootedVariance

namespace ActualMartingaleProjection

noncomputable section

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The literal zero-one occupation variable `xi_u`. -/
def occupationIndicator (I : IndepFinset G) (u : V) : ℝ :=
  if u ∈ I.val then 1 else 0

/-- Literal total occupation `X`. -/
def occupationCount (I : IndepFinset G) : ℝ := I.val.card

/-- The actual canonical centered occupation count `X-s`. -/
def centeredOccupationCount (C : CanonicalFirstRecoveryState G)
    (I : IndepFinset G) : ℝ :=
  occupationCount I - (C.index : ℝ)

/-- The occupation pattern observed on `S`. -/
def restriction (S : Finset V) (I : IndepFinset G) : Finset V := I.val ∩ S

/-- The finite fiber of configurations agreeing with `I` on `S`. -/
def restrictionFiber (S : Finset V) (I : IndepFinset G) :
    Finset (IndepFinset G) :=
  Finset.univ.filter (fun J => restriction S J = restriction S I)

@[simp] theorem mem_restrictionFiber {S : Finset V} {I J : IndepFinset G} :
    J ∈ restrictionFiber S I ↔ restriction S J = restriction S I := by
  simp [restrictionFiber]

@[simp] theorem self_mem_restrictionFiber (S : Finset V) (I : IndepFinset G) :
    I ∈ restrictionFiber S I := by simp

/-- Actual probability mass of an observation fiber. -/
def restrictionFiberMass (C : CanonicalFirstRecoveryState G)
    (S : Finset V) (I : IndepFinset G) : ℝ :=
  ∑ J ∈ restrictionFiber S I, C.law.probability J

/-- Every actual configuration has strictly positive hard-core probability. -/
theorem law_probability_pos (C : CanonicalFirstRecoveryState G)
    (I : IndepFinset G) : 0 < C.law.probability I := by
  rw [C.law_probability]
  exact div_pos (pow_pos C.activity_pos _) (independenceEval_pos G C.activity_pos)

/-- The observation fiber containing an actual configuration has positive mass,
so the finite conditional expectation below never uses a zero denominator. -/
theorem restrictionFiberMass_pos (C : CanonicalFirstRecoveryState G)
    (S : Finset V) (I : IndepFinset G) : 0 < restrictionFiberMass C S I := by
  unfold restrictionFiberMass
  have hterm : C.law.probability I ≤
      ∑ J ∈ restrictionFiber S I, C.law.probability J := by
    apply Finset.single_le_sum
    · intro J hJ
      exact C.law.probability_nonneg J
    · exact self_mem_restrictionFiber S I
  exact lt_of_lt_of_le (law_probability_pos C I) hterm

/-- Genuine finite conditional expectation given the literal pattern `xi_S`.
It is the probability-weighted average over configurations agreeing on `S`. -/
def conditionalExpectation (C : CanonicalFirstRecoveryState G)
    (S : Finset V) (f : IndepFinset G → ℝ) (I : IndepFinset G) : ℝ :=
  (∑ J ∈ restrictionFiber S I, C.law.probability J * f J) /
    restrictionFiberMass C S I

/-- Conditional expectation depends only on the observed restriction. -/
theorem conditionalExpectation_eq_of_restriction_eq
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (f : IndepFinset G → ℝ) {I I' : IndepFinset G}
    (h : restriction S I = restriction S I') :
    conditionalExpectation C S f I = conditionalExpectation C S f I' := by
  have hfiber : restrictionFiber S I = restrictionFiber S I' := by
    ext J
    simp only [mem_restrictionFiber]
    rw [h]
  simp [conditionalExpectation, restrictionFiberMass, hfiber]

/-- Constants are fixed by the actual finite conditional expectation. -/
@[simp] theorem conditionalExpectation_const
    (C : CanonicalFirstRecoveryState G) (S : Finset V) (a : ℝ)
    (I : IndepFinset G) :
    conditionalExpectation C S (fun _ => a) I = a := by
  unfold conditionalExpectation restrictionFiberMass
  simp_rw [mul_comm (C.law.probability _) a]
  rw [← Finset.mul_sum]
  change (a * restrictionFiberMass C S I) / restrictionFiberMass C S I = a
  apply div_eq_iff (ne_of_gt (restrictionFiberMass_pos C S I)) |>.2
  ring

/-- Literal parent occupation.  At a component root the empty sum implements
Appendix D's virtual absent parent convention. -/
def parentOccupationIndicator (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) : ℝ := by
  classical
  exact ∑ p : V, if R.IsChild (G := G) p u then occupationIndicator I p else 0

/-- The literal innovation `eta_u` from (D.16), using the original activity. -/
def eta (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) : ℝ :=
  occupationIndicator I u -
    R.occupationProbability (G := G) C u *
      (1 - parentOccupationIndicator R I u)

/-- A set is ancestor-closed when it contains every rooted ancestor of each
of its vertices. -/
def AncestorClosed (R : ComponentRooting G) (S : Finset V) : Prop :=
  ∀ ⦃u v : V⦄, v ∈ S → R.IsDescendant (G := G) u v → u ∈ S

/-- Every parent of an observed vertex is observed. -/
theorem AncestorClosed.parent_mem (R : ComponentRooting G) {S : Finset V}
    (hS : AncestorClosed R S) {p u : V} (hu : u ∈ S)
    (hpu : R.IsChild (G := G) p u) : p ∈ S :=
  hS hu (Relation.ReflTransGen.single hpu)

/-- No descendant of an unobserved vertex belongs to an ancestor-closed set. -/
theorem AncestorClosed.no_descendant_mem (R : ComponentRooting G)
    {S : Finset V} (hS : AncestorClosed R S) {u v : V}
    (hu : u ∉ S) (huv : R.IsDescendant (G := G) u v) : v ∉ S := by
  intro hv
  exact hu (hS hv huv)

/-- At a component root, the virtual-parent occupation is literally zero. -/
@[simp] theorem parentOccupationIndicator_root
    (R : ComponentRooting G) (I : IndepFinset G) {u : V}
    (hu : u = R.rootOf (G := G) u) :
    parentOccupationIndicator R I u = 0 := by
  classical
  unfold parentOccupationIndicator
  apply Finset.sum_eq_zero
  intro p hp
  simp [R.not_isChild_of_eq_root (G := G) hu]

/-- Away from a root, the parent sum is the occupation indicator of the unique
selected parent. -/
theorem parentOccupationIndicator_eq_selectedParent
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) {u : V} (hu : u ≠ R.rootOf (G := G) u) :
    parentOccupationIndicator R I u =
      occupationIndicator I (R.selectedParent (G := G) u hu) := by
  classical
  unfold parentOccupationIndicator
  let p : V := R.selectedParent (G := G) u hu
  have hp : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hu
  rw [Finset.sum_eq_single p]
  · simp [hp, p]
  · intro q hq hqp
    by_cases hqchild : R.IsChild (G := G) q u
    · exact (hqp (R.isChild_unique (G := G) C.isForest hqchild hp)).elim
    · simp [hqchild]
  · simp

/-- The literal indicator sum is the configuration cardinality. -/
theorem sum_occupationIndicator (I : IndepFinset G) :
    (∑ u : V, occupationIndicator I u) = occupationCount I := by
  classical
  unfold occupationIndicator occupationCount
  rw [← Finset.sum_filter]
  simp

/-- Reindex the parent-occupation terms over rooted child sets. -/
theorem sum_parentOccupationIndicator
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (d p : V → ℝ) :
    (∑ u : V, d u * p u * parentOccupationIndicator R I u) =
      ∑ r : V, occupationIndicator I r *
        (∑ u ∈ R.children (G := G) r, p u * d u) := by
  classical
  unfold parentOccupationIndicator
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [ComponentRooting.children, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases h : R.IsChild (G := G) r u
  · simp [h]
    ring
  · simp [h]

/-- The actual expectation of one literal occupation indicator is the standard
closed-neighborhood deletion ratio.  This is proved by a finite equivalence,
not by a probabilistic assumption. -/
theorem expectation_occupationIndicator_eq_ratio
    (C : CanonicalFirstRecoveryState G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I * occupationIndicator I u) =
      C.activity * independenceEval (deleteClosedNeighborhood G u) C.activity /
        independenceEval G C.activity := by
  classical
  letI : Fintype (AvoidingIndepFinset G u) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset G u) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype {x : V // x ≠ u ∧ ¬ G.Adj u x} :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  calc
    (∑ I : IndepFinset G, C.law.probability I * occupationIndicator I u) =
        ∑ q : AvoidingIndepFinset G u ⊕ ContainingIndepFinset G u,
          Sum.elim (fun _ => 0)
            (fun I => C.activity ^ I.val.val.card /
              independenceEval G C.activity) q := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv G u)
      intro I
      by_cases h : u ∈ I.val <;>
        simp [occupationIndicator, indepFinsetPartitionEquiv, h,
          Forest.CanonicalFirstRecoveryState.law_probability]
    _ = ∑ I : ContainingIndepFinset G u,
          C.activity ^ I.val.val.card / independenceEval G C.activity := by
      rw [Fintype.sum_sum_type]
      simp
    _ = ∑ J : IndepFinset (deleteClosedNeighborhood G u),
          C.activity ^ (J.val.card + 1) / independenceEval G C.activity := by
      symm
      apply Fintype.sum_equiv (containingEquiv G u)
      intro J
      rw [containingEquiv_card]
    _ = C.activity *
          (∑ J : IndepFinset (deleteClosedNeighborhood G u),
            C.activity ^ J.val.card) / independenceEval G C.activity := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      rw [pow_add, pow_one]
      ring
    _ = C.activity * independenceEval (deleteClosedNeighborhood G u) C.activity /
          independenceEval G C.activity := by
      congr 1
      exact congrArg (fun x : ℝ => C.activity * x)
        (independenceEval_eq_sum (G := deleteClosedNeighborhood G u) C.activity).symm

/-- The actual global occupation marginal factors as `a_u p_u`. -/
theorem expectation_occupationIndicator_eq_parentAbsent_mul_probability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I * occupationIndicator I u) =
      R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u := by
  rw [expectation_occupationIndicator_eq_ratio]
  exact (R.parentAbsentProbability_mul_occupationProbability (G := G) C u).symm

/-- The expected literal parent-absence indicator is the inherited actual
parent-absence probability. -/
theorem expectation_one_sub_parentOccupationIndicator
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I *
      (1 - parentOccupationIndicator R I u)) =
      R.parentAbsentProbability (G := G) C u := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · have ha : R.parentAbsentProbability (G := G) C u = 1 := by
      rw [hu]
      exact R.parentAbsentProbability_rootOf (G := G) C u
    calc
      (∑ I : IndepFinset G, C.law.probability I *
          (1 - parentOccupationIndicator R I u)) =
          ∑ I : IndepFinset G, C.law.probability I := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [parentOccupationIndicator_root R I hu]
        ring
      _ = 1 := C.law.probability_sum
      _ = R.parentAbsentProbability (G := G) C u := ha.symm
  · let p : V := R.selectedParent (G := G) u hu
    have hp : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hu
    rw [R.parentAbsentProbability_child (G := G) C hp]
    have hm := expectation_occupationIndicator_eq_parentAbsent_mul_probability C R p
    calc
      (∑ I : IndepFinset G, C.law.probability I *
          (1 - parentOccupationIndicator R I u)) =
        (∑ I : IndepFinset G, C.law.probability I) -
          ∑ I : IndepFinset G, C.law.probability I * occupationIndicator I p := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro I hI
            rw [parentOccupationIndicator_eq_selectedParent C R I hu]
            change _ = _ - C.law.probability I * occupationIndicator I p
            ring
      _ = 1 - R.parentAbsentProbability (G := G) C p *
          R.occupationProbability (G := G) C p := by
        rw [C.law.probability_sum, hm]

/-- The literal innovation is centered under the actual global hard-core law.
This is the unconditional part of (D.19), derived from finite sums. -/
theorem expectation_eta_eq_zero
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I * eta C R I u) = 0 := by
  classical
  unfold eta
  rw [show (∑ I : IndepFinset G, C.law.probability I *
      (occupationIndicator I u - R.occupationProbability (G := G) C u *
        (1 - parentOccupationIndicator R I u))) =
      (∑ I : IndepFinset G, C.law.probability I * occupationIndicator I u) -
      R.occupationProbability (G := G) C u *
        (∑ I : IndepFinset G, C.law.probability I *
          (1 - parentOccupationIndicator R I u)) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    ring]
  rw [expectation_occupationIndicator_eq_parentAbsent_mul_probability,
    expectation_one_sub_parentOccupationIndicator]
  ring

/-- Before identifying the deterministic constant, expansion and child
reindexing give the affine pointwise identity. -/
theorem sum_eta_eq_occupationCount_sub_constant
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) :
    (∑ u : V, R.conditionalMeanDifference (G := G) C u * eta C R I u) =
      occupationCount I -
        ∑ u : V, R.occupationProbability (G := G) C u *
          R.conditionalMeanDifference (G := G) C u := by
  classical
  let d : V → ℝ := R.conditionalMeanDifference (G := G) C
  let p : V → ℝ := R.occupationProbability (G := G) C
  let x : V → ℝ := occupationIndicator I
  have hparent := sum_parentOccupationIndicator C R I d p
  have hrec : ∀ u : V,
      d u + ∑ v ∈ R.children (G := G) u, p v * d v = 1 := by
    intro u
    have h := R.conditionalMeanDifference_eq_one_sub_sum (G := G) C u
    dsimp only [d, p]
    linarith
  change (∑ u : V, d u * eta C R I u) =
    occupationCount I - ∑ u : V, p u * d u
  calc
    (∑ u : V, d u * eta C R I u) =
        ∑ u : V, (d u * x u - d u * p u +
          d u * p u * parentOccupationIndicator R I u) := by
      apply Finset.sum_congr rfl
      intro u hu
      unfold eta
      dsimp only [d, p, x]
      ring
    _ = (∑ u : V, d u * x u) - (∑ u : V, d u * p u) +
        ∑ u : V, d u * p u * parentOccupationIndicator R I u := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ u : V, d u * x u) - (∑ u : V, d u * p u) +
        ∑ r : V, x r * (∑ u ∈ R.children (G := G) r, p u * d u) := by
      rw [hparent]
    _ = ((∑ u : V, d u * x u) +
        ∑ u : V, x u * (∑ v ∈ R.children (G := G) u, p v * d v)) -
        ∑ u : V, d u * p u := by ring
    _ = (∑ u : V, x u *
        (d u + ∑ v ∈ R.children (G := G) u, p v * d v)) -
        ∑ u : V, d u * p u := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ = (∑ u : V, x u) - ∑ u : V, d u * p u := by
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      rw [hrec]
      ring
    _ = occupationCount I - ∑ u : V, p u * d u := by
      rw [sum_occupationIndicator]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      ring

/-- The actual expected total occupation is the canonical index. -/
theorem expectation_occupationCount_eq_index
    (C : CanonicalFirstRecoveryState G) :
    (∑ I : IndepFinset G, C.law.probability I * occupationCount I) =
      (C.index : ℝ) := by
  rw [← C.law_mean]
  rfl

/-- The deterministic constant in the affine expansion is the canonical mean. -/
theorem sum_probability_mul_difference_eq_index
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    (∑ u : V, R.occupationProbability (G := G) C u *
      R.conditionalMeanDifference (G := G) C u) = (C.index : ℝ) := by
  classical
  let d : V → ℝ := R.conditionalMeanDifference (G := G) C
  let p : V → ℝ := R.occupationProbability (G := G) C
  let K : ℝ := ∑ u : V, p u * d u
  have hzero :
      (∑ I : IndepFinset G, C.law.probability I *
        (∑ u : V, d u * eta C R I u)) = 0 := by
    rw [show (∑ I : IndepFinset G, C.law.probability I *
        (∑ u : V, d u * eta C R I u)) =
        ∑ u : V, d u *
          (∑ I : IndepFinset G, C.law.probability I * eta C R I u) by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro I hI
      ring]
    apply Finset.sum_eq_zero
    intro u hu
    rw [expectation_eta_eq_zero]
    ring
  have haffine :
      (∑ I : IndepFinset G, C.law.probability I *
        (∑ u : V, d u * eta C R I u)) = (C.index : ℝ) - K := by
    calc
      _ = ∑ I : IndepFinset G, C.law.probability I * (occupationCount I - K) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [sum_eta_eq_occupationCount_sub_constant C R I]
      _ = (∑ I : IndepFinset G, C.law.probability I * occupationCount I) -
          K * (∑ I : IndepFinset G, C.law.probability I) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro I hI
        ring
      _ = (C.index : ℝ) - K := by
        rw [expectation_occupationCount_eq_index, C.law.probability_sum]
        ring
  change K = (C.index : ℝ)
  linarith

/-- Pointwise first identity of (D.17), proved from the literal finite-law
innovations and the inherited rooted recursion. -/
theorem centeredOccupationCount_eq_sum_eta
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) :
    centeredOccupationCount C I =
      ∑ u : V, R.conditionalMeanDifference (G := G) C u * eta C R I u := by
  rw [sum_eta_eq_occupationCount_sub_constant C R I,
    sum_probability_mul_difference_eq_index C R]
  rfl


/-- Restriction agreement fixes every observed occupation indicator. -/
theorem occupationIndicator_eq_of_restriction_eq
    {S : Finset V} {I J : IndepFinset G} {u : V}
    (hu : u ∈ S) (hIJ : restriction S I = restriction S J) :
    occupationIndicator I u = occupationIndicator J u := by
  have hmem : u ∈ restriction S I ↔ u ∈ restriction S J := by
    rw [hIJ]
  simp only [restriction, Finset.mem_inter, hu, and_true] at hmem
  by_cases hI : u ∈ I.val <;> by_cases hJ : u ∈ J.val <;>
    simp [occupationIndicator, hI, hJ] at hmem ⊢

/-- Restriction equality also fixes the selected parent of an observed child. -/
theorem parentOccupationIndicator_eq_of_restriction_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : AncestorClosed R S)
    {I J : IndepFinset G} {u : V} (hu : u ∈ S)
    (hIJ : restriction S I = restriction S J) :
    parentOccupationIndicator R I u = parentOccupationIndicator R J u := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · rw [parentOccupationIndicator_root R I hroot,
      parentOccupationIndicator_root R J hroot]
  · rw [parentOccupationIndicator_eq_selectedParent C R I hroot,
      parentOccupationIndicator_eq_selectedParent C R J hroot]
    apply occupationIndicator_eq_of_restriction_eq
      (AncestorClosed.parent_mem (G := G) R hS hu
        (R.selectedParent_isChild (G := G) u hroot)) hIJ

/-- Eta is constant on every observed restriction fiber. -/
theorem eta_eq_of_restriction_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : AncestorClosed R S)
    {I J : IndepFinset G} {u : V} (hu : u ∈ S)
    (hIJ : restriction S I = restriction S J) :
    eta C R I u = eta C R J u := by
  rw [eta, eta, occupationIndicator_eq_of_restriction_eq hu hIJ,
    parentOccupationIndicator_eq_of_restriction_eq C R hS hu hIJ]

/-- The rooted descendant set of an unobserved vertex is disjoint from the
observed ancestor-closed set. -/
theorem descendants_disjoint_of_ancestorClosed
    (R : ComponentRooting G) {S : Finset V}
    (hS : AncestorClosed R S) {u : V} (hu : u ∉ S) :
    Disjoint (R.descendants (G := G) u) S := by
  rw [Finset.disjoint_left]
  intro v hvD hvS
  exact hu (hS hvS ((R.mem_descendants (G := G) u v).mp hvD))

/-- Every edge from a descendant subtree to its complement is the parent edge. -/
theorem adj_descendant_complement_eq_parent
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {u x y : V} (hx : x ∈ R.descendants (G := G) u)
    (hy : y ∉ R.descendants (G := G) u) (hxy : G.Adj x y) :
    ∃ p, R.IsChild (G := G) p u ∧ y = p := by
  have hxd := (R.mem_descendants (G := G) u x).mp hx
  rcases (R.adj_iff_isChild_or_reverse (G := G) C.isForest).mp hxy with hdown | hup
  · exact (hy ((R.mem_descendants (G := G) u y).mpr (hxd.tail hdown))).elim
  · by_cases hxu : x = u
    · subst x
      exact ⟨y, hup, rfl⟩
    · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hxd with hux | ⟨q, huq, hqx⟩
      · exact (hxu hux).elim
      · have hyq : y = q := R.isChild_unique (G := G) C.isForest hup hqx
        exact (hy ((R.mem_descendants (G := G) u y).mpr (hyq ▸ huq))).elim

/-- A parent-before-child observation cannot contain a crossing edge from an
unobserved descendant subtree when that parent is absent. -/
theorem not_adj_descendant_of_restriction_eq_of_parent_absent
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V)
    {u : V}
    (hparent : ∀ ⦃p⦄, R.IsChild (G := G) p u → p ∈ S)
    (I B : IndepFinset G) (hBI : restriction S B = restriction S I)
    (hzero : parentOccupationIndicator R I u = 0)
    {x y : V} (hx : x ∈ R.descendants (G := G) u)
    (hyB : y ∈ B.val) (hyD : y ∉ R.descendants (G := G) u) :
    ¬ G.Adj x y := by
  intro hxy
  obtain ⟨p, hpu, hyp⟩ := adj_descendant_complement_eq_parent C R hx hyD hxy
  subst y
  have hpS : p ∈ S := hparent hpu
  have hpI : p ∈ I.val := by
    have hpB : p ∈ B.val := hyB
    have hpR : p ∈ restriction S B := Finset.mem_inter.mpr ⟨hpB, hpS⟩
    have hpR' : p ∈ restriction S I := by rw [hBI] at hpR; exact hpR
    exact (Finset.mem_inter.mp hpR').1
  have hpocc : occupationIndicator I p = 1 := by simp [occupationIndicator, hpI]
  have : parentOccupationIndicator R I u = 1 := by
    by_cases hroot : u = R.rootOf (G := G) u
    · exfalso
      exact (R.not_isChild_of_eq_root (G := G) hroot hpu).elim
    · rw [parentOccupationIndicator_eq_selectedParent C R I hroot]
      have heq := R.selectedParent_eq_of_isChild (G := G) C hpu hroot
      rw [heq, hpocc]
  linarith

/-- The complement of a rooted descendant subtree, used for a fine finite
conditioning fiber. -/
noncomputable def descendantComplement (R : ComponentRooting G) (u : V) : Finset V :=
  (Finset.univ : Finset V) \ R.descendants (G := G) u

/-- Configurations agreeing on every vertex outside a descendant subtree. -/
noncomputable def descendantFiber (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) :=
  {J : IndepFinset G //
    restriction (descendantComplement R u) J =
      restriction (descendantComplement R u) I}

noncomputable instance descendantFiberFintype (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) : Fintype (descendantFiber R u I) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Lift an independent set of an induced rooted subtree to the ambient graph. -/
noncomputable def subtreeLift (R : ComponentRooting G) (u : V)
    (T : IndepFinset (R.Subtree (G := G) u)) : IndepFinset G :=
  (indepFinsetInduceEquiv G (fun x => x ∈ R.descendants (G := G) u) T).val

@[simp] theorem subtreeLift_card (R : ComponentRooting G) (u : V)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    (subtreeLift R u T).val.card = T.val.card := by
  exact indepFinsetInduceEquiv_card G
    (fun x => x ∈ R.descendants (G := G) u) T

/-- The descendant restriction as an ambient independent set with support. -/
noncomputable def ambientDescendantPart (R : ComponentRooting G) (u : V)
    (J : IndepFinset G) :
    RestrictedIndepFinset G (fun x => x ∈ R.descendants (G := G) u) :=
  ⟨⟨J.val ∩ R.descendants (G := G) u,
    J.property.mono Finset.inter_subset_left⟩, by
    intro x hx
    exact (Finset.mem_inter.mp hx).2⟩

/-- The descendant part of an ambient independent configuration. -/
noncomputable def subtreePart (R : ComponentRooting G) (u : V)
    (J : IndepFinset G) : IndepFinset (R.Subtree (G := G) u) :=
  (indepFinsetInduceEquiv G
    (fun x => x ∈ R.descendants (G := G) u)).symm
      (ambientDescendantPart R u J)

@[simp] theorem subtreeLift_part_val (R : ComponentRooting G) (u : V)
    (J : IndepFinset G) :
    (subtreeLift R u (subtreePart R u J)).val =
      J.val ∩ R.descendants (G := G) u := by
  have h := (indepFinsetInduceEquiv G
    (fun x => x ∈ R.descendants (G := G) u)).apply_symm_apply
      (ambientDescendantPart R u J)
  exact congrArg (fun K => K.val.val) h

@[simp] theorem subtreeLift_mem_descendants
    (R : ComponentRooting G) (u : V)
    (T : IndepFinset (R.Subtree (G := G) u)) {x : V}
    (hx : x ∈ (subtreeLift R u T).val) :
    x ∈ R.descendants (G := G) u := by
  exact (indepFinsetInduceEquiv G
    (fun y => y ∈ R.descendants (G := G) u) T).property x hx

/-- On a fine fiber, the fixed outside configuration is unchanged. -/
theorem descendantFiber_outside_eq
    (R : ComponentRooting G) (u : V) (I : IndepFinset G)
    (J : descendantFiber R u I) :
    J.1.val \ R.descendants (G := G) u =
      I.val \ R.descendants (G := G) u := by
  have hmem := Finset.ext_iff.mp J.2
  ext x
  have hmemx := hmem x
  change (x ∈ J.1.val ∩ descendantComplement R u ↔
    x ∈ I.val ∩ descendantComplement R u) at hmemx
  constructor
  · intro hx
    have hi' := hmemx.mp (Finset.mem_inter.mpr ⟨
      (Finset.mem_sdiff.mp hx).1,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩⟩)
    have hii := Finset.mem_inter.mp hi'
    have hiO := Finset.mem_sdiff.mp hii.2
    exact Finset.mem_sdiff.mpr ⟨hii.1, hiO.2⟩
  · intro hx
    have hj' := hmemx.mpr (Finset.mem_inter.mpr ⟨
      (Finset.mem_sdiff.mp hx).1,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩⟩)
    have hjj := Finset.mem_inter.mp hj'
    have hjO := Finset.mem_sdiff.mp hjj.2
    exact Finset.mem_sdiff.mpr ⟨hjj.1, hjO.2⟩

/-- The exact fine-fiber separator needed before constructing the product
bijection: if the fixed parent is absent, no ambient independent set in the
fine fiber can have an edge from the varying subtree to its fixed outside. -/
theorem descendantFiber_no_cross_edge
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (u : V) (I : IndepFinset G)
    (hzero : parentOccupationIndicator R I u = 0)
    (J : descendantFiber R u I)
    {x y : V} (hx : x ∈ R.descendants (G := G) u)
    (hy : y ∈ J.1.val) (hyO : y ∈ descendantComplement R u) :
    ¬ G.Adj x y := by
  apply not_adj_descendant_of_restriction_eq_of_parent_absent C R
    (descendantComplement R u)
    (by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        R.not_mem_descendants_child (G := G) hp⟩)
    I J.1 J.2 hzero hx hy (Finset.mem_sdiff.mp hyO).2



/-- Glue a subtree configuration to the fixed outside of `I`.  This is the
literal configuration map used in the finite spatial-Markov fiber argument. -/
noncomputable def glueSubtree
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) : IndepFinset G := by
  refine ⟨I.val \ R.descendants (G := G) u ∪
      (subtreeLift R u T).val, ?_⟩
  intro x hx y hy hne hxy
  rcases Finset.mem_union.mp hx with hxO | hxD
  · rcases Finset.mem_union.mp hy with hyO | hyD
    · exact I.property (Finset.mem_sdiff.mp hxO).1
        (Finset.mem_sdiff.mp hyO).1 hne hxy
    · exact (descendantFiber_no_cross_edge C R u I hzero
        ⟨I, rfl⟩ (subtreeLift_mem_descendants R u T hyD)
        (Finset.mem_sdiff.mp hxO).1
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hxO).2⟩))
        (G.symm hxy)
  · rcases Finset.mem_union.mp hy with hyO | hyD
    · exact descendantFiber_no_cross_edge C R u I hzero
        ⟨I, rfl⟩ (subtreeLift_mem_descendants R u T hxD)
        (Finset.mem_sdiff.mp hyO).1
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hyO).2⟩)
        hxy
    · exact (subtreeLift R u T).property hxD hyD hne hxy

@[simp] theorem glueSubtree_outside_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    (glueSubtree C R u I hzero T).val \ R.descendants (G := G) u =
      I.val \ R.descendants (G := G) u := by
  ext x
  constructor
  · intro hx
    have hnot : x ∉ R.descendants (G := G) u :=
      (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (Finset.mem_sdiff.mp hx).1 with hxi | hxt
    · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxi).1, hnot⟩
    · exact (hnot (subtreeLift_mem_descendants R u T hxt)).elim
  · intro hx
    exact Finset.mem_sdiff.mpr ⟨
      Finset.mem_union.mpr (Or.inl hx),
      (Finset.mem_sdiff.mp hx).2⟩

@[simp] theorem glueSubtree_restriction_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    restriction (descendantComplement R u) (glueSubtree C R u I hzero T) =
      restriction (descendantComplement R u) I := by
  ext x
  simp only [restriction, Finset.mem_inter]
  constructor
  · rintro ⟨hx, hxO⟩
    have hglue : x ∈ (glueSubtree C R u I hzero T).val \
        R.descendants (G := G) u :=
      Finset.mem_sdiff.mpr ⟨hx, (Finset.mem_sdiff.mp hxO).2⟩
    have hi : x ∈ I.val \ R.descendants (G := G) u := by
      rw [← glueSubtree_outside_eq C R u I hzero T]
      exact hglue
    exact ⟨(Finset.mem_sdiff.mp hi).1, hxO⟩
  · rintro ⟨hx, hxO⟩
    have hi : x ∈ I.val \ R.descendants (G := G) u :=
      Finset.mem_sdiff.mpr ⟨hx, (Finset.mem_sdiff.mp hxO).2⟩
    have hglue : x ∈ (glueSubtree C R u I hzero T).val \
        R.descendants (G := G) u := by
      rw [glueSubtree_outside_eq C R u I hzero T]
      exact hi
    exact ⟨(Finset.mem_sdiff.mp hglue).1, hxO⟩


@[simp] theorem glueSubtree_inter_descendants_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    (glueSubtree C R u I hzero T).val ∩ R.descendants (G := G) u =
      (subtreeLift R u T).val := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hO | hD
    · exact ((Finset.mem_sdiff.mp hO).2 (Finset.mem_inter.mp hx).2).elim
    · exact hD
  · intro hx
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_union.mpr (Or.inr hx),
      subtreeLift_mem_descendants R u T hx⟩

@[simp] theorem subtreePart_glueSubtree
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    subtreePart R u (glueSubtree C R u I hzero T) = T := by
  let e := indepFinsetInduceEquiv G
    (fun x => x ∈ R.descendants (G := G) u)
  have hpart : ambientDescendantPart R u
      (glueSubtree C R u I hzero T) = e T := by
    apply Subtype.ext
    apply Subtype.ext
    exact glueSubtree_inter_descendants_eq C R u I hzero T
  unfold subtreePart
  rw [hpart]
  exact e.symm_apply_apply T

@[simp] theorem glueSubtree_subtreePart
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (J : descendantFiber R u I) :
    glueSubtree C R u I hzero (subtreePart R u J.1) = J.1 := by
  have hout := descendantFiber_outside_eq R u I J
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hO | hD
    · have hJO : x ∈ J.1.val \ R.descendants (G := G) u := by
        rw [hout]
        exact hO
      exact (Finset.mem_sdiff.mp hJO).1
    · have hD' := hD
      rw [subtreeLift_part_val R u J.1] at hD'
      exact (Finset.mem_inter.mp hD').1
  · intro hx
    by_cases hxd : x ∈ R.descendants (G := G) u
    · have hL : x ∈ (subtreeLift R u (subtreePart R u J.1)).val := by
        rw [subtreeLift_part_val R u J.1]
        exact Finset.mem_inter.mpr ⟨hx, hxd⟩
      exact Finset.mem_union.mpr (Or.inr hL)
    · have hJO : x ∈ J.1.val \ R.descendants (G := G) u :=
        Finset.mem_sdiff.mpr ⟨hx, hxd⟩
      have hIO : x ∈ I.val \ R.descendants (G := G) u := by
        rw [← hout]
        exact hJO
      exact Finset.mem_union.mpr (Or.inl hIO)


/-- Exact finite bijection between a descendant restriction fiber and subtree
configurations, when the fixed parent is absent.  This is the finite
configuration-space core of the spatial-Markov numerator/mass identity. -/
noncomputable def descendantFiberEquiv
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0) :
    descendantFiber R u I ≃ IndepFinset (R.Subtree (G := G) u) := by
  let e : descendantFiber R u I ≃ IndepFinset (R.Subtree (G := G) u) :=
    { toFun := fun J => subtreePart R u J.1
      invFun := fun T =>
        ⟨glueSubtree C R u I hzero T,
          glueSubtree_restriction_eq C R u I hzero T⟩
      left_inv := by
        intro J
        apply Subtype.ext
        exact glueSubtree_subtreePart C R u I hzero J
      right_inv := by
        intro T
        simpa using subtreePart_glueSubtree C R u I hzero T }
  exact e


@[simp] theorem glueSubtree_card_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    (glueSubtree C R u I hzero T).val.card =
      (I.val \ R.descendants (G := G) u).card +
        (subtreeLift R u T).val.card := by
  unfold glueSubtree
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro x hxO hxD
  exact (Finset.mem_sdiff.mp hxO).2
    (subtreeLift_mem_descendants R u T hxD)

@[simp] theorem descendantFiber_card_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) (hzero : parentOccupationIndicator R I u = 0)
    (J : descendantFiber R u I) :
    J.1.val.card =
      (I.val \ R.descendants (G := G) u).card +
        (subtreePart R u J.1).val.card := by
  have hcard := glueSubtree_card_eq C R u I hzero (subtreePart R u J.1)
  have hglue := glueSubtree_subtreePart C R u I hzero J
  rw [hglue] at hcard
  simpa only [subtreeLift_card] using hcard

/-- The outside hard-core weight divided by the global partition function,
with the descendant partition function restored for the subtree law. -/
noncomputable def fiberFactor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G) : ℝ :=
  C.activity ^ (I.val \ R.descendants (G := G) u).card *
      R.rootedP (G := G) C u / independenceEval G C.activity

/-- Literal hard-core probability factorization on an absent-parent fine fiber.
The factor depends only on the fixed outside configuration. -/
theorem law_probability_fiber_factor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G)
    (hzero : parentOccupationIndicator R I u = 0)
    (J : descendantFiber R u I) :
    C.law.probability J.1 =
      fiberFactor C R u I *
        (R.subtreeLaw (G := G) C u).probability
          (subtreePart R u J.1) := by
  change C.activity ^ J.1.val.card / independenceEval G C.activity =
    (C.activity ^ (I.val \ R.descendants (G := G) u).card *
        independenceEval (R.Subtree (G := G) u) C.activity /
      independenceEval G C.activity) *
      (C.activity ^ (subtreePart R u J.1).val.card /
        independenceEval (R.Subtree (G := G) u) C.activity)
  rw [descendantFiber_card_eq C R u I hzero J]
  have hG : independenceEval G C.activity ≠ 0 :=
    ne_of_gt (independenceEval_pos G C.activity_pos)
  have hsub : independenceEval (R.Subtree (G := G) u) C.activity ≠ 0 :=
    ne_of_gt (independenceEval_pos (R.Subtree (G := G) u) C.activity_pos)
  field_simp [hG, hsub]
  rw [pow_add]


/-- The actual subtree-law marginal of the rooted vertex.  This is a direct
finite partition of `IndepFinset (R.Subtree u)` into root-vacant and
root-occupied configurations; its value is the inherited ratio
`rootedA/rootedP`, not a postulated local law. -/
theorem subtreeLaw_root_occupation_marginal
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ T : IndepFinset (R.Subtree (G := G) u),
      (R.subtreeLaw (G := G) C u).probability T *
        (if R.subtreeRoot (G := G) u ∈ T.val then (1 : ℝ) else 0)) =
      R.occupationProbability (G := G) C u := by
  classical
  let H := R.Subtree (G := G) u
  let r := R.subtreeRoot (G := G) u
  letI : Fintype (AvoidingIndepFinset H r) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset H r) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  calc
    (∑ T : IndepFinset H,
        (ComponentRooting.subtreeLaw (G := G) C R u).probability T *
          (if r ∈ T.val then (1 : ℝ) else 0)) =
        ∑ q : AvoidingIndepFinset H r ⊕ ContainingIndepFinset H r,
          Sum.elim (fun _ => 0)
            (fun T => C.activity ^ T.val.val.card /
              independenceEval H C.activity) q := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv H r)
      intro T
      by_cases h : r ∈ T.val <;>
        simp [H, r, ComponentRooting.subtreeLaw, indepFinsetPartitionEquiv, h,
          Forest.CanonicalFirstRecoveryState.law_probability,
          Forest.hardCoreLaw]
    _ = ∑ T : ContainingIndepFinset H r,
          C.activity ^ T.val.val.card / independenceEval H C.activity := by
      rw [Fintype.sum_sum_type]
      simp
    _ = ∑ U : IndepFinset (deleteClosedNeighborhood H r),
          C.activity ^ (U.val.card + 1) / independenceEval H C.activity := by
      symm
      apply Fintype.sum_equiv (containingEquiv H r)
      intro U
      rw [containingEquiv_card]
    _ = C.activity *
          (∑ U : IndepFinset (deleteClosedNeighborhood H r),
            C.activity ^ U.val.card) / independenceEval H C.activity := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      rw [pow_add, pow_one]
      ring
    _ = C.activity *
          independenceEval (deleteClosedNeighborhood H r) C.activity /
            independenceEval H C.activity := by
      congr 1
      exact congrArg (fun x : ℝ => C.activity * x)
        (independenceEval_eq_sum (G := deleteClosedNeighborhood H r)
          C.activity).symm
    _ = R.occupationProbability (G := G) C u := by
      simp [H, r, ComponentRooting.occupationProbability,
        ComponentRooting.rootedP, ComponentRooting.rootedA]


/-- The root membership test is preserved by the induced-subtree lift. -/
theorem subtreeLift_root_mem_iff
    (R : ComponentRooting G) (u : V)
    (T : IndepFinset (R.Subtree (G := G) u)) :
    R.subtreeRoot (G := G) u ∈ T.val ↔
      u ∈ (subtreeLift R u T).val := by
  change (⟨u, R.self_mem_descendants (G := G) u⟩ ∈ T.val) ↔
    u ∈ Finset.map (Function.Embedding.subtype
      (fun x => x ∈ R.descendants (G := G) u)) T.val
  rw [Finset.mem_map]
  constructor
  · intro h
    exact ⟨⟨u, R.self_mem_descendants (G := G) u⟩, h, rfl⟩
  · rintro ⟨x, hx, hxu⟩
    have hxeq : x = ⟨u, R.self_mem_descendants (G := G) u⟩ := by
      apply Subtype.ext
      exact hxu
    simpa [hxeq] using hx

/-- The actual eta numerator on the full descendant-complement fiber is zero.
This is an honest finite sum: the proof uses the compiled configuration
bijection, the literal hard-core probability factor, and the direct subtree-law
root marginal. -/
theorem descendantComplement_eta_numerator_eq_zero
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (I : IndepFinset G)
    (hzero : parentOccupationIndicator R I u = 0) :
    ∑ J ∈ restrictionFiber (descendantComplement R u) I,
      C.law.probability J * eta C R J u = 0 := by
  classical
  let S := descendantComplement R u
  have hsum : ∀ (f : IndepFinset G → ℝ),
      (∑ J ∈ restrictionFiber S I, f J) =
        ∑ J : descendantFiber R u I, f J.1 := by
    intro f
    apply Finset.sum_subtype
    intro J
    simp [S, restrictionFiber, descendantFiber]
  have hparent : ∀ J : descendantFiber R u I,
      parentOccupationIndicator R J.1 u = 0 := by
    intro J
    by_cases hroot : u = R.rootOf (G := G) u
    · exact parentOccupationIndicator_root R J.1 hroot
    · let p : V := R.selectedParent (G := G) u hroot
      have hp : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hroot
      have hpnot : p ∉ R.descendants (G := G) u :=
        R.not_mem_descendants_child (G := G) hp
      have hpS : p ∈ S := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpnot⟩
      have hocc : occupationIndicator J.1 p = occupationIndicator I p :=
        occupationIndicator_eq_of_restriction_eq hpS J.2
      have hIp : occupationIndicator I p = 0 := by
        rw [← parentOccupationIndicator_eq_selectedParent C R I hroot]
        exact hzero
      rw [parentOccupationIndicator_eq_selectedParent C R J.1 hroot]
      rw [hocc, hIp]
  have hrootIndicator : ∀ J : descendantFiber R u I,
      (if R.subtreeRoot (G := G) u ∈ (subtreePart R u J.1).val
        then (1 : ℝ) else 0) = occupationIndicator J.1 u := by
    intro J
    by_cases huJ : u ∈ J.1.val
    · have huLift : u ∈ (subtreeLift R u (subtreePart R u J.1)).val := by
        rw [subtreeLift_part_val R u J.1]
        exact Finset.mem_inter.mpr ⟨huJ, R.self_mem_descendants (G := G) u⟩
      have hroot : R.subtreeRoot (G := G) u ∈
          (subtreePart R u J.1).val :=
        (subtreeLift_root_mem_iff R u (subtreePart R u J.1)).2 huLift
      simp [occupationIndicator, huJ, hroot]
    · have huLift : u ∉ (subtreeLift R u (subtreePart R u J.1)).val := by
        intro huLift
        apply huJ
        rw [subtreeLift_part_val R u J.1] at huLift
        exact (Finset.mem_inter.mp huLift).1
      have hroot : R.subtreeRoot (G := G) u ∉
          (subtreePart R u J.1).val :=
        fun h => huLift ((subtreeLift_root_mem_iff R u
          (subtreePart R u J.1)).1 h)
      simp [occupationIndicator, huJ, hroot]
  have hoccSum :
      (∑ J : descendantFiber R u I,
        C.law.probability J.1 * occupationIndicator J.1 u) =
        fiberFactor C R u I *
          (∑ T : IndepFinset (R.Subtree (G := G) u),
            (R.subtreeLaw (G := G) C u).probability T *
              (if R.subtreeRoot (G := G) u ∈ T.val then (1 : ℝ) else 0)) := by
    calc
      (∑ J : descendantFiber R u I,
          C.law.probability J.1 * occupationIndicator J.1 u) =
          ∑ J : descendantFiber R u I,
            (fiberFactor C R u I *
              (R.subtreeLaw (G := G) C u).probability
                (subtreePart R u J.1)) * occupationIndicator J.1 u := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [law_probability_fiber_factor C R u I hzero J]
      _ = ∑ J : descendantFiber R u I,
            fiberFactor C R u I *
              ((R.subtreeLaw (G := G) C u).probability
                (subtreePart R u J.1) *
                (if R.subtreeRoot (G := G) u ∈
                    (subtreePart R u J.1).val then (1 : ℝ) else 0)) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hrootIndicator J]
        ring
      _ = fiberFactor C R u I *
          (∑ J : descendantFiber R u I,
            (R.subtreeLaw (G := G) C u).probability
              (subtreePart R u J.1) *
              (if R.subtreeRoot (G := G) u ∈
                  (subtreePart R u J.1).val then (1 : ℝ) else 0)) := by
        rw [Finset.mul_sum]
      _ = fiberFactor C R u I *
          (∑ T : IndepFinset (R.Subtree (G := G) u),
            (R.subtreeLaw (G := G) C u).probability T *
              (if R.subtreeRoot (G := G) u ∈ T.val then (1 : ℝ) else 0)) := by
        congr 1
        simpa [descendantFiberEquiv] using
          (Equiv.sum_comp (descendantFiberEquiv C R u I hzero)
            (fun T : IndepFinset (R.Subtree (G := G) u) =>
              (R.subtreeLaw (G := G) C u).probability T *
                (if R.subtreeRoot (G := G) u ∈ T.val then (1 : ℝ) else 0)))
  have hmass :
      (∑ J : descendantFiber R u I, C.law.probability J.1) =
        fiberFactor C R u I := by
    calc
      (∑ J : descendantFiber R u I, C.law.probability J.1) =
          ∑ J : descendantFiber R u I,
            fiberFactor C R u I *
              (R.subtreeLaw (G := G) C u).probability
                (subtreePart R u J.1) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [law_probability_fiber_factor C R u I hzero J]
      _ = fiberFactor C R u I *
          (∑ J : descendantFiber R u I,
            (R.subtreeLaw (G := G) C u).probability
              (subtreePart R u J.1)) := by
        rw [Finset.mul_sum]
      _ = fiberFactor C R u I *
          (∑ T : IndepFinset (R.Subtree (G := G) u),
            (R.subtreeLaw (G := G) C u).probability T) := by
        congr 1
        simpa [descendantFiberEquiv] using
          (Equiv.sum_comp (descendantFiberEquiv C R u I hzero)
            (fun T : IndepFinset (R.Subtree (G := G) u) =>
              (R.subtreeLaw (G := G) C u).probability T))
      _ = fiberFactor C R u I := by
        rw [(R.subtreeLaw (G := G) C u).probability_sum]
        ring
  rw [hsum (fun J => C.law.probability J * eta C R J u)]
  calc
    (∑ J : descendantFiber R u I,
        C.law.probability J.1 * eta C R J.1 u) =
        ∑ J : descendantFiber R u I,
          C.law.probability J.1 *
            (occupationIndicator J.1 u -
              R.occupationProbability (G := G) C u) := by
      apply Finset.sum_congr rfl
      intro J hJ
      rw [eta, hparent J]
      ring
    _ = (∑ J : descendantFiber R u I,
          C.law.probability J.1 * occupationIndicator J.1 u) -
        R.occupationProbability (G := G) C u *
          (∑ J : descendantFiber R u I, C.law.probability J.1) := by
      calc
        (∑ J : descendantFiber R u I,
            C.law.probability J.1 *
              (occupationIndicator J.1 u -
                R.occupationProbability (G := G) C u)) =
            ∑ J : descendantFiber R u I,
              (C.law.probability J.1 * occupationIndicator J.1 u -
                R.occupationProbability (G := G) C u *
                  C.law.probability J.1) := by
          apply Finset.sum_congr rfl
          intro J hJ
          ring
        _ = (∑ J : descendantFiber R u I,
              C.law.probability J.1 * occupationIndicator J.1 u) -
            (∑ J : descendantFiber R u I,
              R.occupationProbability (G := G) C u * C.law.probability J.1) := by
          rw [Finset.sum_sub_distrib]
        _ = (∑ J : descendantFiber R u I,
              C.law.probability J.1 * occupationIndicator J.1 u) -
            R.occupationProbability (G := G) C u *
              (∑ J : descendantFiber R u I, C.law.probability J.1) := by
          rw [Finset.mul_sum]
    _ = fiberFactor C R u I *
          (∑ T : IndepFinset (R.Subtree (G := G) u),
            (R.subtreeLaw (G := G) C u).probability T *
              (if R.subtreeRoot (G := G) u ∈ T.val then (1 : ℝ) else 0)) -
        R.occupationProbability (G := G) C u * fiberFactor C R u I := by
      rw [hoccSum, hmass]
    _ = 0 := by
      rw [subtreeLaw_root_occupation_marginal]
      ring


/-- Restriction to a smaller set follows from agreement on a superset. -/
theorem restriction_eq_of_subset
    {S D : Finset V} (hSD : S ⊆ D) {I J : IndepFinset G}
    (hIJ : restriction D I = restriction D J) :
    restriction S I = restriction S J := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ restriction D I := by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hx).1, hSD (Finset.mem_inter.mp hx).2⟩
    rw [hIJ] at hx'
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx').1, (Finset.mem_inter.mp hx).2⟩
  · intro hx
    have hx' : x ∈ restriction D J := by
      exact Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hx).1, hSD (Finset.mem_inter.mp hx).2⟩
    rw [← hIJ] at hx'
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hx').1, (Finset.mem_inter.mp hx).2⟩

/-- A rooted parent is outside the descendant subtree of its child. -/
theorem parent_mem_descendantComplement
    (R : ComponentRooting G) {p u : V}
    (hpu : R.IsChild (G := G) p u) :
    p ∈ descendantComplement R u := by
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
    R.not_mem_descendants_child (G := G) hpu⟩

/-- Agreement off a descendant subtree fixes the child's parent indicator. -/
theorem parentOccupationIndicator_eq_of_descendantComplement_restriction_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (u : V) {I J : IndepFinset G}
    (hIJ : restriction (descendantComplement R u) I =
      restriction (descendantComplement R u) J) :
    parentOccupationIndicator R I u = parentOccupationIndicator R J u := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · rw [parentOccupationIndicator_root R I hroot,
      parentOccupationIndicator_root R J hroot]
  · rw [parentOccupationIndicator_eq_selectedParent C R I hroot,
      parentOccupationIndicator_eq_selectedParent C R J hroot]
    exact occupationIndicator_eq_of_restriction_eq
      (parent_mem_descendantComplement R
        (R.selectedParent_isChild (G := G) u hroot)) hIJ

/-- If the actual parent is occupied, hard-core exclusion makes eta zero. -/
theorem eta_eq_zero_of_parentOccupationIndicator_ne_zero
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V)
    (hparent : parentOccupationIndicator R I u ≠ 0) :
    eta C R I u = 0 := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · exact (hparent (parentOccupationIndicator_root R I hroot)).elim
  · let p : V := R.selectedParent (G := G) u hroot
    have hpu : R.IsChild (G := G) p u :=
      R.selectedParent_isChild (G := G) u hroot
    have hpI : p ∈ I.val := by
      by_contra hpI
      apply hparent
      rw [parentOccupationIndicator_eq_selectedParent C R I hroot]
      simp [occupationIndicator, p, hpI]
    have huI : u ∉ I.val := by
      intro huI
      exact I.property hpI huI hpu.1.ne hpu.1
    have hpone : parentOccupationIndicator R I u = 1 := by
      rw [parentOccupationIndicator_eq_selectedParent C R I hroot]
      simp [occupationIndicator, p, hpI]
    rw [eta, hpone]
    simp [occupationIndicator, huI]

/-- Honest finite numerator centering over every ancestor-closed observation fiber. -/
theorem restrictionFiber_eta_numerator_eq_zero_of_ancestorClosed
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (hS : AncestorClosed R S) (u : V) (hu : u ∉ S)
    (I : IndepFinset G) :
    ∑ J ∈ restrictionFiber S I,
      C.law.probability J * eta C R J u = 0 := by
  classical
  let D := descendantComplement R u
  let F := restrictionFiber S I
  have hSD : S ⊆ D := by
    intro v hvS
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      intro hvD
      exact hu (hS hvS ((R.mem_descendants (G := G) u v).mp hvD))⟩
  rw [show (∑ J ∈ restrictionFiber S I,
      C.law.probability J * eta C R J u) =
      ∑ J ∈ F, C.law.probability J * eta C R J u by rfl]
  rw [← Finset.sum_fiberwise F (fun J : IndepFinset G => restriction D J)
    (fun J => C.law.probability J * eta C R J u)]
  apply Finset.sum_eq_zero
  intro K hK
  by_cases hex : ∃ J : IndepFinset G, J ∈ F ∧ restriction D J = K
  · obtain ⟨J₀, hJ₀F, hJ₀K⟩ := hex
    have hfilter : F.filter (fun J : IndepFinset G => restriction D J = K) =
        restrictionFiber D J₀ := by
      ext J
      simp only [Finset.mem_filter, mem_restrictionFiber]
      constructor
      · rintro ⟨hJF, hJK⟩
        exact hJK.trans hJ₀K.symm
      · intro hDJ
        have hSJ : restriction S J = restriction S J₀ :=
          restriction_eq_of_subset hSD hDJ
        have hJ₀SI : restriction S J₀ = restriction S I :=
          (mem_restrictionFiber.mp hJ₀F)
        exact ⟨mem_restrictionFiber.mpr (hSJ.trans hJ₀SI),
          hDJ.trans hJ₀K⟩
    rw [hfilter]
    by_cases hzero : parentOccupationIndicator R J₀ u = 0
    · exact descendantComplement_eta_numerator_eq_zero C R u J₀ hzero
    · apply Finset.sum_eq_zero
      intro J hJ
      rw [eta_eq_zero_of_parentOccupationIndicator_ne_zero C R J u]
      · ring
      · have hparentEq :=
          parentOccupationIndicator_eq_of_descendantComplement_restriction_eq
            C R u (mem_restrictionFiber.mp hJ)
        rw [hparentEq]
        exact hzero
  · apply Finset.sum_eq_zero
    intro J hJF
    exact (hex ⟨J, (Finset.mem_filter.mp hJF).1,
      (Finset.mem_filter.mp hJF).2⟩).elim

/-- Literal finite conditional centering for an unobserved vertex. -/
theorem conditionalExpectation_eta_eq_zero_of_unobserved
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (hS : AncestorClosed R S) (u : V) (hu : u ∉ S)
    (I : IndepFinset G) :
    conditionalExpectation C S (fun J => eta C R J u) I = 0 := by
  unfold conditionalExpectation
  rw [restrictionFiber_eta_numerator_eq_zero_of_ancestorClosed
    C R S hS u hu I]
  simp


/-- The outside of a descendant subtree is ancestor-closed. -/
theorem descendantComplement_ancestorClosed
    (R : ComponentRooting G) (u : V) :
    AncestorClosed R (descendantComplement R u) := by
  intro a b hb hab
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro ha
  apply (Finset.mem_sdiff.mp hb).2
  exact (R.mem_descendants (G := G) u b).mpr
    (ComponentRooting.IsDescendant.trans (G := G) R
      ((R.mem_descendants (G := G) u a).mp ha) hab)

@[simp] theorem occupationIndicator_sq
    (I : IndepFinset G) (u : V) :
    occupationIndicator I u ^ 2 = occupationIndicator I u := by
  by_cases h : u ∈ I.val <;> simp [occupationIndicator, h]

theorem parentOccupationIndicator_sq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    parentOccupationIndicator R I u ^ 2 = parentOccupationIndicator R I u := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · rw [parentOccupationIndicator_root R I hroot]
    ring
  · rw [parentOccupationIndicator_eq_selectedParent C R I hroot]
    by_cases hp : R.selectedParent (G := G) u hroot ∈ I.val <;>
      simp [occupationIndicator, hp]


/-- Occupying a child excludes its selected parent. -/
theorem occupation_mul_parentAbsent
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    occupationIndicator I u *
      (1 - parentOccupationIndicator R I u) = occupationIndicator I u := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · rw [parentOccupationIndicator_root R I hroot]
    ring
  · let p := R.selectedParent (G := G) u hroot
    have hpu : R.IsChild (G := G) p u := R.selectedParent_isChild (G := G) u hroot
    by_cases hp : p ∈ I.val
    · have hu : u ∉ I.val := by
        intro hu
        exact I.property hp hu hpu.1.ne hpu.1
      simp [occupationIndicator, parentOccupationIndicator_eq_selectedParent C R I hroot,
        p, hp, hu]
    · simp [parentOccupationIndicator_eq_selectedParent C R I hroot,
        occupationIndicator, p, hp]

/-- The pointwise eta-square expansion used for its actual second moment. -/
theorem eta_sq_expansion
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (I : IndepFinset G) (u : V) :
    eta C R I u ^ 2 =
      occupationIndicator I u -
        2 * R.occupationProbability (G := G) C u * occupationIndicator I u +
        R.occupationProbability (G := G) C u ^ 2 *
          (1 - parentOccupationIndicator R I u) := by
  have hxi := occupationIndicator_sq I u
  have hp := parentOccupationIndicator_sq C R I u
  have hcross := occupation_mul_parentAbsent C R I u
  have hA : (1 - parentOccupationIndicator R I u) ^ 2 =
      1 - parentOccupationIndicator R I u := by
    nlinarith
  rw [eta]
  calc
    (occupationIndicator I u -
        R.occupationProbability (G := G) C u *
          (1 - parentOccupationIndicator R I u)) ^ 2 =
        occupationIndicator I u ^ 2 -
          2 * R.occupationProbability (G := G) C u *
            (occupationIndicator I u *
              (1 - parentOccupationIndicator R I u)) +
          R.occupationProbability (G := G) C u ^ 2 *
            (1 - parentOccupationIndicator R I u) ^ 2 := by ring
    _ = occupationIndicator I u -
          2 * R.occupationProbability (G := G) C u * occupationIndicator I u +
          R.occupationProbability (G := G) C u ^ 2 *
            (1 - parentOccupationIndicator R I u) := by
      rw [hxi, hcross, hA]

/-- Actual eta second moment, `E eta_u^2 = a_u p_u q_u`. -/
theorem expectation_eta_sq_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ I : IndepFinset G, C.law.probability I * eta C R I u ^ 2) =
      R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u *
        R.vacancyProbability (G := G) C u := by
  have hxi := expectation_occupationIndicator_eq_parentAbsent_mul_probability C R u
  have hA := expectation_one_sub_parentOccupationIndicator C R u
  calc
    (∑ I : IndepFinset G, C.law.probability I * eta C R I u ^ 2) =
        ∑ I : IndepFinset G, C.law.probability I *
          (occupationIndicator I u -
            2 * R.occupationProbability (G := G) C u * occupationIndicator I u +
            R.occupationProbability (G := G) C u ^ 2 *
              (1 - parentOccupationIndicator R I u)) := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [eta_sq_expansion C R I u]
    _ = (∑ I : IndepFinset G,
          C.law.probability I * occupationIndicator I u) -
        2 * R.occupationProbability (G := G) C u *
          (∑ I : IndepFinset G,
            C.law.probability I * occupationIndicator I u) +
        R.occupationProbability (G := G) C u ^ 2 *
          (∑ I : IndepFinset G,
            C.law.probability I *
              (1 - parentOccupationIndicator R I u)) := by
      rw [show (∑ I : IndepFinset G, C.law.probability I *
          (occupationIndicator I u -
            2 * R.occupationProbability (G := G) C u * occupationIndicator I u +
            R.occupationProbability (G := G) C u ^ 2 *
              (1 - parentOccupationIndicator R I u))) =
          ∑ I : IndepFinset G,
            (C.law.probability I * occupationIndicator I u -
              2 * R.occupationProbability (G := G) C u *
                (C.law.probability I * occupationIndicator I u) +
              R.occupationProbability (G := G) C u ^ 2 *
                (C.law.probability I *
                  (1 - parentOccupationIndicator R I u))) by
        apply Finset.sum_congr rfl
        intro I hI
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u *
        R.vacancyProbability (G := G) C u := by
      rw [hxi, hA, R.vacancyProbability_eq_one_sub_occupationProbability]
      ring


theorem conditionalExpectation_centeredOccupationCount_eq_observed
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (hS : AncestorClosed R S) (I : IndepFinset G) :
    conditionalExpectation C S (fun J => centeredOccupationCount C J) I =
      ∑ u ∈ S, R.conditionalMeanDifference (G := G) C u * eta C R I u := by
  classical
  let F := restrictionFiber S I
  let d : V → ℝ := R.conditionalMeanDifference (G := G) C
  have hnum :
      (∑ J ∈ F, C.law.probability J * centeredOccupationCount C J) =
        (∑ u ∈ S, d u * eta C R I u) *
          (∑ J ∈ F, C.law.probability J) := by
    calc
      (∑ J ∈ F, C.law.probability J * centeredOccupationCount C J) =
          ∑ J ∈ F, C.law.probability J *
            (∑ u : V, d u * eta C R J u) := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [centeredOccupationCount_eq_sum_eta C R J]
      _ = ∑ u : V, d u *
            (∑ J ∈ F, C.law.probability J * eta C R J u) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro J hJ
        ring
      _ = (∑ u ∈ (Finset.univ : Finset V) \ S,
            d u * (∑ J ∈ F, C.law.probability J * eta C R J u)) +
          ∑ u ∈ S,
            d u * (∑ J ∈ F, C.law.probability J * eta C R J u) := by
        rw [← Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
          (Finset.subset_univ S)]
      _ = ∑ u ∈ S,
            d u * (∑ J ∈ F, C.law.probability J * eta C R J u) := by
        have hzeroComp :
            (∑ u ∈ (Finset.univ : Finset V) \ S,
              d u * (∑ J ∈ F, C.law.probability J * eta C R J u)) = 0 := by
          apply Finset.sum_eq_zero
          intro u hu
          have huS : u ∉ S := (Finset.mem_sdiff.mp hu).2
          rw [restrictionFiber_eta_numerator_eq_zero_of_ancestorClosed
            C R S hS u huS I]
          ring
        rw [hzeroComp]
        ring
      _ = ∑ u ∈ S, (d u * eta C R I u) *
            (∑ J ∈ F, C.law.probability J) := by
        apply Finset.sum_congr rfl
        intro u hu
        have hconst : ∀ J ∈ F, eta C R J u = eta C R I u := by
          intro J hJF
          exact eta_eq_of_restriction_eq C R hS hu
            (mem_restrictionFiber.mp hJF)
        calc
          d u * (∑ J ∈ F, C.law.probability J * eta C R J u) =
              d u * (∑ J ∈ F, C.law.probability J * eta C R I u) := by
            congr 1
            apply Finset.sum_congr rfl
            intro J hJF
            rw [hconst J hJF]
          _ = d u * (eta C R I u * (∑ J ∈ F, C.law.probability J)) := by
            have hsum :
                (∑ J ∈ F, C.law.probability J * eta C R I u) =
                  eta C R I u * (∑ J ∈ F, C.law.probability J) := by
              calc
                (∑ J ∈ F, C.law.probability J * eta C R I u) =
                    ∑ J ∈ F, eta C R I u * C.law.probability J := by
                      apply Finset.sum_congr rfl
                      intro J hJF
                      ring
                _ = eta C R I u * (∑ J ∈ F, C.law.probability J) := by
                      rw [Finset.mul_sum]
            rw [hsum]
          _ = (d u * eta C R I u) *
              (∑ J ∈ F, C.law.probability J) := by ring
      _ = (∑ u ∈ S, d u * eta C R I u) *
            (∑ J ∈ F, C.law.probability J) := by
        rw [Finset.sum_mul]
  unfold conditionalExpectation
  rw [hnum]
  change (∑ u ∈ S, R.conditionalMeanDifference (G := G) C u *
      eta C R I u) *
      (∑ J ∈ restrictionFiber S I, C.law.probability J) /
      restrictionFiberMass C S I =
    ∑ u ∈ S, R.conditionalMeanDifference (G := G) C u * eta C R I u
  rw [show (∑ J ∈ restrictionFiber S I, C.law.probability J) =
      restrictionFiberMass C S I by rfl]
  apply (div_eq_iff (ne_of_gt (restrictionFiberMass_pos C S I))).2
  ring


/-- A product with one observed eta and one unobserved eta has zero actual
finite numerator. -/
theorem expectation_product_eta_eq_zero_of_observed_unobserved
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (hS : AncestorClosed R S)
    {u v : V} (hu : u ∈ S) (hv : v ∉ S) :
    (∑ I : IndepFinset G,
      C.law.probability I * eta C R I u * eta C R I v) = 0 := by
  classical
  let F : Finset (IndepFinset G) := Finset.univ
  rw [← Finset.sum_fiberwise F (fun I : IndepFinset G => restriction S I)
    (fun I => C.law.probability I * eta C R I u * eta C R I v)]
  apply Finset.sum_eq_zero
  intro K hK
  by_cases hex : ∃ I : IndepFinset G, restriction S I = K
  · obtain ⟨I₀, hI₀K⟩ := hex
    have hfilter : F.filter (fun I : IndepFinset G => restriction S I = K) =
        restrictionFiber S I₀ := by
      ext J
      simp only [Finset.mem_filter, mem_restrictionFiber]
      constructor
      · rintro ⟨hJF, hJK⟩
        exact hJK.trans hI₀K.symm
      · intro hJI₀
        exact ⟨by simp [F], hJI₀.trans hI₀K⟩
    rw [hfilter]
    have hzero := restrictionFiber_eta_numerator_eq_zero_of_ancestorClosed
      C R S hS v hv I₀
    have hconst : ∀ J ∈ restrictionFiber S I₀,
        eta C R J u = eta C R I₀ u := by
      intro J hJ
      exact eta_eq_of_restriction_eq C R hS hu
        (mem_restrictionFiber.mp hJ)
    calc
      (∑ J ∈ restrictionFiber S I₀,
          C.law.probability J * eta C R J u * eta C R J v) =
          ∑ J ∈ restrictionFiber S I₀,
            (C.law.probability J * eta C R J v) * eta C R I₀ u := by
        apply Finset.sum_congr rfl
        intro J hJ
        rw [hconst J hJ]
        ring
      _ = (∑ J ∈ restrictionFiber S I₀,
            C.law.probability J * eta C R J v) * eta C R I₀ u := by
        rw [Finset.sum_mul]
      _ = 0 := by rw [hzero]; ring
  · apply Finset.sum_eq_zero
    intro J hJ
    exact (hex ⟨J, (Finset.mem_filter.mp hJ).2⟩).elim

/-- Distinct actual innovations are pairwise orthogonal. -/
theorem expectation_eta_mul_eta_eq_zero_of_ne
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {u v : V} (huv : u ≠ v) :
    (∑ I : IndepFinset G,
      C.law.probability I * eta C R I u * eta C R I v) = 0 := by
  classical
  by_cases h : R.IsDescendant (G := G) u v
  · let S := descendantComplement R v
    have hS : AncestorClosed R S := descendantComplement_ancestorClosed R v
    have huD : u ∉ R.descendants (G := G) v := by
      intro huD
      have huvlt := R.depth_lt_of_isDescendant_of_ne (G := G) h huv
      have hvl_u := R.depth_le_of_isDescendant (G := G)
        ((R.mem_descendants (G := G) v u).mp huD)
      omega
    have huS : u ∈ S := by
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, huD⟩
    have hvS : v ∉ S := by
      intro hvS
      exact (Finset.mem_sdiff.mp hvS).2
        (R.self_mem_descendants (G := G) v)
    exact expectation_product_eta_eq_zero_of_observed_unobserved
      C R S hS huS hvS
  · let S := descendantComplement R u
    have hS : AncestorClosed R S := descendantComplement_ancestorClosed R u
    have hvS : v ∈ S := by
      have hvD : v ∉ R.descendants (G := G) u := by
        intro hvD
        exact h ((R.mem_descendants (G := G) u v).mp hvD)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvD⟩
    have huS : u ∉ S := by
      intro huS
      exact (Finset.mem_sdiff.mp huS).2
        (R.self_mem_descendants (G := G) u)
    have hz := expectation_product_eta_eq_zero_of_observed_unobserved
      C R S hS hvS huS
    calc
      (∑ I : IndepFinset G,
          C.law.probability I * eta C R I u * eta C R I v) =
          ∑ I : IndepFinset G,
            C.law.probability I * eta C R I v * eta C R I u := by
        apply Finset.sum_congr rfl
        intro I hI
        ring
      _ = 0 := hz



/-- The literal D.17 partial martingale sum `Z_S`. -/
def martingaleProjection
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (I : IndepFinset G) : ℝ :=
  ∑ u ∈ S, R.conditionalMeanDifference (G := G) C u * eta C R I u

/-- Expectation of an arbitrary real observable under the actual finite law. -/
def lawExpectation (C : CanonicalFirstRecoveryState G)
    (f : IndepFinset G → ℝ) : ℝ :=
  ∑ I : IndepFinset G, C.law.probability I * f I

/-- Variance of an arbitrary real observable under the actual finite law. -/
def lawVariance (C : CanonicalFirstRecoveryState G)
    (f : IndepFinset G → ℝ) : ℝ :=
  lawExpectation C (fun I => (f I - lawExpectation C f) ^ 2)

/-- The literal conditional expectation of `X-s` is `Z_S`. -/
theorem conditionalExpectation_centeredOccupationCount_eq_martingaleProjection
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (hS : AncestorClosed R S) (I : IndepFinset G) :
    conditionalExpectation C S (fun J => centeredOccupationCount C J) I =
      martingaleProjection C R S I := by
  exact conditionalExpectation_centeredOccupationCount_eq_observed C R S hS I

/-- Every partial martingale sum is centered under the actual law. -/
theorem expectation_martingaleProjection_eq_zero
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    lawExpectation C (martingaleProjection C R S) = 0 := by
  classical
  unfold lawExpectation martingaleProjection
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        (∑ u ∈ S,
          R.conditionalMeanDifference (G := G) C u * eta C R I u)) =
        ∑ u ∈ S, R.conditionalMeanDifference (G := G) C u *
          (∑ I : IndepFinset G, C.law.probability I * eta C R I u) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro I hI
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [expectation_eta_eq_zero]
      ring

/-- Orthogonality evaluates the second moment of every finite eta sum. -/
theorem expectation_sq_sum_eta
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    (∑ I : IndepFinset G, C.law.probability I *
      (∑ u ∈ S,
        R.conditionalMeanDifference (G := G) C u * eta C R I u) ^ 2) =
      ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
  classical
  let d : V → ℝ := R.conditionalMeanDifference (G := G) C
  have hdouble :
      (∑ I : IndepFinset G, C.law.probability I *
        (∑ u ∈ S, d u * eta C R I u) ^ 2) =
        ∑ u ∈ S, ∑ v ∈ S, d u * d v *
          (∑ I : IndepFinset G,
            C.law.probability I * eta C R I u * eta C R I v) := by
    calc
      (∑ I : IndepFinset G, C.law.probability I *
          (∑ u ∈ S, d u * eta C R I u) ^ 2) =
          ∑ I : IndepFinset G, ∑ u ∈ S, ∑ v ∈ S,
            C.law.probability I *
              ((d u * eta C R I u) * (d v * eta C R I v)) := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [pow_two, Finset.sum_mul_sum]
        simp_rw [Finset.mul_sum]
      _ = ∑ u ∈ S, ∑ v ∈ S, ∑ I : IndepFinset G,
            C.law.probability I *
              ((d u * eta C R I u) * (d v * eta C R I v)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.sum_comm]
      _ = ∑ u ∈ S, ∑ v ∈ S, d u * d v *
            (∑ I : IndepFinset G,
              C.law.probability I * eta C R I u * eta C R I v) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I hI
        ring
  rw [hdouble]
  apply Finset.sum_congr rfl
  intro u hu
  calc
    (∑ v ∈ S, d u * d v *
        (∑ I : IndepFinset G,
          C.law.probability I * eta C R I u * eta C R I v)) =
        d u * d u *
          (∑ I : IndepFinset G,
            C.law.probability I * eta C R I u ^ 2) := by
      rw [Finset.sum_eq_single u]
      · apply congrArg (fun z : ℝ => d u * d u * z)
        apply Finset.sum_congr rfl
        intro I hI
        ring
      · intro v hvS hvu
        rw [expectation_eta_mul_eta_eq_zero_of_ne C R (Ne.symm hvu)]
        ring
      · exact fun huS => (huS hu).elim
    _ = R.vertexVarianceContribution (G := G) C u := by
      rw [expectation_eta_sq_eq C R u]
      unfold ComponentRooting.vertexVarianceContribution
      dsimp [d]
      ring

/-- D.18 first identity: the actual variance of `Z_S` is the sum of `g(u)`. -/
theorem lawVariance_martingaleProjection_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    lawVariance C (martingaleProjection C R S) =
      ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
  rw [lawVariance, expectation_martingaleProjection_eq_zero]
  unfold lawExpectation martingaleProjection
  simp only [sub_zero]
  exact expectation_sq_sum_eta C R S

/-- Removing the observed terms leaves exactly the complementary eta sum. -/
theorem centeredOccupationCount_sub_martingaleProjection
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (I : IndepFinset G) :
    centeredOccupationCount C I - martingaleProjection C R S I =
      ∑ u ∈ (Finset.univ : Finset V) \ S,
        R.conditionalMeanDifference (G := G) C u * eta C R I u := by
  rw [centeredOccupationCount_eq_sum_eta C R I]
  have hsplit := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
    (f := fun u => R.conditionalMeanDifference (G := G) C u * eta C R I u)
    (Finset.subset_univ S)
  unfold martingaleProjection
  linarith

/-- D.18 second identity: the residual mean square is total variance minus the
observed variance contributions. -/
theorem expectation_sq_residual_eq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    (∑ I : IndepFinset G, C.law.probability I *
      (centeredOccupationCount C I - martingaleProjection C R S I) ^ 2) =
      C.variance -
        ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        (centeredOccupationCount C I - martingaleProjection C R S I) ^ 2) =
        ∑ I : IndepFinset G, C.law.probability I *
          (∑ u ∈ (Finset.univ : Finset V) \ S,
            R.conditionalMeanDifference (G := G) C u * eta C R I u) ^ 2 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [centeredOccupationCount_sub_martingaleProjection C R S I]
    _ = ∑ u ∈ (Finset.univ : Finset V) \ S,
          R.vertexVarianceContribution (G := G) C u := by
      exact expectation_sq_sum_eta C R ((Finset.univ : Finset V) \ S)
    _ = C.variance -
          ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u := by
      have hsplit := Finset.sum_sdiff (s₁ := S) (s₂ := (Finset.univ : Finset V))
        (f := fun u => R.vertexVarianceContribution (G := G) C u)
        (Finset.subset_univ S)
      rw [R.sum_vertexVarianceContribution_eq_variance (G := G) C] at hsplit
      linarith

/-- Finite tower property for the literal restriction-fiber conditional
expectation. -/
theorem lawExpectation_conditionalExpectation
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (f : IndepFinset G → ℝ) :
    (∑ I : IndepFinset G, C.law.probability I *
      conditionalExpectation C S f I) =
      ∑ I : IndepFinset G, C.law.probability I * f I := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (IndepFinset G))
    (restriction S) (fun I => C.law.probability I * conditionalExpectation C S f I)]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (IndepFinset G))
    (restriction S) (fun I => C.law.probability I * f I)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hne : (Finset.univ.filter
      (fun I : IndepFinset G => restriction S I = T)).Nonempty
  · obtain ⟨I₀, hI₀⟩ := hne
    have hI₀T : restriction S I₀ = T := by simpa using hI₀
    have hconst : ∀ I ∈ Finset.univ.filter
        (fun I : IndepFinset G => restriction S I = T),
        conditionalExpectation C S f I = conditionalExpectation C S f I₀ := by
      intro I hI
      apply conditionalExpectation_eq_of_restriction_eq
      have hIT : restriction S I = T := by simpa using hI
      exact hIT.trans hI₀T.symm
    calc
      (∑ I ∈ Finset.univ with restriction S I = T,
          C.law.probability I * conditionalExpectation C S f I) =
          (∑ I ∈ Finset.univ with restriction S I = T,
            C.law.probability I) * conditionalExpectation C S f I₀ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I hI
        rw [hconst I hI]
      _ = restrictionFiberMass C S I₀ * conditionalExpectation C S f I₀ := by
        congr 1
        unfold restrictionFiberMass restrictionFiber
        apply Finset.sum_congr
        · ext I
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hI₀T]
        · intro I hI
          rfl
      _ = ∑ I ∈ Finset.univ with restriction S I = T,
          C.law.probability I * f I := by
        unfold conditionalExpectation
        rw [mul_div_cancel₀ _ (ne_of_gt (restrictionFiberMass_pos C S I₀))]
        unfold restrictionFiber
        apply Finset.sum_congr
        · ext I
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hI₀T]
        · intro I hI
          rfl
  · have hempty : Finset.univ.filter
        (fun I : IndepFinset G => restriction S I = T) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

theorem conditionalExpectation_restriction_mul
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (g : Finset V → ℝ) (f : IndepFinset G → ℝ) (I : IndepFinset G) :
    conditionalExpectation C S (fun J => g (restriction S J) * f J) I =
      g (restriction S I) * conditionalExpectation C S f I := by
  classical
  unfold conditionalExpectation
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  change C.law.probability J * (g (restriction S J) * f J) =
    g (restriction S I) * (C.law.probability J * f J)
  rw [(mem_restrictionFiber.mp hJ)]
  ring

 theorem lawExpectation_restriction_mul_conditionalExpectation
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (g : Finset V → ℝ) (f : IndepFinset G → ℝ) :
    (∑ I : IndepFinset G, C.law.probability I *
      (g (restriction S I) * conditionalExpectation C S f I)) =
      ∑ I : IndepFinset G, C.law.probability I *
        (g (restriction S I) * f I) := by
  calc
    (∑ I : IndepFinset G, C.law.probability I *
        (g (restriction S I) * conditionalExpectation C S f I)) =
      ∑ I : IndepFinset G, C.law.probability I *
        conditionalExpectation C S
          (fun J => g (restriction S J) * f J) I := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [conditionalExpectation_restriction_mul C S g f I]
    _ = ∑ I : IndepFinset G, C.law.probability I *
        (g (restriction S I) * f I) :=
      lawExpectation_conditionalExpectation C S
        (fun J => g (restriction S J) * f J)

