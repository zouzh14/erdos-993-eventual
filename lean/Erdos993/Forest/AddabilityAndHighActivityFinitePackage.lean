import Erdos993.Forest.BipartitionConditioning
import Erdos993.Forest.ActualRootedVariance
import Erdos993.Forest.IndexVarianceLocalization

/-!
# Addability and the finite high-activity package

This module proves the finite statements C.35--C.39 for the actual hard-core
law.  The lower activity bound is always an explicit theorem hypothesis.  The
only canonical first-recovery data used by a conditional law are the global
rank and the coefficient rise at that rank.
-/

open scoped BigOperators

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

namespace Erdos993
namespace Forest

noncomputable section

open ActualRootedVariance

noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-! ## The one addability statistic and its natural count -/

/-- The actual finite set of vertices addable to `s`. -/
def addableVertices (s : IndepFinset G) : Finset V :=
  Finset.univ.filter fun v =>
    v ∉ s.val ∧ ∀ u ∈ s.val, ¬ G.Adj v u

/-- Natural-valued version of the addability count. -/
def naturalAddableCount (s : IndepFinset G) : ℕ :=
  (addableVertices (G := G) s).card

@[simp] theorem mem_addableVertices (s : IndepFinset G) (v : V) :
    v ∈ addableVertices (G := G) s ↔
      v ∉ s.val ∧ ∀ u ∈ s.val, ¬ G.Adj v u := by
  simp [addableVertices]

/-- The real cast of the natural count is exactly the C.42--C.43 statistic. -/
theorem natCast_naturalAddableCount_eq_actualAddableCount
    (s : IndepFinset G) :
    (naturalAddableCount (G := G) s : ℝ) =
      actualAddableCount (G := G) s := by
  classical
  simp [naturalAddableCount, addableVertices, actualAddableCount,
    addableIndicator]

/-- Package spelling of the indicator; definitionally the one exported by
`BipartitionConditioning`. -/
abbrev finitePackageAddableIndicator (s : IndepFinset G) (v : V) : ℝ :=
  addableIndicator (G := G) s v

/-- Package spelling of the real count; definitionally the one exported by
`BipartitionConditioning`. -/
abbrev finitePackageAddableCount (s : IndepFinset G) : ℝ :=
  actualAddableCount (G := G) s

@[simp] theorem finitePackageAddableIndicator_eq_conditioning
    (s : IndepFinset G) (v : V) :
    finitePackageAddableIndicator (G := G) s v =
      addableIndicator (G := G) s v := rfl

@[simp] theorem finitePackageAddableCount_eq_conditioning
    (s : IndepFinset G) :
    finitePackageAddableCount (G := G) s =
      actualAddableCount (G := G) s := rfl

/-! ## C.35: exact insertion double-count -/

/-- The literal uniform mean of the actual real addability count on rank `k`.
The denominator is the actual number of independent `k`-sets. -/
def uniformRankAddableMean (k : ℕ) : ℝ :=
  (∑ s : IndepFinset G,
      if s.val.card = k then actualAddableCount (G := G) s else 0) /
    independenceCoefficients G k

/-- Fixed-site rank-preserving form of the insertion/erasure bijection. -/
theorem ranked_singleSite_addable_eq_occupied (v : V) (k : ℕ) :
    (∑ s : IndepFinset G,
      if s.val.card = k then addableIndicator (G := G) s v else 0) =
    ∑ t : IndepFinset G,
      if t.val.card = k + 1 then occupiedIndicator (G := G) t v else 0 := by
  classical
  let fA : AddableAt G v → ℝ := fun s =>
    if s.1.val.card = k then 1 else 0
  let fO : OccupiedAt G v → ℝ := fun t =>
    if t.1.val.card = k + 1 then 1 else 0
  calc
    (∑ s : IndepFinset G,
        if s.val.card = k then addableIndicator (G := G) s v else 0) =
      ∑ s : IndepFinset G,
        if (v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u)
        then (if s.val.card = k then 1 else 0) else 0 := by
          apply Finset.sum_congr rfl
          intro s hs
          unfold addableIndicator
          by_cases hr : s.val.card = k <;>
            by_cases ha : v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u <;>
            simp [hr, ha]
    _ = ∑ s : AddableAt G v, fA s := by
        unfold fA
        rw [← Finset.sum_filter]
        exact Finset.sum_subtype
          (Finset.univ.filter fun s : IndepFinset G =>
            v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u)
          (by intro s; simp)
          (fun s : IndepFinset G => if s.val.card = k then 1 else 0)
    _ = ∑ t : OccupiedAt G v, fO t := by
      rw [← (addableOccupiedEquiv (G := G) v).sum_comp]
      apply Finset.sum_congr rfl
      intro s hs
      unfold fA fO
      change (if s.1.val.card = k then 1 else 0) =
        if (insertAddable (G := G) v s).val.card = k + 1 then 1 else 0
      rw [insertAddable_card (G := G)]
      simp only [Nat.add_one_inj]
    _ = ∑ t : IndepFinset G,
        if (v ∈ t.val) then
          (if t.val.card = k + 1 then 1 else 0) else 0 := by
      unfold fO
      symm
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype
        (Finset.univ.filter fun t : IndepFinset G => v ∈ t.val)
        (by intro t; simp)
        (fun t : IndepFinset G => if t.val.card = k + 1 then 1 else 0)
    _ = ∑ t : IndepFinset G,
        if t.val.card = k + 1 then occupiedIndicator (G := G) t v else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      unfold occupiedIndicator
      by_cases hr : t.val.card = k + 1 <;> by_cases ho : v ∈ t.val <;>
        simp [hr, ho]

/-- The unnormalized insertion double count:
`sum_{|I|=k} A(I) = (k+1) i_{k+1}`. -/
theorem rank_addable_sum_eq_succ_mul_coefficient (k : ℕ) :
    (∑ s : IndepFinset G,
      if s.val.card = k then actualAddableCount (G := G) s else 0) =
    ((k + 1 : ℕ) : ℝ) * independenceCoefficients G (k + 1) := by
  classical
  calc
    (∑ s : IndepFinset G,
        if s.val.card = k then actualAddableCount (G := G) s else 0) =
      ∑ v : V, ∑ s : IndepFinset G,
        if s.val.card = k then addableIndicator (G := G) s v else 0 := by
      unfold actualAddableCount
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      split <;> simp_all
    _ = ∑ v : V, ∑ t : IndepFinset G,
        if t.val.card = k + 1 then occupiedIndicator (G := G) t v else 0 := by
      apply Finset.sum_congr rfl
      intro v hv
      exact ranked_singleSite_addable_eq_occupied (G := G) v k
    _ = ∑ t : IndepFinset G,
        if t.val.card = k + 1 then (t.val.card : ℝ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      split
      · rw [sum_occupiedIndicator (G := G)]
      · simp_all
    _ = ((k + 1 : ℕ) : ℝ) * independenceCoefficients G (k + 1) := by
      rw [← Finset.sum_filter]
      simp only [independenceCoefficients, independenceCoeff]
      have hconst :
          (∑ t ∈ Finset.univ.filter
              (fun t : IndepFinset G => t.val.card = k + 1),
            (t.val.card : ℝ)) =
          ∑ _t ∈ Finset.univ.filter
              (fun t : IndepFinset G => t.val.card = k + 1),
            ((k + 1 : ℕ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact_mod_cast (Finset.mem_filter.mp ht).2
      rw [hconst]
      simp [mul_comm]
      ring

/-- **C.35.** Exact insertion double-count with explicit real casts. -/
theorem C35_insertion_double_count (k : ℕ)
    (hk : 0 < independenceCoefficients G k) :
    independenceCoefficients G k * uniformRankAddableMean (G := G) k =
      ((k + 1 : ℕ) : ℝ) * independenceCoefficients G (k + 1) := by
  unfold uniformRankAddableMean
  rw [mul_div_cancel₀ _ (ne_of_gt hk),
    rank_addable_sum_eq_succ_mul_coefficient (G := G)]

/-! ## C.36: unchanged-activity expectation identity -/

/-- Literal hard-core expectation of the one actual addability count. -/
def hardCoreExpectedAddable (z : ℝ) (hz : 0 < z) : ℝ :=
  ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
    actualAddableCount (G := G) s

@[simp] theorem finitePackageExpectedAddable_eq_conditioning
    (z : ℝ) (hz : 0 < z) :
    hardCoreExpectedAddable (G := G) z hz =
      ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
        actualAddableCount (G := G) s := rfl

/-- **C.36.** At the same global activity,
`z * E_z[A] = E_z[X]`. -/
theorem C36_activity_mul_expectedAddable_eq_mean
    (z : ℝ) (hz : 0 < z) :
    z * hardCoreExpectedAddable (G := G) z hz =
      (hardCoreLaw G z hz).mean := by
  classical
  unfold hardCoreExpectedAddable FiniteLatticeLaw.mean actualAddableCount
  calc
    z * (∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
          ∑ v : V, addableIndicator (G := G) s v) =
      ∑ s : IndepFinset G, ∑ v : V,
        z * ((hardCoreLaw G z hz).probability s *
          addableIndicator (G := G) s v) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum, Finset.mul_sum]
    _ = ∑ v : V, ∑ s : IndepFinset G,
        z * ((hardCoreLaw G z hz).probability s *
          addableIndicator (G := G) s v) := by
      rw [Finset.sum_comm]
    _ = ∑ v : V, z * ∑ s : IndepFinset G,
        (hardCoreLaw G z hz).probability s *
          addableIndicator (G := G) s v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
    _ = ∑ v : V, singleSiteOccupationProbability (G := G) z hz v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [sum_probability_mul_addableIndicator (G := G) z hz v,
        ← singleSiteOccupationProbability_eq_z_mul_addable (G := G) z hz v]
    _ = ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
        (s.val.card : ℝ) := by
      simp_rw [← sum_probability_mul_occupiedIndicator (G := G) z hz]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.mul_sum, sum_occupiedIndicator (G := G)]

/-- Canonical specialization of C.36. -/
theorem C36_canonical (C : CanonicalFirstRecoveryState G) :
    C.activity * hardCoreExpectedAddable (G := G) C.activity C.activity_pos =
      (C.index : ℝ) := by
  rw [C36_activity_mul_expectedAddable_eq_mean (G := G)]
  exact C.mean_eq_index

/-! ## C.37: literal conditioning on the global first-recovery rank -/

/-- Literal normalized finite hard-core conditional expectation of addability
on the global event `X=k`. -/
def hardCoreConditionalExpectedAddable (z : ℝ) (hz : 0 < z) (k : ℕ) : ℝ :=
  (∑ s : IndepFinset G,
      if s.val.card = k then
        (hardCoreLaw G z hz).probability s * actualAddableCount (G := G) s
      else 0) /
    (hardCoreLaw G z hz).rankMass k

/-- A fixed-rank hard-core conditional law is literally uniform. -/
theorem hardCoreConditionalExpectedAddable_eq_uniform
    (z : ℝ) (hz : 0 < z) (k : ℕ)
    (hk : 0 < independenceCoefficients G k) :
    hardCoreConditionalExpectedAddable (G := G) z hz k =
      uniformRankAddableMean (G := G) k := by
  let S : ℝ := ∑ s : IndepFinset G,
    if s.val.card = k then actualAddableCount (G := G) s else 0
  let w : ℝ := z ^ k / independenceEval G z
  have hw : w ≠ 0 := div_ne_zero (ne_of_gt (pow_pos hz k))
    (ne_of_gt (independenceEval_pos G hz))
  have hnum :
      (∑ s : IndepFinset G,
        if s.val.card = k then
          (hardCoreLaw G z hz).probability s * actualAddableCount (G := G) s
        else 0) = w * S := by
    unfold S w
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hsk : s.val.card = k
    · simp [hsk, hardCoreLaw]
    · simp [hsk]
  unfold hardCoreConditionalExpectedAddable uniformRankAddableMean
  rw [hnum, hardCoreLaw_rankMass_eq_coefficient]
  unfold w S
  field_simp [ne_of_gt hk, ne_of_gt (pow_pos hz k),
    ne_of_gt (independenceEval_pos G hz)]

/-- Exact coefficient-ratio form of the global rank conditional expectation. -/
theorem hardCoreConditionalExpectedAddable_eq_ratio
    (z : ℝ) (hz : 0 < z) (k : ℕ)
    (hk : 0 < independenceCoefficients G k) :
    hardCoreConditionalExpectedAddable (G := G) z hz k =
      ((k + 1 : ℕ) : ℝ) * independenceCoefficients G (k + 1) /
        independenceCoefficients G k := by
  rw [hardCoreConditionalExpectedAddable_eq_uniform (G := G) z hz k hk]
  unfold uniformRankAddableMean
  rw [rank_addable_sum_eq_succ_mul_coefficient (G := G)]

/-- **C.37, identity.** The literal conditional hard-core expectation at the
global first-recovery rank. -/
theorem C37_conditionalExpectedAddable_eq
    (C : CanonicalFirstRecoveryState G) :
    hardCoreConditionalExpectedAddable (G := G)
        C.activity C.activity_pos C.index =
      ((C.index + 1 : ℕ) : ℝ) *
          independenceCoefficients G (C.index + 1) /
        independenceCoefficients G C.index := by
  exact hardCoreConditionalExpectedAddable_eq_ratio (G := G)
    C.activity C.activity_pos C.index C.center_coeff_pos

/-- **C.37, strict form.** Global first recovery gives
`E[A | X=s] > s+1`. -/
theorem C37_conditionalExpectedAddable_gt
    (C : CanonicalFirstRecoveryState G) :
    ((C.index + 1 : ℕ) : ℝ) <
      hardCoreConditionalExpectedAddable (G := G)
        C.activity C.activity_pos C.index := by
  rw [C37_conditionalExpectedAddable_eq (G := G) C]
  apply (lt_div_iff₀ C.center_coeff_pos).2
  have hrise := C.firstRecovery.isRecovery.2
  have hspos : (0 : ℝ) < ((C.index + 1 : ℕ) : ℝ) := by positivity
  nlinarith

/-! ## Global marginal and moment adapters used by C.38--C.39 -/

/-- The sum of actual global occupation marginals is the hard-core mean. -/
theorem sum_singleSiteOccupationProbability_eq_mean
    (z : ℝ) (hz : 0 < z) :
    (∑ v : V, singleSiteOccupationProbability (G := G) z hz v) =
      (hardCoreLaw G z hz).mean := by
  classical
  simp_rw [← sum_probability_mul_occupiedIndicator (G := G) z hz]
  rw [Finset.sum_comm]
  calc
    (∑ s : IndepFinset G, ∑ v : V,
        (hardCoreLaw G z hz).probability s *
          occupiedIndicator (G := G) s v) =
      ∑ s : IndepFinset G,
        (hardCoreLaw G z hz).probability s * (s.val.card : ℝ) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [← Finset.mul_sum, sum_occupiedIndicator (G := G)]
    _ = (hardCoreLaw G z hz).mean := rfl

/-- A bounded natural statistic satisfies `E[X^2] ≤ n E[X]`. -/
theorem FiniteLatticeLaw.secondMoment_le_natCast_mul_mean_of_stat_le
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (n : ℕ)
    (hstat : ∀ a, L.stat a ≤ n) :
    L.secondMoment ≤ (n : ℝ) * L.mean := by
  unfold secondMoment mean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  calc
    L.probability a * (L.stat a : ℝ) ^ 2 ≤
        L.probability a * ((n : ℝ) * (L.stat a : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (L.probability_nonneg a)
      have hx0 : (0 : ℝ) ≤ L.stat a := Nat.cast_nonneg _
      have hxn : (L.stat a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hstat a
      nlinarith
    _ = (n : ℝ) * (L.probability a * (L.stat a : ℝ)) := by ring

/-! ## Rooted subtree product adapters -/

/-- The vertices strictly below a child, viewed in the ambient component. -/
def childRemainder (R : ComponentRooting G) (v : V) : Finset V :=
  (R.descendants (G := G) v).erase v

/-- The root-deleted descendant branch is exactly the union of the strict
child remainders. -/
theorem mem_childRemainder_biUnion_iff
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u x : V) :
    x ∈ (R.children (G := G) u).biUnion (childRemainder (G := G) R) ↔
      x ∈ R.descendants (G := G) u ∧ x ≠ u ∧ ¬ G.Adj u x := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨v, hv, hx⟩
    have hvchild := (R.mem_children (G := G) u v).mp hv
    have hxerase := Finset.mem_erase.mp hx
    have hxdesc := (R.mem_descendants (G := G) v x).mp hxerase.2
    have hxdescu := R.child_descendant (G := G) hvchild hxdesc
    refine ⟨(R.mem_descendants (G := G) u x).mpr hxdescu, ?_, ?_⟩
    · intro hxu
      subst x
      exact R.not_mem_descendants_child (G := G) hvchild hxerase.2
    · intro hadj
      have hxchild :=
        (R.adj_of_descendant_iff_isChild (G := G) hG hxdescu).mp hadj
      have hvx : v = x :=
        R.child_eq_of_common_descendant (G := G) hG hvchild hxchild hxdesc
          Relation.ReflTransGen.refl
      exact hxerase.1 hvx.symm
  · rintro ⟨hxdesc, hxne, hxnadj⟩
    have hxrel := (R.mem_descendants (G := G) u x).mp hxdesc
    rcases (R.isDescendant_iff_eq_or_child_descendant (G := G) u x).mp hxrel with
      hxu | ⟨v, hvchild, hxv⟩
    · exact (hxne hxu.symm).elim
    · apply Finset.mem_biUnion.mpr
      refine ⟨v, (R.mem_children (G := G) u v).mpr hvchild,
        Finset.mem_erase.mpr ⟨?_, (R.mem_descendants (G := G) v x).mpr hxv⟩⟩
      intro hxvEq
      subst x
      exact hxnadj hvchild.1

/-- Identity-on-vertices graph isomorphism for the occupied-root remainder. -/
def deleteClosedSubtreeRootIsoChildRemainders
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) ≃g
      G.induce (↑((R.children (G := G) u).biUnion
        (childRemainder (G := G) R)) : Set V) where
  toEquiv :=
    { toFun := fun x => ⟨x.1.1,
        (mem_childRemainder_biUnion_iff (G := G) hG R u x.1.1).2 ⟨
          x.1.2, by
            intro hxu
            apply x.2.1
            exact Subtype.ext hxu, by
            intro hadj
            apply x.2.2
            exact hadj⟩⟩
      invFun := fun x => ⟨⟨x.1,
          ((mem_childRemainder_biUnion_iff (G := G) hG R u x.1).1 x.2).1⟩,
        by
          have hx := (mem_childRemainder_biUnion_iff
            (G := G) hG R u x.1).1 x.2
          exact ⟨by
            intro hEq
            exact hx.2.1 (congrArg Subtype.val hEq), hx.2.2⟩⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  map_rel_iff' := by intro x y; rfl

/-- Identity-on-vertices graph isomorphism for one strict child remainder. -/
def deleteSubtreeRootIsoRemainder
    (R : ComponentRooting G) (v : V) :
    deleteVertex (R.Subtree (G := G) v) (R.subtreeRoot (G := G) v) ≃g
      G.induce (↑(childRemainder (G := G) R v) : Set V) where
  toEquiv :=
    { toFun := fun x => ⟨x.1.1,
        Finset.mem_erase.mpr ⟨by
          intro hxv
          apply x.2
          exact Subtype.ext hxv, x.1.2⟩⟩
      invFun := fun x => ⟨⟨x.1, (Finset.mem_erase.mp x.2).2⟩, by
        intro hEq
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val hEq)⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  map_rel_iff' := by intro x y; rfl

theorem independenceEval_eq_of_graphIso
    {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (z : ℝ) :
    independenceEval H z = independenceEval K z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]

/-- Strict child remainders are pairwise disjoint. -/
theorem childRemainders_pairwiseDisjoint
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    (R.children (G := G) u).toSet.PairwiseDisjoint
      (childRemainder (G := G) R) := by
  classical
  intro v hv w hw hvw
  apply Finset.disjoint_left.2
  intro x hxv hxw
  have hdescDisj :=
    R.children_pairwiseDisjoint_descendants (G := G) hG u hv hw hvw
  exact (Finset.disjoint_left.1 hdescDisj)
    (Finset.mem_erase.mp hxv).2 (Finset.mem_erase.mp hxw).2

/-- Different strict child remainders have no ambient edge between them. -/
theorem childRemainders_cross_nonadjacent
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    ∀ a ∈ R.children (G := G) u, ∀ b ∈ R.children (G := G) u, a ≠ b →
      ∀ ⦃x : V⦄ ⦃y : V⦄,
        x ∈ childRemainder (G := G) R a →
        y ∈ childRemainder (G := G) R b → ¬ G.Adj x y := by
  classical
  intro a ha b hb hab x y hx hy
  exact R.not_adj_of_distinct_child_descendants (G := G) hG
    ((R.mem_children (G := G) u a).mp ha)
    ((R.mem_children (G := G) u b).mp hb) hab
    ((R.mem_descendants (G := G) a x).mp (Finset.mem_erase.mp hx).2)
    ((R.mem_descendants (G := G) b y).mp (Finset.mem_erase.mp hy).2)

/-- Exact subtree ratio/product recurrence:
`A_u = z * ∏_{v child of u} Q_v`, at the unchanged global activity. -/
theorem rootedA_eq_activity_mul_prod_rootedQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.rootedA (G := G) C u =
      C.activity * ∏ v ∈ R.children (G := G) u,
        R.rootedQ (G := G) C v := by
  classical
  unfold ComponentRooting.rootedA ComponentRooting.rootedQ
  apply congrArg (fun t : ℝ => C.activity * t)
  calc
    independenceEval
        (deleteClosedNeighborhood (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) C.activity =
      independenceEval
        (G.induce (↑((R.children (G := G) u).biUnion
          (childRemainder (G := G) R)) : Set V)) C.activity :=
        independenceEval_eq_of_graphIso
          (deleteClosedSubtreeRootIsoChildRemainders
            (G := G) C.isForest R u) C.activity
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval
          (G.induce (↑(childRemainder (G := G) R v) : Set V))
          C.activity := by
      exact independenceEval_induceFinset_biUnion G
        (R.children (G := G) u) (childRemainder (G := G) R)
        (childRemainders_pairwiseDisjoint (G := G) C.isForest R u)
        (childRemainders_cross_nonadjacent (G := G) C.isForest R u)
        C.activity
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) C.activity := by
      apply Finset.prod_congr rfl
      intro v hv
      exact (independenceEval_eq_of_graphIso
        (deleteSubtreeRootIsoRemainder (G := G) R v) C.activity).symm

/-- A root-vacant subtree partition function is bounded by the unrestricted one. -/
theorem rootedQ_le_rootedP
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.rootedQ (G := G) C u ≤ R.rootedP (G := G) C u := by
  rw [R.rootedP_eq_rootedQ_add_rootedA (G := G) C u]
  exact le_add_of_nonneg_right (R.rootedA_pos (G := G) C u).le

/-- The occupied contribution is at most `z` times the vacant contribution. -/
theorem rootedA_le_activity_mul_rootedQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.rootedA (G := G) C u ≤ C.activity * R.rootedQ (G := G) C u := by
  rw [rootedA_eq_activity_mul_prod_rootedQ (G := G) C R u,
    R.rootedQ_eq_prod_rootedP (G := G) C u]
  apply mul_le_mul_of_nonneg_left _ C.activity_pos.le
  exact Finset.prod_le_prod
    (fun v _ => (R.rootedQ_pos (G := G) C v).le)
    (fun v _ => rootedQ_le_rootedP (G := G) C R v)

/-- Universal finite hard-core vacancy bound on every actual descendant subtree. -/
theorem one_div_one_add_activity_le_vacancyProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    1 / (1 + C.activity) ≤ R.vacancyProbability (G := G) C u := by
  have hP := R.rootedP_pos (G := G) C u
  have hA := rootedA_le_activity_mul_rootedQ (G := G) C R u
  unfold ComponentRooting.vacancyProbability
  apply (div_le_div_iff₀ (by linarith [C.activity_pos]) hP).2
  rw [R.rootedP_eq_rootedQ_add_rootedA (G := G) C u]
  nlinarith

/-- Under `z<27`, every actual descendant-subtree vacancy probability is
strictly larger than `1/28`. -/
theorem one_div_twentyEight_lt_vacancyProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (hz27 : C.activity < 27) :
    (1 : ℝ) / 28 < R.vacancyProbability (G := G) C u := by
  refine lt_of_lt_of_le ?_
    (one_div_one_add_activity_le_vacancyProbability (G := G) C R u)
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 28)
    (by linarith [C.activity_pos] : 0 < 1 + C.activity)).2
  nlinarith

/-- With at most one child, the exact rooted odds exceed `3/56`. -/
theorem rootedA_div_rootedQ_gt_three_div_fiftySix_of_children_card_le_one
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (hcard : (R.children (G := G) u).card ≤ 1) :
    (3 : ℝ) / 56 < R.rootedA (G := G) C u / R.rootedQ (G := G) C u := by
  classical
  by_cases h0 : R.children (G := G) u = ∅
  · rw [rootedA_eq_activity_mul_prod_rootedQ (G := G) C R u,
      R.rootedQ_eq_prod_rootedP (G := G) C u, h0]
    simp
    norm_num at hzlow ⊢
    linarith
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h0
    have hsing : R.children (G := G) u = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv, ?_⟩
      intro w hw
      exact (Finset.card_le_one.mp hcard) w hw v hv
    have hvac := one_div_twentyEight_lt_vacancyProbability
      (G := G) C R v hz27
    rw [rootedA_eq_activity_mul_prod_rootedQ (G := G) C R u,
      R.rootedQ_eq_prod_rootedP (G := G) C u, hsing]
    simp only [Finset.prod_singleton]
    unfold ComponentRooting.vacancyProbability at hvac
    have hQ := R.rootedQ_pos (G := G) C v
    have hP := R.rootedP_pos (G := G) C v
    have huv : (3 : ℝ) / 56 < C.activity * (R.rootedQ (G := G) C v /
        R.rootedP (G := G) C v) := by nlinarith
    calc
      (3 : ℝ) / 56 < C.activity *
          (R.rootedQ (G := G) C v / R.rootedP (G := G) C v) := huv
      _ = (C.activity * R.rootedQ (G := G) C v) /
          R.rootedP (G := G) C v := by ring

/-- A low-outdegree rooted vertex has actual conditional occupation probability
strictly larger than `3/59`. -/
theorem occupationProbability_gt_three_div_fiftyNine_of_children_card_le_one
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (hcard : (R.children (G := G) u).card ≤ 1) :
    (3 : ℝ) / 59 < R.occupationProbability (G := G) C u := by
  have hodds :=
    rootedA_div_rootedQ_gt_three_div_fiftySix_of_children_card_le_one
      (G := G) C R u hzlow hz27 hcard
  have hQ := R.rootedQ_pos (G := G) C u
  have hA := R.rootedA_pos (G := G) C u
  unfold ComponentRooting.occupationProbability
  rw [R.rootedP_eq_rootedQ_add_rootedA (G := G) C u]
  have hcross := (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 56) hQ).1 hodds
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 59) (add_pos hQ hA)).2
  nlinarith

/-! ## Finite partition monotonicity adapter -/

private noncomputable def inducedLift
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x) :
    IndepFinset (G.induce {x | q x}) → IndepFinset (G.induce {x | p x}) := by
  intro s
  let sq := indepFinsetInduceEquiv G q s
  exact (indepFinsetInduceEquiv G p).symm
    ⟨sq.val, fun x hx => hqp x (sq.property x hx)⟩
private theorem induceEquiv_val
    (G : SimpleGraph V) (p : V → Prop)
    (s : IndepFinset (G.induce {x | p x})) :
    (indepFinsetInduceEquiv G p s).val.val =
      Finset.map (Function.Embedding.subtype p) s.val := by
  rfl
private theorem inducedLift_ambient
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x)
    (s : IndepFinset (G.induce {x | q x})) :
    (indepFinsetInduceEquiv G p (inducedLift G p q hqp s)).val.val =
      (indepFinsetInduceEquiv G q s).val.val := by
  unfold inducedLift
  rw [Equiv.apply_symm_apply]
private theorem inducedLift_injective
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x) :
    Function.Injective (inducedLift G p q hqp) := by
  intro s t h
  apply Subtype.ext
  apply Finset.map_injective (Function.Embedding.subtype q)
  have hh := congrArg (fun r => (indepFinsetInduceEquiv G p r).val.val) h
  have hps :
      (indepFinsetInduceEquiv G p (inducedLift G p q hqp s)).val.val =
        Finset.map (Function.Embedding.subtype q) s.val := by
    calc
      _ = (indepFinsetInduceEquiv G q s).val.val := inducedLift_ambient G p q hqp s
      _ = _ := induceEquiv_val G q s
  have hpt :
      (indepFinsetInduceEquiv G p (inducedLift G p q hqp t)).val.val =
        Finset.map (Function.Embedding.subtype q) t.val := by
    calc
      _ = (indepFinsetInduceEquiv G q t).val.val := inducedLift_ambient G p q hqp t
      _ = _ := induceEquiv_val G q t
  exact hps.symm.trans (by
    dsimp at hh
    exact hh.trans hpt)
private theorem inducedLift_card
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x)
    (s : IndepFinset (G.induce {x | q x})) :
    (inducedLift G p q hqp s).val.card = s.val.card := by
  have hh := congrArg Finset.card (inducedLift_ambient G p q hqp s)
  rw [induceEquiv_val, induceEquiv_val] at hh
  simpa using hh
private theorem inducedLift_apply_val_mem
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x)
    (s : IndepFinset (G.induce {x | q x}))
    {x : {y // p y}} (hx : x ∈ (inducedLift G p q hqp s).val) :
    q x.1 := by
  have hx' : x.1 ∈
      (indepFinsetInduceEquiv G p (inducedLift G p q hqp s)).val.val := by
    rw [induceEquiv_val]
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  rw [inducedLift_ambient G p q hqp s, induceEquiv_val] at hx'
  obtain ⟨y, hy, hxy⟩ := Finset.mem_map.mp hx'
  simpa [← hxy] using y.property

/-- Partition-function monotonicity for nested induced vertex predicates. -/
theorem independenceEval_induce_mono
    (G : SimpleGraph V) (p q : V → Prop) (hqp : ∀ x, q x → p x)
    (z : ℝ) (hz : 0 ≤ z) :
    independenceEval (G.induce {x | q x}) z ≤
      independenceEval (G.induce {x | p x}) z := by
  classical
  rw [independenceEval_eq_sum, independenceEval_eq_sum]
  let e := inducedLift G p q hqp
  let target := Finset.univ.filter
    (fun t : IndepFinset (G.induce {x | p x}) =>
      ∀ x ∈ t.val, q x.1)
  have hsum : (∑ s : IndepFinset (G.induce {x | q x}), z ^ s.val.card) =
      ∑ t ∈ target, z ^ t.val.card := by
    apply Finset.sum_bij (fun s _ => e s)
    · intro s hs
      simp only [target, Finset.mem_filter, Finset.mem_univ, true_and]
      intro x hx
      exact inducedLift_apply_val_mem G p q hqp s hx
    · intro s hs t ht hst
      exact inducedLift_injective G p q hqp hst
    · intro t ht
      have hqt : ∀ x ∈ t.val, q x.1 := (Finset.mem_filter.mp ht).2
      have hqambient : ∀ x ∈ (indepFinsetInduceEquiv G p t).val.val, q x := by
        rw [induceEquiv_val]
        intro x hx
        rw [Finset.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact hqt y hy
      let s : IndepFinset (G.induce {x | q x}) :=
        (indepFinsetInduceEquiv G q).symm
          ⟨(indepFinsetInduceEquiv G p t).val, hqambient⟩
      refine ⟨s, Finset.mem_univ _, ?_⟩
      have heq :
          (indepFinsetInduceEquiv G p (e s)) =
            (indepFinsetInduceEquiv G p t) := by
        apply Subtype.ext
        apply Subtype.ext
        exact (inducedLift_ambient G p q hqp s).trans
          (congrArg (fun r : RestrictedIndepFinset G q => r.val.val)
            ((indepFinsetInduceEquiv G q).apply_symm_apply
              ⟨(indepFinsetInduceEquiv G p t).val, hqambient⟩))
      exact (indepFinsetInduceEquiv G p).injective heq
    · intro s hs
      exact congrArg (fun n : ℕ => z ^ n)
        (inducedLift_card G p q hqp s).symm
  rw [hsum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro t ht hnot
    exact pow_nonneg hz _


/-! ## One-vertex partition recurrence and deletion bound -/

theorem independenceEval_deleteVertex_real (z : ℝ) (v : V) :
    independenceEval G z =
      independenceEval (deleteVertex G v) z +
        z * independenceEval (deleteClosedNeighborhood G v) z := by
  classical
  letI : Fintype (AvoidingIndepFinset G v) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset G v) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  calc
    independenceEval G z = ∑ s : IndepFinset G, z ^ s.val.card :=
      independenceEval_eq_sum G z
    _ = ∑ q : AvoidingIndepFinset G v ⊕ ContainingIndepFinset G v,
        Sum.elim (fun s => z ^ s.val.val.card)
          (fun s => z ^ s.val.val.card) q := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv G v)
      intro q
      by_cases h : v ∈ q.val <;>
        simp [indepFinsetPartitionEquiv, h]
    _ = (∑ s : AvoidingIndepFinset G v, z ^ s.val.val.card) +
        (∑ s : ContainingIndepFinset G v, z ^ s.val.val.card) := by
      exact Fintype.sum_sum_type _
    _ = (∑ s : IndepFinset (deleteVertex G v), z ^ s.val.card) +
        z * (∑ s : IndepFinset (deleteClosedNeighborhood G v), z ^ s.val.card) := by
      congr 1
      · symm
        apply Fintype.sum_equiv (avoidingEquiv G v)
        intro s
        rw [avoidingEquiv_card]
      · rw [Finset.mul_sum]
        symm
        apply Fintype.sum_equiv (containingEquiv G v)
        intro s
        rw [containingEquiv_card, pow_add, pow_one]
        ring
    _ = independenceEval (deleteVertex G v) z +
        z * independenceEval (deleteClosedNeighborhood G v) z := by
      rw [independenceEval_eq_sum, independenceEval_eq_sum]

theorem independenceEval_deleteVertex_le_mul
    (z : ℝ) (hz : 0 ≤ z) (v : V) :
    independenceEval G z ≤
      (1 + z) * independenceEval (deleteVertex G v) z := by
  rw [independenceEval_deleteVertex_real (G := G) z v]
  have hmono : independenceEval (deleteClosedNeighborhood G v) z ≤
      independenceEval (deleteVertex G v) z := by
    change independenceEval (G.induce {x | x ≠ v ∧ ¬ G.Adj v x}) z ≤
      independenceEval (G.induce {x | x ≠ v}) z
    exact independenceEval_induce_mono G (fun x => x ≠ v)
      (fun x => x ≠ v ∧ ¬ G.Adj v x) (fun x hx => hx.1) z hz
  nlinarith


/-! ## Rooted-to-global one-site marginal bridge -/

private theorem eval_iso2
    {A B : Type*} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (z : ℝ) :
    independenceEval H z = independenceEval K z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]
private theorem eval_sum2
    {A B : Type*} [Fintype A] [Fintype B]
    (H : SimpleGraph A) (K : SimpleGraph B) (z : ℝ) :
    independenceEval (H ⊕g K) z = independenceEval H z * independenceEval K z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_sum, Polynomial.map_mul, Polynomial.eval_mul]
private noncomputable def unionIso2 (G : SimpleGraph V) (a b : Finset V)
    (hd : Disjoint a b)
    (hcross : ∀ ⦃x y : V⦄, x ∈ a → y ∈ b → ¬ G.Adj x y) :
    G.induce (↑a : Set V) ⊕g G.induce (↑b : Set V) ≃g
      G.induce (↑(a ∪ b) : Set V) := by
  classical
  refine
    { toEquiv := Equiv.Finset.union a b hd
      map_rel_iff' := ?_ }
  rintro (x | x) (y | y)
  · simp
  · have hxy : ¬ G.Adj (x : V) (y : V) := hcross x.2 y.2
    simp [SimpleGraph.sum_adj, hxy]
  · have hxy : ¬ G.Adj (x : V) (y : V) := fun h => hcross y.2 x.2 h.symm
    simp [SimpleGraph.sum_adj, hxy]
  · simp
private def inducedUnionIso2 (G : SimpleGraph V) (q : V → Prop)
    (a b : Finset V) (hab : ∀ x, x ∈ a ∪ b ↔ q x) :
    G.induce (↑(a ∪ b) : Set V) ≃g G.induce {x | q x} := by
  refine
    { toEquiv :=
        { toFun := fun x => ⟨x.1, (hab x.1).1 x.2⟩
          invFun := fun x => ⟨x.1, (hab x.1).2 x.2⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      map_rel_iff' := by intro x y; rfl }
private def trueIso2 (G : SimpleGraph V) :
    G.induce {x | (True : Prop)} ≃g G := by
  refine
    { toEquiv :=
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, trivial⟩
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
      map_rel_iff' := by intro x y; rfl }

private theorem eval_induced_union2 {q : V → Prop}
    [Fintype (↑({x | q x} : Set V))]
    (a b : Finset V) (z : ℝ)
    (hd : Disjoint a b)
    (hcross : ∀ ⦃x y : V⦄, x ∈ a → y ∈ b → ¬ G.Adj x y)
    (hab : ∀ x, x ∈ a ∪ b ↔ q x) :
    independenceEval (G.induce {x | q x}) z =
      independenceEval (G.induce (↑a : Set V)) z *
        independenceEval (G.induce (↑b : Set V)) z := by
  rw [← eval_iso2 (inducedUnionIso2 G q a b hab) z]
  rw [← eval_iso2 (unionIso2 G a b hd hcross) z]
  exact eval_sum2 _ _ _

private theorem absentRatio2 (z : ℝ) (hz : 0 < z) (p : V) :
    (∑ s : IndepFinset G,
      if p ∉ s.val then (hardCoreLaw G z hz).probability s else 0) =
      independenceEval (deleteVertex G p) z / independenceEval G z := by
  classical
  letI : Fintype (AvoidingIndepFinset G p) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  let t : Finset (IndepFinset G) :=
    Finset.univ.filter (fun s => p ∉ s.val)
  calc
    (∑ s : IndepFinset G,
      if p ∉ s.val then z ^ s.val.card / independenceEval G z else 0) =
      (∑ s ∈ t, z ^ s.val.card / independenceEval G z) := by
      symm
      rw [Finset.sum_filter]
    _ = (∑ s ∈ t, z ^ s.val.card) / independenceEval G z := by
      rw [Finset.sum_div]
    _ = (∑ s : AvoidingIndepFinset G p,
        z ^ s.1.val.card) / independenceEval G z := by
      congr 1
      exact Finset.sum_subtype t (by intro s; simp [t]) (fun s => z ^ s.val.card)
    _ = independenceEval (deleteVertex G p) z / independenceEval G z := by
      congr 1
      rw [independenceEval_eq_sum (G := deleteVertex G p)]
      apply Fintype.sum_equiv (avoidingEquiv G p).symm
      intro s
      have hc := avoidingEquiv_card (G := G) p ((avoidingEquiv G p).symm s)
      simpa using congrArg (fun n : ℕ => z ^ n) hc

private theorem occupationRatio2 (z : ℝ) (hz : 0 < z) (v : V) :
    singleSiteOccupationProbability (G := G) z hz v =
      z * independenceEval (deleteClosedNeighborhood G v) z /
        independenceEval G z := by
  classical
  letI : Fintype (OccupiedAt G v) :=
    Subtype.fintype (fun s : IndepFinset G => v ∈ s.val)
  letI : Fintype (ContainingIndepFinset G v) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  unfold singleSiteOccupationProbability
  calc
    (∑ s : OccupiedAt G v, (hardCoreLaw G z hz).probability s.1) =
        (∑ s : OccupiedAt G v, z ^ s.1.val.card /
          independenceEval G z) := by simp [hardCoreLaw]
    _ = (z * ∑ s : OccupiedAt G v, z ^ (s.1.val.erase v).card) /
          independenceEval G z := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro s
      have hcard : s.1.val.card = (s.1.val.erase v).card + 1 := by
        rw [Finset.card_erase_add_one s.2]
      rw [hcard, pow_add, pow_one]
      ring
    _ = z * independenceEval (deleteClosedNeighborhood G v) z /
          independenceEval G z := by
      field_simp [ne_of_gt (independenceEval_pos G hz)]
      rw [independenceEval_eq_sum]
      let idE : ContainingIndepFinset G v ≃ OccupiedAt G v :=
        { toFun := fun s => ⟨s.1, s.2⟩
          invFun := fun s => ⟨s.1, s.2⟩
          left_inv := by intro s; rfl
          right_inv := by intro s; rfl }
      let e := (containingEquiv G v).trans idE
      symm
      apply Fintype.sum_equiv e
      intro s
      have hc := containingEquiv_card (G := G) v s
      have he := Finset.card_erase_add_one (containingEquiv G v s).2
      have hcard : ((containingEquiv G v s).val.val.erase v).card = s.val.card := by
        omega
      exact congrArg (fun n : ℕ => z ^ n) hcard.symm

private theorem parent_isChild2 (R : ComponentRooting G) {v p : V}
    (hv : v ≠ R.rootOf (G := G) v)
    (hp : R.parent (G := G) v = some p) :
    R.IsChild (G := G) p v := by
  unfold ComponentRooting.parent at hp
  simp only [dif_neg hv] at hp
  have hp' := Option.some.inj hp
  subst p
  let c := G.connectedComponentMk v
  let hr : R.rootOf (G := G) v ∈ c.supp := R.root_mem c
  let hv' : v ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
  let path := Classical.choose ((c.reachable_of_mem_supp hr hv').exists_path_of_dist)
  have hpath := (Classical.choose_spec ((c.reachable_of_mem_supp hr hv').exists_path_of_dist))
  have hpnn : ¬ path.Nil := SimpleGraph.Walk.not_nil_of_ne hv.symm
  have hprefix : path.dropLast.length = G.dist (R.rootOf (G := G) v) path.penultimate :=
    SimpleGraph.length_eq_dist_of_subwalk hpath.2
      ((SimpleGraph.Walk.isSubwalk_rfl path).dropLast)
  refine ⟨path.adj_penultimate hpnn, ?_⟩
  change G.dist (R.rootOf (G := G) v) v =
    G.dist (R.rootOf (G := G) v) path.penultimate + 1
  calc
    G.dist (R.rootOf (G := G) v) v = path.length := hpath.2.symm
    _ = path.dropLast.length + 1 := (path.length_dropLast_add_one hpnn).symm
    _ = G.dist (R.rootOf (G := G) v) path.penultimate + 1 := by rw [hprefix]

private theorem edge_boundary2 (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u x y : V} (hux : R.IsDescendant (G := G) u x)
    (hyout : y ∉ R.descendants (G := G) u) (hxy : G.Adj x y) :
    x = u ∧ R.IsChild (G := G) y u := by
  have hparent : ∀ {a b : V}, R.IsDescendant (G := G) a b → a ≠ b →
      ∀ {q : V}, R.IsChild (G := G) q b →
        R.IsDescendant (G := G) a q := by
    intro a b hab hne q hq
    induction hab using Relation.ReflTransGen.trans_induction_on with
    | refl => exact (hne rfl).elim
    | single hchild =>
        have hey : q = _ := R.isChild_unique (G := G) hG hq hchild
        subst q
        exact Relation.ReflTransGen.refl
    | @trans aa bb cc h₁ h₂ ih₁ ih₂ =>
        by_cases hbc : bb = cc
        · subst cc
          exact ih₁ hne hq
        · exact h₁.trans (ih₂ hbc hq)
  rcases (R.adj_iff_isChild_or_reverse (G := G) hG).mp hxy with hxy | hyx
  · exact (hyout ((R.mem_descendants (G := G) u y).mpr
        (Relation.ReflTransGen.trans hux (Relation.ReflTransGen.single hxy)))).elim
  · by_cases hxu : x = u
    · subst x
      exact ⟨rfl, hyx⟩
    · exact (hyout ((R.mem_descendants (G := G) u y).mpr
        (hparent hux (fun h => hxu h.symm) hyx))).elim

private theorem marginalBridge2 (hG : G.IsAcyclic)
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    singleSiteOccupationProbability (G := G) C.activity C.activity_pos u =
      R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u := by
  classical
  let D : Finset V := R.descendants (G := G) u
  let A : Finset V := (R.children (G := G) u).biUnion
    (childRemainder (G := G) R)
  have hA : ∀ x, x ∈ A ↔ x ∈ D ∧ x ≠ u ∧ ¬ G.Adj u x := by
    intro x
    simpa [A, D] using
      (mem_childRemainder_biUnion_iff (G := G) hG R u x)
  have hlocal : R.occupationProbability (G := G) C u =
      C.activity * independenceEval (G.induce (↑A : Set V)) C.activity /
        independenceEval (G.induce (↑D : Set V)) C.activity := by
    unfold ComponentRooting.occupationProbability
    unfold ComponentRooting.rootedA ComponentRooting.rootedP
    have hP : 0 < independenceEval (R.Subtree (G := G) u) C.activity :=
      independenceEval_pos _ C.activity_pos
    have hD : 0 < independenceEval (G.induce (↑D : Set V)) C.activity :=
      independenceEval_pos _ C.activity_pos
    apply (div_eq_div_iff (ne_of_gt hP) (ne_of_gt hD)).2
    calc
      _ = C.activity * independenceEval (G.induce (↑A : Set V)) C.activity *
          independenceEval (G.induce (↑D : Set V)) C.activity := by
        exact congrArg (fun t : ℝ => C.activity * t *
          independenceEval (G.induce (↑D : Set V)) C.activity)
          (independenceEval_eq_of_graphIso
            (deleteClosedSubtreeRootIsoChildRemainders (G := G) hG R u)
            C.activity)
      _ = _ := by rfl
  have hboundary : ∀ {x y : V}, x ∈ D → y ∉ D → G.Adj x y →
      x = u ∧ R.IsChild (G := G) y u := by
    intro x y hx hy hxy
    exact edge_boundary2 (G := G) hG R
      ((R.mem_descendants (G := G) u x).mp hx) hy hxy
  by_cases hroot : u = R.rootOf (G := G) u
  · let B : Finset V := Finset.univ.filter (fun x => x ∉ D)
    have hdisjD : Disjoint D B := by
      rw [Finset.disjoint_left]
      intro x hxD hxB
      exact (Finset.mem_filter.mp hxB).2 hxD
    have hcrossD : ∀ ⦃x y : V⦄, x ∈ D → y ∈ B → ¬ G.Adj x y := by
      intro x y hx hy hxy
      rcases hboundary hx (Finset.mem_filter.mp hy).2 hxy with ⟨hxu, hchild⟩
      exact R.not_isChild_of_eq_root (G := G) hroot hchild
    have hcross : ∀ ⦃x y : V⦄, x ∈ A → y ∈ B → ¬ G.Adj x y := by
      intro x y hx hy hxy
      exact hcrossD ((hA x).mp hx).1 hy hxy
    have hfull : ∀ x, x ∈ D ∪ B ↔ True := by
      intro x
      constructor
      · intro; trivial
      · intro
        by_cases hx : x ∈ D
        · exact Finset.mem_union.mpr (Or.inl hx)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
    have hclosed : ∀ x, x ∈ A ∪ B ↔ x ≠ u ∧ ¬ G.Adj u x := by
      intro x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact ⟨(hA x).mp hx |>.2.1, (hA x).mp hx |>.2.2⟩
        · have hnotD := (Finset.mem_filter.mp hx).2
          have hxu : x ≠ u := by
            intro hxu
            apply hnotD
            subst x
            exact R.self_mem_descendants (G := G) u
          have hnadj : ¬ G.Adj u x := by
            intro hadj
            rcases hboundary (R.self_mem_descendants (G := G) u) hnotD hadj with ⟨_, hc⟩
            exact R.not_isChild_of_eq_root (G := G) hroot hc
          exact ⟨hxu, hnadj⟩
      · rintro ⟨hxu, hnadj⟩
        by_cases hx : x ∈ D
        · exact Finset.mem_union.mpr (Or.inl ((hA x).mpr ⟨hx, hxu, hnadj⟩))
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
    have hden := eval_induced_union2 (G := G) (q := fun _ => True)
      D B C.activity (by simpa [B] using hdisjD) (by
        intro x y hx hy hxy
        exact hcrossD hx hy hxy) hfull
    have hnum := eval_induced_union2 (G := G)
      (q := fun x => x ≠ u ∧ ¬ G.Adj u x) A B C.activity
      (by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        exact (Finset.mem_filter.mp hxB).2 ((hA x).mp hxA).1)
      hcross hclosed
    have hden' : independenceEval G C.activity =
        independenceEval (G.induce (↑D : Set V)) C.activity *
          independenceEval (G.induce (↑B : Set V)) C.activity := by
      calc
        independenceEval G C.activity =
            independenceEval (G.induce {x | (True : Prop)}) C.activity :=
          (eval_iso2 (trueIso2 G) C.activity).symm
        _ = _ := hden
    have hnum' : independenceEval (deleteClosedNeighborhood G u) C.activity =
        independenceEval (G.induce (↑A : Set V)) C.activity *
          independenceEval (G.induce (↑B : Set V)) C.activity := by
      simpa [deleteClosedNeighborhood] using hnum
    have hlocal' := hlocal
    have hglobal := occupationRatio2 (G := G) C.activity C.activity_pos u
    have hpabs : R.parentAbsentProbability (G := G) C u = 1 := by
      rw [hroot]
      exact R.parentAbsentProbability_rootOf (G := G) C u
    rw [hglobal, hlocal', hpabs]
    simp only [one_mul]
    rw [hnum', hden']
    have hDpos : 0 < independenceEval (G.induce (↑D : Set V)) C.activity :=
      independenceEval_pos _ C.activity_pos
    have hBpos : 0 < independenceEval (G.induce (↑B : Set V)) C.activity :=
      independenceEval_pos _ C.activity_pos
    field_simp [ne_of_gt hDpos, ne_of_gt hBpos]
  · let p := R.selectedParent (G := G) u hroot
    have hpc : R.IsChild (G := G) p u :=
      R.selectedParent_isChild (G := G) u hroot
    let B : Finset V := (Finset.univ.erase p).filter (fun x => x ∉ D)
    have hDp : ∀ x, x ∈ D → x ≠ p := by
      intro x hx
      intro hxp
      subst x
      exact R.not_mem_descendants_child (G := G) hpc hx
    have hcross : ∀ ⦃x y : V⦄, x ∈ A → y ∈ B → ¬ G.Adj x y := by
      intro x y hx hy hxy
      have hb := (hA x).mp hx
      rcases hboundary hb.1 (Finset.mem_filter.mp hy).2 hxy with ⟨hxu, hchild⟩
      have hpy : y = p := R.isChild_unique (G := G) hG hchild hpc
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1 hpy
    have hcrossD : ∀ ⦃x y : V⦄, x ∈ D → y ∈ B → ¬ G.Adj x y := by
      intro x y hx hy hxy
      rcases hboundary hx (Finset.mem_filter.mp hy).2 hxy with ⟨hxu, hchild⟩
      have hpy : y = p := R.isChild_unique (G := G) hG hchild hpc
      exact (Finset.mem_erase.mp (Finset.mem_filter.mp hy).1).1 hpy
    have hdel : ∀ x, x ∈ D ∪ B ↔ x ≠ p := by
      intro x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact hDp x hx
        · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1
      · intro hxp
        by_cases hx : x ∈ D
        · exact Finset.mem_union.mpr (Or.inl hx)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ _⟩, hx⟩))
    have hclosed : ∀ x, x ∈ A ∪ B ↔ x ≠ u ∧ ¬ G.Adj u x := by
      intro x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact ⟨(hA x).mp hx |>.2.1, (hA x).mp hx |>.2.2⟩
        · have hnotD := (Finset.mem_filter.mp hx).2
          have hxu : x ≠ u := by
            intro hxu
            apply hnotD
            subst x
            exact R.self_mem_descendants (G := G) u
          have hnadj : ¬ G.Adj u x := by
            intro hadj
            rcases hboundary (R.self_mem_descendants (G := G) u) hnotD hadj with ⟨_, hc⟩
            have hxp : x = p := R.isChild_unique (G := G) hG hc hpc
            exact (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).1 hxp
          exact ⟨hxu, hnadj⟩
      · rintro ⟨hxu, hnadj⟩
        by_cases hx : x ∈ D
        · exact Finset.mem_union.mpr (Or.inl ((hA x).mpr ⟨hx, hxu, hnadj⟩))
        · have hxp : x ≠ p := by
            intro hxp
            apply hnadj
            subst x
            exact hpc.1.symm
          exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
            ⟨Finset.mem_erase.mpr ⟨hxp, Finset.mem_univ _⟩, hx⟩))
    have hdel' := eval_induced_union2 (G := G) (q := fun x => x ≠ p)
      D B C.activity (by
        rw [Finset.disjoint_left]
        intro x hxD hxB
        exact (Finset.mem_filter.mp hxB).2 hxD)
      hcrossD hdel
    have hnum := eval_induced_union2 (G := G)
      (q := fun x => x ≠ u ∧ ¬ G.Adj u x) A B C.activity
      (by
        rw [Finset.disjoint_left]
        intro x hxA hxB
        exact (Finset.mem_filter.mp hxB).2 ((hA x).mp hxA).1)
      hcross hclosed
    have hnum' : independenceEval (deleteClosedNeighborhood G u) C.activity =
        independenceEval (G.induce (↑A : Set V)) C.activity *
          independenceEval (G.induce (↑B : Set V)) C.activity := by
      simpa [deleteClosedNeighborhood] using hnum
    have hglobal := occupationRatio2 (G := G) C.activity C.activity_pos u
    have hpabs : R.parentAbsentProbability (G := G) C u =
        independenceEval (deleteVertex G p) C.activity /
          independenceEval G C.activity := by
      exact R.parentAbsentProbability_eq_deleteVertex_ratio (G := G) C hroot
    have hdelGraph : independenceEval (deleteVertex G p) C.activity =
        independenceEval (G.induce (↑D : Set V)) C.activity *
          independenceEval (G.induce (↑B : Set V)) C.activity := by
      simpa [deleteVertex] using hdel'
    rw [hglobal, hlocal, hpabs]
    rw [hnum', hdelGraph]
    have hGpos : 0 < independenceEval G C.activity :=
      independenceEval_pos _ C.activity_pos
    have hDpos : 0 < independenceEval (G.induce (↑D : Set V)) C.activity :=
      independenceEval_pos _ C.activity_pos
    field_simp [ne_of_gt hGpos, ne_of_gt hDpos]


/-- Exact rooted-to-global one-site marginal cancellation identity. -/
theorem singleSiteOccupationProbability_eq_parentAbsent_mul_occupationProbability
    (hG : G.IsAcyclic) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    singleSiteOccupationProbability (G := G) C.activity C.activity_pos u =
      R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u := by
  exact marginalBridge2 (G := G) hG C R u

/-- Every parent-absence event has the universal finite hard-core lower bound. -/
theorem one_div_one_add_activity_le_parentAbsentProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    1 / (1 + C.activity) ≤ R.parentAbsentProbability (G := G) C u := by
  classical
  by_cases hroot : u = R.rootOf (G := G) u
  · rw [hroot, R.parentAbsentProbability_rootOf (G := G) C]
    apply (div_le_iff₀ (by linarith [C.activity_pos])).2
    nlinarith [C.activity_pos]
  · let p := R.selectedParent (G := G) u hroot
    have hdel := independenceEval_deleteVertex_le_mul
      (G := G) C.activity C.activity_pos.le p
    have hZ : 0 < independenceEval G C.activity :=
      independenceEval_pos _ C.activity_pos
    have hratio : 1 / (1 + C.activity) ≤
        independenceEval (deleteVertex G p) C.activity /
          independenceEval G C.activity := by
      apply (div_le_div_iff₀ (by linarith [C.activity_pos]) hZ).2
      nlinarith
    have hsum' : R.parentAbsentProbability (G := G) C u =
        independenceEval (deleteVertex G p) C.activity /
          independenceEval G C.activity := by
      exact R.parentAbsentProbability_eq_deleteVertex_ratio (G := G) C hroot
    rw [hsum']
    exact hratio

/-- Under `z < 27`, the global absence probability of every parent is
strictly larger than `1/28`. -/
theorem one_div_twentyEight_lt_parentAbsentProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V)
    (hz27 : C.activity < 27) :
    (1 : ℝ) / 28 < R.parentAbsentProbability (G := G) C u := by
  refine lt_of_lt_of_le ?_
    (one_div_one_add_activity_le_parentAbsentProbability (G := G) C R u)
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 28)
    (by linarith [C.activity_pos] : 0 < 1 + C.activity)).2
  nlinarith

/-- Every rooted vertex with at most one child has global occupation above
`3/1652`. -/
theorem singleSiteOccupationProbability_gt_three_div_1652_of_children_card_le_one
    (hG : G.IsAcyclic) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (hcard : (R.children (G := G) u).card ≤ 1) :
    (3 : ℝ) / 1652 <
      singleSiteOccupationProbability (G := G) C.activity C.activity_pos u := by
  have hpa := one_div_twentyEight_lt_parentAbsentProbability
    (G := G) C R u hz27
  have hro := occupationProbability_gt_three_div_fiftyNine_of_children_card_le_one
    (G := G) C R u hzlow hz27 hcard
  have hid := singleSiteOccupationProbability_eq_parentAbsent_mul_occupationProbability
    (G := G) hG C R u
  rw [hid]
  have hropos : 0 < R.occupationProbability (G := G) C u :=
    lt_trans (by norm_num : (0 : ℝ) < 3 / 59) hro
  have hpa0 : 0 < R.parentAbsentProbability (G := G) C u :=
    lt_trans (by norm_num : (0 : ℝ) < 1 / 28) hpa
  calc
    (3 : ℝ) / 1652 = (1 / 28) * (3 / 59) := by norm_num
    _ < (1 / 28) * R.occupationProbability (G := G) C u :=
      mul_lt_mul_of_pos_left hro (by norm_num)
    _ < R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u :=
      mul_lt_mul_of_pos_right hpa hropos


theorem lowChild_count (hG : G.IsAcyclic) (R : ComponentRooting G)
    (hV : Nonempty V) :
    2 * (Finset.univ.filter (fun u => (R.children (G := G) u).card ≤ 1)).card ≥
      Fintype.card V + 1 := by
  classical
  let L : Finset V := Finset.univ.filter (fun u => (R.children (G := G) u).card ≤ 1)
  let H : Finset V := Finset.univ.filter (fun u => ¬ ((R.children (G := G) u).card ≤ 1))
  let S : Finset V := Finset.univ.biUnion (fun u => R.children (G := G) u)
  have hpair : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint
      (fun u => R.children (G := G) u) := by
    intro u hu v hv huv
    change Disjoint (R.children (G := G) u) (R.children (G := G) v)
    rw [Finset.disjoint_left]
    intro x hxu hxv
    apply huv
    exact R.isChild_unique (G := G) hG
      ((R.mem_children (G := G) u x).mp hxu)
      ((R.mem_children (G := G) v x).mp hxv)
  have hScard : S.card = ∑ u ∈ (Finset.univ : Finset V),
      (R.children (G := G) u).card := by
    exact Finset.card_biUnion hpair
  have hSsub : S ⊆ (Finset.univ : Finset V) := by
    intro x hx
    simp only [S, Finset.mem_biUnion] at hx
    simp
  obtain ⟨v⟩ := hV
  let r := R.rootOf (G := G) v
  have hrroot : r = R.rootOf (G := G) r := by simp [r]
  have hrnot : r ∉ S := by
    intro hrs
    rcases Finset.mem_biUnion.mp hrs with ⟨u, hu, hru⟩
    exact R.not_isChild_of_eq_root (G := G) hrroot
      ((R.mem_children (G := G) u r).mp hru)
  have hSproper : S ⊂ (Finset.univ : Finset V) := by
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, by
      intro heq
      exact hrnot (heq ▸ Finset.mem_univ r)⟩
  have hSlt : S.card < Fintype.card V := by
    simpa using Finset.card_lt_card hSproper
  have hsum_lt : ∑ u ∈ (Finset.univ : Finset V),
      (R.children (G := G) u).card < Fintype.card V := by
    rw [← hScard]
    exact hSlt
  have hhigh : 2 * H.card ≤ ∑ u ∈ (Finset.univ : Finset V),
      (R.children (G := G) u).card := by
    calc
      2 * H.card = ∑ u ∈ H, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ u ∈ H, (R.children (G := G) u).card := by
        apply Finset.sum_le_sum
        intro u hu
        have hnot : ¬ ((R.children (G := G) u).card ≤ 1) :=
          (Finset.mem_filter.mp hu).2
        have hcard : 2 ≤ (R.children (G := G) u).card := by
          omega
        exact hcard
      _ ≤ ∑ u ∈ (Finset.univ : Finset V),
          (R.children (G := G) u).card := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact Finset.filter_subset _ _
        · intro u hu hnu
          exact Nat.zero_le _
  have hhigh' : 2 * H.card < Fintype.card V := hhigh.trans_lt hsum_lt
  have hdisj : Disjoint L H := by
    rw [Finset.disjoint_left]
    intro x hxL hxH
    exact (Finset.mem_filter.mp hxH).2 (Finset.mem_filter.mp hxL).2
  have hunion : L ∪ H = (Finset.univ : Finset V) := by
    ext x
    by_cases h : (R.children (G := G) x).card ≤ 1
    · simp [L, H, h]
    · have h' : 1 < (R.children (G := G) x).card := by omega
      simp [L, H, h, h']
  have hpartition : L.card + H.card = Fintype.card V := by
    calc
      L.card + H.card = (L ∪ H).card :=
        (Finset.card_union_of_disjoint hdisj).symm
      _ = Fintype.card V := by rw [hunion]; simp
  have hLH : 2 * H.card < L.card + H.card := by simpa [hpartition] using hhigh'
  have hLtarget : Fintype.card V + 1 ≤ 2 * L.card := by
    omega
  simpa [L] using hLtarget


private theorem singleSiteOccupationProbability_nonneg (C : CanonicalFirstRecoveryState G) (u : V) :
    0 ≤ singleSiteOccupationProbability (G := G) C.activity C.activity_pos u := by
  unfold singleSiteOccupationProbability
  apply Finset.sum_nonneg
  intro s hs
  exact (hardCoreLaw G C.activity C.activity_pos).probability_nonneg s.1

theorem C38_order_plus_one_lt (C : CanonicalFirstRecoveryState G)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27) :
    ((C.order + 1 : ℕ) : ℝ) < (3304 / 3) * (C.index : ℝ) := by
  classical
  let R : ComponentRooting G := Classical.choice
    (nonempty_componentRooting (G := G))
  let L : Finset V := Finset.univ.filter
    (fun u => (R.children (G := G) u).card ≤ 1)
  have hcardpos : 0 < Fintype.card V := by
    have hi : 0 < C.index := C.firstRecovery.index_pos
    have hio : C.index ≤ C.order := C.index_le_order
    exact lt_of_lt_of_le hi hio
  have hV : Nonempty V := Fintype.card_pos_iff.mp hcardpos
  have hcount := lowChild_count (G := G) C.isForest R hV
  have hLpos : 0 < L.card := by
    dsimp [L]
    have hcount' : 2 * L.card ≥ Fintype.card V + 1 := by simpa [L] using hcount
    omega
  have hlow : ∀ u ∈ L, (3 : ℝ) / 1652 <
      singleSiteOccupationProbability (G := G) C.activity C.activity_pos u := by
    intro u hu
    apply singleSiteOccupationProbability_gt_three_div_1652_of_children_card_le_one
      (G := G) C.isForest C R u hzlow hz27
    exact (Finset.mem_filter.mp (show u ∈ Finset.univ.filter
      (fun u => (R.children (G := G) u).card ≤ 1) from by simpa [L] using hu)).2
  have hsumstrict :
      (∑ u ∈ (Finset.univ : Finset V),
        if u ∈ L then (3 : ℝ) / 1652 else 0) <
        ∑ u ∈ (Finset.univ : Finset V),
          singleSiteOccupationProbability (G := G) C.activity C.activity_pos u := by
    apply Finset.sum_lt_sum
    · intro u hu
      by_cases hLu : u ∈ L
      · simpa [hLu] using (hlow u hLu).le
      · simpa [hLu] using singleSiteOccupationProbability_nonneg (G := G) C u
    · obtain ⟨u, hu⟩ := Finset.card_pos.mp hLpos
      refine ⟨u, Finset.mem_univ _, ?_⟩
      simpa [hu] using hlow u hu
  have hleft :
      (∑ u ∈ (Finset.univ : Finset V),
        if u ∈ L then (3 : ℝ) / 1652 else 0) =
        (L.card : ℝ) * ((3 : ℝ) / 1652) := by
    calc
      _ = ∑ u ∈ L, (3 : ℝ) / 1652 := by
        rw [← Finset.sum_filter]
        congr 1
        ext u
        simp [L]
      _ = (L.card : ℝ) * ((3 : ℝ) / 1652) := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hmean := sum_singleSiteOccupationProbability_eq_mean
    (G := G) C.activity C.activity_pos
  rw [hleft, hmean, C.mean_eq_index] at hsumstrict
  have hcountR : ((Fintype.card V + 1 : ℕ) : ℝ) ≤ 2 * (L.card : ℝ) := by
    exact_mod_cast hcount
  have hcardorder : C.order = Fintype.card V := rfl
  have hcast : ((C.order + 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) + 1 := by
    norm_num [hcardorder]
  have hscaled : 2 * (L.card : ℝ) <
      (3304 / 3) * (C.index : ℝ) := by
    norm_num at hsumstrict ⊢
    linarith [hsumstrict]
  have hnatcast : ((Fintype.card V + 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) + 1 := by
    norm_num
  rw [hnatcast] at hcountR
  have hbound : (Fintype.card V : ℝ) + 1 <
      (3304 / 3) * (C.index : ℝ) := by
    exact hcountR.trans_lt hscaled
  rw [hcast]
  exact hbound

theorem C39_order_and_variance_lt (C : CanonicalFirstRecoveryState G)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27) :
    (C.order : ℝ) < (3304 / 3) * (C.index : ℝ) ∧
      C.variance < (3304 / 3) * (C.index : ℝ)^2 := by
  have h38 := C38_order_plus_one_lt (G := G) C hzlow hz27
  have horder : (C.order : ℝ) < (3304 / 3) * (C.index : ℝ) := by
    have hplus : (C.order : ℝ) < ((C.order + 1 : ℕ) : ℝ) := by norm_num
    exact hplus.trans h38
  have hstat : ∀ s, C.law.stat s ≤ C.order := by
    intro s
    exact hardCoreLaw_stat_le_order G C.activity C.activity_pos s
  have hsecond := FiniteLatticeLaw.secondMoment_le_natCast_mul_mean_of_stat_le
    C.law C.order hstat
  rw [C.law_mean] at hsecond
  rw [C.law_secondMoment_eq_variance_add_index_sq] at hsecond
  have hvar : C.variance ≤ (C.order : ℝ) * (C.index : ℝ) := by
    nlinarith [sq_nonneg (C.index : ℝ)]
  have hidx : 0 < (C.index : ℝ) := by exact_mod_cast C.firstRecovery.index_pos
  have hmul := mul_lt_mul_of_pos_right horder hidx
  have hstrict : (C.order : ℝ) * (C.index : ℝ) <
      (3304 / 3) * (C.index : ℝ)^2 := by
    nlinarith
  exact ⟨horder, hvar.trans_lt hstrict⟩


end
end Forest
end Erdos993
