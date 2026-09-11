import Erdos993.Forest.ActualRootedVariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Erdos993
namespace UniformFourthMoment

open scoped BigOperators

noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α
noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

universe u

variable {V : Type u} [Fintype V]

/-- The finite sample space of one independent Bernoulli seed per vertex. -/
abbrev BernoulliAssignment (V : Type u) := V → Bool

/-- The product mass of a Bernoulli assignment with vertex probabilities `p`. -/
noncomputable def bernoulliWeight (p : V → ℝ) (ω : BernoulliAssignment V) : ℝ :=
  ∏ v, if ω v then p v else 1 - p v

@[simp] theorem bernoulliWeight_empty [IsEmpty V] (p : V → ℝ)
    (ω : BernoulliAssignment V) : bernoulliWeight p ω = 1 := by
  simp [bernoulliWeight]

/-- The explicit product mass is nonnegative under the usual Bernoulli bounds. -/
theorem bernoulliWeight_nonneg (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (ω : BernoulliAssignment V) : 0 ≤ bernoulliWeight p ω := by
  unfold bernoulliWeight
  apply Finset.prod_nonneg
  intro v hv
  by_cases hω : ω v
  · simp [hω, hp v]
  · simp [hω, sub_nonneg.mpr (hp1 v)]

/-- Normalization of the explicit finite independent Bernoulli law. -/
theorem sum_bernoulliWeight (p : V → ℝ) :
    ∑ ω : BernoulliAssignment V, bernoulliWeight p ω = 1 := by
  unfold bernoulliWeight
  have h := Finset.prod_univ_sum
    (fun _ : V => (Finset.univ : Finset Bool))
    (fun v b => if b then p v else 1 - p v)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  apply Finset.prod_eq_one
  intro v hv
  rw [Fintype.sum_bool]
  simp

/-- The corresponding finite lattice law records the number of true seeds. -/
noncomputable def independentBernoulliLaw (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1) :
    Forest.FiniteLatticeLaw (BernoulliAssignment V) where
  stat ω := (Finset.univ.filter (fun v => ω v)).card
  probability ω := bernoulliWeight p ω
  probability_nonneg := bernoulliWeight_nonneg p hp hp1
  probability_sum := sum_bernoulliWeight p

@[simp] theorem independentBernoulliLaw_probability (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (ω : BernoulliAssignment V) :
    (independentBernoulliLaw p hp hp1).probability ω = bernoulliWeight p ω := rfl

@[simp] theorem independentBernoulliLaw_stat (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) (hp1 : ∀ v, p v ≤ 1)
    (ω : BernoulliAssignment V) :
    (independentBernoulliLaw p hp hp1).stat ω =
      (Finset.univ.filter (fun v => ω v)).card := rfl

/-! ## Rooted availability recursion on the explicit seed space -/

open ActualRootedVariance

variable {G : SimpleGraph V}

/-- Descendant-subtree partition function at an arbitrary positive global activity. -/
noncomputable def rootedPAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  independenceEval (R.Subtree (G := G) u) z

/-- Root-vacant descendant-subtree partition function at the same activity. -/
noncomputable def rootedQAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  independenceEval
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z

/-- Root-occupied descendant-subtree partition function, including the root weight. -/
noncomputable def rootedAAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  z * independenceEval
    (deleteClosedNeighborhood (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z

set_option maxHeartbeats 800000 in
/-- Exact two-state recurrence at an arbitrary positive global activity. -/
theorem rootedPAt_eq_rootedQAt_add_rootedAAt
    (R : ComponentRooting G) (z : ℝ) (u : V) :
    rootedPAt R z u = rootedQAt R z u + rootedAAt R z u := by
  let H := R.Subtree (G := G) u
  let r := R.subtreeRoot (G := G) u
  have hrec := rooted_recurrence H r
  apply_fun fun p : Polynomial ℕ =>
    Polynomial.eval z (p.map (Nat.castRingHom ℝ)) at hrec
  simpa [rootedPAt, rootedQAt, rootedAAt, independenceEval,
    independencePolynomialReal, rootedAvoidingPolynomial, rootedOccupiedRemainder,
    Polynomial.map_add, Polynomial.map_mul] using hrec

/-- Local Bernoulli parameter of a vertex in its free descendant-subtree law. -/
noncomputable def rootedOccupationProbabilityAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  rootedAAt R z u / rootedPAt R z u

/-- Complementary local vacancy probability. -/
noncomputable def rootedVacancyProbabilityAt
    (R : ComponentRooting G) (z : ℝ) (u : V) : ℝ :=
  rootedQAt R z u / rootedPAt R z u

/-- The Bernoulli parameter is strictly positive at positive activity. -/
theorem rootedOccupationProbabilityAt_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedOccupationProbabilityAt R z u := by
  apply div_pos
  · exact mul_pos hz (independenceEval_pos _ hz)
  · exact independenceEval_pos _ hz

/-- The local occupation and vacancy probabilities sum to one. -/
theorem rootedOccupationProbabilityAt_add_vacancy
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u + rootedVacancyProbabilityAt R z u = 1 := by
  rw [rootedOccupationProbabilityAt, rootedVacancyProbabilityAt, ← add_div,
    add_comm, ← rootedPAt_eq_rootedQAt_add_rootedAAt]
  exact div_self (ne_of_gt (independenceEval_pos _ hz))

/-- The local Bernoulli parameter is at most one. -/
theorem rootedOccupationProbabilityAt_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u ≤ 1 := by
  have hq : 0 ≤ rootedVacancyProbabilityAt R z u := by
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u]

/-- The explicit independent seed law for the actual rooted availability sampler.
Every coordinate uses the original global activity `z` through its descendant law. -/
noncomputable def hardCoreBernoulliSeedLaw
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    Forest.FiniteLatticeLaw (BernoulliAssignment V) :=
  independentBernoulliLaw (fun v => rootedOccupationProbabilityAt R z v)
    (fun v => (rootedOccupationProbabilityAt_pos R z hz v).le)
    (rootedOccupationProbabilityAt_le_one R z hz)

/-- The seed mass is definitionally evaluated at the unchanged global activity. -/
theorem hardCoreBernoulliSeedLaw_probability_uses_global_activity
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (ω : BernoulliAssignment V) :
    (hardCoreBernoulliSeedLaw R z hz).probability ω =
      ∏ v, if ω v then rootedAAt R z v / rootedPAt R z v
        else 1 - rootedAAt R z v / rootedPAt R z v := rfl

noncomputable local instance classicalPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Occupation generated at a prescribed depth.  At depth zero the vertex uses
its own Bernoulli seed.  At the successor step it is occupied exactly when its
seed is true and every oriented parent is vacant at the preceding step. -/
noncomputable def occupationAtDepth
    (R : ComponentRooting G) (ω : BernoulliAssignment V) : ℕ → V → Bool
  | 0, v => ω v
  | n + 1, v =>
      ω v && decide (∀ u, R.IsChild (G := G) u v → occupationAtDepth R ω n u = false)

/-- The generated occupation indicator evaluates the recursion at the actual
root distance. -/
noncomputable def generatedOccupation
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (v : V) : Bool :=
  occupationAtDepth R ω (R.depth (G := G) v) v

/-- A child cannot be generated occupied when its parent is generated occupied. -/
theorem generatedOccupation_child_false
    (R : ComponentRooting G) (ω : BernoulliAssignment V) {u v : V}
    (huv : R.IsChild (G := G) u v)
    (hu : generatedOccupation R ω u = true) :
    generatedOccupation R ω v = false := by
  change occupationAtDepth R ω (R.depth (G := G) u) u = true at hu
  unfold generatedOccupation
  rw [R.depth_child (G := G) huv]
  simp only [occupationAtDepth]
  by_cases hseed : ω v = true
  · simp only [hseed, Bool.true_and]
    have hnot : ¬ (∀ w, R.IsChild (G := G) w v →
        occupationAtDepth R ω (R.depth (G := G) u) w = false) := by
      intro hall
      have := hall u huv
      rw [hu] at this
      contradiction
    simp [hnot]
  · have hfalse : ω v = false := Bool.eq_false_of_not_eq_true hseed
    simp [hfalse]

/-- The generated occupied vertex finset. -/
noncomputable def generatedFinset
    (R : ComponentRooting G) (ω : BernoulliAssignment V) : Finset V :=
  Finset.univ.filter (fun v => generatedOccupation R ω v)

/-- Recursive availability always produces an actual independent set. -/
theorem generatedFinset_isIndepSet
    (hG : G.IsAcyclic) (R : ComponentRooting G) (ω : BernoulliAssignment V) :
    G.IsIndepSet (generatedFinset R ω : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv huv hadj
  have hu' : generatedOccupation R ω u = true := by
    simpa [generatedFinset] using hu
  have hv' : generatedOccupation R ω v = true := by
    simpa [generatedFinset] using hv
  rcases (R.adj_iff_isChild_or_reverse (G := G) hG).mp hadj with hchild | hchild
  · have := generatedOccupation_child_false R ω hchild hu'
    rw [hv'] at this
    contradiction
  · have := generatedOccupation_child_false R ω hchild hv'
    rw [hu'] at this
    contradiction

/-- The deterministic output of the explicit finite availability sampler. -/
noncomputable def generatedIndependentSet
    (hG : G.IsAcyclic) (R : ComponentRooting G) (ω : BernoulliAssignment V) :
    IndepFinset G :=
  IndepFinset.ofIsIndepSet (generatedFinset R ω)
    (generatedFinset_isIndepSet hG R ω)

@[simp] theorem generatedIndependentSet_val
    (hG : G.IsAcyclic) (R : ComponentRooting G) (ω : BernoulliAssignment V) :
    (generatedIndependentSet hG R ω).val = generatedFinset R ω := rfl

/-! ## The exact typed coupling target -/

/-- Push the independent seed law through recursive availability and retain the
occupation-count statistic. -/
noncomputable def generatedCountLaw
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    Forest.FiniteLatticeLaw (BernoulliAssignment V) where
  stat ω := (generatedIndependentSet hG R ω).val.card
  probability ω := (hardCoreBernoulliSeedLaw R z hz).probability ω
  probability_nonneg := (hardCoreBernoulliSeedLaw R z hz).probability_nonneg
  probability_sum := (hardCoreBernoulliSeedLaw R z hz).probability_sum

@[simp] theorem generatedCountLaw_probability
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (ω : BernoulliAssignment V) :
    (generatedCountLaw hG R z hz).probability ω =
      bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω := rfl

@[simp] theorem generatedCountLaw_stat
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (ω : BernoulliAssignment V) :
    (generatedCountLaw hG R z hz).stat ω = (generatedFinset R ω).card := rfl

/-- Strong configuration-level form of exact coupling: every independent set
has exactly its hard-core probability after summing its availability fibers. -/
def ExactHardCoreConfigurationCoupling
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) : Prop :=
  ∀ s : IndepFinset G,
    (∑ ω : BernoulliAssignment V,
      if generatedIndependentSet hG R ω = s then
        (generatedCountLaw hG R z hz).probability ω else 0) =
      (Forest.hardCoreLaw G z hz).probability s

/-- Requested occupation-count-law equality, stated in the project's native
`rankMass` interface. -/
def ExactHardCoreCountCoupling
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) : Prop :=
  ∀ k : ℕ,
    (generatedCountLaw hG R z hz).rankMass k =
      (Forest.hardCoreLaw G z hz).rankMass k

/-- On the empty forest the configuration coupling is exact (both laws are
concentrated on the unique empty independent set). -/
theorem exactHardCoreConfigurationCoupling_empty [IsEmpty V]
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ExactHardCoreConfigurationCoupling hG R z hz := by
  letI : Unique (IndepFinset G) :=
    { default := IndepFinset.empty G
      uniq := fun s => by
        apply Subtype.ext
        exact Finset.eq_empty_of_isEmpty s.val }
  have hdefault : (default : IndepFinset G).val = ∅ :=
    Finset.eq_empty_of_isEmpty (default : IndepFinset G).val
  have heval : independenceEval G z = 1 := by
    rw [independenceEval_eq_sum]
    simp [hdefault]
  intro s
  have hs : s = (default : IndepFinset G) := Unique.eq_default s
  subst s
  have hgen (ω : BernoulliAssignment V) : generatedIndependentSet hG R ω =
      (default : IndepFinset G) := Unique.eq_default _
  simp [generatedCountLaw, hardCoreBernoulliSeedLaw, independentBernoulliLaw,
    bernoulliWeight, Forest.hardCoreLaw, heval, hdefault, hgen]

/-! ## Arbitrary-activity rooted product identities -/

/-- Root-vacant subtree partition functions are positive at positive activity. -/
theorem rootedQAt_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedQAt R z u :=
  independenceEval_pos _ hz

/-- Root-occupied subtree contributions are positive at positive activity. -/
theorem rootedAAt_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedAAt R z u :=
  mul_pos hz (independenceEval_pos _ hz)

theorem independenceEval_graphIso
    {A B : Type u} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {K : SimpleGraph B} (e : H ≃g K) (z : ℝ) :
    independenceEval H z = independenceEval K z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]

private noncomputable def childVertexUnionAt
    (R : ComponentRooting G) (u : V) : Finset V :=
  (R.children (G := G) u).biUnion (fun w => R.descendants (G := G) w)

private noncomputable def deleteSubtreeRootIsoChildUnionAt
    (R : ComponentRooting G) (u : V) :
    deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ childVertexUnionAt (G := G) R u} := by
  classical
  have hdecomp : R.descendants (G := G) u =
      insert u (childVertexUnionAt (G := G) R u) := by
    simpa only [childVertexUnionAt] using
      R.descendants_eq_insert_biUnion_children (G := G) u
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u} ≃
      {x : V // x ∈ childVertexUnionAt (G := G) R u} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          have hmem : x.1.1 ∈ insert u (childVertexUnionAt (G := G) R u) := by
            rw [← hdecomp]
            exact x.1.2
          rcases Finset.mem_insert.mp hmem with hxu | hx
          · exfalso
            apply x.2
            apply Subtype.ext
            exact hxu
          · exact hx⟩
      invFun := fun y =>
        ⟨⟨y.1, by
            rw [hdecomp]
            exact Finset.mem_insert_of_mem y.2⟩,
          by
            intro hroot
            have hyu : y.1 = u := congrArg Subtype.val hroot
            have hyunion : y.1 ∈ (R.children (G := G) u).biUnion
                (fun w => R.descendants (G := G) w) := by
              simpa only [childVertexUnionAt] using y.2
            obtain ⟨w, hw, hyw⟩ := Finset.mem_biUnion.mp hyunion
            exact (R.not_mem_descendants_child (G := G)
              ((R.mem_children (G := G) u w).mp hw)) (hyu ▸ hyw)⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro y
        apply Subtype.ext
        rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- At the unchanged arbitrary global activity, deleting a subtree root leaves
exactly the mutually nonadjacent child subtrees. -/
theorem rootedQAt_eq_prod_rootedPAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u : V) :
    rootedQAt R z u =
      ∏ v ∈ R.children (G := G) u, rootedPAt R z v := by
  classical
  unfold rootedQAt rootedPAt
  calc
    independenceEval
        (deleteVertex (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) z =
      independenceEval
        (G.induce {x | x ∈ childVertexUnionAt (G := G) R u}) z :=
          independenceEval_graphIso
            (deleteSubtreeRootIsoChildUnionAt (G := G) R u) z
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval (R.Subtree (G := G) v) z := by
      apply independenceEval_induceFinset_biUnion G
        (R.children (G := G) u)
        (fun v => R.descendants (G := G) v)
        (R.children_pairwiseDisjoint_descendants (G := G) hG u)
      intro v hv w hw hvw x y hx hy
      exact R.not_adj_of_distinct_child_descendants (G := G) hG
        ((R.mem_children (G := G) u v).mp hv)
        ((R.mem_children (G := G) u w).mp hw) hvw
        ((R.mem_descendants (G := G) v x).mp hx)
        ((R.mem_descendants (G := G) w y).mp hy)

private noncomputable def properDescendantsAt
    (R : ComponentRooting G) (u : V) : Finset V :=
  (R.descendants (G := G) u).erase u

private noncomputable def deleteSubtreeRootIsoProperDescendantsAt
    (R : ComponentRooting G) (u : V) :
    deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ properDescendantsAt (G := G) R u} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u} ≃
      {x : V // x ∈ properDescendantsAt (G := G) R u} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          rw [properDescendantsAt, Finset.mem_erase]
          exact ⟨by
            intro h
            apply x.2
            apply Subtype.ext
            exact h, x.1.2⟩⟩
      invFun := fun y =>
        have hy : y.1 ∈ (R.descendants (G := G) u).erase u := by
          simpa only [properDescendantsAt] using y.2
        ⟨⟨y.1, (Finset.mem_erase.mp hy).2⟩, by
          intro h
          exact (Finset.mem_erase.mp hy).1 (congrArg Subtype.val h)⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

private noncomputable def deleteClosedSubtreeRootIsoProperChildUnionAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ (R.children (G := G) u).biUnion
        (fun v => properDescendantsAt (G := G) R v)} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u ∧
          ¬ (R.Subtree (G := G) u).Adj (R.subtreeRoot (G := G) u) x} ≃
      {x : V // x ∈ (R.children (G := G) u).biUnion
        (fun v => properDescendantsAt (G := G) R v)} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          rw [Finset.mem_biUnion]
          have hxdesc := (R.mem_descendants (G := G) u x.1.1).mp x.1.2
          rcases (R.isDescendant_iff_eq_or_child_descendant (G := G) u x.1.1).mp hxdesc with
            hxu | ⟨v, huv, hvx⟩
          · exact (x.2.1 (Subtype.ext hxu.symm)).elim
          · refine ⟨v, (R.mem_children (G := G) _ _).mpr huv, Finset.mem_erase.mpr ⟨?_,
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
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- At the unchanged arbitrary global activity, the occupied-root contribution
is `z` times the product of the root-vacant child contributions. -/
theorem rootedAAt_eq_z_mul_prod_rootedQAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (u : V) :
    rootedAAt R z u = z *
      ∏ v ∈ R.children (G := G) u, rootedQAt R z v := by
  classical
  unfold rootedAAt rootedQAt
  congr 1
  calc
    independenceEval
        (deleteClosedNeighborhood (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) z =
      independenceEval
        (G.induce {x | x ∈ (R.children (G := G) u).biUnion
          (fun v => properDescendantsAt (G := G) R v)}) z :=
        independenceEval_graphIso
          (deleteClosedSubtreeRootIsoProperChildUnionAt (G := G) hG R u) z
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval (G.induce {x | x ∈ properDescendantsAt (G := G) R v}) z := by
      apply independenceEval_induceFinset_biUnion G
        (R.children (G := G) u)
        (fun v => properDescendantsAt (G := G) R v)
      · intro v hv w hw hvw
        exact (R.children_pairwiseDisjoint_descendants (G := G) hG u
          hv hw hvw).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      · intro v hv w hw hvw x y hx hy
        exact R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) _ _).mp hv)
          ((R.mem_children (G := G) _ _).mp hw) hvw
          ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hx).2)
          ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2)
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z := by
      apply Finset.prod_congr rfl
      intro v hv
      exact (independenceEval_graphIso
        (deleteSubtreeRootIsoProperDescendantsAt (G := G) R v) z).symm

private noncomputable def induceUnivIso (G : SimpleGraph V) :
    G.induce ((Finset.univ : Finset V) : Set V) ≃g G := by
  let e : {x : V // x ∈ (Finset.univ : Finset V)} ≃ V :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- The whole-forest partition function is the product of descendant-subtree
partition functions at the selected component roots, including the empty
forest as the empty product. -/
theorem independenceEval_eq_prod_componentRoots_rootedPAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) :
    independenceEval G z =
      ∏ r ∈ R.componentRoots (G := G), rootedPAt R z r := by
  classical
  calc
    independenceEval G z =
        independenceEval (G.induce ((Finset.univ : Finset V) : Set V)) z :=
      (independenceEval_graphIso (induceUnivIso G) z).symm
    _ = independenceEval
        (G.induce (↑((R.componentRoots (G := G)).biUnion
          (fun r => R.descendants (G := G) r)) : Set V)) z := by
      rw [R.componentRoots_biUnion_descendants (G := G)]
    _ = ∏ r ∈ R.componentRoots (G := G),
        independenceEval (G.induce
          (↑(R.descendants (G := G) r) : Set V)) z := by
      apply independenceEval_induceFinset_biUnion G
        (R.componentRoots (G := G))
        (fun r => R.descendants (G := G) r)
        (R.componentRoots_pairwiseDisjoint_descendants (G := G))
      intro r hr s hs hrs x y hx hy
      exact R.componentRoots_no_cross_edges (G := G)
        r hr s hs hrs x hx y hy
    _ = _ := rfl

/-! ## Exact generated-configuration seed fibers -/

/-- The depth-indexed implementation satisfies the expected local availability
equation at every vertex. -/
theorem generatedOccupation_eq_seed_and_predecessors
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (v : V) :
    generatedOccupation R ω v =
      (ω v && decide (∀ u, R.IsChild (G := G) u v →
        generatedOccupation R ω u = false)) := by
  unfold generatedOccupation
  cases hdepth : R.depth (G := G) v with
  | zero =>
      simp only [occupationAtDepth]
      have hall : ∀ u, R.IsChild (G := G) u v →
          generatedOccupation R ω u = false := by
        intro u huv
        have hd := R.depth_child (G := G) huv
        rw [hdepth] at hd
        omega
      have hall' : ∀ u, R.IsChild (G := G) u v →
          occupationAtDepth R ω (R.depth (G := G) u) u = false := by
        simpa only [generatedOccupation] using hall
      have hdec : decide (∀ u, R.IsChild (G := G) u v →
          occupationAtDepth R ω (R.depth (G := G) u) u = false) = true :=
        decide_eq_true_iff.mpr hall'
      rw [hdec]
      simp
  | succ n =>
      simp only [occupationAtDepth]
      congr 2
      apply propext
      constructor
      · intro hall u huv
        have hd := R.depth_child (G := G) huv
        rw [hdepth] at hd
        have hu : R.depth (G := G) u = n := by omega
        rw [hu]
        exact hall u huv
      · intro hall u huv
        have hd := R.depth_child (G := G) huv
        rw [hdepth] at hd
        have hu : R.depth (G := G) u = n := by omega
        have := hall u huv
        rw [hu] at this
        exact this

/-- Vertices forced vacant by an occupied parent in the target independent set. -/
noncomputable def blockedBy
    (R : ComponentRooting G) (s : IndepFinset G) : Finset V :=
  Finset.univ.filter fun v =>
    ∃ u, u ∈ s.val ∧ R.IsChild (G := G) u v

/-- Vertices which are absent and not blocked, hence whose seed must be false. -/
noncomputable def availableAbsent
    (R : ComponentRooting G) (s : IndepFinset G) : Finset V :=
  Finset.univ \ (s.val ∪ blockedBy R s)

@[simp] theorem mem_blockedBy
    (R : ComponentRooting G) (s : IndepFinset G) (v : V) :
    v ∈ blockedBy R s ↔ ∃ u, u ∈ s.val ∧ R.IsChild (G := G) u v := by
  simp [blockedBy]

@[simp] theorem mem_availableAbsent
    (R : ComponentRooting G) (s : IndepFinset G) (v : V) :
    v ∈ availableAbsent R s ↔ v ∉ s.val ∧ v ∉ blockedBy R s := by
  simp [availableAbsent]

/-- Complete pointwise seed-fiber characterization.  Seeds at `blockedBy R s`
are intentionally unrestricted. -/
theorem generatedIndependentSet_eq_iff_seed_constraints
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (s : IndepFinset G) :
    generatedIndependentSet hG R ω = s ↔
      (∀ v ∈ s.val, ω v = true) ∧
      (∀ v ∈ availableAbsent R s, ω v = false) := by
  constructor
  · intro heq
    have hval : generatedFinset R ω = s.val :=
      congrArg Subtype.val heq
    constructor
    · intro v hv
      have hocc : generatedOccupation R ω v = true := by
        have : v ∈ generatedFinset R ω := by simpa [hval] using hv
        simpa [generatedFinset] using this
      rw [generatedOccupation_eq_seed_and_predecessors] at hocc
      have hboth : ω v = true ∧
          decide (∀ u, R.IsChild (G := G) u v →
            generatedOccupation R ω u = false) = true := by
        simpa using hocc
      exact hboth.1
    · intro v hv
      have hvnot : v ∉ s.val := (mem_availableAbsent R s v).mp hv |>.1
      have hocc : generatedOccupation R ω v = false := by
        by_contra ht
        have ht' : generatedOccupation R ω v = true :=
          Bool.eq_true_of_not_eq_false ht
        have hmem : v ∈ generatedFinset R ω := by
          simp [generatedFinset, ht']
        rw [hval] at hmem
        exact hvnot hmem
      have hall : ∀ u, R.IsChild (G := G) u v →
          generatedOccupation R ω u = false := by
        intro u huv
        by_contra ht
        have ht' : generatedOccupation R ω u = true :=
          Bool.eq_true_of_not_eq_false ht
        have humem : u ∈ s.val := by
          rw [← hval]
          simp [generatedFinset, ht']
        have hvblocked : v ∈ blockedBy R s :=
          (mem_blockedBy R s v).mpr ⟨u, humem, huv⟩
        exact ((mem_availableAbsent R s v).mp hv).2 hvblocked
      have hdec : decide (∀ u, R.IsChild (G := G) u v →
          generatedOccupation R ω u = false) = true :=
        decide_eq_true_iff.mpr hall
      rw [generatedOccupation_eq_seed_and_predecessors, hdec] at hocc
      simpa using hocc
  · rintro ⟨hone, hzero⟩
    have hind : ∀ n : ℕ, ∀ v : V, R.depth (G := G) v = n →
        (generatedOccupation R ω v = true ↔ v ∈ s.val) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro v hvdepth
          rw [generatedOccupation_eq_seed_and_predecessors]
          by_cases hvs : v ∈ s.val
          · have hseed : ω v = true := hone v hvs
            have hall : ∀ u, R.IsChild (G := G) u v →
                generatedOccupation R ω u = false := by
              intro u huv
              have hdu := R.depth_child (G := G) huv
              have hudepth : R.depth (G := G) u < n := by
                rw [hvdepth] at hdu
                omega
              have hunot : u ∉ s.val := by
                intro hus
                have hsind := s.property
                rw [SimpleGraph.isIndepSet_iff] at hsind
                exact hsind hus hvs huv.1.ne huv.1
              have huiff := ih (R.depth (G := G) u) hudepth u rfl
              exact Bool.eq_false_of_not_eq_true (fun hut => hunot (huiff.mp hut))
            have hdec : decide (∀ u, R.IsChild (G := G) u v →
                generatedOccupation R ω u = false) = true :=
              decide_eq_true_iff.mpr hall
            simp [hseed, hdec, hvs]
          · by_cases hvb : v ∈ blockedBy R s
            · obtain ⟨u, hus, huv⟩ := (mem_blockedBy R s v).mp hvb
              have hdu := R.depth_child (G := G) huv
              have hudepth : R.depth (G := G) u < n := by
                rw [hvdepth] at hdu
                omega
              have huiff := ih (R.depth (G := G) u) hudepth u rfl
              have huocc : generatedOccupation R ω u = true := huiff.mpr hus
              have hnot : ¬ (∀ w, R.IsChild (G := G) w v →
                  generatedOccupation R ω w = false) := by
                intro hall
                have hfalse := hall u huv
                rw [huocc] at hfalse
                contradiction
              have hdec : decide (∀ w, R.IsChild (G := G) w v →
                  generatedOccupation R ω w = false) = false :=
                decide_eq_false_iff_not.mpr hnot
              simp [hdec, hvs]
            · have hvavail : v ∈ availableAbsent R s :=
                (mem_availableAbsent R s v).mpr ⟨hvs, hvb⟩
              have hseed : ω v = false := hzero v hvavail
              simp [hseed, hvs]
    apply Subtype.ext
    ext v
    have hviff := hind (R.depth (G := G) v) v rfl
    simp only [generatedIndependentSet_val, generatedFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hviff

/-- Summing a product Bernoulli mass over assignments with disjoint true and
false coordinate constraints.  Every other coordinate, in particular every
blocked-parent coordinate, is summed over both Boolean values. -/
theorem bernoulliWeight_seedConstraintFiber
    (p : V → ℝ) (one zero : Finset V) (hdisj : Disjoint one zero) :
    (∑ ω : BernoulliAssignment V,
      if (∀ v ∈ one, ω v = true) ∧ (∀ v ∈ zero, ω v = false)
      then bernoulliWeight p ω else 0) =
      (∏ v ∈ one, p v) * (∏ v ∈ zero, (1 - p v)) := by
  classical
  let g : V → Bool → ℝ := fun v b =>
    if v ∈ one then (if b then p v else 0)
    else if v ∈ zero then (if b then 0 else 1 - p v)
    else if b then p v else 1 - p v
  have hpoint (ω : BernoulliAssignment V) :
      (if (∀ v ∈ one, ω v = true) ∧ (∀ v ∈ zero, ω v = false)
        then bernoulliWeight p ω else 0) = ∏ v, g v (ω v) := by
    by_cases hc : (∀ v ∈ one, ω v = true) ∧ (∀ v ∈ zero, ω v = false)
    · rw [if_pos hc]
      unfold bernoulliWeight
      apply Finset.prod_congr rfl
      intro v hv
      by_cases hvone : v ∈ one
      · simp [g, hvone, hc.1 v hvone]
      · by_cases hvzero : v ∈ zero
        · simp [g, hvone, hvzero, hc.2 v hvzero]
        · simp [g, hvone, hvzero]
    · rw [if_neg hc]
      have hbad : (∃ v ∈ one, ω v = false) ∨
          (∃ v ∈ zero, ω v = true) := by
        simp only [not_and_or] at hc
        rcases hc with hc | hc
        · left
          push Not at hc
          obtain ⟨v, hv, hne⟩ := hc
          exact ⟨v, hv, Bool.eq_false_of_not_eq_true hne⟩
        · right
          push Not at hc
          obtain ⟨v, hv, hne⟩ := hc
          exact ⟨v, hv, Bool.eq_true_of_not_eq_false hne⟩
      rcases hbad with ⟨v, hv, hω⟩ | ⟨v, hv, hω⟩
      · symm
        apply (Finset.prod_eq_zero (Finset.mem_univ v))
        simp [g, hv, hω]
      · symm
        apply (Finset.prod_eq_zero (Finset.mem_univ v))
        have hvnot : v ∉ one := by
          intro hone
          exact Finset.disjoint_left.mp hdisj hone hv
        simp [g, hvnot, hv, hω]
  simp_rw [hpoint]
  have hsum := Finset.prod_univ_sum
    (fun _ : V => (Finset.univ : Finset Bool)) g
  rw [Fintype.piFinset_univ] at hsum
  rw [← hsum]
  have hcoordinate (v : V) :
      (∑ b : Bool, g v b) =
        (if v ∈ one then p v else if v ∈ zero then 1 - p v else 1) := by
    rw [Fintype.sum_bool]
    by_cases hvone : v ∈ one
    · simp [g, hvone]
    · by_cases hvzero : v ∈ zero <;> simp [g, hvone, hvzero]
  simp_rw [hcoordinate]
  calc
    (∏ v, if v ∈ one then p v else if v ∈ zero then 1 - p v else 1) =
        ∏ v, ((if v ∈ one then p v else 1) *
          (if v ∈ zero then 1 - p v else 1)) := by
      apply Finset.prod_congr rfl
      intro v hv
      by_cases hvone : v ∈ one
      · have hvzero : v ∉ zero := fun hz =>
          Finset.disjoint_left.mp hdisj hvone hz
        simp [hvone, hvzero]
      · by_cases hvzero : v ∈ zero <;> simp [hvone, hvzero]
    _ = (∏ v, if v ∈ one then p v else 1) *
        (∏ v, if v ∈ zero then 1 - p v else 1) :=
      Finset.prod_mul_distrib
    _ = (∏ v ∈ one, p v) * (∏ v ∈ zero, (1 - p v)) := by
      have honeprod : (∏ v : V, if v ∈ one then p v else 1) =
          ∏ v ∈ one, p v := by
        rw [Finset.prod_ite]
        simp
      have hzeroprod : (∏ v : V, if v ∈ zero then 1 - p v else 1) =
          ∏ v ∈ zero, (1 - p v) := by
        rw [Finset.prod_ite]
        simp
      rw [honeprod, hzeroprod]

/-- Exact mass of a generated-configuration fiber after explicitly summing all
unrestricted blocked-parent seeds. -/
theorem generated_fiber_mass_eq_fixed_product
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    (∑ ω : BernoulliAssignment V,
      if generatedIndependentSet hG R ω = s then
        bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω
      else 0) =
      (∏ v ∈ s.val, rootedOccupationProbabilityAt R z v) *
      (∏ v ∈ availableAbsent R s, rootedVacancyProbabilityAt R z v) := by
  classical
  have hd : Disjoint s.val (availableAbsent R s) := by
    rw [Finset.disjoint_left]
    intro v hv hzero
    exact (mem_availableAbsent R s v).mp hzero |>.1 hv
  rw [show (∑ ω : BernoulliAssignment V,
      if generatedIndependentSet hG R ω = s then
        bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω
      else 0) =
      ∑ ω : BernoulliAssignment V,
        if (∀ v ∈ s.val, ω v = true) ∧
            (∀ v ∈ availableAbsent R s, ω v = false)
        then bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω
        else 0 by
    apply Finset.sum_congr rfl
    intro ω hω
    have hiff := generatedIndependentSet_eq_iff_seed_constraints hG R ω s
    by_cases hgen : generatedIndependentSet hG R ω = s
    · have hc := hiff.mp hgen
      rw [if_pos hgen, if_pos hc]
    · have hc : ¬ ((∀ v ∈ s.val, ω v = true) ∧
          (∀ v ∈ availableAbsent R s, ω v = false)) :=
        fun hc => hgen (hiff.mpr hc)
      rw [if_neg hgen, if_neg hc]]
  rw [bernoulliWeight_seedConstraintFiber _ _ _ hd]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  linarith [rootedOccupationProbabilityAt_add_vacancy R z hz v]
/-! ## Telescoping of the fixed fiber product -/

/-- The fixed-product integrand restricted to a descendant subtree. -/
noncomputable def subtreeConfigurationFactor
    (R : ComponentRooting G) (s : IndepFinset G) (z : ℝ) (u : V) : ℝ :=
  ∏ v ∈ R.descendants (G := G) u,
    if v ∈ s.val then rootedOccupationProbabilityAt R z v
    else if v ∈ availableAbsent R s then rootedVacancyProbabilityAt R z v else 1

/-- The activity product over selected vertices in a descendant subtree. -/
noncomputable def subtreeSelectedActivityProduct
    (R : ComponentRooting G) (s : IndepFinset G) (z : ℝ) (u : V) : ℝ :=
  ∏ v ∈ R.descendants (G := G) u, if v ∈ s.val then z else 1

private theorem subtreeConfigurationFactor_decompose
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) (z : ℝ) (u : V) :
    subtreeConfigurationFactor R s z u =
      (if u ∈ s.val then rootedOccupationProbabilityAt R z u
       else if u ∈ availableAbsent R s then rootedVacancyProbabilityAt R z u else 1) *
      ∏ v ∈ R.children (G := G) u, subtreeConfigurationFactor R s z v := by
  classical
  unfold subtreeConfigurationFactor
  rw [R.descendants_eq_insert_biUnion_children (G := G) u]
  rw [Finset.prod_insert]
  · rw [Finset.prod_biUnion
      (R.children_pairwiseDisjoint_descendants (G := G) hG u)]
  · intro hu
    obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
    exact R.not_mem_descendants_child (G := G)
      ((R.mem_children (G := G) u v).mp hv) huv

private theorem subtreeSelectedActivityProduct_decompose
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) (z : ℝ) (u : V) :
    subtreeSelectedActivityProduct R s z u =
      (if u ∈ s.val then z else 1) *
      ∏ v ∈ R.children (G := G) u, subtreeSelectedActivityProduct R s z v := by
  classical
  unfold subtreeSelectedActivityProduct
  rw [R.descendants_eq_insert_biUnion_children (G := G) u]
  rw [Finset.prod_insert]
  · rw [Finset.prod_biUnion
      (R.children_pairwiseDisjoint_descendants (G := G) hG u)]
  · intro hu
    obtain ⟨v, hv, huv⟩ := Finset.mem_biUnion.mp hu
    exact R.not_mem_descendants_child (G := G)
      ((R.mem_children (G := G) u v).mp hv) huv

private theorem child_blocked_of_selected
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) {u v : V} (hus : u ∈ s.val)
    (hv : v ∈ R.children (G := G) u) : v ∈ blockedBy R s := by
  exact (mem_blockedBy R s v).mpr ⟨u, hus,
    (R.mem_children (G := G) u v).mp hv⟩

private theorem child_not_blocked_of_not_selected
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) {u v : V} (hus : u ∉ s.val)
    (hv : v ∈ R.children (G := G) u) : v ∉ blockedBy R s := by
  intro hb
  obtain ⟨w, hws, hwv⟩ := (mem_blockedBy R s v).mp hb
  have hwu : w = u := R.isChild_unique (G := G) hG hwv
    ((R.mem_children (G := G) u v).mp hv)
  exact hus (hwu ▸ hws)

private theorem blocked_not_selected
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) {u : V} (hu : u ∈ blockedBy R s) : u ∉ s.val := by
  intro hus
  obtain ⟨w, hws, hwu⟩ := (mem_blockedBy R s u).mp hu
  have hsind := s.property
  rw [SimpleGraph.isIndepSet_iff] at hsind
  exact hsind hws hus hwu.1.ne hwu.1

/-- Positivity of an arbitrary-activity descendant partition function. -/
private theorem rootedPAt_pos'
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedPAt R z u :=
  independenceEval_pos _ hz

private theorem subtreeFiberFactor_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) (z : ℝ) (hz : 0 < z) (u : V) :
    subtreeConfigurationFactor R s z u =
      subtreeSelectedActivityProduct R s z u /
        (if u ∈ blockedBy R s then rootedQAt R z u else rootedPAt R z u) := by
  classical
  induction horder : (R.descendants (G := G) u).card using
      Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [subtreeConfigurationFactor_decompose hG R s z u,
        subtreeSelectedActivityProduct_decompose hG R s z u]
      by_cases hub : u ∈ blockedBy R s
      · have hus : u ∉ s.val := blocked_not_selected hG R s hub
        have hu_not_avail : u ∉ availableAbsent R s := by
          intro h
          exact ((mem_availableAbsent R s u).mp h).2 hub
        have hchild : ∀ v ∈ R.children (G := G) u,
            v ∉ blockedBy R s := by
          intro v hv
          exact child_not_blocked_of_not_selected hG R s hus hv
        have hfactor : ∀ v ∈ R.children (G := G) u,
            subtreeConfigurationFactor R s z v =
              subtreeSelectedActivityProduct R s z v / rootedPAt R z v := by
          intro v hv
          have hi := ih (R.descendants (G := G) v).card (by
            rw [← horder]
            exact R.subtreeOrder_child_lt (G := G)
              ((R.mem_children (G := G) u v).mp hv)) v rfl
          simpa [hchild v hv] using hi
        have hprod :
            (∏ v ∈ R.children (G := G) u,
              subtreeConfigurationFactor R s z v) =
              ∏ v ∈ R.children (G := G) u,
                subtreeSelectedActivityProduct R s z v /
                  rootedPAt R z v := by
          apply Finset.prod_congr rfl
          intro v hv
          exact hfactor v hv
        rw [hprod]
        simp only [hus, hu_not_avail, hub, ↓reduceIte]
        rw [rootedQAt_eq_prod_rootedPAt hG R z u]
        rw [Finset.prod_div_distrib]
        ring
      · by_cases hus : u ∈ s.val
        · have hchild : ∀ v ∈ R.children (G := G) u,
              v ∈ blockedBy R s := by
            intro v hv
            exact child_blocked_of_selected hG R s hus hv
          have hfactor : ∀ v ∈ R.children (G := G) u,
              subtreeConfigurationFactor R s z v =
                subtreeSelectedActivityProduct R s z v / rootedQAt R z v := by
            intro v hv
            have hi := ih (R.descendants (G := G) v).card (by
              rw [← horder]
              exact R.subtreeOrder_child_lt (G := G)
                ((R.mem_children (G := G) u v).mp hv)) v rfl
            simpa [hchild v hv] using hi
          have hprod :
              (∏ v ∈ R.children (G := G) u,
                subtreeConfigurationFactor R s z v) =
                ∏ v ∈ R.children (G := G) u,
                  subtreeSelectedActivityProduct R s z v /
                    rootedQAt R z v := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hfactor v hv
          rw [hprod]
          simp only [hus, hub, ↓reduceIte]
          rw [rootedOccupationProbabilityAt]
          rw [rootedAAt_eq_z_mul_prod_rootedQAt hG R z u]
          rw [Finset.prod_div_distrib]
          have hQprod :
              (∏ v ∈ R.children (G := G) u, rootedQAt R z v) ≠ 0 := by
            apply ne_of_gt
            apply Finset.prod_pos
            intro v hv
            exact rootedQAt_pos R z hz v
          field_simp [ne_of_gt (rootedPAt_pos' R z hz u), hQprod]
        · have huavail : u ∈ availableAbsent R s :=
            (mem_availableAbsent R s u).mpr ⟨hus, hub⟩
          have hchild : ∀ v ∈ R.children (G := G) u,
              v ∉ blockedBy R s := by
            intro v hv
            exact child_not_blocked_of_not_selected hG R s hus hv
          have hfactor : ∀ v ∈ R.children (G := G) u,
              subtreeConfigurationFactor R s z v =
                subtreeSelectedActivityProduct R s z v / rootedPAt R z v := by
            intro v hv
            have hi := ih (R.descendants (G := G) v).card (by
              rw [← horder]
              exact R.subtreeOrder_child_lt (G := G)
                ((R.mem_children (G := G) u v).mp hv)) v rfl
            simpa [hchild v hv] using hi
          have hprod :
              (∏ v ∈ R.children (G := G) u,
                subtreeConfigurationFactor R s z v) =
                ∏ v ∈ R.children (G := G) u,
                  subtreeSelectedActivityProduct R s z v /
                    rootedPAt R z v := by
            apply Finset.prod_congr rfl
            intro v hv
            exact hfactor v hv
          rw [hprod]
          simp only [hus, hub, huavail, ↓reduceIte]
          rw [rootedVacancyProbabilityAt]
          rw [rootedQAt_eq_prod_rootedPAt hG R z u]
          rw [Finset.prod_div_distrib]
          have hPprod :
              (∏ v ∈ R.children (G := G) u, rootedPAt R z v) ≠ 0 := by
            apply ne_of_gt
            apply Finset.prod_pos
            intro v hv
            exact rootedPAt_pos' R z hz v
          field_simp [ne_of_gt (rootedPAt_pos' R z hz u), hPprod]

/-- The product over the selected vertices in a whole descendant subtree is
exactly the corresponding activity power. -/
private theorem subtreeSelectedActivityProduct_eq_pow
    (R : ComponentRooting G) (s : IndepFinset G) (z : ℝ) (u : V) :
    subtreeSelectedActivityProduct R s z u =
      z ^ (s.val ∩ R.descendants (G := G) u).card := by
  classical
  unfold subtreeSelectedActivityProduct
  rw [← Finset.prod_filter]
  have hfilter :
      (R.descendants (G := G) u).filter (fun v => v ∈ s.val) =
        s.val ∩ R.descendants (G := G) u := by
    ext v
    simp [and_comm]
  rw [hfilter]
  simp


/-- The fixed fiber product can be regrouped as a product over all vertices. -/
private theorem fixedFiberProduct_eq_univ_factor
    (R : ComponentRooting G) (s : IndepFinset G) (z : ℝ) :
    (∏ v ∈ s.val, rootedOccupationProbabilityAt R z v) *
        (∏ v ∈ availableAbsent R s, rootedVacancyProbabilityAt R z v) =
      ∏ v : V,
        if v ∈ s.val then rootedOccupationProbabilityAt R z v
        else if v ∈ availableAbsent R s then rootedVacancyProbabilityAt R z v else 1 := by
  classical
  have hd : Disjoint s.val (availableAbsent R s) := by
    rw [Finset.disjoint_left]
    intro v hv hzero
    exact (mem_availableAbsent R s v).mp hzero |>.1 hv
  have hone :
      (∏ v ∈ s.val, rootedOccupationProbabilityAt R z v) =
        ∏ v : V, if v ∈ s.val then rootedOccupationProbabilityAt R z v else 1 := by
    rw [Finset.prod_ite]
    simp
  have hzero :
      (∏ v ∈ availableAbsent R s, rootedVacancyProbabilityAt R z v) =
        ∏ v : V, if v ∈ availableAbsent R s then rootedVacancyProbabilityAt R z v else 1 := by
    have hA : availableAbsent R s =
        (Finset.univ.filter (fun v => v ∈ availableAbsent R s)) := by
      ext v
      simp
    rw [hA, Finset.prod_ite]
    simp
  rw [hone, hzero, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v hv
  by_cases hs : v ∈ s.val
  · have hvzero : v ∉ availableAbsent R s := by
      intro hvzero
      exact (mem_availableAbsent R s v).mp hvzero |>.1 hs
    simp [hs, hvzero]
  · by_cases hvzero : v ∈ availableAbsent R s
    · simp [hs, hvzero]
    · simp [hs, hvzero]

/-- Component descendant subtrees regroup the unconditioned fixed-product
integrand, including an empty set of component roots. -/
private theorem univ_factor_eq_component_subtree_factors
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) (z : ℝ) :
    (∏ v : V,
        if v ∈ s.val then rootedOccupationProbabilityAt R z v
        else if v ∈ availableAbsent R s then rootedVacancyProbabilityAt R z v else 1) =
      ∏ r ∈ R.componentRoots (G := G),
        subtreeConfigurationFactor R s z r := by
  classical
  rw [← R.componentRoots_biUnion_descendants (G := G)]
  rw [Finset.prod_biUnion
    (R.componentRoots_pairwiseDisjoint_descendants (G := G))]
  rfl

private theorem componentRoot_not_blocked
    (R : ComponentRooting G) (s : IndepFinset G)
    {r : V} (hr : r ∈ R.componentRoots (G := G)) :
    r ∉ blockedBy R s := by
  intro hb
  obtain ⟨u, hus, hur⟩ := (mem_blockedBy R s r).mp hb
  have hroot : r = R.rootOf (G := G) r := by
    exact (R.mem_componentRoots (G := G) r).mp hr
  exact (R.not_isChild_of_eq_root (G := G) hroot) hur

private theorem component_subtree_selectedProduct_eq_pow
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (s : IndepFinset G) (z : ℝ) :
    (∏ r ∈ R.componentRoots (G := G),
        subtreeSelectedActivityProduct R s z r) = z ^ s.val.card := by
  classical
  rw [show (∏ r ∈ R.componentRoots (G := G),
      subtreeSelectedActivityProduct R s z r) =
      ∏ r ∈ R.componentRoots (G := G),
        ∏ v ∈ R.descendants (G := G) r, if v ∈ s.val then z else 1 by rfl]
  rw [← Finset.prod_biUnion
    (R.componentRoots_pairwiseDisjoint_descendants (G := G))]
  rw [R.componentRoots_biUnion_descendants (G := G)]
  rw [Finset.prod_ite]
  simp

/-- The fixed-product fiber mass is the actual hard-core probability. -/
theorem generated_fiber_mass_eq_hardCore_probability
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    (∑ ω : BernoulliAssignment V,
      if generatedIndependentSet hG R ω = s then
        bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω
      else 0) = (Forest.hardCoreLaw G z hz).probability s := by
  classical
  rw [generated_fiber_mass_eq_fixed_product hG R z hz s]
  rw [fixedFiberProduct_eq_univ_factor R s z]
  rw [univ_factor_eq_component_subtree_factors hG R s z]
  have hlocal : ∀ r ∈ R.componentRoots (G := G),
      subtreeConfigurationFactor R s z r =
        subtreeSelectedActivityProduct R s z r / rootedPAt R z r := by
    intro r hr
    calc
      subtreeConfigurationFactor R s z r =
          subtreeSelectedActivityProduct R s z r /
            (if r ∈ blockedBy R s then rootedQAt R z r else rootedPAt R z r) :=
        subtreeFiberFactor_eq hG R s z hz r
      _ = subtreeSelectedActivityProduct R s z r / rootedPAt R z r := by
        rw [if_neg (componentRoot_not_blocked R s hr)]
  have hcomp :
      (∏ r ∈ R.componentRoots (G := G),
        subtreeConfigurationFactor R s z r) =
        ∏ r ∈ R.componentRoots (G := G),
          subtreeSelectedActivityProduct R s z r / rootedPAt R z r := by
    apply Finset.prod_congr rfl
    intro r hr
    exact hlocal r hr
  rw [hcomp]
  rw [Finset.prod_div_distrib]
  rw [component_subtree_selectedProduct_eq_pow hG R s z]
  rw [← independenceEval_eq_prod_componentRoots_rootedPAt hG R z]
  rfl

/-- The recursive sampler has the exact unconditional configuration pushforward
onto the native finite hard-core law. -/
theorem exactHardCoreConfigurationCoupling_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ExactHardCoreConfigurationCoupling hG R z hz := by
  intro s
  calc
    (∑ ω : BernoulliAssignment V,
        if generatedIndependentSet hG R ω = s then
          (generatedCountLaw hG R z hz).probability ω else 0) =
        ∑ ω : BernoulliAssignment V,
          if generatedIndependentSet hG R ω = s then
            bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) ω else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      rfl
    _ = (Forest.hardCoreLaw G z hz).probability s :=
      generated_fiber_mass_eq_hardCore_probability hG R z hz s

theorem generatedCountLaw_rankMass_eq_of_configurationCoupling
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (hpush : ExactHardCoreConfigurationCoupling hG R z hz) (k : ℕ) :
    (generatedCountLaw hG R z hz).rankMass k =
      (Forest.hardCoreLaw G z hz).rankMass k := by
  classical
  let g : BernoulliAssignment V → IndepFinset G :=
    generatedIndependentSet hG R
  let p : BernoulliAssignment V → ℝ :=
    fun ω => (generatedCountLaw hG R z hz).probability ω
  have hf := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (BernoulliAssignment V)))
    (g := g) (f := fun ω => if (g ω).val.card = k then p ω else 0)
  have hleft :
      (∑ s : IndepFinset G,
        ∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with g ω = s,
          (if (g ω).val.card = k then p ω else 0)) =
        (generatedCountLaw hG R z hz).rankMass k := by
    rw [Forest.FiniteLatticeLaw.rankMass_eq_sum_probability]
    simpa [g, p, generatedCountLaw, generatedFinset, bernoulliWeight] using hf
  have hfiber (s : IndepFinset G) :
      (∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with g ω = s,
        (if (g ω).val.card = k then p ω else 0)) =
      if s.val.card = k then
        ∑ ω : BernoulliAssignment V, if g ω = s then p ω else 0 else 0 := by
    by_cases hs : s.val.card = k
    · simp only [if_pos hs]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hgs : g ω = s
      · simp [hgs, hs]
      · simp [hgs]
    · simp only [if_neg hs]
      rw [Finset.sum_filter]
      apply Finset.sum_eq_zero
      intro ω hω
      by_cases hgs : g ω = s
      · simp [hgs, hs]
      · simp [hgs]
  have hpush' (s : IndepFinset G) :
      (∑ ω : BernoulliAssignment V, if g ω = s then p ω else 0) =
        (Forest.hardCoreLaw G z hz).probability s := by
    simpa [g, p] using hpush s
  rw [← hleft]
  simp_rw [hfiber]
  simp_rw [hpush']
  rw [Forest.FiniteLatticeLaw.rankMass_eq_sum_probability]
  rfl

/-- The conditional transfer can be packaged in the native count-coupling
proposition used by the project API. -/
theorem exactHardCoreCountCoupling_of_configurationCoupling
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (hpush : ExactHardCoreConfigurationCoupling hG R z hz) :
    ExactHardCoreCountCoupling hG R z hz := by
  intro k
  exact generatedCountLaw_rankMass_eq_of_configurationCoupling hG R z hz hpush k

/-- The unconditional native count coupling obtained from the configuration
pushforward and the actual `FiniteLatticeLaw.rankMass`. -/
theorem exactHardCoreCountCoupling_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ExactHardCoreCountCoupling hG R z hz := by
  exact exactHardCoreCountCoupling_of_configurationCoupling hG R z hz
    (exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz)

/-- First direct downstream identity for the actual finite hard-core law: its
native rank masses are the explicitly normalized independence coefficients. -/
theorem actualHardCore_rankMass_eq_tiltedMass
    (z : ℝ) (hz : 0 < z) (k : ℕ) :
    (Forest.hardCoreLaw G z hz).rankMass k =
      tiltedMass (Forest.independenceCoefficients G) z
        (independenceEval G z) k := by
  exact Forest.hardCoreLaw_rankMass_eq G z hz k

/-- The empty-forest instance of native rank-mass coupling is unconditional. -/
theorem generatedCountLaw_rankMass_eq_empty [IsEmpty V]
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (k : ℕ) :
    (generatedCountLaw hG R z hz).rankMass k =
      (Forest.hardCoreLaw G z hz).rankMass k := by
  apply generatedCountLaw_rankMass_eq_of_configurationCoupling hG R z hz
    (exactHardCoreConfigurationCoupling_empty hG R z hz) k

/-! ## Explicit finite-law Doob representation and actual-law transfer -/

noncomputable local instance doobPropDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- Expected value of a statistic under a finite lattice law. -/
noncomputable def lawExpectation (L : Forest.FiniteLatticeLaw (BernoulliAssignment V))
    (X : BernoulliAssignment V → ℝ) : ℝ :=
  ∑ ω, L.probability ω * X ω

/-- The generated occupation count as a real-valued statistic. -/
noncomputable def generatedCountReal (hG : G.IsAcyclic) (R : ComponentRooting G)
    (ω : BernoulliAssignment V) : ℝ :=
  (generatedFinset R ω).card

/-- The actual hard-core occupation count. -/
def hardCoreCountReal (s : IndepFinset G) : ℝ := s.val.card

/-- Pushforward of every real statistic through the exact finite coupling. -/
theorem generatedExpectation_eq_hardCoreExpectation
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (hpush : ExactHardCoreConfigurationCoupling hG R z hz)
    (f : IndepFinset G → ℝ) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      f (generatedIndependentSet hG R ω) =
      ∑ s, (Forest.hardCoreLaw G z hz).probability s * f s := by
  classical
  let g : BernoulliAssignment V → IndepFinset G := generatedIndependentSet hG R
  let p : BernoulliAssignment V → ℝ :=
    fun ω => (generatedCountLaw hG R z hz).probability ω
  have hf := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (BernoulliAssignment V)))
    (g := g) (f := fun ω => p ω * f (g ω))
  have hfiber (s : IndepFinset G) :
      (∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with g ω = s,
        p ω * f (g ω)) =
      f s * ∑ ω : BernoulliAssignment V, if g ω = s then p ω else 0 := by
    rw [Finset.sum_filter]
    calc
      (∑ x, if g x = s then p x * f (g x) else 0) =
          ∑ x, if g x = s then p x * f s else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxs : g x = s <;> simp [hxs]
      _ = f s * ∑ x, if g x = s then p x else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxs : g x = s <;> simp [hxs] <;> ring
  calc
    (∑ ω, (generatedCountLaw hG R z hz).probability ω * f
        (generatedIndependentSet hG R ω)) =
        ∑ s : IndepFinset G,
          ∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with g ω = s,
            p ω * f (g ω) := hf.symm
    _ = ∑ s : IndepFinset G,
        f s * ∑ ω : BernoulliAssignment V, if g ω = s then p ω else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      exact hfiber s
    _ = ∑ s : IndepFinset G,
        f s * (Forest.hardCoreLaw G z hz).probability s := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [hpush]
    _ = ∑ s : IndepFinset G,
        (Forest.hardCoreLaw G z hz).probability s * f s := by
      apply Finset.sum_congr rfl
      intro s hs
      ring

/-- The generated sampler and actual law have the same count mean. -/
theorem generatedCount_mean_eq_hardCore_mean
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (hpush : ExactHardCoreConfigurationCoupling hG R z hz) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      generatedCountReal hG R ω =
      (Forest.hardCoreLaw G z hz).mean := by
  rw [show generatedCountReal hG R = fun ω =>
      hardCoreCountReal (generatedIndependentSet hG R ω) by
    funext ω
    rfl]
  simpa [Forest.FiniteLatticeLaw.mean, hardCoreCountReal] using
    generatedExpectation_eq_hardCoreExpectation hG R z hz hpush
      (fun s => hardCoreCountReal s)

/-- The centered fourth moment also transfers exactly through the coupling. -/
theorem generatedCenteredFourth_eq_hardCoreCenteredFourth
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (hpush : ExactHardCoreConfigurationCoupling hG R z hz) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      (generatedCountReal hG R ω - (Forest.hardCoreLaw G z hz).mean) ^ 4 =
      ∑ s, (Forest.hardCoreLaw G z hz).probability s *
        (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 4 := by
  rw [show generatedCountReal hG R = fun ω =>
      hardCoreCountReal (generatedIndependentSet hG R ω) by
    funext ω
    rfl]
  simpa using generatedExpectation_eq_hardCoreExpectation hG R z hz hpush
    (fun s => (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 4)

/-- A finite prefix atom for a seed-reveal order. -/
noncomputable def samePrefix (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1))
    (ω ω' : BernoulliAssignment V) : Prop :=
  ∀ i : Fin k.1, ω (e ⟨i, by omega⟩) = ω' (e ⟨i, by omega⟩)

/-- Prefix mass of the seed product law. -/
noncomputable def prefixMass (p : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) (ω : BernoulliAssignment V) : ℝ :=
  ∑ ω', if samePrefix e k ω ω' then p ω' else 0

/-- Prefix weighted statistic. -/
noncomputable def prefixWeighted (p : BernoulliAssignment V → ℝ)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) (ω : BernoulliAssignment V) : ℝ :=
  ∑ ω', if samePrefix e k ω ω' then p ω' * X ω' else 0

/-- Explicit finite conditional expectation on prefix atoms. -/
noncomputable def finiteDoobMean (p : BernoulliAssignment V → ℝ)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) (ω : BernoulliAssignment V) : ℝ :=
  if h : prefixMass p e k ω = 0 then 0
  else prefixWeighted p X e k ω / prefixMass p e k ω

/-- The finite Doob increment associated with revealing the next seed. -/
noncomputable def finiteDoobIncrement (p : BernoulliAssignment V → ℝ)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) : ℝ :=
  finiteDoobMean p X e ⟨k.1 + 1, by omega⟩ ω -
    finiteDoobMean p X e ⟨k.1, by omega⟩ ω

/-- A prefix of length `k.castSucc` is the common part of the two next-bit
prefixes of length `k.succ`.  This elementary lemma is the finite filtration
identity underlying (A.13)--(A.14). -/
theorem samePrefix_castSucc_of_samePrefix_succ_update
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω ω' : BernoulliAssignment V) (b : Bool)
    (h : samePrefix e k.succ (Function.update ω (e k) b) ω') :
    samePrefix e k.castSucc ω ω' := by
  classical
  intro i
  let j : Fin (Fintype.card V) := ⟨i.1, by omega⟩
  have hjlt : j.1 < k.succ := by simp [j]
  have hne : e j ≠ e k := by
    intro heq
    have hjk : j = k := e.injective heq
    have hval := congrArg Fin.val hjk
    simp [j] at hval
    omega
  have hp := h ⟨j, hjlt⟩
  simpa [j, Function.update, hne] using hp

/-- The Bernoulli one-step split value: `0` gives the value on the false
subatom and `1` gives the value on the true subatom. -/
noncomputable def finiteDoobBranchValue
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) : Bool → ℝ := fun b =>
  finiteDoobMean p X e k.succ (Function.update ω (e k) b)

/-- The explicit two-point branch has centered increment about its own weighted
mean.  This is the algebraic one-step martingale equation (A.14); no measure API
is required. -/
theorem finiteDoobBranch_centered
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) (b : ℝ) :
    (1 - b) * ((finiteDoobBranchValue p X e k ω false -
        ((1 - b) * finiteDoobBranchValue p X e k ω false +
          b * finiteDoobBranchValue p X e k ω true))) +
      b * ((finiteDoobBranchValue p X e k ω true -
        ((1 - b) * finiteDoobBranchValue p X e k ω false +
          b * finiteDoobBranchValue p X e k ω true))) = 0 := by
  ring

theorem finiteDoobIncrement_eq_difference
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobIncrement p X e k ω =
      finiteDoobMean p X e ⟨k.1 + 1, by omega⟩ ω -
        finiteDoobMean p X e ⟨k.1, by omega⟩ ω := by
  rfl

/-- At time zero every seed lies in the unique prefix atom. -/
theorem samePrefix_zero (e : Fin (Fintype.card V) ≃ V)
    (ω ω' : BernoulliAssignment V) :
    samePrefix e ⟨0, Nat.zero_lt_succ _⟩ ω ω' := by
  intro i
  exact Fin.elim0 i

/-- At terminal time the prefix atom is a singleton. -/
theorem samePrefix_terminal_iff (e : Fin (Fintype.card V) ≃ V)
    (ω ω' : BernoulliAssignment V) :
    samePrefix e ⟨Fintype.card V, Nat.lt_succ_self _⟩ ω ω' ↔ ω = ω' := by
  constructor
  · intro h
    funext v
    let i : Fin (Fintype.card V) := e.symm v
    have hi := h i
    simpa [i] using hi
  · intro h
    subst ω'
    intro i
    rfl

/-- The prefix mass at time zero is the total seed mass. -/
theorem prefixMass_zero
    (p : BernoulliAssignment V → ℝ) (e : Fin (Fintype.card V) ≃ V)
    (ω : BernoulliAssignment V) :
    prefixMass p e ⟨0, Nat.zero_lt_succ _⟩ ω = ∑ ω', p ω' := by
  unfold prefixMass
  apply Finset.sum_congr rfl
  intro ω' hω'
  rw [if_pos (samePrefix_zero e ω ω')]

/-- The zero-time weighted prefix sum is the full expectation numerator. -/
theorem prefixWeighted_zero
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    prefixWeighted p X e ⟨0, Nat.zero_lt_succ _⟩ ω = ∑ ω', p ω' * X ω' := by
  unfold prefixWeighted
  apply Finset.sum_congr rfl
  intro ω' hω'
  rw [if_pos (samePrefix_zero e ω ω')]

/-- Terminal prefix sums reduce to a single atom. -/
theorem prefixMass_terminal
    (p : BernoulliAssignment V → ℝ) (e : Fin (Fintype.card V) ≃ V)
    (ω : BernoulliAssignment V) :
    prefixMass p e ⟨Fintype.card V, Nat.lt_succ_self _⟩ ω = p ω := by
  unfold prefixMass
  simp only [samePrefix_terminal_iff]
  simp

 theorem prefixWeighted_terminal
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    prefixWeighted p X e ⟨Fintype.card V, Nat.lt_succ_self _⟩ ω = p ω * X ω := by
  unfold prefixWeighted
  simp only [samePrefix_terminal_iff]
  simp

/-- Positive product weights make every prefix denominator nonzero. -/
theorem prefixMass_pos
    (p : BernoulliAssignment V → ℝ) (hp : ∀ ω, 0 < p ω)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) : 0 < prefixMass p e k ω := by
  unfold prefixMass
  have hω : samePrefix e k ω ω := by
    intro i
    rfl
  apply Finset.sum_pos'
  · intro x hx
    by_cases hpre : samePrefix e k ω x
    · rw [if_pos hpre]
      exact (hp x).le
    · rw [if_neg hpre]
  · refine ⟨ω, Finset.mem_univ _, ?_⟩
    rw [if_pos hω]
    exact hp ω

/-- Terminal finite conditional expectation equals the revealed statistic. -/
theorem finiteDoobMean_terminal
    (p : BernoulliAssignment V → ℝ) (hp : ∀ ω, 0 < p ω)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    finiteDoobMean p X e ⟨Fintype.card V, Nat.lt_succ_self _⟩ ω = X ω := by
  rw [finiteDoobMean, dif_neg]
  · rw [prefixMass_terminal, prefixWeighted_terminal]
    field_simp [ne_of_gt (hp ω)]
  · exact (prefixMass_pos p hp e _ ω).ne'

/-- Terminal Doob value for the actual generated count. -/
theorem generatedCount_finiteDoobMean_terminal
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    finiteDoobMean (fun ω => (generatedCountLaw hG R z hz).probability ω)
      (generatedCountReal hG R) e
      ⟨Fintype.card V, Nat.lt_succ_self _⟩ ω = generatedCountReal hG R ω := by
  apply finiteDoobMean_terminal
  intro ω'
  unfold generatedCountLaw hardCoreBernoulliSeedLaw independentBernoulliLaw
  unfold bernoulliWeight
  apply Finset.prod_pos
  intro v hv
  by_cases hseed : ω' v
  · rw [if_pos hseed]
    exact rootedOccupationProbabilityAt_pos R z hz v
  · rw [if_neg hseed]
    rw [show 1 - rootedOccupationProbabilityAt R z v =
      rootedVacancyProbabilityAt R z v by
      linarith [rootedOccupationProbabilityAt_add_vacancy R z hz v]]
    exact div_pos (rootedQAt_pos R z hz v) (by
      rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
      exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))

/-- A finite adjacent-difference sum telescopes exactly. -/
theorem sum_fin_adjacent_sub {n : ℕ} (M : Fin (n + 1) → ℝ) :
    (∑ k : Fin n, (M k.succ - M k.castSucc)) =
      M (Fin.last n) - M 0 := by
  rw [Finset.sum_sub_distrib]
  have hsucc := Fin.sum_univ_succ M
  have hcast := Fin.sum_univ_castSucc M
  linarith

/-- The explicit prefix-fiber Doob increments telescope from time zero to time `n`. -/
theorem finiteDoobIncrement_sum_eq_terminal_sub_zero
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    (∑ k : Fin (Fintype.card V), finiteDoobIncrement p X e k ω) =
      finiteDoobMean p X e (Fin.last (Fintype.card V)) ω -
        finiteDoobMean p X e 0 ω := by
  let M : Fin (Fintype.card V + 1) → ℝ := fun k => finiteDoobMean p X e k ω
  simpa [finiteDoobIncrement, M] using sum_fin_adjacent_sub M

/-- The time-zero Doob value is the ordinary weighted mean for a normalized finite law. -/
theorem finiteDoobMean_zero_of_normalized
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V)
    (hnorm : ∑ ω', p ω' = 1) :
    finiteDoobMean p X e 0 ω = ∑ ω', p ω' * X ω' := by
  rw [finiteDoobMean, dif_neg]
  · change prefixWeighted p X e ⟨0, Nat.zero_lt_succ _⟩ ω /
      prefixMass p e ⟨0, Nat.zero_lt_succ _⟩ ω = _
    rw [prefixMass_zero, prefixWeighted_zero, hnorm]
    simp
  · change ¬ prefixMass p e ⟨0, Nat.zero_lt_succ _⟩ ω = 0
    rw [prefixMass_zero, hnorm]
    norm_num

/-- The actual generated-count Doob decomposition: terminal count minus its
finite-law mean is the sum of the explicitly defined prefix-fiber increments. -/
theorem generatedCountReal_sub_mean_eq_sum_finiteDoobIncrement
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    generatedCountReal hG R ω - (generatedCountLaw hG R z hz).mean =
      ∑ k : Fin (Fintype.card V),
        finiteDoobIncrement
          (fun ω => (generatedCountLaw hG R z hz).probability ω)
          (generatedCountReal hG R) e k ω := by
  rw [finiteDoobIncrement_sum_eq_terminal_sub_zero]
  congr 1
  · exact (by simpa only [Fin.last] using
      (generatedCount_finiteDoobMean_terminal hG R z hz e ω).symm)
  · rw [finiteDoobMean_zero_of_normalized]
    · rfl
    · exact (generatedCountLaw hG R z hz).probability_sum

/-- Unconditional expectation transfer from the generated sampler to the native
hard-core law, discharged by the proved seed-fiber coupling. -/
theorem generatedExpectation_eq_hardCoreExpectation_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (f : IndepFinset G → ℝ) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      f (generatedIndependentSet hG R ω) =
      ∑ s, (Forest.hardCoreLaw G z hz).probability s * f s :=
  generatedExpectation_eq_hardCoreExpectation hG R z hz
    (exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz) f

/-- Unconditional equality of the generated count mean and native hard-core mean. -/
theorem generatedCount_mean_eq_hardCore_mean_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    (generatedCountLaw hG R z hz).mean =
      (Forest.hardCoreLaw G z hz).mean := by
  change (∑ ω, (generatedCountLaw hG R z hz).probability ω *
    generatedCountReal hG R ω) = _
  exact generatedCount_mean_eq_hardCore_mean hG R z hz
    (exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz)

/-- Unconditional centered-fourth-moment transfer to `Forest.hardCoreLaw`. -/
theorem generatedCenteredFourth_eq_hardCoreCenteredFourth_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      (generatedCountReal hG R ω - (Forest.hardCoreLaw G z hz).mean) ^ 4 =
      ∑ s, (Forest.hardCoreLaw G z hz).probability s *
        (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 4 :=
  generatedCenteredFourth_eq_hardCoreCenteredFourth hG R z hz
    (exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz)

/-- Unconditional finite-law Doob representation centered at the actual native
hard-core mean.  This is the exact telescoping equation behind (A.12), prior to
the parent-first identification of each increment with the closed form (A.11). -/
theorem actualHardCore_centeredCount_eq_sum_finiteDoobIncrement
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    generatedCountReal hG R ω - (Forest.hardCoreLaw G z hz).mean =
      ∑ k : Fin (Fintype.card V),
        finiteDoobIncrement
          (fun ω => (generatedCountLaw hG R z hz).probability ω)
          (generatedCountReal hG R) e k ω := by
  rw [← generatedCount_mean_eq_hardCore_mean_of_fiberMass hG R z hz]
  exact generatedCountReal_sub_mean_eq_sum_finiteDoobIncrement hG R z hz e ω

/-! ## Actual deterministic displacement bounds (A.15) -/

/-- Actual occupied-minus-vacant displacement at arbitrary global activity `z`. -/
noncomputable def rootedDisplacementAt (R : ComponentRooting G) (z : ℝ)
    (hz : 0 < z) (u : V) : ℝ :=
  R.conditionalMeanDifferenceAt (G := G) z hz u

/-- Exact displacement recurrence at the unchanged activity, equation (A.9). -/
theorem rootedDisplacementAt_eq_one_sub_sum
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedDisplacementAt R z hz u =
      1 - ∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v := by
  simpa [rootedDisplacementAt, rootedOccupationProbabilityAt, rootedAAt, rootedPAt,
    ComponentRooting.occupationProbabilityAt] using
    (R.conditionalMeanDifferenceAt_eq_one_sub_sum (G := G) hG z hz u)

/-- The local occupation probability is bounded by activity times the product
of the child vacancy probabilities. -/
theorem rootedOccupationProbabilityAt_le_z_mul_prod_child_vacancy
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u ≤
      z * ∏ v ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z v := by
  have hA0 : 0 ≤ rootedAAt R z u := (rootedAAt_pos R z hz u).le
  have hQpos : 0 < rootedQAt R z u := rootedQAt_pos R z hz u
  have hQP : rootedQAt R z u ≤ rootedPAt R z u := by
    rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
    exact le_add_of_nonneg_right hA0
  calc
    rootedOccupationProbabilityAt R z u = rootedAAt R z u / rootedPAt R z u := rfl
    _ ≤ rootedAAt R z u / rootedQAt R z u :=
      div_le_div_of_nonneg_left hA0 hQpos hQP
    _ = z * ∏ v ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z v := by
      rw [rootedAAt_eq_z_mul_prod_rootedQAt hG,
        rootedQAt_eq_prod_rootedPAt hG]
      rw [show (z * ∏ v ∈ R.children (G := G) u, rootedQAt R z v) /
          (∏ v ∈ R.children (G := G) u, rootedPAt R z v) =
          z * ((∏ v ∈ R.children (G := G) u, rootedQAt R z v) /
            (∏ v ∈ R.children (G := G) u, rootedPAt R z v)) by ring]
      rw [← Finset.prod_div_distrib]
      rfl

theorem rootedOccupationProbabilityAt_le_ceiling_mul_exp_neg_child_sum
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedOccupationProbabilityAt R z u ≤
      Z * Real.exp (-(∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v)) := by
  have hprod :
      (∏ v ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z v) ≤
        ∏ v ∈ R.children (G := G) u,
          Real.exp (-rootedOccupationProbabilityAt R z v) := by
    apply Finset.prod_le_prod
    · intro v hv
      exact (div_pos (rootedQAt_pos R z hz v) (by
        rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
        exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
    · intro v hv
      rw [show rootedVacancyProbabilityAt R z v =
        1 - rootedOccupationProbabilityAt R z v by
          linarith [rootedOccupationProbabilityAt_add_vacancy R z hz v]]
      exact Real.one_sub_le_exp_neg _
  have hprodexp :
      (∏ v ∈ R.children (G := G) u,
          Real.exp (-rootedOccupationProbabilityAt R z v)) =
        Real.exp (-(∑ v ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z v)) := by
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_neg_distrib]
  rw [hprodexp] at hprod
  calc
    rootedOccupationProbabilityAt R z u ≤
        z * ∏ v ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z v :=
      rootedOccupationProbabilityAt_le_z_mul_prod_child_vacancy hG R z hz u
    _ ≤ z * Real.exp (-(∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v)) :=
      mul_le_mul_of_nonneg_left hprod hz.le
    _ ≤ Z * Real.exp (-(∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v)) :=
      mul_le_mul_of_nonneg_right hzZ (Real.exp_pos _).le

/-- Uniform actual occupation cap `b_v ≤ Z/(1+Z)`. -/
theorem rootedOccupationProbabilityAt_le_ceiling_ratio
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedOccupationProbabilityAt R z u ≤ Z / (1 + Z) := by
  have hprod : (∏ v ∈ R.children (G := G) u, rootedQAt R z v) ≤
      ∏ v ∈ R.children (G := G) u, rootedPAt R z v := by
    apply Finset.prod_le_prod
    · intro v hv
      exact (rootedQAt_pos R z hz v).le
    · intro v hv
      rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
      exact le_add_of_nonneg_right (rootedAAt_pos R z hz v).le
  have hAQ : rootedAAt R z u ≤ z * rootedQAt R z u := by
    rw [rootedAAt_eq_z_mul_prod_rootedQAt hG,
      rootedQAt_eq_prod_rootedPAt hG]
    exact mul_le_mul_of_nonneg_left hprod hz.le
  have hPpos : 0 < rootedPAt R z u := by
    rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
    exact add_pos (rootedQAt_pos R z hz u) (rootedAAt_pos R z hz u)
  have hlocal : rootedOccupationProbabilityAt R z u ≤ z / (1 + z) := by
    rw [rootedOccupationProbabilityAt]
    apply (div_le_div_iff₀ hPpos (by linarith)).2
    rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
    nlinarith
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  calc
    rootedOccupationProbabilityAt R z u ≤ z / (1 + z) := hlocal
    _ ≤ Z / (1 + Z) := by
      apply (div_le_div_iff₀ (by linarith) (by linarith)).2
      nlinarith

/-- Uniform lower bound on actual local vacancy, `q_v ≥ η=(1+Z)⁻¹`. -/
theorem one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    1 / (1 + Z) ≤ rootedVacancyProbabilityAt R z u := by
  have hb := rootedOccupationProbabilityAt_le_ceiling_ratio hG R z Z hz hzZ u
  have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hid : 1 - Z / (1 + Z) = 1 / (1 + Z) := by
    field_simp
    ring
  rw [← hid]
  linarith

/-- Actual rooted Bernoulli energy `e_v=b_v q_v d_v²`. -/
noncomputable def rootedEnergyAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u *
    rootedDisplacementAt R z hz u ^ 2

/-- Second inequality of (A.15): the child `b d²` sum is controlled by
`η⁻¹` times the child energy sum, here `η⁻¹=1+Z`. -/
theorem child_occupation_mul_displacement_sq_sum_le_one_add_ceiling_mul_energy_sum
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    (∑ v ∈ R.children (G := G) u,
      rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v ^ 2) ≤
      (1 + Z) * ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  have hq := one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
    hG R z Z hz hzZ v
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz v).le
  have hd0 : 0 ≤ rootedDisplacementAt R z hz v ^ 2 := sq_nonneg _
  unfold rootedEnergyAt
  have hbd0 : 0 ≤ rootedOccupationProbabilityAt R z v *
      rootedDisplacementAt R z hz v ^ 2 := mul_nonneg hb0 hd0
  have hmul := mul_le_mul_of_nonneg_left hq hbd0
  have hone : 0 < 1 + Z := by linarith
  calc
    rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v ^ 2 =
        (1 + Z) * ((rootedOccupationProbabilityAt R z v *
          rootedDisplacementAt R z hz v ^ 2) * (1 / (1 + Z))) := by
      field_simp
    _ ≤ (1 + Z) * ((rootedOccupationProbabilityAt R z v *
          rootedDisplacementAt R z hz v ^ 2) * rootedVacancyProbabilityAt R z v) :=
      mul_le_mul_of_nonneg_left hmul hone.le
    _ = (1 + Z) * (rootedOccupationProbabilityAt R z v *
          rootedVacancyProbabilityAt R z v * rootedDisplacementAt R z hz v ^ 2) := by ring

/-- Third inequality of (A.15), the weighted child Cauchy--Schwarz bound
`r_v² ≤ s_v t_v`. -/
theorem child_occupation_displacement_sum_sq_le
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    (∑ v ∈ R.children (G := G) u,
      rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v) ^ 2 ≤
      (∑ v ∈ R.children (G := G) u, rootedOccupationProbabilityAt R z v) *
      ∑ v ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro v hv
    exact (rootedOccupationProbabilityAt_pos R z hz v).le
  · intro v hv
    exact mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le (sq_nonneg _)
  · intro v hv
    ring



/-! ## Coarse actual deterministic fourth-power bound (A.16) -/


/-- A coarse calculus-free version of `sup s² exp(-s) ≤ 4`, sufficient for
finite fourth-moment bookkeeping. -/
private theorem sq_mul_exp_neg_le_four {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * Real.exp (-s) ≤ 4 := by
  have hhalf : 0 ≤ 1 + s / 2 := by linarith
  have hsq : (1 + s / 2) ^ 2 ≤ Real.exp (s / 2) ^ 2 := by
    exact (sq_le_sq₀ hhalf (Real.exp_nonneg _)).2 (by
      simpa [add_comm] using (Real.add_one_le_exp (s / 2)))
  have hexp : (1 + s / 2) ^ 2 ≤ Real.exp s := by
    calc
      (1 + s / 2) ^ 2 ≤ Real.exp (s / 2) ^ 2 := hsq
      _ = Real.exp s := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
  have hmain : s ^ 2 ≤ 4 * Real.exp s := by
    nlinarith [hexp, sq_nonneg s]
  rw [Real.exp_neg]
  apply (div_le_iff₀ (Real.exp_pos s)).2
  nlinarith

/-- The explicit finite coefficient used in the coarse A.16 estimate. -/
noncomputable def actualFourthChildConstant (Z : ℝ) : ℝ :=
  64 * Z * (1 + Z) ^ 2

/-- A.16, with the same global activity `z`: a large displacement at `u` is
controlled by the square of the child energy sum.  The constant is deliberately
coarse (`64 Z (1+Z)^2`) so its proof only uses the elementary exponential bound
above. -/
theorem rootedFourthEnergyAt_le_of_two_lt_abs_displacement
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V)
    (hlarge : 2 < |rootedDisplacementAt R z hz u|) :
    rootedOccupationProbabilityAt R z u *
      rootedVacancyProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 4 ≤
      actualFourthChildConstant Z *
        (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ^ 2 := by
  let s : ℝ := ∑ v ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z v
  let r : ℝ := ∑ v ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v
  let t : ℝ := ∑ v ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v ^ 2
  let E : ℝ := ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v
  have hs : 0 ≤ s := by
    dsimp [s]
    apply Finset.sum_nonneg
    intro v hv
    exact (rootedOccupationProbabilityAt_pos R z hz v).le
  have hr2 : r ^ 2 ≤ s * t := by
    dsimp [r, s, t]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro v hv
      exact (rootedOccupationProbabilityAt_pos R z hz v).le
    · intro v hv
      exact mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le (sq_nonneg _)
    · intro v hv
      ring
  have hrec : rootedDisplacementAt R z hz u = 1 - r := by
    exact rootedDisplacementAt_eq_one_sub_sum hG R z hz u
  have habs : |rootedDisplacementAt R z hz u| ≤ 2 * |r| := by
    have htri : |rootedDisplacementAt R z hz u| ≤ 1 + |r| := by
      rw [hrec]
      calc
        |(1 : ℝ) - r| = |(1 : ℝ) + (-r)| := by ring
        _ ≤ |(1 : ℝ)| + |-r| := abs_add_le _ _
        _ = 1 + |r| := by simp
    have hrlarge : 1 < |r| := by
      by_contra hn
      have hrle : |r| ≤ 1 := le_of_not_gt hn
      linarith
    linarith
  have hfour : rootedDisplacementAt R z hz u ^ 4 ≤ 16 * r ^ 4 := by
    have hsq : |rootedDisplacementAt R z hz u| ^ 2 ≤ (2 * |r|) ^ 2 := by
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) (abs_nonneg _))).2 habs
    have hsq' : (|rootedDisplacementAt R z hz u| ^ 2) ^ 2 ≤
        ((2 * |r|) ^ 2) ^ 2 := by
      exact (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).2 hsq
    calc
      rootedDisplacementAt R z hz u ^ 4 =
          (rootedDisplacementAt R z hz u ^ 2) ^ 2 := by ring
      _ = (|rootedDisplacementAt R z hz u| ^ 2) ^ 2 := by rw [sq_abs]
      _ ≤ ((2 * |r|) ^ 2) ^ 2 := hsq'
      _ = 16 * r ^ 4 := by
        calc
          ((2 * |r|) ^ 2) ^ 2 = 16 * |r| ^ 4 := by ring
          _ = 16 * r ^ 4 := by
            congr 1
            calc
              |r| ^ 4 = (|r| ^ 2) ^ 2 := by ring
              _ = (r ^ 2) ^ 2 := by rw [sq_abs]
              _ = r ^ 4 := by ring
  have hbexp : rootedOccupationProbabilityAt R z u ≤ Z * Real.exp (-s) := by
    simpa [s] using rootedOccupationProbabilityAt_le_ceiling_mul_exp_neg_child_sum
      hG R z Z hz hzZ u
  have hq : rootedVacancyProbabilityAt R z u ≤ 1 := by
    have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u]
  have hrt : r ^ 4 ≤ s ^ 2 * t ^ 2 := by
    nlinarith [hr2, sq_nonneg r, sq_nonneg (s * t)]
  have ht : t ≤ (1 + Z) * E := by
    simpa [t, E] using
      child_occupation_mul_displacement_sq_sum_le_one_add_ceiling_mul_energy_sum
        hG R z Z hz hzZ u
  have hE : 0 ≤ E := by
    dsimp [E, rootedEnergyAt]
    apply Finset.sum_nonneg
    intro v hv
    have hqv : 0 ≤ rootedVacancyProbabilityAt R z v := by
      unfold rootedVacancyProbabilityAt
      exact (div_pos (rootedQAt_pos R z hz v)
        (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
            exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
    exact mul_nonneg
      (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le hqv)
      (sq_nonneg _)
  have hmain : s ^ 2 * Real.exp (-s) * t ^ 2 ≤
      4 * (1 + Z) ^ 2 * E ^ 2 := by
    have htexp : s ^ 2 * Real.exp (-s) ≤ 4 := sq_mul_exp_neg_le_four hs
    have ht0 : 0 ≤ t := by
      dsimp [t]
      apply Finset.sum_nonneg
      intro v hv
      exact mul_nonneg (rootedOccupationProbabilityAt_pos R z hz v).le (sq_nonneg _)
    have htb : t ^ 2 ≤ ((1 + Z) * E) ^ 2 := by
      have hcoef : 0 ≤ 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
      exact (sq_le_sq₀ ht0 (mul_nonneg hcoef hE)).2 ht
    have hmul : s ^ 2 * Real.exp (-s) * t ^ 2 ≤ 4 * t ^ 2 := by
      exact mul_le_mul_of_nonneg_right htexp (sq_nonneg t)
    have hscale : 4 * t ^ 2 ≤ 4 * ((1 + Z) * E) ^ 2 := by
      exact mul_le_mul_of_nonneg_left htb (by norm_num)
    nlinarith
  dsimp [actualFourthChildConstant]
  have hb0 : 0 ≤ rootedOccupationProbabilityAt R z u :=
    (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ rootedVacancyProbabilityAt R z u :=
    (by linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
      rootedOccupationProbabilityAt_le_one R z hz u])
  have hmul : rootedOccupationProbabilityAt R z u *
      rootedVacancyProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 4 ≤
      (Z * Real.exp (-s)) * 1 * (16 * r ^ 4) := by
    have hZ : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
    have hexp0 : 0 ≤ Real.exp (-s) := Real.exp_nonneg _
    have hcoef : 0 ≤ Z * Real.exp (-s) := mul_nonneg hZ hexp0
    gcongr
  calc
    rootedOccupationProbabilityAt R z u * rootedVacancyProbabilityAt R z u *
        rootedDisplacementAt R z hz u ^ 4 ≤
        (Z * Real.exp (-s)) * 1 * (16 * r ^ 4) := hmul
    _ ≤ 16 * Z * (s ^ 2 * Real.exp (-s) * t ^ 2) := by
      have hZ : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
      have hexp0 : 0 ≤ Real.exp (-s) := Real.exp_nonneg _
      nlinarith [hfour, hrt]
    _ ≤ 64 * Z * (1 + Z) ^ 2 * E ^ 2 := by
      have hZ : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
      have hscaled := mul_le_mul_of_nonneg_left hmain (mul_nonneg (show 0 ≤ (4 : ℝ) by norm_num) hZ)
      nlinarith


/-! ## Finite algebraic martingale fourth-moment ingredients -/

/-- A finite algebraic fourth-moment step: after a centered increment, the
fourth power grows by at most quadratic-variation and fourth-jump terms. -/
theorem weighted_fourth_step
    (w d : V → ℝ) (x W : ℝ)
    (hw : ∀ a, 0 ≤ w a)
    (hW : ∑ a, w a = W)
    (hcenter : ∑ a, w a * d a = 0) :
    ∑ a, w a * (x + d a) ^ 4 ≤
      W * x ^ 4 + 8 * x ^ 2 * (∑ a, w a * d a ^ 2) +
        3 * (∑ a, w a * d a ^ 4) := by
  have hcross (a : V) :
      4 * x * d a ^ 3 ≤ 2 * x ^ 2 * d a ^ 2 + 2 * d a ^ 4 := by
    nlinarith [sq_nonneg (x * d a - d a ^ 2)]
  have hpoint (a : V) :
      w a * (x + d a) ^ 4 =
        w a * x ^ 4 + 4 * x ^ 3 * (w a * d a) +
          w a * (6 * x ^ 2 * d a ^ 2 + 4 * x * d a ^ 3 + d a ^ 4) := by
    ring
  calc
    ∑ a, w a * (x + d a) ^ 4 =
        ∑ a, (w a * x ^ 4 + 4 * x ^ 3 * (w a * d a) +
          w a * (6 * x ^ 2 * d a ^ 2 + 4 * x * d a ^ 3 + d a ^ 4)) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hpoint a
    _ = (∑ a, w a * x ^ 4) + (∑ a, 4 * x ^ 3 * (w a * d a)) +
          ∑ a, w a * (6 * x ^ 2 * d a ^ 2 + 4 * x * d a ^ 3 + d a ^ 4) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = W * x ^ 4 + 4 * x ^ 3 * (∑ a, w a * d a) +
          ∑ a, w a * (6 * x ^ 2 * d a ^ 2 + 4 * x * d a ^ 3 + d a ^ 4) := by
      rw [show (∑ a, w a * x ^ 4) = (∑ a, w a) * x ^ 4 by
        rw [Finset.sum_mul]]
      rw [show (∑ a, 4 * x ^ 3 * (w a * d a)) =
          4 * x ^ 3 * (∑ a, w a * d a) by rw [Finset.mul_sum]]
      rw [hW]
    _ = W * x ^ 4 +
          ∑ a, w a * (6 * x ^ 2 * d a ^ 2 + 4 * x * d a ^ 3 + d a ^ 4) := by
      rw [hcenter]
      ring
    _ ≤ W * x ^ 4 +
          ∑ a, w a * (8 * x ^ 2 * d a ^ 2 + 3 * d a ^ 4) := by
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left
      · nlinarith [hcross a]
      · exact hw a
    _ = W * x ^ 4 + 8 * x ^ 2 * (∑ a, w a * d a ^ 2) +
          3 * (∑ a, w a * d a ^ 4) := by
      rw [show (∑ a, w a * (8 * x ^ 2 * d a ^ 2 + 3 * d a ^ 4)) =
          ∑ a, (8 * x ^ 2 * (w a * d a ^ 2) + 3 * (w a * d a ^ 4)) by
        apply Finset.sum_congr rfl
        intro a ha
        ring]
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      ring

/-- Bernoulli one-step conditional fourth moment. -/
theorem bernoulli_centered_fourth_le_variance
    (b d : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    b * (d * (1 - b)) ^ 4 + (1 - b) * (d * (0 - b)) ^ 4 ≤
      b * (1 - b) * d ^ 4 := by
  have hq : 0 ≤ 1 - b := by linarith
  have hfac : b * (1 - b) * d ^ 4 -
      (b * (d * (1 - b)) ^ 4 + (1 - b) * (d * (0 - b)) ^ 4) =
      b * (1 - b) * d ^ 4 * (3 * b * (1 - b)) := by ring
  rw [← sub_nonneg]
  rw [hfac]
  positivity



/-- A concrete enumeration property: every edge is revealed from parent to child. -/
def ParentBeforeChild (R : ComponentRooting G)
    (e : Fin (Fintype.card V) ≃ V) : Prop :=
  ∀ {i j : Fin (Fintype.card V)}, R.IsChild (G := G) (e i) (e j) → i < j

/-- Number of vertices of depth strictly below `v`; this is an explicit rank. -/
noncomputable def depthRank (R : ComponentRooting G) (v : V) : ℕ :=
  (Finset.univ.filter (fun u : V => R.depth (G := G) u < R.depth (G := G) v)).card

/-- Strictly smaller depth gives strictly smaller depth rank. -/
theorem depthRank_lt_of_depth_lt (R : ComponentRooting G) {u v : V}
    (hdepth : R.depth (G := G) u < R.depth (G := G) v) :
    depthRank R u < depthRank R v := by
  classical
  unfold depthRank
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans hdepth
  · intro heq
    have hu : u ∈ Finset.univ.filter
        (fun x : V => R.depth (G := G) x < R.depth (G := G) v) := by
      simp [hdepth]
    rw [← heq] at hu
    simp at hu

/-- Tie-break depths by an arbitrary finite index. -/
noncomputable def depthCode (R : ComponentRooting G) (v : V) : ℕ :=
  R.depth (G := G) v * (Fintype.card V + 1) + (Fintype.equivFin V v).1

noncomputable def depthCodeOrder (R : ComponentRooting G) : LinearOrder V :=
  LinearOrder.lift' (depthCode R) (by
    intro a b h
    have hmod := congrArg (fun n => n % (Fintype.card V + 1)) h
    have ha : (depthCode R a) % (Fintype.card V + 1) = (Fintype.equivFin V a).1 := by
      unfold depthCode
      rw [Nat.add_mod, Nat.mul_mod]
      simp
    have hb : (depthCode R b) % (Fintype.card V + 1) = (Fintype.equivFin V b).1 := by
      unfold depthCode
      rw [Nat.add_mod, Nat.mul_mod]
      simp
    have hmod' : depthCode R a % (Fintype.card V + 1) =
        depthCode R b % (Fintype.card V + 1) := by simpa using hmod
    have hv : (Fintype.equivFin V a).1 = (Fintype.equivFin V b).1 := by
      rw [← ha, ← hb]
      exact hmod'
    apply (Fintype.equivFin V).injective
    apply Fin.ext
    exact hv)

noncomputable def parentFirstEquiv (R : ComponentRooting G) :
    Fin (Fintype.card V) ≃ V := by
  letI : LinearOrder V := depthCodeOrder R
  exact (Fintype.orderIsoFinOfCardEq V rfl).toEquiv

/-- The canonical enumeration is strictly ordered by depth. -/
theorem depth_lt_of_parentFirstEquiv_index_lt (R : ComponentRooting G)
    {i j : Fin (Fintype.card V)}
    (hdepth : R.depth (G := G) (parentFirstEquiv R i) <
      R.depth (G := G) (parentFirstEquiv R j)) : i < j := by
  letI : LinearOrder V := depthCodeOrder R
  change R.depth (G := G) ((Fintype.orderIsoFinOfCardEq V rfl) i) <
      R.depth (G := G) ((Fintype.orderIsoFinOfCardEq V rfl) j) at hdepth
  let o : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  have hcode : depthCode R (o i) < depthCode R (o j) := by
    unfold depthCode
    have hi : (Fintype.equivFin V (o i)).1 < Fintype.card V :=
      (Fintype.equivFin V (o i)).2
    have hj : (Fintype.equivFin V (o j)).1 < Fintype.card V :=
      (Fintype.equivFin V (o j)).2
    have hsucc : R.depth (G := G) (o i) + 1 ≤ R.depth (G := G) (o j) := hdepth
    calc
      R.depth (G := G) (o i) * (Fintype.card V + 1) +
          (Fintype.equivFin V (o i)).1 <
          R.depth (G := G) (o i) * (Fintype.card V + 1) +
            (Fintype.card V + 1) := by omega
      _ = (R.depth (G := G) (o i) + 1) * (Fintype.card V + 1) := by ring
      _ ≤ R.depth (G := G) (o j) * (Fintype.card V + 1) :=
        Nat.mul_le_mul_right _ hsucc
      _ ≤ R.depth (G := G) (o j) * (Fintype.card V + 1) +
          (Fintype.equivFin V (o j)).1 := Nat.le_add_right _ _
  exact (o.lt_iff_lt).mp hcode

/-- The concrete depth-code enumeration reveals every parent before its child. -/
theorem parentFirstEquiv_parentBeforeChild (R : ComponentRooting G) :
    ParentBeforeChild R (parentFirstEquiv R) := by
  intro i j hchild
  letI : LinearOrder V := depthCodeOrder R
  change R.IsChild (G := G) ((Fintype.orderIsoFinOfCardEq V rfl) i)
      ((Fintype.orderIsoFinOfCardEq V rfl) j) at hchild
  let o : Fin (Fintype.card V) ≃o V := Fintype.orderIsoFinOfCardEq V rfl
  have hdepth : R.depth (G := G) (o j) = R.depth (G := G) (o i) + 1 :=
    R.depth_child (G := G) hchild
  have hcode : depthCode R (o i) < depthCode R (o j) := by
    unfold depthCode
    rw [hdepth]
    have hi : (Fintype.equivFin V (o i)).1 < Fintype.card V :=
      (Fintype.equivFin V (o i)).2
    have hj : (Fintype.equivFin V (o j)).1 < Fintype.card V :=
      (Fintype.equivFin V (o j)).2
    simp only [Nat.add_mul]
    omega
  have hord : o i < o j := hcode
  exact (o.lt_iff_lt).mp hord

/-- Every proper descendant of the currently exposed vertex has a strictly
future index in the canonical parent-first enumeration. -/
theorem parentFirstEquiv_properDescendant_future
    (R : ComponentRooting G) (k : Fin (Fintype.card V)) (x : V)
    (hxmem : x ∈ R.descendants (G := G) (parentFirstEquiv R k))
    (hxne : x ≠ parentFirstEquiv R k) :
    k.1 < ((parentFirstEquiv R).symm x).1 := by
  have hdesc : R.IsDescendant (G := G) (parentFirstEquiv R k) x :=
    (R.mem_descendants (G := G) _ _).mp hxmem
  have hdepth : R.depth (G := G) (parentFirstEquiv R k) < R.depth (G := G) x :=
    ComponentRooting.depth_lt_of_isDescendant_of_ne (G := G) R hdesc hxne.symm
  apply depth_lt_of_parentFirstEquiv_index_lt R
  simpa using hdepth

/-- Equivalent stage-bound form used by future-coordinate product factorization. -/
theorem parentFirstEquiv_properDescendant_not_exposed
    (R : ComponentRooting G) (k : Fin (Fintype.card V)) (x : V)
    (hxmem : x ∈ R.descendants (G := G) (parentFirstEquiv R k))
    (hxne : x ≠ parentFirstEquiv R k) :
    k.succ.1 ≤ ((parentFirstEquiv R).symm x).1 := by
  exact parentFirstEquiv_properDescendant_future R k x hxmem hxne

/-- Every finite rooted forest, including the empty one, admits a
parent-before-child enumeration. -/
theorem exists_parentBeforeChild (R : ComponentRooting G) :
    ∃ e : Fin (Fintype.card V) ≃ V, ParentBeforeChild R e :=
  ⟨parentFirstEquiv R, parentFirstEquiv_parentBeforeChild R⟩

/-- The generated availability indicator immediately before a vertex is processed. -/
noncomputable def generatedAvailable (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (v : V) : Bool :=
  decide (∀ u, R.IsChild (G := G) u v → generatedOccupation R ω u = false)

/-- Generated occupation factors as availability times the local seed. -/
theorem generatedOccupation_eq_seed_and_available
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (v : V) :
    generatedOccupation R ω v = (ω v && generatedAvailable R ω v) := by
  unfold generatedOccupation generatedAvailable
  cases hdepth : R.depth (G := G) v with
  | zero =>
      simp only [occupationAtDepth]
      have hroot : ∀ u, ¬ R.IsChild (G := G) u v := by
        intro u huv
        have hd := R.depth_child (G := G) huv
        omega
      have hprop : (∀ u, R.IsChild (G := G) u v → generatedOccupation R ω u = false) := by
        intro u huv
        exact (hroot u huv).elim
      rw [show decide (∀ u, R.IsChild (G := G) u v →
          generatedOccupation R ω u = false) = true by
            exact decide_eq_true hprop]
      simp
  | succ n =>
      simp only [occupationAtDepth]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro h u huv
        unfold generatedOccupation
        have hd := R.depth_child (G := G) huv
        rw [hdepth] at hd
        have hu : R.depth (G := G) u = n := by omega
        rw [hu]
        exact h u huv
      · intro h u huv
        have hd := R.depth_child (G := G) huv
        rw [hdepth] at hd
        have hu : R.depth (G := G) u = n := by omega
        have := h u huv
        unfold generatedOccupation at this
        rwa [hu] at this

/-- Agreement of all seeds through depth `n` implies agreement of generated
occupation for every vertex through depth `n`. -/
theorem generatedOccupation_eq_of_seed_eq_of_depth_le
    (R : ComponentRooting G) {ω ω' : BernoulliAssignment V} (n : ℕ)
    (hseed : ∀ x, R.depth (G := G) x ≤ n → ω x = ω' x) :
    ∀ x, R.depth (G := G) x ≤ n →
      generatedOccupation R ω x = generatedOccupation R ω' x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hx
      rw [generatedOccupation_eq_seed_and_available,
        generatedOccupation_eq_seed_and_available, hseed x hx]
      congr 1
      unfold generatedAvailable
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor <;> intro hall u huv
      · have hdu := R.depth_child (G := G) huv
        have hlt : R.depth (G := G) u < n := by omega
        rw [← ih (R.depth (G := G) u) hlt
          (fun y hy => hseed y (by omega)) u (le_refl _)]
        exact hall u huv
      · have hdu := R.depth_child (G := G) huv
        have hlt : R.depth (G := G) u < n := by omega
        rw [ih (R.depth (G := G) u) hlt
          (fun y hy => hseed y (by omega)) u (le_refl _)]
        exact hall u huv

/-- Agreement of all seeds at earlier depths fixes current availability. -/
theorem generatedAvailable_eq_of_seed_eq_depth_lt
    (R : ComponentRooting G) {ω ω' : BernoulliAssignment V} (v : V)
    (hseed : ∀ x, R.depth (G := G) x < R.depth (G := G) v → ω x = ω' x) :
    generatedAvailable R ω v = generatedAvailable R ω' v := by
  unfold generatedAvailable
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor <;> intro hall u huv
  · have hdu := R.depth_child (G := G) huv
    rw [← generatedOccupation_eq_of_seed_eq_of_depth_le R
      (R.depth (G := G) u)
      (fun y hy => hseed y (by omega)) u (le_refl _)]
    exact hall u huv
  · have hdu := R.depth_child (G := G) huv
    rw [generatedOccupation_eq_of_seed_eq_of_depth_le R
      (R.depth (G := G) u)
      (fun y hy => hseed y (by omega)) u (le_refl _)]
    exact hall u huv

/-- In a parent-first order, a prefix fixes the availability of the next vertex. -/
theorem generatedAvailable_eq_of_samePrefix_parentFirst
    (R : ComponentRooting G) (k : Fin (Fintype.card V))
    (ω ω' : BernoulliAssignment V)
    (hpre : samePrefix (parentFirstEquiv R) k.castSucc ω ω') :
    generatedAvailable R ω (parentFirstEquiv R k) =
      generatedAvailable R ω' (parentFirstEquiv R k) := by
  apply generatedAvailable_eq_of_seed_eq_depth_lt
  intro x hx
  let i : Fin (Fintype.card V) := (parentFirstEquiv R).symm x
  have hdepth : R.depth (G := G) (parentFirstEquiv R i) <
      R.depth (G := G) (parentFirstEquiv R k) := by simpa [i] using hx
  have hik : i < k := depth_lt_of_parentFirstEquiv_index_lt R hdepth
  have hs := hpre ⟨i.1, by simpa using hik⟩
  simpa [i] using hs
/-- A prefix atom splits into the two next-coordinate atoms. -/
theorem samePrefix_castSucc_iff_false_or_true
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω ω' : BernoulliAssignment V) :
    samePrefix e k.castSucc ω ω' ↔
      samePrefix e k.succ (Function.update ω (e k) false) ω' ∨
      samePrefix e k.succ (Function.update ω (e k) true) ω' := by
  constructor
  · intro h
    cases hb : ω' (e k)
    · left
      intro i
      have hi : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
      rcases lt_or_eq_of_le hi with hi | hi
      · let j : Fin k.1 := ⟨i.1, hi⟩
        have hs := h j
        have hne : e ⟨i.1, by omega⟩ ≠ e k := by
          intro heq
          exact hi.ne (congrArg Fin.val (e.injective heq))
        simpa [Function.update, hne, j] using hs
      · have heq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
        rw [heq]
        simp [hb]
    · right
      intro i
      have hi : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
      rcases lt_or_eq_of_le hi with hi | hi
      · let j : Fin k.1 := ⟨i.1, hi⟩
        have hs := h j
        have hne : e ⟨i.1, by omega⟩ ≠ e k := by
          intro heq
          exact hi.ne (congrArg Fin.val (e.injective heq))
        simpa [Function.update, hne, j] using hs
      · have heq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
        rw [heq]
        simp [hb]
  · rintro (h | h)
    · exact samePrefix_castSucc_of_samePrefix_succ_update e k ω ω' false h
    · exact samePrefix_castSucc_of_samePrefix_succ_update e k ω ω' true h

/-- The two next-coordinate prefix atoms are disjoint. -/
theorem not_samePrefix_succ_update_false_and_true
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω ω' : BernoulliAssignment V) :
    ¬ (samePrefix e k.succ (Function.update ω (e k) false) ω' ∧
      samePrefix e k.succ (Function.update ω (e k) true) ω') := by
  rintro ⟨hf, ht⟩
  have hf' := hf ⟨k, by simp⟩
  have ht' := ht ⟨k, by simp⟩
  have hf'' : false = ω' (e k) := by simpa using hf'
  have ht'' : true = ω' (e k) := by simpa using ht'
  exact Bool.noConfusion (hf''.trans ht''.symm)

/-- Prefix mass splits exactly into the two next-coordinate masses. -/
theorem prefixMass_split
    (p : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    prefixMass p e k.castSucc ω =
      prefixMass p e k.succ (Function.update ω (e k) false) +
      prefixMass p e k.succ (Function.update ω (e k) true) := by
  unfold prefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω' hω'
  rw [samePrefix_castSucc_iff_false_or_true]
  by_cases hf : samePrefix e k.succ (Function.update ω (e k) false) ω'
  · have hnt : ¬ samePrefix e k.succ (Function.update ω (e k) true) ω' := by
      intro ht
      exact not_samePrefix_succ_update_false_and_true e k ω ω' ⟨hf, ht⟩
    simp [hf, hnt]
  · by_cases ht : samePrefix e k.succ (Function.update ω (e k) true) ω'
    · simp [hf, ht]
    · simp [hf, ht]

/-- Prefix weighted statistics split exactly into the two next-coordinate atoms. -/
theorem prefixWeighted_split
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    prefixWeighted p X e k.castSucc ω =
      prefixWeighted p X e k.succ (Function.update ω (e k) false) +
      prefixWeighted p X e k.succ (Function.update ω (e k) true) := by
  unfold prefixWeighted
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω' hω'
  rw [samePrefix_castSucc_iff_false_or_true]
  by_cases hf : samePrefix e k.succ (Function.update ω (e k) false) ω'
  · have hnt : ¬ samePrefix e k.succ (Function.update ω (e k) true) ω' := by
      intro ht
      exact not_samePrefix_succ_update_false_and_true e k ω ω' ⟨hf, ht⟩
    simp [hf, hnt]
  · by_cases ht : samePrefix e k.succ (Function.update ω (e k) true) ω'
    · simp [hf, ht]
    · simp [hf, ht]
/-- Conditional finite means depend only on the exposed prefix. -/
theorem finiteDoobMean_eq_of_samePrefix
    (p : BernoulliAssignment V → ℝ) (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) {k : Fin (Fintype.card V + 1)}
    (ω ω' : BernoulliAssignment V) (h : samePrefix e k ω ω') :
    finiteDoobMean p X e k ω = finiteDoobMean p X e k ω' := by
  have hiff : ∀ η, samePrefix e k ω η ↔ samePrefix e k ω' η := by
    intro η
    constructor <;> intro hη i
    · exact (h i).symm.trans (hη i)
    · exact (h i).trans (hη i)
  have hm : prefixMass p e k ω = prefixMass p e k ω' := by
    unfold prefixMass
    apply Finset.sum_congr rfl
    intro η hη
    rw [hiff η]
  have hw : prefixWeighted p X e k ω = prefixWeighted p X e k ω' := by
    unfold prefixWeighted
    apply Finset.sum_congr rfl
    intro η hη
    rw [hiff η]
  unfold finiteDoobMean
  rw [hm, hw]

/-- The next revealed Doob value is the branch selected by the actual seed. -/
theorem finiteDoobMean_succ_eq_branchValue_seed
    (p : BernoulliAssignment V → ℝ)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p X e k.succ ω =
      finiteDoobBranchValue p X e k ω (ω (e k)) := by
  unfold finiteDoobBranchValue
  apply finiteDoobMean_eq_of_samePrefix
  intro i
  have hi : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
  rcases lt_or_eq_of_le hi with hi | hi
  · have hne : e ⟨i.1, by omega⟩ ≠ e k := by
      intro heq
      exact hi.ne (congrArg Fin.val (e.injective heq))
    simp [Function.update, hne]
  · have heq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
    rw [heq]
    simp
/-- Abstract branch probability, expressed as the next-true atom mass divided by
its parent atom mass. -/
noncomputable def finiteDoobBranchProbability
    (p : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) : ℝ :=
  prefixMass p e k.succ (Function.update ω (e k) true) /
    prefixMass p e k.castSucc ω

/-- A positive finite law's parent Doob value is the exact Bernoulli mixture of
its two child-prefix values. -/
theorem finiteDoobMean_eq_branch_mixture
    (p : BernoulliAssignment V → ℝ) (hp : ∀ ω, 0 < p ω)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p X e k.castSucc ω =
      (1 - finiteDoobBranchProbability p e k ω) *
          finiteDoobBranchValue p X e k ω false +
        finiteDoobBranchProbability p e k ω *
          finiteDoobBranchValue p X e k ω true := by
  have hparent : prefixMass p e k.castSucc ω ≠ 0 :=
    (prefixMass_pos p hp e k.castSucc ω).ne'
  have hf : prefixMass p e k.succ (Function.update ω (e k) false) ≠ 0 :=
    (prefixMass_pos p hp e k.succ _).ne'
  have ht : prefixMass p e k.succ (Function.update ω (e k) true) ≠ 0 :=
    (prefixMass_pos p hp e k.succ _).ne'
  rw [finiteDoobMean, dif_neg hparent]
  change prefixWeighted p X e k.castSucc ω / prefixMass p e k.castSucc ω =
      (1 - prefixMass p e k.succ (Function.update ω (e k) true) /
          prefixMass p e k.castSucc ω) *
        finiteDoobMean p X e k.succ (Function.update ω (e k) false) +
      (prefixMass p e k.succ (Function.update ω (e k) true) /
          prefixMass p e k.castSucc ω) *
        finiteDoobMean p X e k.succ (Function.update ω (e k) true)
  rw [finiteDoobMean, dif_neg hf, finiteDoobMean, dif_neg ht]
  rw [prefixMass_split p e k ω, prefixWeighted_split p X e k ω]
  have hsum : prefixMass p e k.succ (Function.update ω (e k) false) +
      prefixMass p e k.succ (Function.update ω (e k) true) ≠ 0 := by
    have hpos := add_pos (prefixMass_pos p hp e k.succ
      (Function.update ω (e k) false))
      (prefixMass_pos p hp e k.succ (Function.update ω (e k) true))
    exact hpos.ne'
  field_simp [hsum]
  ring
 theorem finiteDoobMean_add
    (p : BernoulliAssignment V → ℝ) (f g : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => f η + g η) e m ω =
      finiteDoobMean p f e m ω + finiteDoobMean p g e m ω := by
  by_cases hmass : prefixMass p e m ω = 0
  · rw [finiteDoobMean, dif_pos hmass, finiteDoobMean, dif_pos hmass,
      finiteDoobMean, dif_pos hmass]
    ring
  · rw [finiteDoobMean, dif_neg hmass, finiteDoobMean, dif_neg hmass,
      finiteDoobMean, dif_neg hmass]
    unfold prefixWeighted
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro η hη
    by_cases hs : samePrefix e m ω η <;> simp [hs] <;> ring

 theorem finiteDoobMean_sub
    (p : BernoulliAssignment V → ℝ) (f g : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => f η - g η) e m ω =
      finiteDoobMean p f e m ω - finiteDoobMean p g e m ω := by
  by_cases hmass : prefixMass p e m ω = 0
  · rw [finiteDoobMean, dif_pos hmass, finiteDoobMean, dif_pos hmass,
      finiteDoobMean, dif_pos hmass]
    ring
  · rw [finiteDoobMean, dif_neg hmass, finiteDoobMean, dif_neg hmass,
      finiteDoobMean, dif_neg hmass]
    unfold prefixWeighted
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro η hη
    by_cases hs : samePrefix e m ω η <;> simp [hs] <;> ring

 theorem finiteDoobMean_const_mul
    (p : BernoulliAssignment V → ℝ) (c : ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => c * f η) e m ω =
      c * finiteDoobMean p f e m ω := by
  by_cases hmass : prefixMass p e m ω = 0
  · rw [finiteDoobMean, dif_pos hmass, finiteDoobMean, dif_pos hmass]
    ring
  · rw [finiteDoobMean, dif_neg hmass, finiteDoobMean, dif_neg hmass]
    unfold prefixWeighted
    rw [show (∑ η, if samePrefix e m ω η then p η * (c * f η) else 0) =
      c * ∑ η, if samePrefix e m ω η then p η * f η else 0 by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro η hη
      by_cases hs : samePrefix e m ω η <;> simp [hs] <;> ring]
    field_simp


/-- Under positive Bernoulli parameters, the finite Doob increment is exactly
the selected branch displacement from its Bernoulli mixture mean. -/
theorem finiteDoobIncrement_eq_branch_displacement
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hp1 : ∀ v, p v < 1)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V)
    (hbranch : finiteDoobBranchProbability (bernoulliWeight p) e k ω = p (e k)) :
    finiteDoobIncrement (bernoulliWeight p) X e k ω =
      if ω (e k) then
        (1 - p (e k)) *
          (finiteDoobBranchValue (bernoulliWeight p) X e k ω true -
            finiteDoobBranchValue (bernoulliWeight p) X e k ω false)
      else
        -p (e k) *
          (finiteDoobBranchValue (bernoulliWeight p) X e k ω true -
            finiteDoobBranchValue (bernoulliWeight p) X e k ω false) := by
  unfold finiteDoobIncrement
  change finiteDoobMean (bernoulliWeight p) X e k.succ ω -
      finiteDoobMean (bernoulliWeight p) X e k.castSucc ω = _
  rw [finiteDoobMean_succ_eq_branchValue_seed]
  rw [finiteDoobMean_eq_branch_mixture (bernoulliWeight p) _]
  · rw [hbranch]
    cases hω : ω (e k) <;> simp [hω]
    <;> ring
  · intro η
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [hp v, hp1 v]
/-- Every local sampler parameter is strictly below one at positive activity. -/
theorem rootedOccupationProbabilityAt_lt_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u < 1 := by
  have hvac : 0 < rootedVacancyProbabilityAt R z u := by
    exact div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)
  linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u]

/-- The actual recursive sampler's branch probability is its prescribed local
rooted-subtree occupation parameter. -/
theorem hardCoreSeed_branchProbability
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (hprefix : finiteDoobBranchProbability
        (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
        (parentFirstEquiv R) k ω =
      rootedOccupationProbabilityAt R z (parentFirstEquiv R k)) :
    finiteDoobBranchProbability
        (hardCoreBernoulliSeedLaw R z hz).probability
        (parentFirstEquiv R) k ω =
      rootedOccupationProbabilityAt R z (parentFirstEquiv R k) := by
  simpa [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability] using hprefix

/-- Availability-aware exact finite Doob increment formula for the recursive
sampler, conditional only on the branch-mass identity. The factor `A_k` is kept
explicit; unlike manuscript shorthand this theorem never drops availability. -/
theorem generatedCountDoobIncrement_eq_available_branch
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (hbranch : finiteDoobBranchProbability
        (hardCoreBernoulliSeedLaw R z hz).probability
        (parentFirstEquiv R) k ω =
      rootedOccupationProbabilityAt R z (parentFirstEquiv R k))
    (hdisp :
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω true -
        finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω false =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k)) :
    finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        (if ω (parentFirstEquiv R k) then
          (1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k)) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)
        else
          -rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)) := by
  change finiteDoobIncrement
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
      (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω = _
  have hdisp' :
      finiteDoobBranchValue
          (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω true -
        finiteDoobBranchValue
          (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω false =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) := by
    simpa [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability] using hdisp
  rw [finiteDoobIncrement_eq_branch_displacement
    (fun v => rootedOccupationProbabilityAt R z v)
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz)
    (fun η => generatedCountReal hG R η)
    (parentFirstEquiv R) k ω]
  · rw [hdisp']
    cases ha : generatedAvailable R ω (parentFirstEquiv R k) <;>
      cases hb : ω (parentFirstEquiv R k) <;> simp [ha, hb] <;> ring
  · simpa [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability] using hbranch
/-- One-coordinate factorization of the finite product Bernoulli mass. -/
theorem bernoulliWeight_factor_at
    (p : V → ℝ) (η : BernoulliAssignment V) (v : V) :
    bernoulliWeight p η =
      (if η v then p v else 1 - p v) *
        ∏ x ∈ Finset.univ.erase v, (if η x then p x else 1 - p x) := by
  unfold bernoulliWeight
  rw [← Finset.prod_erase_mul Finset.univ
    (fun x => if η x then p x else 1 - p x) (Finset.mem_univ v)]
  ring

/-- Flipping the current coordinate is a bijection between the true and false
next-prefix atoms, and the paired Bernoulli weights have the exact odds ratio. -/
theorem bernoulli_prefix_pair_mass
    (p : V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    (1 - p (e k)) *
        prefixMass (bernoulliWeight p) e k.succ
          (Function.update ω (e k) true) =
      p (e k) *
        prefixMass (bernoulliWeight p) e k.succ
          (Function.update ω (e k) false) := by
  unfold prefixMass
  calc
    (1 - p (e k)) *
        (∑ η, if samePrefix e k.succ (Function.update ω (e k) true) η then
          bernoulliWeight p η else 0) =
      ∑ η ∈ Finset.univ.filter
          (samePrefix e k.succ (Function.update ω (e k) true)),
        (1 - p (e k)) * bernoulliWeight p η := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro η hη
          by_cases hpre : samePrefix e k.succ
              (Function.update ω (e k) true) η <;> simp [hpre]
    _ = ∑ η ∈ Finset.univ.filter
          (samePrefix e k.succ (Function.update ω (e k) false)),
        p (e k) * bernoulliWeight p η := by
      apply Finset.sum_bij (fun η _ => Function.update η (e k) false)
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
        intro i
        have hle : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
        rcases lt_or_eq_of_le hle with hi | hi
        · have hne : e ⟨i.1, by omega⟩ ≠ e k := by
            intro heq
            exact hi.ne (congrArg Fin.val (e.injective heq))
          simpa [Function.update, hne] using hη i
        · have hieq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
          rw [hieq]
          simp
      · intro η₁ h₁ η₂ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        funext x
        by_cases hx : x = e k
        · subst x
          have ht1 : η₁ (e k) = true := by
            have hs := h₁ ⟨k, by simp⟩
            simpa using hs.symm
          have ht2 : η₂ (e k) = true := by
            have hs := h₂ ⟨k, by simp⟩
            simpa using hs.symm
          rw [ht1, ht2]
        · have hfun := congrFun heq x
          simpa [Function.update, hx] using hfun
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
        refine ⟨Function.update η (e k) true, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro i
          have hle : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
          rcases lt_or_eq_of_le hle with hi | hi
          · have hne : e ⟨i.1, by omega⟩ ≠ e k := by
              intro heq
              exact hi.ne (congrArg Fin.val (e.injective heq))
            simpa [Function.update, hne] using hη i
          · have hieq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
            rw [hieq]
            simp
        · funext x
          by_cases hx : x = e k
          · subst x
            have hf : η (e k) = false := by
              have hs := hη ⟨k, by simp⟩
              simpa using hs.symm
            simp [hf]
          · simp [Function.update, hx]
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
        have hat : η (e k) = true := by
          have hs := hη ⟨k, by simp⟩
          simpa using hs.symm
        rw [bernoulliWeight_factor_at, bernoulliWeight_factor_at]
        change (1 - p (e k)) *
            ((if η (e k) then p (e k) else 1 - p (e k)) *
              ∏ x ∈ Finset.univ.erase (e k), if η x then p x else 1 - p x) =
          p (e k) *
            ((if Function.update η (e k) false (e k) then p (e k) else 1 - p (e k)) *
              ∏ x ∈ Finset.univ.erase (e k),
                if Function.update η (e k) false x then p x else 1 - p x)
        rw [hat]
        simp only [ite_true, Function.update_self]
        have hprod :
            (∏ x ∈ Finset.univ.erase (e k),
              if Function.update η (e k) false x then p x else 1 - p x) =
            ∏ x ∈ Finset.univ.erase (e k), if η x then p x else 1 - p x := by
          apply Finset.prod_congr rfl
          intro x hx
          have hne := (Finset.mem_erase.mp hx).1
          simp [Function.update, hne]
        rw [hprod]
        norm_num
        ring
    _ = p (e k) *
        (∑ η, if samePrefix e k.succ (Function.update ω (e k) false) η then
          bernoulliWeight p η else 0) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro η hη
          by_cases hpre : samePrefix e k.succ
              (Function.update ω (e k) false) η <;> simp [hpre]

/-- The next true atom has exactly `p(e k)` times the parent-prefix mass. -/
theorem prefixMass_bernoulli_true_eq_mul_parent
    (p : V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    prefixMass (bernoulliWeight p) e k.succ
        (Function.update ω (e k) true) =
      p (e k) * prefixMass (bernoulliWeight p) e k.castSucc ω := by
  rw [prefixMass_split]
  have hpair := bernoulli_prefix_pair_mass p e k ω
  ring_nf at hpair ⊢
  linarith

/-- Therefore the abstract branch probability of a positive product Bernoulli
law equals the prescribed coordinate parameter. -/
theorem finiteDoobBranchProbability_bernoulli
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hp1 : ∀ v, p v < 1)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobBranchProbability (bernoulliWeight p) e k ω = p (e k) := by
  unfold finiteDoobBranchProbability
  rw [prefixMass_bernoulli_true_eq_mul_parent]
  have hm : prefixMass (bernoulliWeight p) e k.castSucc ω ≠ 0 := by
    apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [hp v, hp1 v]
  field_simp
/-- The actual recursive sampler's branch probability is its prescribed local
rooted-subtree occupation parameter, with no auxiliary hypothesis. -/
theorem hardCoreSeed_branchProbability_exact
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobBranchProbability
        (hardCoreBernoulliSeedLaw R z hz).probability
        (parentFirstEquiv R) k ω =
      rootedOccupationProbabilityAt R z (parentFirstEquiv R k) := by
  change finiteDoobBranchProbability
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v))
      (parentFirstEquiv R) k ω = _
  exact finiteDoobBranchProbability_bernoulli
    (fun v => rootedOccupationProbabilityAt R z v)
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz)
    (parentFirstEquiv R) k ω

/-- Fully branch-mass-specialized availability-aware increment formula. Only the
mathematical branch-displacement identity remains to identify from subtrees. -/
theorem generatedCountDoobIncrement_eq_available_branch_exact
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (hdisp :
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω true -
        finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
          (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω false =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k)) :
    finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        (if ω (parentFirstEquiv R k) then
          (1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k)) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)
        else
          -rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)) := by
  exact generatedCountDoobIncrement_eq_available_branch hG R z hz k ω
    (hardCoreSeed_branchProbability_exact R z hz k ω) hdisp

/-- A statistic which is constant on a prefix atom has that constant as its
finite conditional mean. -/
theorem finiteDoobValue_eq_of_constant_on_prefix
    (μ : BernoulliAssignment V → ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V)
    (hmass : prefixMass μ e m ω ≠ 0)
    (c : ℝ)
    (hc : ∀ η, samePrefix e m ω η → f η = c) :
    finiteDoobMean μ f e m ω = c := by
  unfold finiteDoobMean prefixWeighted prefixMass
  have hsum :
      (∑ η, if samePrefix e m ω η then μ η * f η else 0) =
        c * ∑ η, if samePrefix e m ω η then μ η else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η hη
    by_cases hpre : samePrefix e m ω η
    · rw [if_pos hpre, if_pos hpre, hc η hpre]
      ring
    · simp [hpre]
  rw [hsum]
  change (if prefixMass μ e m ω = 0 then 0 else
    c * prefixMass μ e m ω / prefixMass μ e m ω) = c
  rw [if_neg hmass]
  field_simp

/-- Parent-first measurability makes generated availability constant on the
next prefix atom. -/
theorem generatedAvailable_constant_on_nextPrefix
    (R : ComponentRooting G) (k : Fin (Fintype.card V))
    (ω η : BernoulliAssignment V)
    (hpre : samePrefix (parentFirstEquiv R) k.succ ω η) :
    generatedAvailable R η (parentFirstEquiv R k) =
      generatedAvailable R ω (parentFirstEquiv R k) := by
  exact (generatedAvailable_eq_of_samePrefix_parentFirst R k ω η (fun j =>
    hpre ⟨j.1, lt_trans j.2 (Nat.lt_succ_self k.1)⟩)).symm

/-- The generated count restricted to the descendant subtree of `u`. -/
noncomputable def generatedSubtreeCountReal (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (u : V) : ℝ :=
  ((R.descendants (G := G) u).filter (fun v => generatedOccupation R ω v)).card

/-- The generated count outside the descendant subtree of `u`. -/
noncomputable def generatedOutsideCountReal (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (u : V) : ℝ :=
  (((Finset.univ : Finset V) \ R.descendants (G := G) u).filter
    (fun v => generatedOccupation R ω v)).card

/-- The generated full count splits into the descendants of `u` and their complement. -/
theorem generatedCountReal_eq_subtree_add_outside
    (hG : G.IsAcyclic) (R : ComponentRooting G) (ω : BernoulliAssignment V) (u : V) :
    generatedCountReal hG R ω =
      generatedSubtreeCountReal R ω u + generatedOutsideCountReal R ω u := by
  unfold generatedCountReal
  change ((generatedFinset R ω).card : ℝ) = _
  unfold generatedSubtreeCountReal generatedOutsideCountReal generatedFinset
  have hpart : ((Finset.univ : Finset V).filter (fun v => generatedOccupation R ω v)) =
      ((R.descendants (G := G) u).filter (fun v => generatedOccupation R ω v)) ∪
      (((Finset.univ : Finset V) \ R.descendants (G := G) u).filter
        (fun v => generatedOccupation R ω v)) := by
    ext v
    by_cases h : v ∈ R.descendants (G := G) u <;> simp [h]
  rw [hpart, Finset.card_union_of_disjoint]
  · norm_cast
  · rw [Finset.disjoint_left]
    intro v hv hv'
    exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hv').1).2
      (Finset.mem_filter.mp hv).1

/-- Changing the seed at `u` cannot influence generated occupation outside the
 descendant subtree rooted at `u`. -/
theorem generatedOccupation_update_eq_of_not_descendant
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (u x : V)
    (hx : x ∉ R.descendants (G := G) u) (b : Bool) :
    generatedOccupation R (Function.update ω u b) x = generatedOccupation R ω x := by
  induction hn : R.depth (G := G) x using Nat.strong_induction_on generalizing x with
  | h n ih =>
    rw [generatedOccupation_eq_seed_and_available,
      generatedOccupation_eq_seed_and_available]
    have hxu : x ≠ u := by
      intro h
      subst x
      exact hx (R.self_mem_descendants (G := G) u)
    simp only [Function.update, hxu]
    congr 1
    unfold generatedAvailable
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor <;> intro hall p hpx
    · have hdpx : R.depth (G := G) p < R.depth (G := G) x := by
        rw [R.depth_child (G := G) hpx]
        omega
      have hpnot : p ∉ R.descendants (G := G) u := by
        intro hp
        exact hx ((R.mem_descendants (G := G) u x).mpr
          (((R.mem_descendants (G := G) u p).mp hp).tail hpx))
      rw [← ih (R.depth (G := G) p) (by omega) p hpnot rfl]
      exact hall p hpx
    · have hdpx : R.depth (G := G) p < R.depth (G := G) x := by
        rw [R.depth_child (G := G) hpx]
        omega
      have hpnot : p ∉ R.descendants (G := G) u := by
        intro hp
        exact hx ((R.mem_descendants (G := G) u x).mpr
          (((R.mem_descendants (G := G) u p).mp hp).tail hpx))
      rw [ih (R.depth (G := G) p) (by omega) p hpnot rfl]
      exact hall p hpx

/-- Hence the outside count is unchanged by forcing the seed at `u`. -/
theorem generatedOutsideCountReal_update
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (u : V) (b : Bool) :
    generatedOutsideCountReal R (Function.update ω u b) u =
      generatedOutsideCountReal R ω u := by
  unfold generatedOutsideCountReal
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x hx
  rw [generatedOccupation_update_eq_of_not_descendant R ω u x
    (Finset.mem_sdiff.mp hx).2 b]

/-- Generated occupation at an already exposed vertex is constant on every
prefix atom extending that vertex. -/
theorem generatedOccupation_constant_on_nextPrefix
    (R : ComponentRooting G) (k : Fin (Fintype.card V))
    (ω η : BernoulliAssignment V)
    (hpre : samePrefix (parentFirstEquiv R) k.succ ω η) :
    generatedOccupation R η (parentFirstEquiv R k) =
      generatedOccupation R ω (parentFirstEquiv R k) := by
  have hseed : η (parentFirstEquiv R k) = ω (parentFirstEquiv R k) := by
    simpa using (hpre ⟨k, by simp⟩).symm
  rw [generatedOccupation_eq_seed_and_available,
    generatedOccupation_eq_seed_and_available,
    hseed,
    generatedAvailable_constant_on_nextPrefix R k ω η hpre]

/-- The generated occupation indicator itself has the expected conditional
mean once the vertex is exposed. -/
theorem finiteDoobValue_generatedOccupation_nextPrefix
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => if generatedOccupation R η (parentFirstEquiv R k) then (1 : ℝ) else 0)
        (parentFirstEquiv R) k.succ ω =
      (if generatedOccupation R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) := by
  apply finiteDoobValue_eq_of_constant_on_prefix
  · apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    rw [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability]
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v
    · simp only [Bool.false_eq_true, if_false]
      have hsumone := rootedOccupationProbabilityAt_add_vacancy R z hz v
      have hvac : 0 < rootedVacancyProbabilityAt R z v :=
        div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)
      linarith
    · simpa using rootedOccupationProbabilityAt_pos R z hz v
  · intro η hpre
    rw [generatedOccupation_constant_on_nextPrefix R k ω η hpre]
/-- Availability at `u` depends only on seeds strictly earlier than `u`; hence
forcing the current seed does not change it. -/
theorem generatedAvailable_update_self
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (u : V) (b : Bool) :
    generatedAvailable R (Function.update ω u b) u = generatedAvailable R ω u := by
  apply generatedAvailable_eq_of_seed_eq_depth_lt
  intro x hx
  have hne : x ≠ u := by
    intro h
    subst x
    omega
  simp [Function.update, hne]

/-- The current generated occupation under a forced seed is exactly availability
times that forced Boolean. -/
theorem generatedOccupation_update_self
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (u : V) (b : Bool) :
    generatedOccupation R (Function.update ω u b) u =
      (b && generatedAvailable R ω u) := by
  rw [generatedOccupation_eq_seed_and_available,
    Function.update_self,
    generatedAvailable_update_self]

/-- The branch difference of the generated occupation indicator at the exposed
vertex is precisely its pre-reveal availability indicator. -/
theorem generatedOccupation_branch_difference_self
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (u : V) :
    (if generatedOccupation R (Function.update ω u true) u then (1 : ℝ) else 0) -
      (if generatedOccupation R (Function.update ω u false) u then (1 : ℝ) else 0) =
    (if generatedAvailable R ω u then (1 : ℝ) else 0) := by
  rw [generatedOccupation_update_self, generatedOccupation_update_self]
  cases h : generatedAvailable R ω u <;> simp [h]

/-- If a generated Boolean statistic is already prefix-measurable, then its
branch value equals its forced branch value exactly. -/
theorem finiteDoobBranchValue_boolIndicator_of_constant
    (μ : BernoulliAssignment V → ℝ) (B : BernoulliAssignment V → Bool)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) (b : Bool)
    (hmass : prefixMass μ e k.succ (Function.update ω (e k) b) ≠ 0)
    (hconst : ∀ η,
      samePrefix e k.succ (Function.update ω (e k) b) η →
      B η = B (Function.update ω (e k) b)) :
    finiteDoobBranchValue μ (fun η => if B η then (1 : ℝ) else 0) e k ω b =
      (if B (Function.update ω (e k) b) then (1 : ℝ) else 0) := by
  unfold finiteDoobBranchValue
  apply finiteDoobValue_eq_of_constant_on_prefix _ _ _ _ _ hmass
  intro η hpre
  rw [hconst η hpre]

/-- Exact true-minus-false branch displacement for the occupation indicator of
the currently exposed vertex. -/
theorem finiteDoobBranchValue_generatedOccupation_self_difference
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => if generatedOccupation R η (parentFirstEquiv R k) then (1 : ℝ) else 0)
        (parentFirstEquiv R) k ω true -
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => if generatedOccupation R η (parentFirstEquiv R k) then (1 : ℝ) else 0)
        (parentFirstEquiv R) k ω false =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) := by
  have hpos (η : BernoulliAssignment V) :
      0 < (hardCoreBernoulliSeedLaw R z hz).probability η := by
    rw [hardCoreBernoulliSeedLaw, independentBernoulliLaw_probability]
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases hseed : η v
    · simp only [hseed, Bool.false_eq_true, if_false]
      have hs := rootedOccupationProbabilityAt_add_vacancy R z hz v
      have hvac : 0 < rootedVacancyProbabilityAt R z v :=
        div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)
      linarith
    · simp only [hseed, if_true]
      exact rootedOccupationProbabilityAt_pos R z hz v
  rw [finiteDoobBranchValue_boolIndicator_of_constant
      _ _ _ _ _ true (prefixMass_pos _ hpos _ _ _).ne',
    finiteDoobBranchValue_boolIndicator_of_constant
      _ _ _ _ _ false (prefixMass_pos _ hpos _ _ _).ne']
  · exact generatedOccupation_branch_difference_self R ω (parentFirstEquiv R k)
  · intro η hpre
    exact generatedOccupation_constant_on_nextPrefix R k
      (Function.update ω (parentFirstEquiv R k) false) η hpre
  · intro η hpre
    exact generatedOccupation_constant_on_nextPrefix R k
      (Function.update ω (parentFirstEquiv R k) true) η hpre
/-- Product Bernoulli conditional independence of an unexposed coordinate from
an update-invariant cofactor. -/
theorem finiteDoobMean_bernoulli_future_seed_mul
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hp1 : ∀ v, p v < 1)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) (x : V)
    (hx : m.1 ≤ (e.symm x).1)
    (hf : ∀ η, f (Function.update η x true) = f (Function.update η x false)) :
    finiteDoobMean (bernoulliWeight p)
        (fun η => (if η x then (1 : ℝ) else 0) * f η) e m ω =
      p x * finiteDoobMean (bernoulliWeight p) f e m ω := by
  have hmass : prefixMass (bernoulliWeight p) e m ω ≠ 0 := by
    apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [hp v, hp1 v]
  unfold finiteDoobMean
  rw [dif_neg hmass, dif_neg hmass]
  unfold prefixWeighted
  congr 1
  let flip : BernoulliAssignment V → BernoulliAssignment V := fun η => Function.update η x (!η x)
  have hflip_invol : Function.Involutive flip := by
    intro η
    funext y
    by_cases hy : y = x
    · subst y
      simp [flip]
    · simp [flip, Function.update, hy]
  let hperm : Equiv.Perm (BernoulliAssignment V) :=
    { toFun := flip
      invFun := flip
      left_inv := hflip_invol
      right_inv := hflip_invol }
  have hsumperm (g : BernoulliAssignment V → ℝ) : ∑ η, g η = ∑ η, g (hperm η) := by
    exact (Equiv.sum_comp hperm g).symm
  have hpreflip (η : BernoulliAssignment V) :
      samePrefix e m ω (flip η) ↔ samePrefix e m ω η := by
    constructor <;> intro hs j
    · have hjx : e (⟨j.1, by omega⟩ : Fin (Fintype.card V)) ≠ x := by
        intro heq
        have hind : j.1 = (e.symm x).1 := by
          have hfin : (⟨j.1, by omega⟩ : Fin (Fintype.card V)) = e.symm x := by
            apply e.injective
            simpa using heq
          exact congrArg Fin.val hfin
        omega
      have hsj := hs j
      simpa [flip, Function.update, hjx] using hsj
    · have hjx : e (⟨j.1, by omega⟩ : Fin (Fintype.card V)) ≠ x := by
        intro heq
        have hind : j.1 = (e.symm x).1 := by
          have hfin : (⟨j.1, by omega⟩ : Fin (Fintype.card V)) = e.symm x := by
            apply e.injective
            simpa using heq
          exact congrArg Fin.val hfin
        omega
      simpa [flip, Function.update, hjx] using hs j
  have hfflip (η : BernoulliAssignment V) : f (flip η) = f η := by
    cases hseed : η x
    · have heq : flip η = Function.update η x true := by
        funext y
        by_cases hy : y = x
        · subst y; simp [flip, hseed]
        · simp [flip, Function.update, hy]
      rw [heq, hf η]
      congr 1
      funext y
      by_cases hy : y = x
      · subst y; simp [hseed]
      · simp [Function.update, hy]
    · have heq : flip η = Function.update η x false := by
        funext y
        by_cases hy : y = x
        · subst y; simp [flip, hseed]
        · simp [flip, Function.update, hy]
      rw [heq, ← hf η]
      congr 1
      funext y
      by_cases hy : y = x
      · subst y; simp [hseed]
      · simp [Function.update, hy]
  have hweight_pair (η : BernoulliAssignment V) :
      (if η x then (1 - p x) * bernoulliWeight p η
       else p x * bernoulliWeight p η) =
      (if η x then p x * bernoulliWeight p (flip η)
       else (1 - p x) * bernoulliWeight p (flip η)) := by
    rw [bernoulliWeight_factor_at, bernoulliWeight_factor_at]
    have hprod :
        (∏ y ∈ Finset.univ.erase x,
          if flip η y then p y else 1 - p y) =
        ∏ y ∈ Finset.univ.erase x, if η y then p y else 1 - p y := by
      apply Finset.prod_congr rfl
      intro y hy
      have hyx := (Finset.mem_erase.mp hy).1
      simp [flip, Function.update, hyx]
    rw [hprod]
    cases hseed : η x <;> simp [hseed, flip]
    <;> ring
  let g : BernoulliAssignment V → ℝ := fun η =>
    if samePrefix e m ω η then bernoulliWeight p η * f η else 0
  have hpair_sum :
      ∑ η, (if η x then (1 - p x) * g η else -(p x) * g η) = 0 := by
    have hpermSum := hsumperm (fun η =>
      if η x then (1 - p x) * g η else -(p x) * g η)
    have hdouble :
        (∑ η, (if η x then (1 - p x) * g η else -(p x) * g η)) +
          (∑ η, (if η x then (1 - p x) * g η else -(p x) * g η)) = 0 := by
      calc
        _ = (∑ η, (if η x then (1 - p x) * g η else -(p x) * g η)) +
            (∑ η, (if (hperm η) x then (1 - p x) * g (hperm η) else -(p x) * g (hperm η))) := by
              rw [← hpermSum]
        _ = ∑ η, ((if η x then (1 - p x) * g η else -(p x) * g η) +
            (if (hperm η) x then (1 - p x) * g (hperm η) else -(p x) * g (hperm η))) := by
              rw [Finset.sum_add_distrib]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro η hη
          change _ + (if (flip η) x then _ else _) = 0
          have hpereq : samePrefix e m ω (hperm η) ↔ samePrefix e m ω η := by
            change samePrefix e m ω (flip η) ↔ samePrefix e m ω η
            exact hpreflip η
          have hfeq : f (hperm η) = f η := by
            change f (flip η) = f η
            exact hfflip η
          unfold g
          rw [if_congr hpereq rfl rfl, hfeq]
          by_cases hpre : samePrefix e m ω η
          · simp only [hpre, if_true]
            have hpermflip : hperm η = flip η := rfl
            rw [hpermflip]
            cases hseed : η x
            · have hw := hweight_pair η
              have hflipseed : flip η x = true := by simp [flip, hseed]
              rw [hflipseed, if_pos rfl]
              simp [hseed] at hw
              simp only [hseed, Bool.false_eq_true, if_false]
              calc
                _ = (-p x * bernoulliWeight p η +
                    (1 - p x) * bernoulliWeight p (flip η)) * f η := by ring
                _ = 0 := by rw [← hw]; ring
            · have hw := hweight_pair η
              have hflipseed : flip η x = false := by simp [flip, hseed]
              rw [hflipseed, if_neg Bool.false_ne_true]
              simp [hseed] at hw
              simp only [hseed, if_true]
              calc
                _ = ((1 - p x) * bernoulliWeight p η -
                    p x * bernoulliWeight p (flip η)) * f η := by ring
                _ = 0 := by rw [hw]; ring
          · simp [hpre]
    linarith
  have hweighted :
      (∑ η, if samePrefix e m ω η then bernoulliWeight p η *
          ((if η x then (1 : ℝ) else 0) * f η) else 0) =
        p x * (∑ η, if samePrefix e m ω η then bernoulliWeight p η * f η else 0) := by
    calc
      _ = ∑ η, (if η x then (1 : ℝ) else 0) *
          (if samePrefix e m ω η then bernoulliWeight p η * f η else 0) := by
            apply Finset.sum_congr rfl
            intro η hη
            by_cases hs : samePrefix e m ω η <;> cases hseed : η x <;> simp [hs, hseed]
      _ = p x * (∑ η, if samePrefix e m ω η then bernoulliWeight p η * f η else 0) := by
            rw [Finset.mul_sum]
            have h := hpair_sum
            have hid : ∀ η : BernoulliAssignment V,
                (if η x then (1 - p x) *
                    (if samePrefix e m ω η then bernoulliWeight p η * f η else 0)
                  else -p x * (if samePrefix e m ω η then bernoulliWeight p η * f η else 0)) =
                  (if η x then (1 : ℝ) else 0) *
                      (if samePrefix e m ω η then bernoulliWeight p η * f η else 0) -
                    p x * (if samePrefix e m ω η then bernoulliWeight p η * f η else 0) := by
                intro η
                cases hseed : η x <;> simp only [hseed, Bool.false_eq_true, if_false, if_true]
                <;> by_cases hs : samePrefix e m ω η <;> simp [hs] <;> ring
            rw [Finset.sum_congr rfl (fun η _ => hid η)] at h
            rw [Finset.sum_sub_distrib] at h
            have hmulsum :
                (∑ i, p x * (if samePrefix e m ω i then bernoulliWeight p i * f i else 0)) =
                  p x * ∑ i, if samePrefix e m ω i then bernoulliWeight p i * f i else 0 := by
              rw [Finset.mul_sum]
            rw [hmulsum] at h
            linarith
  rw [hweighted]
  ring

/-- If `v` is the unique parent of `x`, availability at `x` is exactly vacancy of `v`. -/
theorem generatedAvailable_eq_not_occupation_of_isChild
    (hG : G.IsAcyclic) (R : ComponentRooting G) {v x : V}
    (hvx : R.IsChild (G := G) v x) (η : BernoulliAssignment V) :
    generatedAvailable R η x = ! generatedOccupation R η v := by
  unfold generatedAvailable
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.not_eq_true]
  constructor
  · intro hall
    have := hall v hvx
    simpa using this
  · intro hvac w hwx
    have hwv : w = v := R.isChild_unique (G := G) hG hwx hvx
    subst w
    simpa using hvac

/-- Indicator form of parent blocking. -/
theorem generatedOccupationIndicator_child_factor
    (hG : G.IsAcyclic) (R : ComponentRooting G) {v x : V}
    (hvx : R.IsChild (G := G) v x) (η : BernoulliAssignment V) :
    (if generatedOccupation R η x then (1 : ℝ) else 0) =
      (if η x then (1 : ℝ) else 0) *
        (1 - (if generatedOccupation R η v then (1 : ℝ) else 0)) := by
  rw [generatedOccupation_eq_seed_and_available,
    generatedAvailable_eq_not_occupation_of_isChild hG R hvx]
  cases η x <;> cases generatedOccupation R η v <;> norm_num

/-- Generated occupation of a parent is independent of its child's own seed. -/
theorem generatedOccupation_parent_update_child
    (R : ComponentRooting G) {v x : V} (hvx : R.IsChild (G := G) v x)
    (η : BernoulliAssignment V) (b : Bool) :
    generatedOccupation R (Function.update η x b) v = generatedOccupation R η v := by
  apply generatedOccupation_eq_of_seed_eq_of_depth_le R (R.depth (G := G) v)
  · intro y hy
    simp only [Function.update]
    split
    · next h =>
      subst y
      have hd := R.depth_child (G := G) hvx
      omega
    · rfl
  · exact le_rfl

/-- If the current vertex is unavailable before reveal, forcing its seed cannot
change any generated occupation in its descendant subtree. -/
theorem generatedOccupation_update_current_eq_of_unavailable_of_descendant
    (hG : G.IsAcyclic) (R : ComponentRooting G) (ω : BernoulliAssignment V)
    (u x : V) (hA : generatedAvailable R ω u = false)
    (hx : x ∈ R.descendants (G := G) u) :
    generatedOccupation R (Function.update ω u true) x =
      generatedOccupation R (Function.update ω u false) x := by
  have hdesc : R.IsDescendant (G := G) u x :=
    (R.mem_descendants (G := G) u x).mp hx
  induction hdesc with
  | refl =>
      rw [generatedOccupation_update_self, generatedOccupation_update_self, hA]
      rfl
  | @tail v x hprev hvx ih =>
      rw [generatedOccupation_eq_seed_and_available,
        generatedOccupation_eq_seed_and_available]
      have hxu : x ≠ u := by
        intro hxu
        subst x
        have hd := R.depth_child (G := G) hvx
        have hle := R.depth_le_of_isDescendant (G := G) hprev
        omega
      have hv : v ∈ R.descendants (G := G) u :=
        (R.mem_descendants (G := G) u v).mpr hprev
      rw [generatedAvailable_eq_not_occupation_of_isChild hG R hvx,
        generatedAvailable_eq_not_occupation_of_isChild hG R hvx, ih hv]
      simp [Function.update, hxu]

noncomputable def occupationBranchResponse
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) (x : V) : ℝ :=
  finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => if generatedOccupation R η x then (1 : ℝ) else 0)
      (parentFirstEquiv R) k ω true -
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => if generatedOccupation R η x then (1 : ℝ) else 0)
      (parentFirstEquiv R) k ω false

/-- Response at any proper descendant is the product of the child recurrence;
the immediate-child case suffices for the full descendant induction. -/
theorem occupationBranchResponse_child
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    {v x : V} (hvx : R.IsChild (G := G) v x)
    (hxdesc : x ∈ R.descendants (G := G) (parentFirstEquiv R k))
    (hxne : x ≠ parentFirstEquiv R k) :
    occupationBranchResponse R z hz k ω x =
      -rootedOccupationProbabilityAt R z x * occupationBranchResponse R z hz k ω v := by
  let e := parentFirstEquiv R
  let μ := hardCoreBernoulliSeedLaw R z hz
  let p : V → ℝ := fun y => rootedOccupationProbabilityAt R z y
  have hpos : ∀ y, 0 < p y := rootedOccupationProbabilityAt_pos R z hz
  have hlt : ∀ y, p y < 1 := rootedOccupationProbabilityAt_lt_one R z hz
  have hfuture : k.succ.1 ≤ (e.symm x).1 := by
    have hproper : k.1 < ((parentFirstEquiv R).symm x).1 := by
      have hdesc : R.IsDescendant (G := G) (parentFirstEquiv R k) x :=
        (R.mem_descendants (G := G) _ _).mp hxdesc
      have hdepth : R.depth (G := G) (parentFirstEquiv R k) < R.depth (G := G) x :=
        ComponentRooting.depth_lt_of_isDescendant_of_ne (G := G) R hdesc hxne.symm
      apply depth_lt_of_parentFirstEquiv_index_lt R
      simpa using hdepth
    simpa [e] using hproper
  have hbranch (b : Bool) :
      finiteDoobBranchValue μ.probability
          (fun η => if generatedOccupation R η x then (1 : ℝ) else 0)
          e k ω b =
        p x * (1 - finiteDoobBranchValue μ.probability
          (fun η => if generatedOccupation R η v then (1 : ℝ) else 0)
          e k ω b) := by
    unfold finiteDoobBranchValue
    change finiteDoobMean (bernoulliWeight p)
        (fun η => if generatedOccupation R η x then (1 : ℝ) else 0)
        e k.succ (Function.update ω (e k) b) = _
    rw [show (fun η => if generatedOccupation R η x then (1 : ℝ) else 0) =
        (fun η => (if η x then (1 : ℝ) else 0) *
          (1 - (if generatedOccupation R η v then (1 : ℝ) else 0))) by
      funext η
      exact generatedOccupationIndicator_child_factor hG R hvx η]
    rw [finiteDoobMean_bernoulli_future_seed_mul p hpos hlt _ e k.succ _ x hfuture]
    · congr 1
      rw [show (fun η => (1 - (if generatedOccupation R η v then (1 : ℝ) else 0))) =
          (fun η => (1 : ℝ) - (if generatedOccupation R η v then 1 else 0)) by rfl]
      have hmass : prefixMass (bernoulliWeight p) e k.succ
          (Function.update ω (e k) b) ≠ 0 := by
        apply (prefixMass_pos _ ?_ _ _ _).ne'
        intro η
        unfold bernoulliWeight
        apply Finset.prod_pos
        intro y hy
        cases η y <;> simp [hpos y, hlt y]
      have hmassμ : prefixMass μ.probability e k.succ
          (Function.update ω (e k) b) ≠ 0 := by
        simpa [μ, hardCoreBernoulliSeedLaw, p] using hmass
      unfold finiteDoobMean
      rw [dif_neg hmass, dif_neg hmassμ]
      change prefixWeighted (bernoulliWeight p)
          (fun η => (1 : ℝ) - (if generatedOccupation R η v then 1 else 0)) e k.succ
          (Function.update ω (e k) b) /
          prefixMass (bernoulliWeight p) e k.succ (Function.update ω (e k) b) =
        1 - prefixWeighted (bernoulliWeight p)
          (fun η => if generatedOccupation R η v then (1 : ℝ) else 0) e k.succ
          (Function.update ω (e k) b) /
          prefixMass (bernoulliWeight p) e k.succ (Function.update ω (e k) b)
      unfold prefixWeighted
      field_simp
      ring_nf
      rw [prefixMass]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro η hη
      by_cases hs : samePrefix e k.succ (Function.update ω (e k) b) η
      <;> simp [hs]
    · intro η
      have hvocc := generatedOccupation_parent_update_child R hvx η true
      have hvocc' := generatedOccupation_parent_update_child R hvx η false
      rw [hvocc, hvocc']
  unfold occupationBranchResponse
  rw [hbranch true, hbranch false]
  ring


/-- A finite Doob branch value is linear in its observable. -/
theorem finiteDoobBranchValue_add
    (μ : BernoulliAssignment V → ℝ) (f g : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) (b : Bool)
    (hμ : prefixMass μ e k.succ (Function.update ω (e k) b) ≠ 0) :
    finiteDoobBranchValue μ (fun η => f η + g η) e k ω b =
      finiteDoobBranchValue μ f e k ω b + finiteDoobBranchValue μ g e k ω b := by
  unfold finiteDoobBranchValue finiteDoobMean
  rw [dif_neg hμ, dif_neg hμ, dif_neg hμ]
  unfold prefixWeighted
  rw [← add_div]
  apply congrArg (fun t => t / prefixMass μ e k.succ (Function.update ω (e k) b))
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro η hη
  by_cases hs : samePrefix e k.succ (Function.update ω (e k) b) η
  <;> simp [hs]
  ring

noncomputable def localGeneratedSubtreeCountReal (R : ComponentRooting G)
    (ω : BernoulliAssignment V) (u : V) : ℝ :=
  ((R.descendants (G := G) u).filter (fun v => generatedOccupation R ω v)).card

/-- The generated subtree count is the sum of its occupation indicators. -/
theorem localGeneratedSubtreeCountReal_eq_sum_indicators
    (R : ComponentRooting G) (η : BernoulliAssignment V) (u : V) :
    localGeneratedSubtreeCountReal R η u =
      ∑ x ∈ R.descendants (G := G) u,
        if generatedOccupation R η x then (1 : ℝ) else 0 := by
  unfold localGeneratedSubtreeCountReal
  rw [Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]

/-- The weighted numerators of the true and false current-prefix atoms have the
same odds ratio for a current-coordinate-invariant observable. -/
theorem bernoulli_prefix_pair_weighted
    (p : V → ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V)
    (hf : ∀ η, f (Function.update η (e k) true) =
      f (Function.update η (e k) false)) :
    (1 - p (e k)) * prefixWeighted (bernoulliWeight p) f e k.succ
        (Function.update ω (e k) true) =
      p (e k) * prefixWeighted (bernoulliWeight p) f e k.succ
        (Function.update ω (e k) false) := by
  unfold prefixWeighted
  calc
    (1 - p (e k)) *
        (∑ η, if samePrefix e k.succ (Function.update ω (e k) true) η then
          bernoulliWeight p η * f η else 0) =
      ∑ η ∈ Finset.univ.filter
          (samePrefix e k.succ (Function.update ω (e k) true)),
        (1 - p (e k)) * (bernoulliWeight p η * f η) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro η hη
          by_cases hpre : samePrefix e k.succ
              (Function.update ω (e k) true) η <;> simp [hpre]
    _ = ∑ η ∈ Finset.univ.filter
          (samePrefix e k.succ (Function.update ω (e k) false)),
        p (e k) * (bernoulliWeight p η * f η) := by
      apply Finset.sum_bij (fun η _ => Function.update η (e k) false)
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη ⊢
        intro i
        have hle : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
        rcases lt_or_eq_of_le hle with hi | hi
        · have hne : e ⟨i.1, by omega⟩ ≠ e k := by
            intro heq
            exact hi.ne (congrArg Fin.val (e.injective heq))
          simpa [Function.update, hne] using hη i
        · have hieq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
          rw [hieq]
          simp
      · intro η₁ h₁ η₂ h₂ heq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
        funext x
        by_cases hx : x = e k
        · subst x
          have ht1 : η₁ (e k) = true := by
            have hs := h₁ ⟨k, by simp⟩
            simpa using hs.symm
          have ht2 : η₂ (e k) = true := by
            have hs := h₂ ⟨k, by simp⟩
            simpa using hs.symm
          rw [ht1, ht2]
        · have hfun := congrFun heq x
          simpa [Function.update, hx] using hfun
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
        refine ⟨Function.update η (e k) true, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          intro i
          have hle : i.1 ≤ k.1 := Nat.le_of_lt_succ i.2
          rcases lt_or_eq_of_le hle with hi | hi
          · have hne : e ⟨i.1, by omega⟩ ≠ e k := by
              intro heq
              exact hi.ne (congrArg Fin.val (e.injective heq))
            simpa [Function.update, hne] using hη i
          · have hieq : (⟨i.1, by omega⟩ : Fin (Fintype.card V)) = k := Fin.ext hi
            rw [hieq]
            simp
        · funext x
          by_cases hx : x = e k
          · subst x
            have hfalse : η (e k) = false := by
              have hs := hη ⟨k, by simp⟩
              simpa using hs.symm
            simp [hfalse]
          · simp [Function.update, hx]
      · intro η hη
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hη
        have hat : η (e k) = true := by
          have hs := hη ⟨k, by simp⟩
          simpa using hs.symm
        have hfeq : f η = f (Function.update η (e k) false) := by
          rw [← hf η]
          congr 1
          funext x
          by_cases hx : x = e k
          · subst x; simp [hat]
          · simp [Function.update, hx]
        rw [bernoulliWeight_factor_at, bernoulliWeight_factor_at, hfeq]
        change (1 - p (e k)) *
            (((if η (e k) then p (e k) else 1 - p (e k)) *
              ∏ x ∈ Finset.univ.erase (e k), if η x then p x else 1 - p x) * _) =
          p (e k) *
            (((if Function.update η (e k) false (e k) then p (e k) else 1 - p (e k)) *
              ∏ x ∈ Finset.univ.erase (e k),
                if Function.update η (e k) false x then p x else 1 - p x) * _)
        rw [hat]
        simp only [ite_true, Function.update_self]
        have hprod : (∏ x ∈ Finset.univ.erase (e k),
            if Function.update η (e k) false x then p x else 1 - p x) =
            ∏ x ∈ Finset.univ.erase (e k), if η x then p x else 1 - p x := by
          apply Finset.prod_congr rfl
          intro x hx
          simp [Function.update, (Finset.mem_erase.mp hx).1]
        rw [hprod]
        norm_num
        ring
    _ = p (e k) *
        (∑ η, if samePrefix e k.succ (Function.update ω (e k) false) η then
          bernoulliWeight p η * f η else 0) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro η hη
          by_cases hpre : samePrefix e k.succ
              (Function.update ω (e k) false) η <;> simp [hpre]

/-- Current-coordinate invariance gives identical true/false branch means. -/
theorem finiteDoobBranchValue_eq_of_update_current_invariant
    (p : V → ℝ) (hp : ∀ v, 0 < p v) (hp1 : ∀ v, p v < 1)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V)
    (hf : ∀ η, f (Function.update η (e k) true) =
      f (Function.update η (e k) false)) :
    finiteDoobBranchValue (bernoulliWeight p) f e k ω true =
      finiteDoobBranchValue (bernoulliWeight p) f e k ω false := by
  have hmass (b : Bool) : prefixMass (bernoulliWeight p) e k.succ
      (Function.update ω (e k) b) ≠ 0 := by
    apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro y hy
    cases η y <;> simp [hp y, hp1 y]
  unfold finiteDoobBranchValue finiteDoobMean
  rw [dif_neg (hmass true), dif_neg (hmass false)]
  have hw := bernoulli_prefix_pair_weighted p f e k ω hf
  have hm := bernoulli_prefix_pair_mass p e k ω
  have hp0 := hp (e k)
  have hq0 : 0 < 1 - p (e k) := sub_pos.mpr (hp1 (e k))
  have hqne : 1 - p (e k) ≠ 0 := ne_of_gt hq0
  have hnum : prefixWeighted (bernoulliWeight p) f e k.succ
        (Function.update ω (e k) true) =
      p (e k) / (1 - p (e k)) *
        prefixWeighted (bernoulliWeight p) f e k.succ
          (Function.update ω (e k) false) := by
    calc
      _ = (p (e k) * prefixWeighted (bernoulliWeight p) f e k.succ
          (Function.update ω (e k) false)) / (1 - p (e k)) := by
            apply (eq_div_iff hqne).2
            nlinarith [hw]
      _ = _ := by ring
  have hden : prefixMass (bernoulliWeight p) e k.succ
        (Function.update ω (e k) true) =
      p (e k) / (1 - p (e k)) *
        prefixMass (bernoulliWeight p) e k.succ
          (Function.update ω (e k) false) := by
    calc
      _ = (p (e k) * prefixMass (bernoulliWeight p) e k.succ
          (Function.update ω (e k) false)) / (1 - p (e k)) := by
            apply (eq_div_iff hqne).2
            nlinarith [hm]
      _ = _ := by ring
  rw [hnum, hden]
  field_simp [ne_of_gt hp0, hqne, hmass false]

/-- If the current seed cannot affect an observable, its two branch values agree. -/
theorem finiteDoobBranchValue_hardCoreSeed_eq_of_update_current_invariant
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (f : BernoulliAssignment V → ℝ)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (hf : ∀ η, f (Function.update η (parentFirstEquiv R k) true) =
      f (Function.update η (parentFirstEquiv R k) false)) :
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability f
        (parentFirstEquiv R) k ω true =
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability f
        (parentFirstEquiv R) k ω false := by
  change finiteDoobBranchValue
      (bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v)) f
        (parentFirstEquiv R) k ω true = _
  exact finiteDoobBranchValue_eq_of_update_current_invariant
    (fun v => rootedOccupationProbabilityAt R z v)
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz) f (parentFirstEquiv R) k ω hf


/-- The response sum over a descendant subtree satisfies the rooted displacement recurrence. -/
theorem occupationBranchResponse_sum_descendants
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (u : V) (hu : u ∈ R.descendants (G := G) (parentFirstEquiv R k)) :
    (∑ x ∈ R.descendants (G := G) u,
        occupationBranchResponse R z hz k ω x) =
      rootedDisplacementAt R z hz u * occupationBranchResponse R z hz k ω u := by
  induction hn : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [R.descendants_eq_insert_biUnion_children (G := G) u]
      rw [Finset.sum_insert]
      · rw [Finset.sum_biUnion (R.children_pairwiseDisjoint_descendants (G := G) hG u)]
        have hchildren :
            (∑ v ∈ R.children (G := G) u,
                ∑ x ∈ R.descendants (G := G) v,
                  occupationBranchResponse R z hz k ω x) =
              ∑ v ∈ R.children (G := G) u,
                rootedDisplacementAt R z hz v * occupationBranchResponse R z hz k ω v := by
          apply Finset.sum_congr rfl
          intro v hv
          apply ih (R.subtreeOrder (G := G) v)
          · rw [← hn]
            exact R.subtreeOrder_child_lt (G := G)
              ((R.mem_children (G := G) u v).mp hv)
          · exact (R.mem_descendants (G := G) _ _).mpr
              ((R.mem_descendants (G := G) _ _).mp hu |>.tail
                ((R.mem_children (G := G) u v).mp hv))
          · rfl
        rw [hchildren]
        rw [rootedDisplacementAt_eq_one_sub_sum hG R z hz u]
        have hresp : ∀ v ∈ R.children (G := G) u,
            occupationBranchResponse R z hz k ω v =
              -rootedOccupationProbabilityAt R z v *
                occupationBranchResponse R z hz k ω u := by
          intro v hv
          apply occupationBranchResponse_child hG R z hz k ω
            ((R.mem_children (G := G) u v).mp hv)
          · exact (R.mem_descendants (G := G) _ _).mpr
              ((R.mem_descendants (G := G) _ _).mp hu |>.tail
                ((R.mem_children (G := G) u v).mp hv))
          · intro hvu
            subst v
            exact R.not_mem_descendants_child (G := G)
              ((R.mem_children (G := G) u (parentFirstEquiv R k)).mp hv)
              hu
        have hsumresp :
            (∑ v ∈ R.children (G := G) u,
                rootedDisplacementAt R z hz v * occupationBranchResponse R z hz k ω v) =
              ∑ v ∈ R.children (G := G) u,
                rootedDisplacementAt R z hz v *
                  (-rootedOccupationProbabilityAt R z v *
                    occupationBranchResponse R z hz k ω u) := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [hresp v hv]
        rw [hsumresp]
        have hsumfactor :
            (∑ v ∈ R.children (G := G) u,
              rootedDisplacementAt R z hz v *
                (-rootedOccupationProbabilityAt R z v *
                  occupationBranchResponse R z hz k ω u)) =
              -(∑ v ∈ R.children (G := G) u,
                  rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v) *
                occupationBranchResponse R z hz k ω u := by
          calc
            _ = ∑ v ∈ R.children (G := G) u,
                (-(rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v)) *
                  occupationBranchResponse R z hz k ω u := by
                    apply Finset.sum_congr rfl
                    intro v hv
                    ring
            _ = (∑ v ∈ R.children (G := G) u,
                -(rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v)) *
                  occupationBranchResponse R z hz k ω u := by
                    rw [Finset.sum_mul]
            _ = _ := by rw [Finset.sum_neg_distrib]
        rw [hsumfactor]
        ring
      · rw [Finset.mem_biUnion]
        push_neg
        intro v hv
        exact R.not_mem_descendants_child (G := G)
          ((R.mem_children (G := G) u v).mp hv)

/-- The generated count is the sum of its occupation indicators. -/
theorem generatedCountReal_eq_sum_occupationIndicators
    (hG : G.IsAcyclic) (R : ComponentRooting G) (η : BernoulliAssignment V) :
    generatedCountReal hG R η =
      ∑ x, if generatedOccupation R η x then (1 : ℝ) else 0 := by
  classical
  unfold generatedCountReal
  rw [Finset.card_eq_sum_ones]
  push_cast
  calc
    (∑ x ∈ generatedFinset R η, (1 : ℝ)) =
        ∑ x ∈ Finset.univ, if x ∈ generatedFinset R η then (1 : ℝ) else 0 := by
          rw [Finset.sum_ite_mem]
          simp
    _ = _ := by simp [generatedFinset]

/-- A branch value commutes with a finite sum of observables. -/
theorem finiteDoobBranchValue_sum
    (p : BernoulliAssignment V → ℝ) (e : Fin (Fintype.card V) ≃ V)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V)
    (f : V → BernoulliAssignment V → ℝ)
    (b : Bool)
    (hm : prefixMass p e k.succ (Function.update ω (e k) b) ≠ 0) :
    finiteDoobBranchValue p (fun η => ∑ x, f x η) e k ω b =
      ∑ x, finiteDoobBranchValue p (f x) e k ω b := by
  unfold finiteDoobBranchValue finiteDoobMean
  rw [dif_neg hm]
  have hrhs : (∑ x, if h : prefixMass p e k.succ
      (Function.update ω (e k) b) = 0 then 0 else
        prefixWeighted p (f x) e k.succ (Function.update ω (e k) b) /
          prefixMass p e k.succ (Function.update ω (e k) b)) =
      ∑ x, prefixWeighted p (f x) e k.succ (Function.update ω (e k) b) /
          prefixMass p e k.succ (Function.update ω (e k) b) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [dif_neg hm]
  rw [hrhs, ← Finset.sum_div]
  congr 1
  unfold prefixWeighted
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η hη
  by_cases hs : samePrefix e k.succ (Function.update ω (e k) b) η
  · simp only [hs, if_true]
    rw [Finset.mul_sum]
  · simp [hs]

/-- Full-count branch displacement is the sum of occupation responses. -/
theorem generatedCountReal_branch_difference_eq_sum_responses
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedCountReal hG R) (parentFirstEquiv R) k ω true -
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedCountReal hG R) (parentFirstEquiv R) k ω false =
      ∑ x, occupationBranchResponse R z hz k ω x := by
  rw [show generatedCountReal hG R =
      fun η => ∑ x, if generatedOccupation R η x then (1 : ℝ) else 0 from by
    funext η
    exact generatedCountReal_eq_sum_occupationIndicators hG R η]
  have hm (b : Bool) : prefixMass (hardCoreBernoulliSeedLaw R z hz).probability
      (parentFirstEquiv R) k.succ
        (Function.update ω (parentFirstEquiv R k) b) ≠ 0 := by
    apply (prefixMass_pos _ ?_ _ _ _).ne'
    intro η
    change 0 < bernoulliWeight (fun v => rootedOccupationProbabilityAt R z v) η
    unfold bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  rw [finiteDoobBranchValue_sum _ _ _ _ _ true (hm true),
    finiteDoobBranchValue_sum _ _ _ _ _ false (hm false)]
  rw [← Finset.sum_sub_distrib]
  rfl

/-- Occupation responses vanish away from the current descendant subtree. -/
theorem occupationBranchResponse_eq_zero_of_not_descendant
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) (x : V)
    (hx : x ∉ R.descendants (G := G) (parentFirstEquiv R k)) :
    occupationBranchResponse R z hz k ω x = 0 := by
  unfold occupationBranchResponse
  have heq := finiteDoobBranchValue_hardCoreSeed_eq_of_update_current_invariant
    R z hz (fun η => if generatedOccupation R η x then (1 : ℝ) else 0) k ω
    (fun η => by
      change (if generatedOccupation R (Function.update η (parentFirstEquiv R k) true) x
          then (1 : ℝ) else 0) = _
      rw [generatedOccupation_update_eq_of_not_descendant R η
        (parentFirstEquiv R k) x hx true]
      change (if generatedOccupation R η x then (1 : ℝ) else 0) =
        (if generatedOccupation R (Function.update η (parentFirstEquiv R k) false) x
          then 1 else 0)
      rw [generatedOccupation_update_eq_of_not_descendant R η
        (parentFirstEquiv R k) x hx false])
  linarith

/-- Summing all occupation responses reduces to the current descendant subtree. -/
theorem occupationBranchResponse_sum_eq_descendants
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    (∑ x, occupationBranchResponse R z hz k ω x) =
      ∑ x ∈ R.descendants (G := G) (parentFirstEquiv R k),
        occupationBranchResponse R z hz k ω x := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ,
        if x ∈ R.descendants (G := G) (parentFirstEquiv R k) then
          occupationBranchResponse R z hz k ω x else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hxd : x ∈ R.descendants (G := G) (parentFirstEquiv R k)
            · simp [hxd]
            · rw [occupationBranchResponse_eq_zero_of_not_descendant R z hz k ω x hxd]
              simp
    _ = _ := by rw [Finset.sum_ite_mem]; simp

/-- The current occupation response is exactly generated availability. -/
theorem occupationBranchResponse_current
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    occupationBranchResponse R z hz k ω (parentFirstEquiv R k) =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) := by
  exact finiteDoobBranchValue_generatedOccupation_self_difference R z hz k ω

/-- Unconditional full-count branch displacement with the availability factor. -/
theorem generatedCountReal_branch_displacement_available
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedCountReal hG R) (parentFirstEquiv R) k ω true -
      finiteDoobBranchValue (hardCoreBernoulliSeedLaw R z hz).probability
        (generatedCountReal hG R) (parentFirstEquiv R) k ω false =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) := by
  rw [generatedCountReal_branch_difference_eq_sum_responses,
    occupationBranchResponse_sum_eq_descendants,
    occupationBranchResponse_sum_descendants hG R z hz k ω
      (parentFirstEquiv R k) (R.self_mem_descendants (G := G) _),
    occupationBranchResponse_current hG R z hz k ω]
  ring


/-- Unconditional availability-aware exact increment formula for the generated count. -/
theorem generatedCountDoobIncrement_eq_available_exact
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun η => generatedCountReal hG R η) (parentFirstEquiv R) k ω =
      (if generatedAvailable R ω (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        (if ω (parentFirstEquiv R k) then
          (1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k)) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)
        else
          -rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k)) := by
  apply generatedCountDoobIncrement_eq_available_branch_exact hG R z hz k ω
  exact generatedCountReal_branch_displacement_available hG R z hz k ω

/-- Conditional second moment of the availability-aware exact Bernoulli branch
increment. This is the finite A.13 identity once the branch displacement is
identified with `rootedDisplacementAt`. -/
theorem bernoulli_available_increment_second_average
    (a : Bool) (p d : ℝ) :
    (1 - p) *
        ((if a then (1 : ℝ) else 0) * (-p * d)) ^ 2 +
      p * ((if a then (1 : ℝ) else 0) * ((1 - p) * d)) ^ 2 =
    (if a then (1 : ℝ) else 0) * (p * (1 - p) * d ^ 2) := by
  cases a <;> norm_num <;> ring

/-- Conditional fourth moment of the availability-aware exact Bernoulli branch
increment. This is the finite A.14 identity. -/
theorem bernoulli_available_increment_fourth_average
    (a : Bool) (p d : ℝ) :
    (1 - p) *
        ((if a then (1 : ℝ) else 0) * (-p * d)) ^ 4 +
      p * ((if a then (1 : ℝ) else 0) * ((1 - p) * d)) ^ 4 =
    (if a then (1 : ℝ) else 0) *
      (p * (1 - p) * (p ^ 3 + (1 - p) ^ 3) * d ^ 4) := by
  cases a <;> norm_num <;> ring

/-- The Bernoulli fourth coefficient is bounded by its second coefficient when
`p` is a probability. -/
theorem bernoulli_fourth_coefficient_le_second
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    p * (1 - p) * (p ^ 3 + (1 - p) ^ 3) ≤ p * (1 - p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsum : p ^ 3 + (1 - p) ^ 3 ≤ 1 := by
    nlinarith [sq_nonneg p, sq_nonneg (1 - p), mul_nonneg hp hq]
  nlinarith [mul_nonneg hp hq]

/-- Consequently the conditional fourth increment moment is bounded by the
conditional second increment moment times `d²`. -/
theorem bernoulli_available_increment_fourth_le_second_mul_sq
    (a : Bool) (p d : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 - p) * ((if a then (1 : ℝ) else 0) * (-p * d)) ^ 4 +
      p * ((if a then (1 : ℝ) else 0) * ((1 - p) * d)) ^ 4 ≤
    ((if a then (1 : ℝ) else 0) * (p * (1 - p) * d ^ 2)) * d ^ 2 := by
  rw [bernoulli_available_increment_fourth_average]
  cases a
  · norm_num
  · simp only [ite_true, one_mul]
    have hc := bernoulli_fourth_coefficient_le_second p hp hp1
    have hd : 0 ≤ d ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_right hc hd
    ring_nf at this ⊢
    exact this
noncomputable def generatedAvailabilityReal
    (R : ComponentRooting G) (ω : BernoulliAssignment V) (v : V) : ℝ :=
  if generatedAvailable R ω v then 1 else 0

 theorem finiteDoobMean_generatedAvailability
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => generatedAvailabilityReal R η (parentFirstEquiv R k))
      (parentFirstEquiv R) k.castSucc ω =
    generatedAvailabilityReal R ω (parentFirstEquiv R k) := by
  apply finiteDoobValue_eq_of_constant_on_prefix
  · exact (prefixMass_pos _ (fun η => by
      unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
      apply Finset.prod_pos
      intro v hv
      cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
        rootedOccupationProbabilityAt_lt_one R z hz v]) _ _ _).ne'
  · intro η hpre
    unfold generatedAvailabilityReal
    rw [generatedAvailable_eq_of_samePrefix_parentFirst R k ω η hpre]

 theorem finiteDoobMean_generatedAvailability_mul_seed
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        generatedAvailabilityReal R η (parentFirstEquiv R k))
      (parentFirstEquiv R) k.castSucc ω =
    rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
      generatedAvailabilityReal R ω (parentFirstEquiv R k) := by
  let p : V → ℝ := fun v => rootedOccupationProbabilityAt R z v
  change finiteDoobMean (bernoulliWeight p)
      (fun η => (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        generatedAvailabilityReal R η (parentFirstEquiv R k))
      (parentFirstEquiv R) k.castSucc ω = _
  rw [finiteDoobMean_bernoulli_future_seed_mul p
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz)
    (fun η => generatedAvailabilityReal R η (parentFirstEquiv R k))
    (parentFirstEquiv R) k.castSucc ω (parentFirstEquiv R k)]
  · change p (parentFirstEquiv R k) *
      finiteDoobMean (bernoulliWeight p)
        (fun η => generatedAvailabilityReal R η (parentFirstEquiv R k))
        (parentFirstEquiv R) k.castSucc ω = _
    have hA := finiteDoobMean_generatedAvailability R z hz k ω
    change finiteDoobMean (bernoulliWeight p)
      (fun η => generatedAvailabilityReal R η (parentFirstEquiv R k))
      (parentFirstEquiv R) k.castSucc ω = _ at hA
    rw [hA]
  · simp
  · intro η
    unfold generatedAvailabilityReal
    rw [generatedAvailable_update_self, generatedAvailable_update_self]

 theorem finiteDoobMean_generatedOccupation_current
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => if generatedOccupation R η (parentFirstEquiv R k) then (1 : ℝ) else 0)
      (parentFirstEquiv R) k.castSucc ω =
    rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
      generatedAvailabilityReal R ω (parentFirstEquiv R k) := by
  rw [show (fun η => if generatedOccupation R η (parentFirstEquiv R k) then (1 : ℝ) else 0) =
      (fun η => (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        generatedAvailabilityReal R η (parentFirstEquiv R k)) by
    funext η
    rw [generatedOccupation_eq_seed_and_available]
    unfold generatedAvailabilityReal
    cases η (parentFirstEquiv R k) <;>
      cases generatedAvailable R η (parentFirstEquiv R k) <;> norm_num]
  exact finiteDoobMean_generatedAvailability_mul_seed R z hz k ω

 theorem finiteDoobMean_increment_sq_current
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2)
      (parentFirstEquiv R) k.castSucc ω =
    generatedAvailabilityReal R ω (parentFirstEquiv R k) *
      rootedEnergyAt R z hz (parentFirstEquiv R k) := by
  let p : ℝ := rootedOccupationProbabilityAt R z (parentFirstEquiv R k)
  let d : ℝ := rootedDisplacementAt R z hz (parentFirstEquiv R k)
  let A : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k)
  have hD (η : BernoulliAssignment V) :
      finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η =
      A η * (if η (parentFirstEquiv R k) then (1 - p) * d else -p * d) := by
    simpa [A, p, d, generatedAvailabilityReal] using
      generatedCountDoobIncrement_eq_available_exact hG R z hz k η
  rw [show (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2) =
      (fun η => ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) *
        A η) * ((1 - p) ^ 2 * d ^ 2) +
        A η * (p ^ 2 * d ^ 2) -
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η) *
          (p ^ 2 * d ^ 2)) by
    funext η
    rw [hD]
    unfold A generatedAvailabilityReal
    cases η (parentFirstEquiv R k) <;>
      cases generatedAvailable R η (parentFirstEquiv R k) <;> norm_num <;> ring]
  rw [finiteDoobMean_sub]
  rw [finiteDoobMean_add]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * ((1 - p) ^ 2 * d ^ 2)) =
      (fun η => ((1 - p) ^ 2 * d ^ 2) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [show (fun η => A η * (p ^ 2 * d ^ 2)) =
      (fun η => (p ^ 2 * d ^ 2) * A η) by funext η; ring]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * (p ^ 2 * d ^ 2)) =
      (fun η => (p ^ 2 * d ^ 2) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [finiteDoobMean_const_mul, finiteDoobMean_const_mul,
    finiteDoobMean_const_mul]
  rw [finiteDoobMean_generatedAvailability_mul_seed R z hz k ω,
    finiteDoobMean_generatedAvailability R z hz k ω]
  dsimp [A, p, d]
  unfold rootedEnergyAt generatedAvailabilityReal
  cases generatedAvailable R ω (parentFirstEquiv R k)
  · norm_num
  · simp only [ite_true, one_mul]
    have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)
    rw [show rootedVacancyProbabilityAt R z (parentFirstEquiv R k) =
      1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k) by linarith [hpq]]
    ring


 theorem finiteDoobMean_tower_zero
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => finiteDoobMean p X e m η) e
        ⟨0, Nat.zero_lt_succ _⟩ ω =
      finiteDoobMean p X e ⟨0, Nat.zero_lt_succ _⟩ ω := by
  change finiteDoobMean p (fun η => finiteDoobMean p X e m η) e 0 ω =
    finiteDoobMean p X e 0 ω
  rw [finiteDoobMean_zero_of_normalized _ _ _ _ hnorm]
  rw [finiteDoobMean_zero_of_normalized _ _ _ _ hnorm]
  unfold finiteDoobMean
  have hsame (η ξ : BernoulliAssignment V) (h : samePrefix e m η ξ) :
      prefixWeighted p X e m η = prefixWeighted p X e m ξ ∧
      prefixMass p e m η = prefixMass p e m ξ := by
    constructor
    · unfold prefixWeighted
      apply Finset.sum_congr rfl
      intro τ hτ
      have hiff : samePrefix e m η τ ↔ samePrefix e m ξ τ := by
        constructor
        · intro hη
          intro i
          exact (h i).symm.trans (hη i)
        · intro hξ
          intro i
          exact (h i).trans (hξ i)
      by_cases hη : samePrefix e m η τ
      · rw [if_pos hη, if_pos (hiff.mp hη)]
      · rw [if_neg hη, if_neg (fun hx => hη (hiff.mpr hx))]
    · unfold prefixMass
      apply Finset.sum_congr rfl
      intro τ hτ
      have hiff : samePrefix e m η τ ↔ samePrefix e m ξ τ := by
        constructor
        · intro hη
          intro i
          exact (h i).symm.trans (hη i)
        · intro hξ
          intro i
          exact (h i).trans (hξ i)
      by_cases hη : samePrefix e m η τ
      · rw [if_pos hη, if_pos (hiff.mp hη)]
      · rw [if_neg hη, if_neg (fun hx => hη (hiff.mpr hx))]
  have hpoint (η : BernoulliAssignment V) :
      p η * (prefixWeighted p X e m η / prefixMass p e m η) =
      ∑ ξ, if samePrefix e m η ξ then
        p η * p ξ * X ξ / prefixMass p e m ξ else 0 := by
    unfold prefixWeighted
    rw [show (∑ ξ, if samePrefix e m η ξ then
        p η * p ξ * X ξ / prefixMass p e m ξ else 0) =
      ∑ ξ, p η * (if samePrefix e m η ξ then
        p ξ * X ξ else 0) / prefixMass p e m η by
      apply Finset.sum_congr rfl
      intro ξ hξ
      by_cases hpre : samePrefix e m η ξ
      · rw [if_pos hpre, if_pos hpre]
        rw [(hsame η ξ hpre).2]
        ring
      · rw [if_neg hpre, if_neg hpre]
        ring]
    rw [← Finset.sum_div, ← Finset.mul_sum]
    ring
  simp_rw [dif_neg (prefixMass_pos p hp e m _).ne']
  rw [Finset.sum_congr rfl (fun η _ => hpoint η)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  have hmass : prefixMass p e m ξ ≠ 0 := (prefixMass_pos p hp e m ξ).ne'
  rw [show (∑ η, if samePrefix e m η ξ then
      p η * p ξ * X ξ / prefixMass p e m ξ else 0) =
      (∑ η, if samePrefix e m ξ η then p η else 0) *
        (p ξ * X ξ / prefixMass p e m ξ) by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro η hη
    have hsym : samePrefix e m η ξ ↔ samePrefix e m ξ η := by
      constructor
      · intro h
        intro i
        exact (h i).symm
      · intro h
        intro i
        exact (h i).symm
    by_cases hpre : samePrefix e m η ξ
    · rw [if_pos hpre, if_pos (hsym.mp hpre)]
      ring
    · rw [if_neg hpre, if_neg (fun hx => hpre (hsym.mpr hx))]
      ring]
  change prefixMass p e m ξ * (p ξ * X ξ / prefixMass p e m ξ) = p ξ * X ξ
  field_simp [hmass]


 theorem finiteDoobMean_tower_succ_current
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => finiteDoobMean p X e k.succ η)
      e k.castSucc ω = finiteDoobMean p X e k.castSucc ω := by
  let q := finiteDoobBranchProbability p e k ω
  have hbranch (b : Bool) :
      finiteDoobMean p (fun η => finiteDoobMean p X e k.succ η)
        e k.succ (Function.update ω (e k) b) =
      finiteDoobBranchValue p X e k ω b := by
    apply finiteDoobValue_eq_of_constant_on_prefix
    · exact (prefixMass_pos p hp e k.succ _).ne'
    · intro η hpre
      exact (finiteDoobMean_eq_of_samePrefix p X e
        (Function.update ω (e k) b) η hpre).symm
  rw [finiteDoobMean_eq_branch_mixture p hp]
  rw [finiteDoobMean_eq_branch_mixture p hp]
  change (1 - q) * finiteDoobMean p (fun η => finiteDoobMean p X e k.succ η)
      e k.succ (Function.update ω (e k) false) +
    q * finiteDoobMean p (fun η => finiteDoobMean p X e k.succ η)
      e k.succ (Function.update ω (e k) true) = _
  rw [hbranch false, hbranch true]

 theorem finiteDoobIncrement_centered_current
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => finiteDoobIncrement p X e k η) e k.castSucc ω = 0 := by
  change finiteDoobMean p (fun η => finiteDoobMean p X e k.succ η -
      finiteDoobMean p X e k.castSucc η) e k.castSucc ω = 0
  rw [finiteDoobMean_sub]
  have hmeas : finiteDoobMean p (fun η => finiteDoobMean p X e k.castSucc η)
      e k.castSucc ω = finiteDoobMean p X e k.castSucc ω := by
    apply finiteDoobValue_eq_of_constant_on_prefix
    · exact (prefixMass_pos p hp e k.castSucc _).ne'
    · intro η hpre
      exact (finiteDoobMean_eq_of_samePrefix p X e ω η hpre).symm
  rw [finiteDoobMean_tower_succ_current p hp X e k ω, hmeas]
  ring

 theorem finiteDoobMean_eq_of_eq_on_prefix
    (p : BernoulliAssignment V → ℝ) (f g : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V)
    (hfg : ∀ η, samePrefix e m ω η → f η = g η) :
    finiteDoobMean p f e m ω = finiteDoobMean p g e m ω := by
  by_cases hmass : prefixMass p e m ω = 0
  · rw [finiteDoobMean, dif_pos hmass, finiteDoobMean, dif_pos hmass]
  · rw [finiteDoobMean, dif_neg hmass, finiteDoobMean, dif_neg hmass]
    unfold prefixWeighted
    congr 1
    apply Finset.sum_congr rfl
    intro η hη
    by_cases hpre : samePrefix e m ω η
    · rw [if_pos hpre, if_pos hpre, hfg η hpre]
    · rw [if_neg hpre, if_neg hpre]

 theorem finiteDoobMean_measurable_mul
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (f g : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V)
    (hf : ∀ η, samePrefix e m ω η → f η = f ω) :
    finiteDoobMean p (fun η => f η * g η) e m ω =
      f ω * finiteDoobMean p g e m ω := by
  have heq := finiteDoobMean_eq_of_eq_on_prefix p (fun η => f η * g η)
    (fun η => f ω * g η) e m ω (fun η hpre => by
      change f η * g η = f ω * g η
      rw [hf η hpre])
  rw [heq, finiteDoobMean_const_mul]

 theorem finiteDoobMean_sq_add_increment_current
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => (finiteDoobMean p X e k.succ η) ^ 2)
      e k.castSucc ω =
    (finiteDoobMean p X e k.castSucc ω) ^ 2 +
      finiteDoobMean p (fun η => (finiteDoobIncrement p X e k η) ^ 2)
        e k.castSucc ω := by
  let M : BernoulliAssignment V → ℝ := fun η => finiteDoobMean p X e k.castSucc η
  let D : BernoulliAssignment V → ℝ := fun η => finiteDoobIncrement p X e k η
  have hdecomp : (fun η => (finiteDoobMean p X e k.succ η) ^ 2) =
      (fun η => M η ^ 2 + (2 * M η) * D η + D η ^ 2) := by
    funext η
    have hsucc : (⟨k.1 + 1, by omega⟩ : Fin (Fintype.card V + 1)) = k.succ := by
      apply Fin.ext
      simp
    have hcast : (⟨k.1, by omega⟩ : Fin (Fintype.card V + 1)) = k.castSucc := by
      apply Fin.ext
      simp
    dsimp [M, D, finiteDoobIncrement]
    rw [hsucc, hcast]
    ring
  rw [hdecomp, finiteDoobMean_add, finiteDoobMean_add]
  have hM : ∀ η, samePrefix e k.castSucc ω η →
      M η = M ω := by
    intro η hpre
    exact (finiteDoobMean_eq_of_samePrefix p X e ω η hpre).symm
  have hMsq : finiteDoobMean p (fun η => M η ^ 2) e k.castSucc ω = M ω ^ 2 := by
    apply finiteDoobValue_eq_of_constant_on_prefix
    · exact (prefixMass_pos p hp e k.castSucc _).ne'
    · intro η hpre
      rw [hM η hpre]
  have hcross : finiteDoobMean p (fun η => (2 * M η) * D η) e k.castSucc ω = 0 := by
    rw [finiteDoobMean_measurable_mul p hp (fun η => 2 * M η) D e k.castSucc ω]
    · rw [finiteDoobIncrement_centered_current p hp X e k ω]
      ring
    · intro η hpre
      rw [hM η hpre]
  rw [hMsq, hcross]
  dsimp [M]
  ring


 theorem finiteDoob_sq_expectation_step
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V)) :
    (∑ η, p η * (finiteDoobMean p X e k.succ η) ^ 2) =
      (∑ η, p η * (finiteDoobMean p X e k.castSucc η) ^ 2) +
      ∑ η, p η * (finiteDoobIncrement p X e k η) ^ 2 := by
  let A : BernoulliAssignment V → ℝ := fun η => (finiteDoobMean p X e k.succ η) ^ 2
  let B : BernoulliAssignment V → ℝ := fun η => (finiteDoobMean p X e k.castSucc η) ^ 2
  let C : BernoulliAssignment V → ℝ := fun η => (finiteDoobIncrement p X e k η) ^ 2
  have hpoint : ∀ ω, finiteDoobMean p A e k.castSucc ω =
      B ω + finiteDoobMean p C e k.castSucc ω := by
    intro ω
    exact finiteDoobMean_sq_add_increment_current p hp X e k ω
  have hEA : ∑ η, p η * finiteDoobMean p A e k.castSucc η = ∑ η, p η * A η := by
    let ω₀ : BernoulliAssignment V := fun _ => false
    have ht := finiteDoobMean_tower_zero p hp hnorm A e k.castSucc ω₀
    change finiteDoobMean p (fun η => finiteDoobMean p A e k.castSucc η)
      e ⟨0, Nat.zero_lt_succ _⟩ ω₀ =
        finiteDoobMean p A e ⟨0, Nat.zero_lt_succ _⟩ ω₀ at ht
    have hleft := finiteDoobMean_zero_of_normalized p
      (fun η => finiteDoobMean p A e k.castSucc η) e ω₀ hnorm
    have hright := finiteDoobMean_zero_of_normalized p A e ω₀ hnorm
    change finiteDoobMean p (fun η => finiteDoobMean p A e k.castSucc η)
      e 0 ω₀ = finiteDoobMean p A e 0 ω₀ at ht
    rw [hleft, hright] at ht
    exact ht
  have hEC : ∑ η, p η * finiteDoobMean p C e k.castSucc η = ∑ η, p η * C η := by
    let ω₀ : BernoulliAssignment V := fun _ => false
    have ht := finiteDoobMean_tower_zero p hp hnorm C e k.castSucc ω₀
    change finiteDoobMean p (fun η => finiteDoobMean p C e k.castSucc η)
      e ⟨0, Nat.zero_lt_succ _⟩ ω₀ =
        finiteDoobMean p C e ⟨0, Nat.zero_lt_succ _⟩ ω₀ at ht
    have hleft := finiteDoobMean_zero_of_normalized p
      (fun η => finiteDoobMean p C e k.castSucc η) e ω₀ hnorm
    have hright := finiteDoobMean_zero_of_normalized p C e ω₀ hnorm
    change finiteDoobMean p (fun η => finiteDoobMean p C e k.castSucc η)
      e 0 ω₀ = finiteDoobMean p C e 0 ω₀ at ht
    rw [hleft, hright] at ht
    exact ht
  calc
    ∑ η, p η * A η = ∑ η, p η * finiteDoobMean p A e k.castSucc η := hEA.symm
    _ = ∑ η, p η * (B η + finiteDoobMean p C e k.castSucc η) := by
      apply Finset.sum_congr rfl
      intro η hη
      rw [hpoint η]
    _ = (∑ η, p η * B η) +
        ∑ η, p η * finiteDoobMean p C e k.castSucc η := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro η hη
      ring
    _ = (∑ η, p η * B η) + ∑ η, p η * C η := by rw [hEC]
    _ = _ := by rfl


 theorem finiteDoob_sq_expectation_prefix
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) :
    ∀ m : Nat, ∀ hm : m ≤ Fintype.card V,
    (∑ η, p η * (finiteDoobMean p X e ⟨m, Nat.lt_succ_of_le hm⟩ η) ^ 2) =
      (∑ η, p η * (finiteDoobMean p X e 0 η) ^ 2) +
      ∑ k : Fin m, ∑ η, p η *
        (finiteDoobIncrement p X e ⟨k.1, lt_of_lt_of_le k.2 hm⟩ η) ^ 2 := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp
  | succ m ih =>
      intro hm
      have hm' : m ≤ Fintype.card V := Nat.le_trans (Nat.le_succ m) hm
      have hlt : m < Fintype.card V := Nat.lt_of_succ_le hm
      let ktop : Fin (Fintype.card V) := ⟨m, hlt⟩
      have hstep := finiteDoob_sq_expectation_step p hp hnorm X e ktop
      have hsucc : ktop.succ = (⟨m + 1, Nat.lt_succ_of_le hm⟩ : Fin (Fintype.card V + 1)) := by
        apply Fin.ext
        simp [ktop]
      have hcast : ktop.castSucc = (⟨m, Nat.lt_succ_of_le hm'⟩ : Fin (Fintype.card V + 1)) := by
        apply Fin.ext
        simp [ktop]
      rw [hsucc, hcast] at hstep
      rw [hstep, ih hm']
      rw [Fin.sum_univ_castSucc]
      rw [add_assoc]
      congr 1

 theorem finiteDoobMean_full_eq
    (p X : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    finiteDoobMean p X e (Fin.last (Fintype.card V)) ω = X ω := by
  apply finiteDoobValue_eq_of_constant_on_prefix
  · exact (prefixMass_pos p hp e (Fin.last _) _).ne'
  · intro η hpre
    congr 1
    funext v
    let i : Fin (Fintype.card V) := e.symm v
    have hi := hpre i
    change ω (e i) = η (e i) at hi
    simpa [i] using hi.symm

 theorem finiteDoob_sq_expectation_total
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) :
    (∑ η, p η * X η ^ 2) =
      (∑ η, p η * X η) ^ 2 +
      ∑ k : Fin (Fintype.card V), ∑ η, p η *
        (finiteDoobIncrement p X e k η) ^ 2 := by
  have h := finiteDoob_sq_expectation_prefix p hp hnorm X e
    (Fintype.card V) (by rfl)
  rw [show (⟨Fintype.card V, Nat.lt_succ_self _⟩ : Fin (Fintype.card V + 1)) =
      Fin.last (Fintype.card V) by rfl] at h
  rw [Finset.sum_congr rfl (fun η _ => by rw [finiteDoobMean_full_eq p X hp e η])] at h
  have hzero (η : BernoulliAssignment V) : finiteDoobMean p X e 0 η =
      ∑ ξ, p ξ * X ξ := finiteDoobMean_zero_of_normalized p X e η hnorm
  have hzero_sum : (∑ η, p η * (finiteDoobMean p X e 0 η) ^ 2) =
      (∑ ξ, p ξ * X ξ) ^ 2 := by
    rw [show (fun η => p η * (finiteDoobMean p X e 0 η) ^ 2) =
        (fun η => p η * (∑ ξ, p ξ * X ξ) ^ 2) by
      funext η
      rw [hzero η]]
    rw [← Finset.sum_mul, hnorm]
    ring
  rw [hzero_sum] at h
  exact h


 theorem generatedCenteredSecond_eq_hardCoreVariance_of_fiberMass
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∑ ω, (generatedCountLaw hG R z hz).probability ω *
      (generatedCountReal hG R ω - (Forest.hardCoreLaw G z hz).mean) ^ 2 =
      (Forest.hardCoreLaw G z hz).variance := by
  have hpush := exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz
  rw [show generatedCountReal hG R = fun ω =>
      hardCoreCountReal (generatedIndependentSet hG R ω) by
    funext ω
    rfl]
  simpa [Forest.FiniteLatticeLaw.variance, hardCoreCountReal] using
    generatedExpectation_eq_hardCoreExpectation hG R z hz hpush
      (fun s => (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 2)

 theorem finiteDoobMean_zero_eq_expectation
    (p : BernoulliAssignment V → ℝ)
    (X : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V)
    (hnorm : ∑ η, p η = 1) :
    finiteDoobMean p X e ⟨0, Nat.zero_lt_succ _⟩ ω =
      ∑ η, p η * X η := by
  exact finiteDoobMean_zero_of_normalized p X e ω hnorm

 theorem finiteDoobMean_increment_sq_zero_eq
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2)
      (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω =
    ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2 := by
  exact finiteDoobMean_zero_eq_expectation _ _ _ _
    (hardCoreBernoulliSeedLaw R z hz).probability_sum


 theorem finiteDoobIncrement_sq_expectation_eq_availability_energy
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) :
    ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2 =
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)) *
      rootedEnergyAt R z hz (parentFirstEquiv R k) := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  let Y : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobIncrement μ (fun ξ => generatedCountReal hG R ξ)
      (parentFirstEquiv R) k η) ^ 2
  let E : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k) *
      rootedEnergyAt R z hz (parentFirstEquiv R k)
  let ω₀ : BernoulliAssignment V := fun _ => false
  have hμpos : ∀ η, 0 < μ η := by
    intro η
    dsimp [μ]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hcond : ∀ η, finiteDoobMean μ Y (parentFirstEquiv R) k.castSucc η =
      E η := by
    intro η
    exact finiteDoobMean_increment_sq_current hG R z hz k η
  have htowerY := finiteDoobMean_tower_zero μ hμpos
    (hardCoreBernoulliSeedLaw R z hz).probability_sum
    Y (parentFirstEquiv R) k.castSucc ω₀
  have hzero : finiteDoobMean μ Y (parentFirstEquiv R) 0 ω₀ =
      finiteDoobMean μ E (parentFirstEquiv R) 0 ω₀ := by
    change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ =
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀
    rw [← htowerY]
    rw [show (fun η => finiteDoobMean μ Y (parentFirstEquiv R) k.castSucc η) =
        E by
      funext η
      exact hcond η]
  change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ =
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ at hzero
  rw [finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum,
    finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum] at hzero
  dsimp [μ, Y, E] at hzero
  calc
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2) =
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedAvailabilityReal R η (parentFirstEquiv R k) *
          rootedEnergyAt R z hz (parentFirstEquiv R k)) := hzero
    _ = (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)) *
      rootedEnergyAt R z hz (parentFirstEquiv R k) := by
      rw [show (fun η => (hardCoreBernoulliSeedLaw R z hz).probability η *
          (generatedAvailabilityReal R η (parentFirstEquiv R k) *
            rootedEnergyAt R z hz (parentFirstEquiv R k))) =
        (fun η => ((hardCoreBernoulliSeedLaw R z hz).probability η *
          generatedAvailabilityReal R η (parentFirstEquiv R k)) *
            rootedEnergyAt R z hz (parentFirstEquiv R k)) by
          funext η; ring]
      rw [Finset.sum_mul]


 theorem finiteDoobMean_increment_fourth_current_le
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) (ω : BernoulliAssignment V) :
    finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
      (fun η => (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4)
      (parentFirstEquiv R) k.castSucc ω ≤
    generatedAvailabilityReal R ω (parentFirstEquiv R k) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4) := by
  let p : ℝ := rootedOccupationProbabilityAt R z (parentFirstEquiv R k)
  let q : ℝ := rootedVacancyProbabilityAt R z (parentFirstEquiv R k)
  let d : ℝ := rootedDisplacementAt R z hz (parentFirstEquiv R k)
  let A : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k)
  have hD (η : BernoulliAssignment V) :
      finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η =
      A η * (if η (parentFirstEquiv R k) then q * d else -p * d) := by
    have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)
    rw [show q = 1 - p by dsimp [q, p]; linarith [hpq]]
    simpa [A, p, d, generatedAvailabilityReal] using
      generatedCountDoobIncrement_eq_available_exact hG R z hz k η
  have hfun : (fun η => (finiteDoobIncrement
        (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) =
      (fun η => ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η) *
          (q ^ 4 * d ^ 4) +
        A η * (p ^ 4 * d ^ 4) -
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η) *
          (p ^ 4 * d ^ 4)) := by
    funext η
    rw [hD]
    unfold A generatedAvailabilityReal
    cases η (parentFirstEquiv R k) <;>
      cases generatedAvailable R η (parentFirstEquiv R k) <;> norm_num <;> ring
  rw [hfun, finiteDoobMean_sub, finiteDoobMean_add]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * (q ^ 4 * d ^ 4)) =
      (fun η => (q ^ 4 * d ^ 4) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [show (fun η => A η * (p ^ 4 * d ^ 4)) =
      (fun η => (p ^ 4 * d ^ 4) * A η) by funext η; ring]
  rw [show (fun η =>
      (if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η * (p ^ 4 * d ^ 4)) =
      (fun η => (p ^ 4 * d ^ 4) *
        ((if η (parentFirstEquiv R k) then (1 : ℝ) else 0) * A η)) by
      funext η; ring]
  rw [finiteDoobMean_const_mul, finiteDoobMean_const_mul,
    finiteDoobMean_const_mul]
  rw [finiteDoobMean_generatedAvailability_mul_seed R z hz k ω,
    finiteDoobMean_generatedAvailability R z hz k ω]
  have hp0 : 0 ≤ p := by dsimp [p]; exact (rootedOccupationProbabilityAt_pos R z hz _).le
  have hp1 : p ≤ 1 := by dsimp [p]; exact rootedOccupationProbabilityAt_le_one R z hz _
  have hqdef : q = 1 - p := by
    dsimp [q, p]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)]
  have hcoeff := bernoulli_fourth_coefficient_le_second p hp0 hp1
  rw [← hqdef] at hcoeff
  unfold generatedAvailabilityReal
  cases hav : generatedAvailable R ω (parentFirstEquiv R k)
  · norm_num
  · simp only [ite_true, one_mul]
    dsimp [p, q, d] at hcoeff ⊢
    have hd4 : 0 ≤ rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4 := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hcoeff hd4
    have hpq := rootedOccupationProbabilityAt_add_vacancy R z hz (parentFirstEquiv R k)
    rw [show rootedVacancyProbabilityAt R z (parentFirstEquiv R k) =
      1 - rootedOccupationProbabilityAt R z (parentFirstEquiv R k) by linarith [hpq]]
      at hscaled ⊢
    ring_nf at hscaled ⊢
    exact hscaled


 theorem finiteDoobIncrement_fourth_expectation_le_availability_fourth_energy
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (k : Fin (Fintype.card V)) :
    ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4 ≤
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4) := by
  let μ := (hardCoreBernoulliSeedLaw R z hz).probability
  let Y : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobIncrement μ (fun ξ => generatedCountReal hG R ξ)
      (parentFirstEquiv R) k η) ^ 4
  let E : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4)
  let ω₀ : BernoulliAssignment V := fun _ => false
  have hμpos : ∀ η, 0 < μ η := by
    intro η
    dsimp [μ]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hcond : ∀ η, finiteDoobMean μ Y (parentFirstEquiv R) k.castSucc η ≤ E η := by
    intro η
    exact finiteDoobMean_increment_fourth_current_le hG R z hz k η
  have htowerY := finiteDoobMean_tower_zero μ hμpos
    (hardCoreBernoulliSeedLaw R z hz).probability_sum
    Y (parentFirstEquiv R) k.castSucc ω₀
  have hzero : finiteDoobMean μ Y (parentFirstEquiv R) 0 ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) 0 ω₀ := by
    change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀
    rw [← htowerY]
    rw [finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum,
      finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum]
    apply Finset.sum_le_sum
    intro η hη
    exact mul_le_mul_of_nonneg_left (hcond η)
      ((hardCoreBernoulliSeedLaw R z hz).probability_nonneg η)
  change finiteDoobMean μ Y (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ ≤
      finiteDoobMean μ E (parentFirstEquiv R) ⟨0, Nat.zero_lt_succ _⟩ ω₀ at hzero
  rw [finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum,
    finiteDoobMean_zero_eq_expectation _ _ _ _
      (hardCoreBernoulliSeedLaw R z hz).probability_sum] at hzero
  dsimp [μ, Y, E] at hzero
  calc
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) ≤
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedAvailabilityReal R η (parentFirstEquiv R k) *
          (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
            rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
            rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4)) := hzero
    _ = (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)) *
      (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
        rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
        rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4) := by
      rw [show (fun η => (hardCoreBernoulliSeedLaw R z hz).probability η *
          (generatedAvailabilityReal R η (parentFirstEquiv R k) *
            (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
              rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
              rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4))) =
        (fun η => ((hardCoreBernoulliSeedLaw R z hz).probability η *
          generatedAvailabilityReal R η (parentFirstEquiv R k)) *
            (rootedOccupationProbabilityAt R z (parentFirstEquiv R k) *
              rootedVacancyProbabilityAt R z (parentFirstEquiv R k) *
              rootedDisplacementAt R z hz (parentFirstEquiv R k) ^ 4)) by
          funext η; ring]
      rw [Finset.sum_mul]


 theorem sum_increment_sq_expectation_eq_hardCoreVariance
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∑ k : Fin (Fintype.card V),
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 2 =
      (Forest.hardCoreLaw G z hz).variance := by
  let p := (hardCoreBernoulliSeedLaw R z hz).probability
  let X := fun ξ => generatedCountReal hG R ξ
  have hp : ∀ η, 0 < p η := by
    intro η
    dsimp [p]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hiso := finiteDoob_sq_expectation_total p hp
    (hardCoreBernoulliSeedLaw R z hz).probability_sum X (parentFirstEquiv R)
  have hmean : (∑ η, p η * X η) = (Forest.hardCoreLaw G z hz).mean := by
    exact generatedCount_mean_eq_hardCore_mean_of_fiberMass hG R z hz
  have hsecond : (∑ η, p η * (X η - (Forest.hardCoreLaw G z hz).mean) ^ 2) =
      (Forest.hardCoreLaw G z hz).variance :=
    generatedCenteredSecond_eq_hardCoreVariance_of_fiberMass hG R z hz
  dsimp [p, X] at hiso hmean hsecond ⊢
  have hcenter :
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedCountReal hG R η - (Forest.hardCoreLaw G z hz).mean) ^ 2) =
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedCountReal hG R η) ^ 2) -
        (Forest.hardCoreLaw G z hz).mean ^ 2 := by
    rw [show (fun η => (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedCountReal hG R η - (Forest.hardCoreLaw G z hz).mean) ^ 2) =
      (fun η => (hardCoreBernoulliSeedLaw R z hz).probability η *
          (generatedCountReal hG R η) ^ 2 -
        2 * (Forest.hardCoreLaw G z hz).mean *
          ((hardCoreBernoulliSeedLaw R z hz).probability η * generatedCountReal hG R η) +
        (hardCoreBernoulliSeedLaw R z hz).probability η *
          (Forest.hardCoreLaw G z hz).mean ^ 2) by funext η; ring]
    rw [show (fun η =>
        (hardCoreBernoulliSeedLaw R z hz).probability η *
          (generatedCountReal hG R η) ^ 2 -
        2 * (Forest.hardCoreLaw G z hz).mean *
          ((hardCoreBernoulliSeedLaw R z hz).probability η * generatedCountReal hG R η) +
        (hardCoreBernoulliSeedLaw R z hz).probability η *
          (Forest.hardCoreLaw G z hz).mean ^ 2) =
      (fun η => ((hardCoreBernoulliSeedLaw R z hz).probability η *
          (generatedCountReal hG R η) ^ 2 -
        2 * (Forest.hardCoreLaw G z hz).mean *
          ((hardCoreBernoulliSeedLaw R z hz).probability η * generatedCountReal hG R η)) +
        (hardCoreBernoulliSeedLaw R z hz).probability η *
          (Forest.hardCoreLaw G z hz).mean ^ 2) by funext η; ring]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [show (fun x => 2 * (Forest.hardCoreLaw G z hz).mean *
        ((hardCoreBernoulliSeedLaw R z hz).probability x * generatedCountReal hG R x)) =
      (fun x => (2 * (Forest.hardCoreLaw G z hz).mean) *
        ((hardCoreBernoulliSeedLaw R z hz).probability x * generatedCountReal hG R x)) by rfl]
    rw [← Finset.mul_sum]
    rw [show (fun x => (hardCoreBernoulliSeedLaw R z hz).probability x *
        (Forest.hardCoreLaw G z hz).mean ^ 2) =
      (fun x => (hardCoreBernoulliSeedLaw R z hz).probability x *
        ((Forest.hardCoreLaw G z hz).mean ^ 2)) by rfl]
    rw [← Finset.sum_mul]
    rw [(hardCoreBernoulliSeedLaw R z hz).probability_sum, hmean]
    ring
  rw [hmean] at hiso
  rw [hsecond] at hcenter
  linarith [hiso, hcenter]

 theorem availability_energy_sum_eq_hardCoreVariance
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∑ k : Fin (Fintype.card V),
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        generatedAvailabilityReal R η (parentFirstEquiv R k)) *
        rootedEnergyAt R z hz (parentFirstEquiv R k) =
      (Forest.hardCoreLaw G z hz).variance := by
  rw [← sum_increment_sq_expectation_eq_hardCoreVariance hG R z hz]
  apply Finset.sum_congr rfl
  intro k hk
  exact (finiteDoobIncrement_sq_expectation_eq_availability_energy hG R z hz k).symm


 theorem rootedFourthEnergyAt_le_four_mul_energy_of_abs_le_two
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V)
    (hsmall : |rootedDisplacementAt R z hz u| ≤ 2) :
    rootedOccupationProbabilityAt R z u *
      rootedVacancyProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 4 ≤
      4 * rootedEnergyAt R z hz u := by
  have hd0 : 0 ≤ |rootedDisplacementAt R z hz u| := abs_nonneg _
  have hd2 : rootedDisplacementAt R z hz u ^ 2 ≤ 4 := by
    rw [← sq_abs]
    nlinarith
  have hb : 0 ≤ rootedOccupationProbabilityAt R z u :=
    (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq : 0 ≤ rootedVacancyProbabilityAt R z u := by
    unfold rootedVacancyProbabilityAt
    exact (div_pos (rootedQAt_pos R z hz u)
      (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
          exact add_pos (rootedQAt_pos R z hz u) (rootedAAt_pos R z hz u))).le
  unfold rootedEnergyAt
  nlinarith [mul_nonneg (mul_nonneg hb hq)
    (sq_nonneg (rootedDisplacementAt R z hz u))]

 theorem children_pairwiseDisjoint_global
    (hG : G.IsAcyclic) (R : ComponentRooting G) :
    (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint
      (fun u => R.children (G := G) u) := by
  intro u hu v hv huv
  change Disjoint (R.children (G := G) u) (R.children (G := G) v)
  rw [Finset.disjoint_left]
  intro x hxu hxv
  apply huv
  exact R.isChild_unique (G := G) hG
    ((R.mem_children (G := G) u x).mp hxu)
    ((R.mem_children (G := G) v x).mp hxv)

 theorem sum_child_energy_le_total
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    (∑ u, ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ≤
      ∑ v, rootedEnergyAt R z hz v := by
  classical
  have hdis := children_pairwiseDisjoint_global (G := G) hG R
  rw [← Finset.sum_biUnion hdis]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro v hv hnot
  unfold rootedEnergyAt
  have hb := (rootedOccupationProbabilityAt_pos R z hz v).le
  have hq : 0 ≤ rootedVacancyProbabilityAt R z v := by
    unfold rootedVacancyProbabilityAt
    exact (div_pos (rootedQAt_pos R z hz v)
      (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
          exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
  positivity

 theorem sum_sq_child_energy_le_total_sq
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    (∑ u, (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ^ 2) ≤
      (∑ v, rootedEnergyAt R z hz v) ^ 2 := by
  let A : ℝ := ∑ v, rootedEnergyAt R z hz v
  let s : V → ℝ := fun u => ∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v
  have he (v : V) : 0 ≤ rootedEnergyAt R z hz v := by
    unfold rootedEnergyAt
    have hb := (rootedOccupationProbabilityAt_pos R z hz v).le
    have hq : 0 ≤ rootedVacancyProbabilityAt R z v := by
      unfold rootedVacancyProbabilityAt
      exact (div_pos (rootedQAt_pos R z hz v)
        (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
            exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
    positivity
  have hA : 0 ≤ A := by dsimp [A]; exact Finset.sum_nonneg fun v hv => he v
  have hs (u : V) : 0 ≤ s u := by
    dsimp [s]
    exact Finset.sum_nonneg fun v hv => he v
  have hsA (u : V) : s u ≤ A := by
    dsimp [s, A]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => he _)
  have hsum : ∑ u, s u ≤ A := by
    simpa [s, A] using sum_child_energy_le_total (G := G) hG R z hz
  calc
    (∑ u, (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ^ 2) =
        ∑ u, s u ^ 2 := by rfl
    _ ≤ ∑ u, A * s u := by
      apply Finset.sum_le_sum
      intro u hu
      nlinarith [hs u, hsA u]
    _ = A * ∑ u, s u := by rw [Finset.mul_sum]
    _ ≤ A * A := mul_le_mul_of_nonneg_left hsum hA
    _ = (∑ v, rootedEnergyAt R z hz v) ^ 2 := by simp [A, pow_two]

 theorem sum_rooted_fourth_energy_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ u, rootedOccupationProbabilityAt R z u *
      rootedVacancyProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 4) ≤
      4 * (∑ u, rootedEnergyAt R z hz u) +
      actualFourthChildConstant Z * (∑ u, rootedEnergyAt R z hz u) ^ 2 := by
  calc
    (∑ u, rootedOccupationProbabilityAt R z u *
      rootedVacancyProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 4) ≤
      ∑ u, (4 * rootedEnergyAt R z hz u +
        actualFourthChildConstant Z *
          (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ^ 2) := by
      apply Finset.sum_le_sum
      intro u hu
      by_cases hsmall : |rootedDisplacementAt R z hz u| ≤ 2
      · have h := rootedFourthEnergyAt_le_four_mul_energy_of_abs_le_two R z hz u hsmall
        have hC : 0 ≤ actualFourthChildConstant Z := by
          dsimp [actualFourthChildConstant]
          have hZ : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
          positivity
        have hs : 0 ≤ (∑ v ∈ R.children (G := G) u,
          rootedEnergyAt R z hz v) ^ 2 := sq_nonneg _
        nlinarith [mul_nonneg hC hs]
      · have hlarge : 2 < |rootedDisplacementAt R z hz u| := lt_of_not_ge hsmall
        have h := rootedFourthEnergyAt_le_of_two_lt_abs_displacement
          (G := G) hG R z Z hz hzZ u hlarge
        have he : 0 ≤ rootedEnergyAt R z hz u := by
          unfold rootedEnergyAt
          have hb := (rootedOccupationProbabilityAt_pos R z hz u).le
          have hq : 0 ≤ rootedVacancyProbabilityAt R z u := by
            unfold rootedVacancyProbabilityAt
            exact (div_pos (rootedQAt_pos R z hz u)
              (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
                  exact add_pos (rootedQAt_pos R z hz u) (rootedAAt_pos R z hz u))).le
          positivity
        nlinarith
    _ = 4 * (∑ u, rootedEnergyAt R z hz u) +
        actualFourthChildConstant Z *
          ∑ u, (∑ v ∈ R.children (G := G) u, rootedEnergyAt R z hz v) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * (∑ u, rootedEnergyAt R z hz u) +
        actualFourthChildConstant Z * (∑ u, rootedEnergyAt R z hz u) ^ 2 := by
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left
      · exact sum_sq_child_energy_le_total_sq (G := G) hG R z hz
      · dsimp [actualFourthChildConstant]
        have hZ : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
        positivity

/-- Under the product seed law, occupation at a vertex factors as its local
Bernoulli occupation probability times generated availability. This is the
expectation-level availability bridge; it deliberately avoids identifying the
generated state pointwise with a separate canonical recovery state. -/
theorem generatedOccupation_expectation_eq_probability_mul_availability
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) :
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (if generatedOccupation R η u then (1 : ℝ) else 0)) =
      rootedOccupationProbabilityAt R z u *
        (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          generatedAvailabilityReal R η u) := by
  rw [Finset.sum_congr rfl (fun η _ => by
    change (hardCoreBernoulliSeedLaw R z hz).probability η *
        (if generatedOccupation R η u then (1 : ℝ) else 0) = _
    rw [show (if generatedOccupation R η u then (1 : ℝ) else 0) =
        (if η u then (1 : ℝ) else 0) * generatedAvailabilityReal R η u by
      rw [generatedOccupation_eq_seed_and_available]
      unfold generatedAvailabilityReal
      cases η u <;> cases generatedAvailable R η u <;> norm_num])]
  let p : V → ℝ := fun v => rootedOccupationProbabilityAt R z v
  change (∑ η, bernoulliWeight p η * ((if η u then (1 : ℝ) else 0) *
    generatedAvailabilityReal R η u)) = p u *
      ∑ η, bernoulliWeight p η * generatedAvailabilityReal R η u
  have h := finiteDoobMean_bernoulli_future_seed_mul p
    (rootedOccupationProbabilityAt_pos R z hz)
    (rootedOccupationProbabilityAt_lt_one R z hz)
    (fun η => generatedAvailabilityReal R η u)
    (parentFirstEquiv R) (0 : Fin (Fintype.card V + 1)) (fun _ => false) u
    (Nat.zero_le _) (fun η => by
      change (if generatedAvailable R (Function.update η u true) u then (1 : ℝ) else 0) =
        (if generatedAvailable R (Function.update η u false) u then 1 else 0)
      rw [generatedAvailable_update_self, generatedAvailable_update_self])
  rw [finiteDoobMean_zero_of_normalized _ _ _ _ (sum_bernoulliWeight p),
    finiteDoobMean_zero_of_normalized _ _ _ _ (sum_bernoulliWeight p)] at h
  simpa only [ite_mul, one_mul, zero_mul] using h

/-- Generated availability has a uniform expectation lower bound under bounded
activity. For a root it is identically one; for a nonroot it is the vacancy
indicator of its unique parent, whose occupation probability is at most
`Z / (1 + Z)`. -/
theorem generatedAvailability_expectation_lower_bound
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    1 / (1 + Z) ≤
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        generatedAvailabilityReal R η u := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · have hA (η : BernoulliAssignment V) : generatedAvailabilityReal R η u = 1 := by
      unfold generatedAvailabilityReal generatedAvailable
      rw [if_pos]
      rw [decide_eq_true_eq]
      intro v hv
      exact (R.not_isChild_of_eq_root (G := G) hu hv).elim
    rw [Finset.sum_congr rfl (fun η _ => by rw [hA η])]
    have hnorm := (hardCoreBernoulliSeedLaw R z hz).probability_sum
    have hsum : (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η * 1) = 1 := by
      simpa using hnorm
    rw [hsum]
    have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
    exact (div_le_one (by linarith)).2 (by linarith)
  · obtain ⟨v, hvu⟩ := R.exists_isChild_of_ne_root (G := G) hu
    have hA (η : BernoulliAssignment V) :
        generatedAvailabilityReal R η u =
          1 - (if generatedOccupation R η v then (1 : ℝ) else 0) := by
      unfold generatedAvailabilityReal
      rw [generatedAvailable_eq_not_occupation_of_isChild hG R hvu]
      cases generatedOccupation R η v <;> norm_num
    rw [Finset.sum_congr rfl (fun η _ => by rw [hA η])]
    have hrewrite :
        (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (1 - (if generatedOccupation R η v then (1 : ℝ) else 0))) =
        1 - ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (if generatedOccupation R η v then (1 : ℝ) else 0) := by
      calc
        _ = (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η) -
            ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
              (if generatedOccupation R η v then (1 : ℝ) else 0) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro η hη
                ring
        _ = _ := by rw [(hardCoreBernoulliSeedLaw R z hz).probability_sum]
    rw [hrewrite]
    have hocc_le :
        (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (if generatedOccupation R η v then (1 : ℝ) else 0)) ≤ Z / (1 + Z) := by
      calc
        _ = rootedOccupationProbabilityAt R z v *
            (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
              generatedAvailabilityReal R η v) :=
          generatedOccupation_expectation_eq_probability_mul_availability
            hG R z hz v
        _ ≤ Z / (1 + Z) := by
          have hAsum : (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
              generatedAvailabilityReal R η v) ≤ 1 := by
            calc
              _ ≤ ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η * 1 := by
                apply Finset.sum_le_sum
                intro η hη
                apply mul_le_mul_of_nonneg_left _
                  ((hardCoreBernoulliSeedLaw R z hz).probability_nonneg η)
                unfold generatedAvailabilityReal
                split <;> norm_num
              _ = 1 := by rw [← Finset.sum_mul,
                (hardCoreBernoulliSeedLaw R z hz).probability_sum]; ring
          have hb := rootedOccupationProbabilityAt_le_ceiling_ratio hG R z Z hz hzZ v
          have hp0 := (rootedOccupationProbabilityAt_pos R z hz v).le
          nlinarith
    have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
    have hid : 1 - Z / (1 + Z) = 1 / (1 + Z) := by field_simp; ring
    rw [← hid]
    linarith

 theorem finiteDoobMean_mono_of_pos
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (f g : BernoulliAssignment V → ℝ) (hfg : ∀ η, f η ≤ g η)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p f e m ω ≤ finiteDoobMean p g e m ω := by
  have hmasspos := prefixMass_pos p hp e m ω
  rw [finiteDoobMean, dif_neg hmasspos.ne', finiteDoobMean, dif_neg hmasspos.ne']
  apply (div_le_div_iff_of_pos_right hmasspos).2
  unfold prefixWeighted
  apply Finset.sum_le_sum
  intro η hη
  by_cases hs : samePrefix e m ω η
  · rw [if_pos hs, if_pos hs]
    exact mul_le_mul_of_nonneg_left (hfg η) (hp η).le
  · rw [if_neg hs, if_neg hs]

 theorem finiteDoobMean_centered_fourth_step_current
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => (finiteDoobMean p X e k.succ η - c) ^ 4)
      e k.castSucc ω ≤
    (finiteDoobMean p X e k.castSucc ω - c) ^ 4 +
      8 * (finiteDoobMean p X e k.castSucc ω - c) ^ 2 *
        finiteDoobMean p (fun η => (finiteDoobIncrement p X e k η) ^ 2)
          e k.castSucc ω +
      3 * finiteDoobMean p (fun η => (finiteDoobIncrement p X e k η) ^ 4)
          e k.castSucc ω := by
  let M : BernoulliAssignment V → ℝ := fun η => finiteDoobMean p X e k.castSucc η - c
  let D : BernoulliAssignment V → ℝ := fun η => finiteDoobIncrement p X e k η
  have hsucc (η : BernoulliAssignment V) :
      finiteDoobMean p X e k.succ η - c = M η + D η := by
    dsimp [M, D, finiteDoobIncrement]
    have hs : (⟨k.1 + 1, by omega⟩ : Fin (Fintype.card V + 1)) = k.succ := by ext; simp
    have hc : (⟨k.1, by omega⟩ : Fin (Fintype.card V + 1)) = k.castSucc := by ext; simp
    rw [hs, hc]
    ring
  have hpoint (η : BernoulliAssignment V) :
      (M η + D η) ^ 4 ≤
        M η ^ 4 + 4 * M η ^ 3 * D η +
          8 * M η ^ 2 * D η ^ 2 + 3 * D η ^ 4 := by
    have hcubic : 4 * M η * D η ^ 3 ≤
        2 * M η ^ 2 * D η ^ 2 + 2 * D η ^ 4 := by
      nlinarith [sq_nonneg (M η * D η - D η ^ 2)]
    nlinarith
  rw [show (fun η => (finiteDoobMean p X e k.succ η - c) ^ 4) =
      (fun η => (M η + D η) ^ 4) by funext η; rw [hsucc η]]
  calc
    finiteDoobMean p (fun η => (M η + D η) ^ 4) e k.castSucc ω ≤
        finiteDoobMean p (fun η => M η ^ 4 + 4 * M η ^ 3 * D η +
          8 * M η ^ 2 * D η ^ 2 + 3 * D η ^ 4) e k.castSucc ω :=
      finiteDoobMean_mono_of_pos p hp _ _ hpoint e k.castSucc ω
    _ = _ := by
      rw [finiteDoobMean_add, finiteDoobMean_add, finiteDoobMean_add]
      have hM : ∀ η, samePrefix e k.castSucc ω η → M η = M ω := by
        intro η hpre
        dsimp [M]
        rw [finiteDoobMean_eq_of_samePrefix p X e ω η hpre]
      have hM4 : finiteDoobMean p (fun η => M η ^ 4) e k.castSucc ω = M ω ^ 4 := by
        apply finiteDoobValue_eq_of_constant_on_prefix
        · exact (prefixMass_pos p hp e k.castSucc _).ne'
        · intro η hpre
          rw [hM η hpre]
      have hcross : finiteDoobMean p (fun η => 4 * M η ^ 3 * D η)
          e k.castSucc ω = 0 := by
        rw [finiteDoobMean_measurable_mul p hp (fun η => 4 * M η ^ 3) D e k.castSucc ω]
        · rw [finiteDoobIncrement_centered_current p hp X e k ω]
          ring
        · intro η hpre
          rw [hM η hpre]
      have hsq : finiteDoobMean p (fun η => 8 * M η ^ 2 * D η ^ 2)
          e k.castSucc ω = 8 * M ω ^ 2 * finiteDoobMean p (fun η => D η ^ 2)
            e k.castSucc ω := by
        rw [finiteDoobMean_measurable_mul p hp (fun η => 8 * M η ^ 2)
          (fun η => D η ^ 2) e k.castSucc ω]
        · intro η hpre
          rw [hM η hpre]
      have hfour : finiteDoobMean p (fun η => 3 * D η ^ 4) e k.castSucc ω =
          3 * finiteDoobMean p (fun η => D η ^ 4) e k.castSucc ω := by
        exact finiteDoobMean_const_mul p 3 (fun η => D η ^ 4) e k.castSucc ω
      rw [hM4, hcross, hsq, hfour]
      dsimp [M, D]
      ring

 theorem rootedEnergyAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (v : V) :
    0 ≤ rootedEnergyAt R z hz v := by
  unfold rootedEnergyAt
  have hb := (rootedOccupationProbabilityAt_pos R z hz v).le
  have hq : 0 ≤ rootedVacancyProbabilityAt R z v := by
    unfold rootedVacancyProbabilityAt
    exact (div_pos (rootedQAt_pos R z hz v)
      (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
          exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
  positivity

 theorem sum_rootedEnergy_le_one_add_Z_mul_variance
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ v, rootedEnergyAt R z hz v) ≤
      (1 + Z) * (Forest.hardCoreLaw G z hz).variance := by
  have hden : 0 < 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  let w : Fin (Fintype.card V) → ℝ := fun k =>
    ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)
  have hw (k : Fin (Fintype.card V)) : 1 / (1 + Z) ≤ w k := by
    exact generatedAvailability_expectation_lower_bound hG R z Z hz hzZ _
  have hscale (k : Fin (Fintype.card V)) : 1 ≤ (1 + Z) * w k := by
    have h := (div_le_iff₀ hden).mp (hw k)
    nlinarith
  have hterm (k : Fin (Fintype.card V)) :
      rootedEnergyAt R z hz (parentFirstEquiv R k) ≤
        (1 + Z) * (w k * rootedEnergyAt R z hz (parentFirstEquiv R k)) := by
    have he := rootedEnergyAt_nonneg R z hz (parentFirstEquiv R k)
    nlinarith [mul_nonneg (sub_nonneg.mpr (hscale k)) he]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hterm k)
  rw [← Finset.mul_sum] at hsum
  have hv := availability_energy_sum_eq_hardCoreVariance hG R z hz
  change (∑ k, w k * rootedEnergyAt R z hz (parentFirstEquiv R k)) = _ at hv
  rw [hv] at hsum
  have hreindex : (∑ k : Fin (Fintype.card V),
      rootedEnergyAt R z hz (parentFirstEquiv R k)) =
      ∑ v : V, rootedEnergyAt R z hz v := by
    exact Equiv.sum_comp (parentFirstEquiv R) (fun v => rootedEnergyAt R z hz v)
  rwa [hreindex] at hsum

 theorem sum_increment_fourth_expectation_le_variance_bound
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ k : Fin (Fintype.card V),
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) ≤
      4 * (1 + Z) * (Forest.hardCoreLaw G z hz).variance +
        actualFourthChildConstant Z * (1 + Z) ^ 2 *
          (Forest.hardCoreLaw G z hz).variance ^ 2 := by
  let A : ℝ := ∑ v, rootedEnergyAt R z hz v
  let F : V → ℝ := fun v =>
    rootedOccupationProbabilityAt R z v * rootedVacancyProbabilityAt R z v *
      rootedDisplacementAt R z hz v ^ 4
  let w : Fin (Fintype.card V) → ℝ := fun k =>
    ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      generatedAvailabilityReal R η (parentFirstEquiv R k)
  have hF0 (v : V) : 0 ≤ F v := by
    dsimp [F]
    have hb := (rootedOccupationProbabilityAt_pos R z hz v).le
    have hq : 0 ≤ rootedVacancyProbabilityAt R z v := by
      unfold rootedVacancyProbabilityAt
      exact (div_pos (rootedQAt_pos R z hz v)
        (by rw [rootedPAt_eq_rootedQAt_add_rootedAAt]
            exact add_pos (rootedQAt_pos R z hz v) (rootedAAt_pos R z hz v))).le
    positivity
  have hw1 (k : Fin (Fintype.card V)) : w k ≤ 1 := by
    calc
      w k ≤ ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η * 1 := by
        dsimp [w]
        apply Finset.sum_le_sum
        intro η hη
        apply mul_le_mul_of_nonneg_left _
          ((hardCoreBernoulliSeedLaw R z hz).probability_nonneg η)
        unfold generatedAvailabilityReal
        split <;> norm_num
      _ = 1 := by rw [← Finset.sum_mul,
        (hardCoreBernoulliSeedLaw R z hz).probability_sum]; ring
  have hinc : (∑ k : Fin (Fintype.card V),
      ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) ≤
      ∑ k : Fin (Fintype.card V), F (parentFirstEquiv R k) := by
    apply Finset.sum_le_sum
    intro k hk
    calc
      _ ≤ w k * F (parentFirstEquiv R k) := by
        exact finiteDoobIncrement_fourth_expectation_le_availability_fourth_energy
          hG R z hz k
      _ ≤ F (parentFirstEquiv R k) := by
        nlinarith [hF0 (parentFirstEquiv R k),
          mul_nonneg (sub_nonneg.mpr (hw1 k)) (hF0 (parentFirstEquiv R k))]
  have hreindex : (∑ k : Fin (Fintype.card V), F (parentFirstEquiv R k)) =
      ∑ v : V, F v := Equiv.sum_comp (parentFirstEquiv R) F
  rw [hreindex] at hinc
  have hfour : (∑ v : V, F v) ≤ 4 * A + actualFourthChildConstant Z * A ^ 2 := by
    exact sum_rooted_fourth_energy_le hG R z Z hz hzZ
  have hA : A ≤ (1 + Z) * (Forest.hardCoreLaw G z hz).variance := by
    exact sum_rootedEnergy_le_one_add_Z_mul_variance hG R z Z hz hzZ
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg (fun v hv => rootedEnergyAt_nonneg R z hz v)
  have hV0 : 0 ≤ (Forest.hardCoreLaw G z hz).variance :=
    (Forest.hardCoreLaw G z hz).variance_nonneg
  have hL0 : 0 ≤ 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  have hC0 : 0 ≤ actualFourthChildConstant Z := by
    dsimp [actualFourthChildConstant]
    have : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
    positivity
  have hAsq : A ^ 2 ≤ (1 + Z) ^ 2 * (Forest.hardCoreLaw G z hz).variance ^ 2 := by
    nlinarith
  calc
    _ ≤ ∑ v : V, F v := hinc
    _ ≤ 4 * A + actualFourthChildConstant Z * A ^ 2 := hfour
    _ ≤ 4 * ((1 + Z) * (Forest.hardCoreLaw G z hz).variance) +
        actualFourthChildConstant Z * ((1 + Z) ^ 2 *
          (Forest.hardCoreLaw G z hz).variance ^ 2) := by
      gcongr
    _ = _ := by ring


 theorem finiteDoobMean_constant
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (c : ℝ) (e : Fin (Fintype.card V) ≃ V)
    (m : Fin (Fintype.card V + 1)) (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun _ => c) e m ω = c := by
  classical
  rw [finiteDoobMean]
  rw [dif_neg (prefixMass_pos p hp e m ω).ne']
  unfold prefixWeighted prefixMass
  rw [show (∑ x, if samePrefix e m ω x then p x * c else 0) =
      (∑ x, if samePrefix e m ω x then p x else 0) * c by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro η hη
    by_cases hs : samePrefix e m ω η <;> simp [hs]]
  exact mul_div_cancel_left₀ c (prefixMass_pos p hp e m ω).ne'

 theorem finiteDoobMean_sub_const
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (f : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => f η - c) e m ω = finiteDoobMean p f e m ω - c := by
  rw [finiteDoobMean_sub, finiteDoobMean_constant p hp]

 theorem finiteDoobMean_centered_full_eq
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => X η - c) e (Fin.last (Fintype.card V)) ω =
      X ω - c := by
  exact finiteDoobMean_full_eq p (fun η => X η - c) hp e ω

 theorem finiteDoobMean_centered_zero_eq_zero
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (hc : ∑ η, p η * X η = c)
    (e : Fin (Fintype.card V) ≃ V) (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => X η - c) e 0 ω = 0 := by
  rw [finiteDoobMean_sub_const p hp]
  rw [finiteDoobMean_zero_of_normalized p X e ω hnorm, hc]
  ring

 theorem finiteDoobMean_centered_eq_sub
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p (fun η => X η - c) e m ω = finiteDoobMean p X e m ω - c :=
  finiteDoobMean_sub_const p hp X c e m ω

 theorem finiteDoob_expectation_eq
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1)) :
    ∑ η, p η * finiteDoobMean p f e m η = ∑ η, p η * f η := by
  let ω₀ : BernoulliAssignment V := fun _ => false
  have ht := finiteDoobMean_tower_zero p hp hnorm f e m ω₀
  change finiteDoobMean p (fun η => finiteDoobMean p f e m η) e 0 ω₀ =
    finiteDoobMean p f e 0 ω₀ at ht
  rw [finiteDoobMean_zero_of_normalized p _ e ω₀ hnorm,
    finiteDoobMean_zero_of_normalized p f e ω₀ hnorm] at ht
  exact ht

 theorem finiteDoobMean_sq_le_mean_sq
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    (finiteDoobMean p f e m ω) ^ 2 ≤
      finiteDoobMean p (fun η => (f η) ^ 2) e m ω := by
  classical
  have hmasspos := prefixMass_pos p hp e m ω
  rw [finiteDoobMean, dif_neg hmasspos.ne', finiteDoobMean, dif_neg hmasspos.ne']
  let r : BernoulliAssignment V → ℝ := fun η =>
    if samePrefix e m ω η then p η * f η else 0
  let a : BernoulliAssignment V → ℝ := fun η =>
    if samePrefix e m ω η then p η else 0
  let b : BernoulliAssignment V → ℝ := fun η =>
    if samePrefix e m ω η then p η * f η ^ 2 else 0
  have hcs : (∑ η, r η) ^ 2 ≤ (∑ η, a η) * ∑ η, b η := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro η hη
      dsimp [a]
      split
      · exact (hp η).le
      · norm_num
    · intro η hη
      dsimp [b]
      split
      · exact mul_nonneg (hp η).le (sq_nonneg (f η))
      · norm_num
    · intro η hη
      dsimp [r, a, b]
      split <;> ring
  change ((∑ η, r η) / ∑ η, a η) ^ 2 ≤ (∑ η, b η) / ∑ η, a η
  have hm : 0 < ∑ η, a η := by exact hmasspos
  calc
    ((∑ η, r η) / ∑ η, a η) ^ 2 =
        (∑ η, r η) ^ 2 / (∑ η, a η) ^ 2 := by rw [div_pow]
    _ ≤ ((∑ η, a η) * ∑ η, b η) / (∑ η, a η) ^ 2 := by
      exact div_le_div_of_nonneg_right hcs (sq_nonneg _)
    _ = (∑ η, b η) / ∑ η, a η := by field_simp


 theorem finiteDoob_centered_fourth_expectation_step
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V)) :
    (∑ η, p η * (finiteDoobMean p X e k.succ η - c) ^ 4) ≤
      (∑ η, p η * (finiteDoobMean p X e k.castSucc η - c) ^ 4) +
      8 * (∑ η, p η * ((finiteDoobMean p X e k.castSucc η - c) ^ 2 *
        finiteDoobMean p (fun ξ => (finiteDoobIncrement p X e k ξ) ^ 2)
          e k.castSucc η)) +
      3 * (∑ η, p η * (finiteDoobIncrement p X e k η) ^ 4) := by
  let A : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobMean p X e k.succ η - c) ^ 4
  let B : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobMean p X e k.castSucc η - c) ^ 4
  let C : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobMean p X e k.castSucc η - c) ^ 2 *
      finiteDoobMean p (fun ξ => (finiteDoobIncrement p X e k ξ) ^ 2)
        e k.castSucc η
  let Q : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobIncrement p X e k η) ^ 4
  have hpoint (η : BernoulliAssignment V) :
      finiteDoobMean p A e k.castSucc η ≤ B η + 8 * C η +
        3 * finiteDoobMean p Q e k.castSucc η := by
    simpa [A, B, C, Q, mul_assoc] using
      finiteDoobMean_centered_fourth_step_current p hp X c e k η
  have hEA : (∑ η, p η * finiteDoobMean p A e k.castSucc η) = ∑ η, p η * A η :=
    finiteDoob_expectation_eq p hp hnorm A e k.castSucc
  have hEQ : (∑ η, p η * finiteDoobMean p Q e k.castSucc η) = ∑ η, p η * Q η :=
    finiteDoob_expectation_eq p hp hnorm Q e k.castSucc
  calc
    (∑ η, p η * (finiteDoobMean p X e k.succ η - c) ^ 4) =
        ∑ η, p η * A η := by rfl
    _ = ∑ η, p η * finiteDoobMean p A e k.castSucc η := hEA.symm
    _ ≤ ∑ η, p η * (B η + 8 * C η +
          3 * finiteDoobMean p Q e k.castSucc η) := by
      apply Finset.sum_le_sum
      intro η hη
      exact mul_le_mul_of_nonneg_left (hpoint η) (hp η).le
    _ = (∑ η, p η * B η) + 8 * (∑ η, p η * C η) +
          3 * (∑ η, p η * finiteDoobMean p Q e k.castSucc η) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro η hη
      ring
    _ = (∑ η, p η * B η) + 8 * (∑ η, p η * C η) +
          3 * (∑ η, p η * Q η) := by rw [hEQ]
    _ = _ := by rfl


 theorem finiteDoob_generated_centered_fourth_expectation_step
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (c : ℝ)
    (k : Fin (Fintype.card V)) :
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.succ η - c) ^ 4) ≤
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η - c) ^ 4) +
      8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
        (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
            (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η - c) ^ 2) +
      3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
          (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := by
  let p := (hardCoreBernoulliSeedLaw R z hz).probability
  let X : BernoulliAssignment V → ℝ := fun ξ => generatedCountReal hG R ξ
  let M : BernoulliAssignment V → ℝ := fun η =>
    finiteDoobMean p X (parentFirstEquiv R) k.castSucc η - c
  let H : BernoulliAssignment V → ℝ := fun η =>
    generatedAvailabilityReal R η (parentFirstEquiv R k) *
      rootedEnergyAt R z hz (parentFirstEquiv R k)
  let Q : BernoulliAssignment V → ℝ := fun η =>
    (finiteDoobIncrement p X (parentFirstEquiv R) k η) ^ 4
  have hp : ∀ η, 0 < p η := by
    intro η
    dsimp [p]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hgeneric := finiteDoob_centered_fourth_expectation_step p hp
    (hardCoreBernoulliSeedLaw R z hz).probability_sum X c (parentFirstEquiv R) k
  have hcross :
      (∑ η, p η * (M η ^ 2 * finiteDoobMean p
        (fun ξ => (finiteDoobIncrement p X (parentFirstEquiv R) k ξ) ^ 2)
          (parentFirstEquiv R) k.castSucc η)) ≤
      rootedEnergyAt R z hz (parentFirstEquiv R k) *
        ∑ η, p η * M η ^ 2 := by
    rw [Finset.sum_congr rfl (fun η _ => by
      rw [finiteDoobMean_increment_sq_current hG R z hz k η])]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro η hη
    have hA0 : 0 ≤ generatedAvailabilityReal R η (parentFirstEquiv R k) := by
      unfold generatedAvailabilityReal
      split <;> norm_num
    have hA1 : generatedAvailabilityReal R η (parentFirstEquiv R k) ≤ 1 := by
      unfold generatedAvailabilityReal
      split <;> norm_num
    have hE0 := rootedEnergyAt_nonneg R z hz (parentFirstEquiv R k)
    have hp0 := (hp η).le
    have hM0 : 0 ≤ M η ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hp0 hM0,
      mul_nonneg (mul_nonneg hp0 hM0) hE0,
      mul_nonneg (sub_nonneg.mpr hA1) hE0,
      mul_nonneg (mul_nonneg hp0 hM0)
        (mul_nonneg (sub_nonneg.mpr hA1) hE0)]
  have hgeneric' :
      (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.succ η - c) ^ 4) ≤
      (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.castSucc η - c) ^ 4) +
      8 * (∑ η, p η * (M η ^ 2 * finiteDoobMean p
        (fun ξ => (finiteDoobIncrement p X (parentFirstEquiv R) k ξ) ^ 2)
          (parentFirstEquiv R) k.castSucc η)) +
      3 * (∑ η, p η * Q η) := by
    simpa [M, Q] using hgeneric
  calc
    _ ≤ (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.castSucc η - c) ^ 4) +
        8 * (∑ η, p η * (M η ^ 2 * finiteDoobMean p
          (fun ξ => (finiteDoobIncrement p X (parentFirstEquiv R) k ξ) ^ 2)
            (parentFirstEquiv R) k.castSucc η)) +
        3 * (∑ η, p η * Q η) := hgeneric'
    _ ≤ (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.castSucc η - c) ^ 4) +
        8 * (rootedEnergyAt R z hz (parentFirstEquiv R k) *
          ∑ η, p η * M η ^ 2) +
        3 * (∑ η, p η * Q η) := by gcongr
    _ = _ := by simp only [p, X, M, Q]; ring


 theorem finiteDoob_centered_fourth_expectation_prefix_sum
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (K : Fin (Fintype.card V) → ℝ)
    (e : Fin (Fintype.card V) ≃ V)
    (hstep : ∀ k : Fin (Fintype.card V),
      (∑ η, p η * (finiteDoobMean p X e k.succ η - c) ^ 4) ≤
        (∑ η, p η * (finiteDoobMean p X e k.castSucc η - c) ^ 4) + K k) :
    ∀ m : Nat, ∀ hm : m ≤ Fintype.card V,
    (∑ η, p η *
      (finiteDoobMean p X e ⟨m, Nat.lt_succ_of_le hm⟩ η - c) ^ 4) ≤
      (∑ η, p η * (finiteDoobMean p X e 0 η - c) ^ 4) +
        ∑ k : Fin m, K ⟨k.1, lt_of_lt_of_le k.2 hm⟩ := by
  intro m
  induction m with
  | zero =>
      intro hm
      simp
  | succ m ih =>
      intro hm
      have hm' : m ≤ Fintype.card V := Nat.le_trans (Nat.le_succ m) hm
      have hlt : m < Fintype.card V := Nat.lt_of_succ_le hm
      let ktop : Fin (Fintype.card V) := ⟨m, hlt⟩
      have hs := hstep ktop
      have hsucc : ktop.succ = (⟨m + 1, Nat.lt_succ_of_le hm⟩ :
          Fin (Fintype.card V + 1)) := by
        apply Fin.ext
        simp [ktop]
      have hcast : ktop.castSucc = (⟨m, Nat.lt_succ_of_le hm'⟩ :
          Fin (Fintype.card V + 1)) := by
        apply Fin.ext
        simp [ktop]
      rw [hsucc, hcast] at hs
      calc
        _ ≤ (∑ η, p η *
            (finiteDoobMean p X e ⟨m, Nat.lt_succ_of_le hm'⟩ η - c) ^ 4) +
              K ktop := hs
        _ ≤ ((∑ η, p η * (finiteDoobMean p X e 0 η - c) ^ 4) +
              ∑ k : Fin m, K ⟨k.1, lt_of_lt_of_le k.2 hm'⟩) + K ktop := by
          linarith [ih hm']
        _ = (∑ η, p η * (finiteDoobMean p X e 0 η - c) ^ 4) +
              ∑ k : Fin (m + 1), K ⟨k.1, lt_of_lt_of_le k.2 hm⟩ := by
          rw [Fin.sum_univ_castSucc]
          dsimp [ktop]
          ring

 theorem finiteDoob_centered_fourth_expectation_total_of_steps
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (K : Fin (Fintype.card V) → ℝ)
    (hc : ∑ η, p η * X η = c)
    (e : Fin (Fintype.card V) ≃ V)
    (hstep : ∀ k : Fin (Fintype.card V),
      (∑ η, p η * (finiteDoobMean p X e k.succ η - c) ^ 4) ≤
        (∑ η, p η * (finiteDoobMean p X e k.castSucc η - c) ^ 4) + K k) :
    (∑ η, p η * (X η - c) ^ 4) ≤ ∑ k, K k := by
  have h := finiteDoob_centered_fourth_expectation_prefix_sum p hp hnorm X c K e hstep
    (Fintype.card V) (by rfl)
  rw [show (⟨Fintype.card V, Nat.lt_succ_self _⟩ : Fin (Fintype.card V + 1)) =
      Fin.last (Fintype.card V) by rfl] at h
  rw [Finset.sum_congr rfl (fun η _ => by rw [finiteDoobMean_full_eq p X hp e η])] at h
  have hzero (η : BernoulliAssignment V) : finiteDoobMean p X e 0 η = c := by
    rw [finiteDoobMean_zero_of_normalized p X e η hnorm, hc]
  have hzero_sum : (∑ η, p η * (finiteDoobMean p X e 0 η - c) ^ 4) = 0 := by
    apply Finset.sum_eq_zero
    intro η hη
    rw [hzero η]
    ring
  rw [hzero_sum, zero_add] at h
  exact h


 theorem finiteDoob_centered_sq_expectation_le
    (p : BernoulliAssignment V → ℝ) (hp : ∀ η, 0 < p η)
    (hnorm : ∑ η, p η = 1)
    (X : BernoulliAssignment V → ℝ) (c : ℝ)
    (e : Fin (Fintype.card V) ≃ V) (m : Fin (Fintype.card V + 1)) :
    (∑ η, p η * (finiteDoobMean p X e m η - c) ^ 2) ≤
      ∑ η, p η * (X η - c) ^ 2 := by
  have hpoint (η : BernoulliAssignment V) :
      (finiteDoobMean p X e m η - c) ^ 2 ≤
        finiteDoobMean p (fun ξ => (X ξ - c) ^ 2) e m η := by
    rw [← finiteDoobMean_centered_eq_sub p hp]
    exact finiteDoobMean_sq_le_mean_sq p hp (fun ξ => X ξ - c) e m η
  calc
    _ ≤ ∑ η, p η * finiteDoobMean p (fun ξ => (X ξ - c) ^ 2) e m η := by
      apply Finset.sum_le_sum
      intro η hη
      exact mul_le_mul_of_nonneg_left (hpoint η) (hp η).le
    _ = _ := finiteDoob_expectation_eq p hp hnorm (fun ξ => (X ξ - c) ^ 2) e m

 theorem generated_finiteDoob_centered_sq_expectation_le_variance
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (m : Fin (Fintype.card V + 1)) :
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
        (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) m η -
        (Forest.hardCoreLaw G z hz).mean) ^ 2) ≤
      (Forest.hardCoreLaw G z hz).variance := by
  let p := (hardCoreBernoulliSeedLaw R z hz).probability
  have hp : ∀ η, 0 < p η := by
    intro η
    dsimp [p]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have h := finiteDoob_centered_sq_expectation_le p hp
    (hardCoreBernoulliSeedLaw R z hz).probability_sum
    (fun ξ => generatedCountReal hG R ξ) (Forest.hardCoreLaw G z hz).mean
    (parentFirstEquiv R) m
  have hv := generatedCenteredSecond_eq_hardCoreVariance_of_fiberMass hG R z hz
  have hv' :
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedCountReal hG R η - (Forest.hardCoreLaw G z hz).mean) ^ 2) =
      (Forest.hardCoreLaw G z hz).variance := by
    simpa [generatedCountLaw] using hv
  dsimp [p] at h
  rw [hv'] at h
  exact h


 theorem generatedCenteredFourth_le_explicit
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
      (generatedCountReal hG R η - (Forest.hardCoreLaw G z hz).mean) ^ 4) ≤
      (20 * (1 + Z) + 3 * actualFourthChildConstant Z * (1 + Z) ^ 2) *
        (Forest.hardCoreLaw G z hz).variance *
        (1 + (Forest.hardCoreLaw G z hz).variance) := by
  let p : BernoulliAssignment V → ℝ :=
    (hardCoreBernoulliSeedLaw R z hz).probability
  let X : BernoulliAssignment V → ℝ := fun η => generatedCountReal hG R η
  let c : ℝ := (Forest.hardCoreLaw G z hz).mean
  let V0 : ℝ := (Forest.hardCoreLaw G z hz).variance
  let K : Fin (Fintype.card V) → ℝ := fun k =>
    8 * rootedEnergyAt R z hz (parentFirstEquiv R k) * V0 +
      3 * ∑ η, p η *
        (finiteDoobIncrement p X (parentFirstEquiv R) k η) ^ 4
  have hp : ∀ η, 0 < p η := by
    intro η
    dsimp [p]
    unfold hardCoreBernoulliSeedLaw independentBernoulliLaw bernoulliWeight
    apply Finset.prod_pos
    intro v hv
    cases η v <;> simp [rootedOccupationProbabilityAt_pos R z hz v,
      rootedOccupationProbabilityAt_lt_one R z hz v]
  have hnorm : ∑ η, p η = 1 := by
    dsimp [p]
    exact (hardCoreBernoulliSeedLaw R z hz).probability_sum
  have hmean : ∑ η, p η * X η = c := by
    dsimp [p, X, c]
    exact generatedCount_mean_eq_hardCore_mean_of_fiberMass hG R z hz
  have hstep : ∀ k : Fin (Fintype.card V),
      (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.succ η - c) ^ 4) ≤
        (∑ η, p η * (finiteDoobMean p X (parentFirstEquiv R) k.castSucc η - c) ^ 4) + K k := by
    intro k
    have hmain := finiteDoob_generated_centered_fourth_expectation_step
      (G := G) hG R z hz c k
    have hsq := generated_finiteDoob_centered_sq_expectation_le_variance
      (G := G) hG R z hz k.castSucc
    have hinc := finiteDoobIncrement_fourth_expectation_le_availability_fourth_energy
      (G := G) hG R z hz k
    have hV : 0 ≤ V0 := by
      dsimp [V0]
      exact (Forest.hardCoreLaw G z hz).variance_nonneg
    have hE : 0 ≤ rootedEnergyAt R z hz (parentFirstEquiv R k) :=
      rootedEnergyAt_nonneg R z hz (parentFirstEquiv R k)
    dsimp [p, X, c, V0, K] at hmain hsq ⊢
    calc
      _ ≤ (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
            (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η -
            (Forest.hardCoreLaw G z hz).mean) ^ 4) +
          8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
            (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
              (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
                (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η -
                (Forest.hardCoreLaw G z hz).mean) ^ 2) +
          3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
            (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := hmain
      _ ≤ (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
          (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
            (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η -
            (Forest.hardCoreLaw G z hz).mean) ^ 4) +
          8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
            (Forest.hardCoreLaw G z hz).variance +
          3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
            (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := by
        have hmul :
            8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
                (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
                  (finiteDoobMean (hardCoreBernoulliSeedLaw R z hz).probability
                    (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k.castSucc η -
                    (Forest.hardCoreLaw G z hz).mean) ^ 2) ≤
              8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
                (Forest.hardCoreLaw G z hz).variance := by
          exact mul_le_mul_of_nonneg_left hsq (by positivity)
        linarith [hmul]
      _ = _ := by ring
  have htotal :
      (∑ η, p η * (X η - c) ^ 4) ≤ ∑ k, K k :=
    finiteDoob_centered_fourth_expectation_total_of_steps p hp hnorm X c K hmean
      (parentFirstEquiv R) hstep
  dsimp [p, X, c, K, V0] at htotal
  have htotal' :
      (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
        (generatedCountReal hG R η - (Forest.hardCoreLaw G z hz).mean) ^ 4) ≤
      8 * (∑ k : Fin (Fintype.card V),
        rootedEnergyAt R z hz (parentFirstEquiv R k)) *
          (Forest.hardCoreLaw G z hz).variance +
        3 * (∑ k : Fin (Fintype.card V),
          ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
            (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := by
    calc
      _ ≤ ∑ k : Fin (Fintype.card V),
          (8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
              (Forest.hardCoreLaw G z hz).variance +
            3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
              (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4)) := htotal
      _ = _ := by
        rw [Finset.sum_add_distrib]
        calc
          (∑ k : Fin (Fintype.card V),
              8 * rootedEnergyAt R z hz (parentFirstEquiv R k) *
                (Forest.hardCoreLaw G z hz).variance) +
              ∑ k : Fin (Fintype.card V),
                3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
                  (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                    (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) =
            (∑ k : Fin (Fintype.card V),
              (8 * (Forest.hardCoreLaw G z hz).variance) *
                rootedEnergyAt R z hz (parentFirstEquiv R k)) +
              ∑ k : Fin (Fintype.card V),
                3 * (∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
                  (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                    (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := by
              apply congrArg₂ (· + ·)
              · apply Finset.sum_congr rfl
                intro k hk
                ring
              · rfl
          _ = (8 * (Forest.hardCoreLaw G z hz).variance) *
                (∑ k : Fin (Fintype.card V),
                  rootedEnergyAt R z hz (parentFirstEquiv R k)) +
              3 * (∑ k : Fin (Fintype.card V),
                ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
                  (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
                    (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := by
              rw [Finset.mul_sum, Finset.mul_sum]
          _ = _ := by ring
  have hincsum := sum_increment_fourth_expectation_le_variance_bound
    (G := G) hG R z Z hz hzZ
  have hAsum := sum_rootedEnergy_le_one_add_Z_mul_variance
    (G := G) hG R z Z hz hzZ
  have hAsum' :
      (∑ k : Fin (Fintype.card V), rootedEnergyAt R z hz (parentFirstEquiv R k)) ≤
        (1 + Z) * (Forest.hardCoreLaw G z hz).variance := by
    calc
      _ = ∑ v : V, rootedEnergyAt R z hz v :=
        Equiv.sum_comp (parentFirstEquiv R) (fun v => rootedEnergyAt R z hz v)
      _ ≤ _ := hAsum
  have hV : 0 ≤ (Forest.hardCoreLaw G z hz).variance :=
    (Forest.hardCoreLaw G z hz).variance_nonneg
  have hZ : 0 ≤ 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  have hE : 0 ≤ ∑ v : V, rootedEnergyAt R z hz v := by
    exact Finset.sum_nonneg (fun v hv => rootedEnergyAt_nonneg R z hz v)
  have hfourC : 0 ≤ actualFourthChildConstant Z := by
    dsimp [actualFourthChildConstant]
    have : 0 ≤ Z := (lt_of_lt_of_le hz hzZ).le
    positivity
  calc
    _ ≤ 8 * (∑ k : Fin (Fintype.card V),
        rootedEnergyAt R z hz (parentFirstEquiv R k)) *
          (Forest.hardCoreLaw G z hz).variance +
        3 * (∑ k : Fin (Fintype.card V),
          ∑ η, (hardCoreBernoulliSeedLaw R z hz).probability η *
            (finiteDoobIncrement (hardCoreBernoulliSeedLaw R z hz).probability
              (fun ξ => generatedCountReal hG R ξ) (parentFirstEquiv R) k η) ^ 4) := htotal'
    _ ≤ 8 * ((1 + Z) * (Forest.hardCoreLaw G z hz).variance) *
          (Forest.hardCoreLaw G z hz).variance +
        3 * (4 * (1 + Z) * (Forest.hardCoreLaw G z hz).variance +
          actualFourthChildConstant Z * (1 + Z) ^ 2 *
            (Forest.hardCoreLaw G z hz).variance ^ 2) := by
      have hAprod :
          (∑ k : Fin (Fintype.card V), rootedEnergyAt R z hz (parentFirstEquiv R k)) *
              (Forest.hardCoreLaw G z hz).variance ≤
            ((1 + Z) * (Forest.hardCoreLaw G z hz).variance) *
              (Forest.hardCoreLaw G z hz).variance :=
        mul_le_mul_of_nonneg_right hAsum' hV
      have hAprod8 := mul_le_mul_of_nonneg_left hAprod
        (by norm_num : (0 : ℝ) ≤ 8)
      have hInc3 := mul_le_mul_of_nonneg_left hincsum
        (by norm_num : (0 : ℝ) ≤ 3)
      linarith [hAprod8, hInc3]
    _ ≤ _ := by
      have hV2 : 0 ≤ (Forest.hardCoreLaw G z hz).variance ^ 2 := sq_nonneg _
      have hZV : 0 ≤ (1 + Z) * (Forest.hardCoreLaw G z hz).variance :=
        mul_nonneg hZ hV
      have hCterm : 0 ≤ actualFourthChildConstant Z * (1 + Z) ^ 2 *
          (Forest.hardCoreLaw G z hz).variance ^ 2 := by positivity
      have hCcoef : 0 ≤ 3 * actualFourthChildConstant Z * (1 + Z) ^ 2 := by
        positivity
      have hCcoefV := mul_nonneg hCcoef hV
      have hZV2 : 0 ≤ (1 + Z) * (Forest.hardCoreLaw G z hz).variance ^ 2 :=
        mul_nonneg hZ hV2
      nlinarith



 theorem generatedAvailability_expectation_eq_parentAbsentProbability
    (C : Forest.CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (∑ η, (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability η *
      generatedAvailabilityReal R η u) =
      R.parentAbsentProbability (G := G) C u := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · have hav (η : BernoulliAssignment V) : generatedAvailabilityReal R η u = 1 := by
      unfold generatedAvailabilityReal generatedAvailable
      rw [if_pos]
      exact decide_eq_true (by
        intro v hv
        exact (R.not_isChild_of_eq_root (G := G) hu hv).elim)
    have hpa : R.parentAbsentProbability (G := G) C u = 1 := by
      rw [hu]
      exact R.parentAbsentProbability_rootOf (G := G) C u
    rw [hpa]
    rw [show (fun η => (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability η *
        generatedAvailabilityReal R η u) =
      (fun η => (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability η) by
        funext η
        rw [hav η, mul_one]]
    exact (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability_sum
  · let p : V := R.selectedParent (G := G) u hu
    have hpu : R.IsChild (G := G) p u :=
      R.selectedParent_isChild (G := G) u hu
    let f : IndepFinset G → ℝ := fun s => if p ∉ s.val then 1 else 0
    have hpoint (η : BernoulliAssignment V) :
        generatedAvailabilityReal R η u = f (generatedIndependentSet C.isForest R η) := by
      unfold generatedAvailabilityReal f generatedIndependentSet generatedFinset
      rw [generatedAvailable_eq_not_occupation_of_isChild C.isForest R hpu]
      cases hocc : generatedOccupation R η p <;> simp [hocc]
    have hpush := exactHardCoreConfigurationCoupling_of_fiberMass
      C.isForest R C.activity C.activity_pos
    have htransfer := generatedExpectation_eq_hardCoreExpectation
      C.isForest R C.activity C.activity_pos hpush f
    calc
      (∑ η, (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability η *
          generatedAvailabilityReal R η u) =
          ∑ η, (generatedCountLaw C.isForest R C.activity C.activity_pos).probability η *
            f (generatedIndependentSet C.isForest R η) := by
              apply Finset.sum_congr rfl
              intro η hη
              rw [hpoint]
              rfl
      _ = ∑ s, (Forest.hardCoreLaw G C.activity C.activity_pos).probability s * f s :=
        htransfer
      _ = R.parentAbsentProbability (G := G) C u := by
        rw [R.parentAbsentProbability_eq_globalLaw_event (G := G) C hu]
        apply Finset.sum_congr rfl
        intro s hs
        dsimp [f, p]
        by_cases hm : R.selectedParent (G := G) u hu ∈ s.val <;>
          simp [hm, Forest.CanonicalFirstRecoveryState.law]

 theorem availability_energy_sum_eq_canonical_variance
    (C : Forest.CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    ∑ k : Fin (Fintype.card V),
      (∑ η, (hardCoreBernoulliSeedLaw R C.activity C.activity_pos).probability η *
        generatedAvailabilityReal R η (parentFirstEquiv R k)) *
        rootedEnergyAt R C.activity C.activity_pos (parentFirstEquiv R k) =
      C.variance := by
  calc
    _ = ∑ k : Fin (Fintype.card V),
        R.parentAbsentProbability (G := G) C (parentFirstEquiv R k) *
          rootedEnergyAt R C.activity C.activity_pos (parentFirstEquiv R k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [generatedAvailability_expectation_eq_parentAbsentProbability C R]
    _ = ∑ k : Fin (Fintype.card V),
        R.vertexVarianceContribution (G := G) C (parentFirstEquiv R k) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [rootedEnergyAt, rootedOccupationProbabilityAt,
        rootedVacancyProbabilityAt, rootedDisplacementAt,
        ComponentRooting.vertexVarianceContribution,
        ComponentRooting.occupationProbability, ComponentRooting.vacancyProbability,
        ComponentRooting.conditionalMeanDifference,
        rootedAAt, rootedPAt, rootedQAt,
        ComponentRooting.rootedA, ComponentRooting.rootedP, ComponentRooting.rootedQ,
        ComponentRooting.conditionalMeanDifferenceAt,
        ComponentRooting.occupiedMeanAt, ComponentRooting.vacantMeanAt,
        ComponentRooting.occupiedMean, ComponentRooting.vacantMean]
      ring
    _ = ∑ v : V, R.vertexVarianceContribution (G := G) C v :=
      Equiv.sum_comp (parentFirstEquiv R)
        (fun v => R.vertexVarianceContribution (G := G) C v)
    _ = C.variance := R.sum_vertexVarianceContribution_eq_variance (G := G) C

/-- The explicit finite coefficient in the uniform fourth-moment theorem. -/
noncomputable def C4 (Z : ℝ) : ℝ :=
  20 * (1 + Z) + 3 * actualFourthChildConstant Z * (1 + Z) ^ 2

 theorem C4_nonneg_of_nonneg {Z : ℝ} (hZ : 0 ≤ Z) : 0 ≤ C4 Z := by
  dsimp [C4, actualFourthChildConstant]
  positivity

/-- Polynomial form of the explicit A.3 coefficient. -/
theorem C4_eq_polynomial (Z : ℝ) :
    C4 Z = 20 * (1 + Z) + 192 * Z * (1 + Z) ^ 4 := by
  dsimp [C4, actualFourthChildConstant]
  ring

/-- Uniform fourth-moment theorem A.3 for the actual finite hard-core law. -/
theorem hardCoreCenteredFourth_le_C4
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z Z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ s, (Forest.hardCoreLaw G z hz).probability s *
      (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 4) ≤
      C4 Z * (Forest.hardCoreLaw G z hz).variance *
        (1 + (Forest.hardCoreLaw G z hz).variance) := by
  have hpush := exactHardCoreConfigurationCoupling_of_fiberMass hG R z hz
  have hgen := generatedCenteredFourth_le_explicit hG R z Z hz hzZ
  have heq := generatedCenteredFourth_eq_hardCoreCenteredFourth hG R z hz hpush
  calc
    _ = ∑ ω, (generatedCountLaw hG R z hz).probability ω *
        (generatedCountReal hG R ω - (Forest.hardCoreLaw G z hz).mean) ^ 4 :=
      heq.symm
    _ ≤ C4 Z * (Forest.hardCoreLaw G z hz).variance *
        (1 + (Forest.hardCoreLaw G z hz).variance) := by
      simpa [C4, generatedCountLaw] using hgen

/-- Public rooting-free form of theorem A.3.  It applies to every finite forest,
including the empty forest, under the advertised positive ceiling assumptions. -/
theorem uniformFourthMoment_A3
    (hG : G.IsAcyclic) (z Z : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ s, (Forest.hardCoreLaw G z hz).probability s *
      (hardCoreCountReal s - (Forest.hardCoreLaw G z hz).mean) ^ 4) ≤
      C4 Z * (Forest.hardCoreLaw G z hz).variance *
        (1 + (Forest.hardCoreLaw G z hz).variance) := by
  obtain ⟨R⟩ := nonempty_componentRooting (G := G)
  exact hardCoreCenteredFourth_le_C4 hG R z Z hz hzZ

/-- Cardinality-spelled corollary of the public A.3 theorem. -/
theorem uniformFourthMoment_A3_card
    (hG : G.IsAcyclic) (z Z : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z) :
    (∑ s, (Forest.hardCoreLaw G z hz).probability s *
      ((s.val.card : ℝ) - (Forest.hardCoreLaw G z hz).mean) ^ 4) ≤
      C4 Z * (Forest.hardCoreLaw G z hz).variance *
        (1 + (Forest.hardCoreLaw G z hz).variance) := by
  simpa [hardCoreCountReal] using uniformFourthMoment_A3 hG z Z hZ hz hzZ

end UniformFourthMoment
end Erdos993
