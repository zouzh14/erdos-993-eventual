import Erdos993.IndependencePolynomial

open scoped BigOperators
open Polynomial

namespace Erdos993

universe u

section Induce

variable {V : Type u} (G : SimpleGraph V) (p : V → Prop)

/-- Independent finsets of `G` all of whose vertices satisfy `p`. -/
def RestrictedIndepFinset := {s : IndepFinset G // ∀ x ∈ s.val, p x}

/-- An independent finset of an induced graph is exactly an independent finset
of the original graph supported on the inducing set. -/
noncomputable def indepFinsetInduceEquiv :
    IndepFinset (G.induce {x | p x}) ≃ RestrictedIndepFinset G p := by
  classical
  let e : {x // p x} ↪ V := Function.Embedding.subtype p
  refine
    { toFun := fun s =>
        ⟨⟨s.val.map e, ?_⟩, ?_⟩
      invFun := fun s =>
        ⟨s.val.val.subtype p, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hs := s.property
    rw [SimpleGraph.isIndepSet_iff] at hs ⊢
    intro x hx y hy hxy
    change x ∈ Finset.map e s.val at hx
    change y ∈ Finset.map e s.val at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hs hx' hy' (by simpa using hxy)
  · intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨x', _, rfl⟩ := hx
    exact x'.property
  · have hs := s.val.property
    rw [SimpleGraph.isIndepSet_iff] at hs ⊢
    intro x hx y hy hxy
    apply hs (Finset.mem_subtype.mp hx) (Finset.mem_subtype.mp hy)
    exact fun h => hxy (Subtype.ext h)
  · intro s
    apply Subtype.ext
    apply Finset.map_injective (Function.Embedding.subtype p)
    rw [Finset.subtype_map]
    apply Finset.filter_eq_self.mpr
    intro x hx
    rw [Finset.mem_map] at hx
    obtain ⟨x', _, rfl⟩ := hx
    exact x'.property
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    exact Finset.subtype_map_of_mem s.property

@[simp] theorem indepFinsetInduceEquiv_card
    (s : IndepFinset (G.induce {x | p x})) :
    ((indepFinsetInduceEquiv G p s).val.val.card) = s.val.card := by
  exact Finset.card_map _

end Induce

section Delete

variable {V : Type u} [Fintype V] (G : SimpleGraph V) (v : V)

noncomputable local instance restrictedFintype {α : Type*} [Fintype α] (q : α → Prop) :
    Fintype {x : α // q x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The graph `G - v`, represented as the graph induced on vertices unequal to `v`. -/
abbrev deleteVertex : SimpleGraph {x : V // x ≠ v} := G.induce {x | x ≠ v}

/-- The graph `G - N[v]`, represented as the graph induced outside the closed
neighborhood of `v`. -/
abbrev deleteClosedNeighborhood : SimpleGraph {x : V // x ≠ v ∧ ¬ G.Adj v x} :=
  G.induce {x | x ≠ v ∧ ¬ G.Adj v x}

/-- Independent finsets of `G` avoiding `v`. -/
def AvoidingIndepFinset := {s : IndepFinset G // v ∉ s.val}

/-- Independent finsets of `G` containing `v`. -/
def ContainingIndepFinset := {s : IndepFinset G // v ∈ s.val}

noncomputable local instance avoidingFintype : Fintype (AvoidingIndepFinset G v) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable local instance containingFintype : Fintype (ContainingIndepFinset G v) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Partition independent finsets according to whether they contain `v`. -/
noncomputable def indepFinsetPartitionEquiv :
    IndepFinset G ≃ (AvoidingIndepFinset G v ⊕ ContainingIndepFinset G v) := by
  classical
  refine
    { toFun := fun s => if h : v ∈ s.val then Sum.inr ⟨s, h⟩ else Sum.inl ⟨s, h⟩
      invFun := Sum.elim Subtype.val Subtype.val
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    by_cases h : v ∈ s.val <;> simp [h]
  · intro q
    cases q with
    | inl s => simp [s.property]
    | inr s => simp [s.property]

/-- Deleting `v` from the vertex type is weight-preservingly equivalent to
requiring an independent finset of `G` to avoid `v`. -/
noncomputable def avoidingEquiv :
    IndepFinset (deleteVertex G v) ≃ AvoidingIndepFinset G v := by
  classical
  refine (indepFinsetInduceEquiv G (fun x => x ≠ v)).trans ?_
  refine
    { toFun := fun s => ⟨s.val, ?_⟩
      invFun := fun s => ⟨s.val, ?_⟩
      left_inv := by intro s; rfl
      right_inv := by intro s; rfl }
  · intro hv
    exact (s.property v hv) rfl
  · intro x hx h
    subst x
    exact s.property hx

omit [Fintype V] in
@[simp] theorem avoidingEquiv_card (s : IndepFinset (deleteVertex G v)) :
    ((avoidingEquiv G v s).val.val.card) = s.val.card := by
  exact indepFinsetInduceEquiv_card G (fun x => x ≠ v) s

/-- Removing the occupied vertex `v` gives a weight-shifting equivalence between
independent finsets containing `v` and independent finsets in `G - N[v]`. -/
noncomputable def containingEquiv :
    IndepFinset (deleteClosedNeighborhood G v) ≃ ContainingIndepFinset G v := by
  classical
  let e := indepFinsetInduceEquiv G (fun x => x ≠ v ∧ ¬ G.Adj v x)
  refine
    { toFun := fun s =>
        ⟨⟨insert v (e s).val.val, ?_⟩, Finset.mem_insert_self v _⟩
      invFun := fun s => ?_
      left_inv := ?_
      right_inv := ?_ }
  · have hs := s.property
    rw [SimpleGraph.isIndepSet_iff] at hs ⊢
    intro x hx y hy hxy
    change x ∈ insert v (e s).val.val at hx
    change y ∈ insert v (e s).val.val at hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with hxv | hx
    · subst x
      rcases hy with hyv | hy
      · exact (hxy hyv.symm).elim
      · exact (e s).property y hy |>.2
    · rcases hy with hyv | hy
      · subst y
        exact fun h => ((e s).property x hx |>.2) ((G.adj_comm x v).mp h)
      · exact (e s).val.property hx hy hxy
  · have hrest : ∀ x ∈ s.val.val.erase v, x ≠ v ∧ ¬ G.Adj v x := by
      intro x hx
      have hxS : x ∈ s.val.val := (Finset.mem_erase.mp hx).2
      have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
      refine ⟨hxv, ?_⟩
      have hs := s.val.property
      rw [SimpleGraph.isIndepSet_iff] at hs
      exact hs s.property hxS (Ne.symm hxv)
    have hind : G.IsIndepSet (s.val.val.erase v : Set V) :=
      s.val.property.mono (by intro x hx; exact (Finset.mem_erase.mp hx).2)
    exact (e.symm ⟨⟨s.val.val.erase v, hind⟩, hrest⟩)
  · intro s
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    dsimp only
    have hnot : v ∉ (e s).val.val := by
      intro hv
      exact ((e s).property v hv).1 rfl
    rw [Finset.erase_insert hnot]
  · intro s
    apply Subtype.ext
    apply Subtype.ext
    dsimp only
    rw [e.apply_symm_apply]
    exact Finset.insert_erase s.property

omit [Fintype V] in
@[simp] theorem containingEquiv_card (s : IndepFinset (deleteClosedNeighborhood G v)) :
    ((containingEquiv G v s).val.val.card) = s.val.card + 1 := by
  classical
  change (insert v ((indepFinsetInduceEquiv G (fun x => x ≠ v ∧ ¬ G.Adj v x) s).val.val)).card = _
  rw [Finset.card_insert_of_notMem]
  · rw [indepFinsetInduceEquiv_card]
    rfl
  · intro hv
    exact ((indepFinsetInduceEquiv G (fun x => x ≠ v ∧ ¬ G.Adj v x) s).property v hv).1 rfl

set_option maxHeartbeats 1200000 in
/-- **Vertex-deletion recurrence** for the natural-coefficient independence
polynomial: `I_G = I_{G-v} + X I_{G-N[v]}`. -/
theorem independencePolynomial_deleteVertex :
    independencePolynomial G =
      independencePolynomial (deleteVertex G v) +
        X * independencePolynomial (deleteClosedNeighborhood G v) := by
  classical
  rw [independencePolynomial, independencePolynomial, independencePolynomial]
  symm
  calc
    (∑ s : IndepFinset (deleteVertex G v), X ^ s.val.card) +
        X * (∑ s : IndepFinset (deleteClosedNeighborhood G v), X ^ s.val.card) =
      (∑ s : AvoidingIndepFinset G v, X ^ s.val.val.card) +
        (∑ s : ContainingIndepFinset G v, X ^ s.val.val.card) := by
          congr 1
          · apply Fintype.sum_equiv (avoidingEquiv G v)
            intro s
            rw [avoidingEquiv_card]
          · rw [Finset.mul_sum]
            apply Fintype.sum_equiv (containingEquiv G v)
            intro s
            rw [containingEquiv_card, pow_add, pow_one]
            exact mul_comm _ _
    _ = ∑ q : AvoidingIndepFinset G v ⊕ ContainingIndepFinset G v,
          Sum.elim (fun s => X ^ s.val.val.card) (fun s => X ^ s.val.val.card) q := by
      symm
      exact Fintype.sum_sum_type _
    _ = ∑ s : IndepFinset G, X ^ s.val.card := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv G v).symm
      intro q
      cases q <;> rfl

end Delete

end Erdos993
