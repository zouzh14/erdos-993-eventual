import Erdos993.IndependencePolynomial

/-! Invariance of the independence polynomial under graph isomorphism. -/

namespace Erdos993

open Polynomial

universe u v
variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- A graph isomorphism gives a cardinality-preserving equivalence of independent
vertex finsets. -/
noncomputable def indepFinsetIsoEquiv (e : G ≃g H) : IndepFinset G ≃ IndepFinset H := by
  classical
  refine
    { toFun := fun s => ⟨s.val.map e.toEquiv.toEmbedding, ?_⟩
      invFun := fun t => ⟨t.val.map e.symm.toEquiv.toEmbedding, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    change x ∈ s.val.map e.toEquiv.toEmbedding at hx
    change y ∈ s.val.map e.toEquiv.toEmbedding at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    change ¬ H.Adj (e x') (e y')
    rw [e.map_rel_iff]
    have hs := s.property
    rw [SimpleGraph.isIndepSet_iff] at hs
    exact hs hx' hy' (by simpa using hxy)
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    change x ∈ t.val.map e.symm.toEquiv.toEmbedding at hx
    change y ∈ t.val.map e.symm.toEquiv.toEmbedding at hy
    rw [Finset.mem_map] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    change ¬ G.Adj (e.symm x') (e.symm y')
    rw [e.symm.map_rel_iff]
    have ht := t.property
    rw [SimpleGraph.isIndepSet_iff] at ht
    exact ht hx' hy' (by simpa using hxy)
  · intro s
    apply Subtype.ext
    change (Equiv.finsetCongr e.toEquiv).symm
      ((Equiv.finsetCongr e.toEquiv) s.val) = s.val
    exact (Equiv.finsetCongr e.toEquiv).symm_apply_apply s.val
  · intro t
    apply Subtype.ext
    change (Equiv.finsetCongr e.toEquiv)
      ((Equiv.finsetCongr e.toEquiv).symm t.val) = t.val
    exact (Equiv.finsetCongr e.toEquiv).apply_symm_apply t.val

@[simp] theorem indepFinsetIsoEquiv_card (e : G ≃g H) (s : IndepFinset G) :
    (indepFinsetIsoEquiv e s).val.card = s.val.card := by
  simp [indepFinsetIsoEquiv]

variable [Fintype V] [Fintype W]

/-- The natural independence polynomial is invariant under graph isomorphism. -/
theorem independencePolynomial_iso (e : G ≃g H) :
    independencePolynomial G = independencePolynomial H := by
  classical
  rw [independencePolynomial, independencePolynomial]
  apply Fintype.sum_equiv (indepFinsetIsoEquiv e)
  intro s
  rw [indepFinsetIsoEquiv_card]

end Erdos993
