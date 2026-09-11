import Erdos993.VertexDeletion

/-! Rooted two-state decomposition for independence polynomials. -/

namespace Erdos993

open Polynomial

variable {V : Type*} [Fintype V]

noncomputable local instance subtypeFintype {p : V → Prop} : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Root-avoiding state: the root is deleted. -/
noncomputable def rootedAvoidingPolynomial (G : SimpleGraph V) (r : V) : Polynomial ℕ :=
  independencePolynomial (deleteVertex G r)

/-- Root-occupied remainder after factoring off the root variable. -/
noncomputable def rootedOccupiedRemainder (G : SimpleGraph V) (r : V) : Polynomial ℕ :=
  independencePolynomial (deleteClosedNeighborhood G r)

/-- Exact rooted recurrence `I(G)=Q_r+X R_r`. -/
theorem rooted_recurrence (G : SimpleGraph V) (r : V) :
    independencePolynomial G =
      rootedAvoidingPolynomial G r + X * rootedOccupiedRemainder G r := by
  simpa [rootedAvoidingPolynomial, rootedOccupiedRemainder] using
    independencePolynomial_deleteVertex (G := G) (v := r)

end Erdos993
