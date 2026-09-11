import Erdos993.IndependencePolynomial

open scoped BigOperators
open Polynomial

namespace Erdos993

universe u v

section Sum

variable {V : Type u} {W : Type v}
variable (G : SimpleGraph V) (H : SimpleGraph W)

/-- Independence in mathlib's disjoint-union graph is componentwise. -/
theorem isIndepSet_sum_iff (s : Finset (V ⊕ W)) :
    (G ⊕g H).IsIndepSet (s : Set (V ⊕ W)) ↔
      G.IsIndepSet (s.toLeft : Set V) ∧ H.IsIndepSet (s.toRight : Set W) := by
  simp only [SimpleGraph.isIndepSet_iff]
  constructor
  · intro hs
    constructor
    · intro x hx y hy hxy
      have hx' : Sum.inl x ∈ s := Finset.mem_toLeft.mp hx
      have hy' : Sum.inl y ∈ s := Finset.mem_toLeft.mp hy
      simpa [SimpleGraph.sum_adj] using hs hx' hy' (by simpa using hxy)
    · intro x hx y hy hxy
      have hx' : Sum.inr x ∈ s := Finset.mem_toRight.mp hx
      have hy' : Sum.inr y ∈ s := Finset.mem_toRight.mp hy
      simpa [SimpleGraph.sum_adj] using hs hx' hy' (by simpa using hxy)
  · rintro ⟨hG, hH⟩
    intro x hx y hy hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            simpa [SimpleGraph.sum_adj] using
              hG (Finset.mem_toLeft.mpr hx) (Finset.mem_toLeft.mpr hy) (by simpa using hxy)
        | inr y => simp [SimpleGraph.sum_adj]
    | inr x =>
        cases y with
        | inl y => simp [SimpleGraph.sum_adj]
        | inr y =>
            simpa [SimpleGraph.sum_adj] using
              hH (Finset.mem_toRight.mpr hx) (Finset.mem_toRight.mpr hy) (by simpa using hxy)

/-- Explicit weight-preserving equivalence of independent finsets in a graph sum
and pairs of independent finsets in the two summands. -/
noncomputable def indepFinsetSumEquiv :
    IndepFinset (G ⊕g H) ≃ (IndepFinset G × IndepFinset H) := by
  classical
  refine
    { toFun := fun s =>
        (⟨s.val.toLeft, (isIndepSet_sum_iff G H s.val).mp s.property |>.1⟩,
         ⟨s.val.toRight, (isIndepSet_sum_iff G H s.val).mp s.property |>.2⟩)
      invFun := fun p =>
        ⟨p.1.val.disjSum p.2.val,
          (isIndepSet_sum_iff G H (p.1.val.disjSum p.2.val)).mpr
            ⟨by simpa only [Finset.toLeft_disjSum] using p.1.property,
             by simpa only [Finset.toRight_disjSum] using p.2.property⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro s
    apply Subtype.ext
    exact Finset.toLeft_disjSum_toRight
  · intro p
    apply Prod.ext <;> apply Subtype.ext <;> simp

@[simp] theorem indepFinsetSumEquiv_card (s : IndepFinset (G ⊕g H)) :
    ((indepFinsetSumEquiv G H s).1.val.card +
      (indepFinsetSumEquiv G H s).2.val.card) = s.val.card := by
  exact Finset.card_toLeft_add_card_toRight

variable [Fintype V] [Fintype W]

/-- The independence polynomial multiplies on mathlib `SimpleGraph.sum`. -/
theorem independencePolynomial_sum :
    independencePolynomial (G ⊕g H) = independencePolynomial G * independencePolynomial H := by
  classical
  rw [independencePolynomial, independencePolynomial, independencePolynomial]
  calc
    (∑ s : IndepFinset (G ⊕g H), X ^ s.val.card) =
        ∑ p : IndepFinset G × IndepFinset H, X ^ (p.1.val.card + p.2.val.card) := by
          apply Fintype.sum_equiv (indepFinsetSumEquiv G H)
          intro s
          rw [indepFinsetSumEquiv_card]
    _ = (∑ a : IndepFinset G, X ^ a.val.card) *
          (∑ b : IndepFinset H, X ^ b.val.card) := by
          rw [Fintype.sum_prod_type]
          simp [pow_add, Finset.sum_mul_sum]

end Sum

end Erdos993
