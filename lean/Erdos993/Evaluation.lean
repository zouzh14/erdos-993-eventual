import Erdos993.IndependencePolynomial

/-! Casts and positive evaluation of the natural independence polynomial. -/

namespace Erdos993

open scoped BigOperators
open Polynomial

variable {V : Type*} [Fintype V]

/-- Independence polynomial with coefficients cast from `ℕ` to a semiring. -/
noncomputable def independencePolynomialCast (R : Type*) [Semiring R]
    (G : SimpleGraph V) : Polynomial R :=
  (independencePolynomial G).map (Nat.castRingHom R)

@[simp] theorem independencePolynomialCast_coeff (R : Type*) [Semiring R]
    (G : SimpleGraph V) (k : ℕ) :
    (independencePolynomialCast R G).coeff k = (independenceCoeff G k : R) := by
  simp [independencePolynomialCast, coeff_independencePolynomial]

/-- Evaluation after casting is the finite hard-core partition sum. -/
theorem independencePolynomialCast_eval (R : Type*) [CommSemiring R]
    (G : SimpleGraph V) (z : R) :
    (independencePolynomialCast R G).eval z =
      ∑ s : IndepFinset G, z ^ s.val.card := by
  classical
  rw [independencePolynomialCast, Polynomial.eval_map]
  change Polynomial.eval₂ (Nat.castRingHom R) z
      (Finset.sum (Finset.univ : Finset (IndepFinset G)) (fun s => X ^ s.val.card)) = _
  rw [Polynomial.eval₂_finset_sum]
  simp

/-- The independence polynomial is strictly positive at every positive real
activity (indeed, the empty independent set contributes `1`). -/
theorem independencePolynomial_eval_pos (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    0 < (independencePolynomialCast ℝ G).eval z := by
  classical
  rw [independencePolynomialCast_eval]
  let e : IndepFinset G := ⟨∅, by simp [SimpleGraph.IsIndepSet]⟩
  apply Finset.sum_pos'
  · intro s hs
    exact pow_nonneg (le_of_lt hz) _
  · refine ⟨e, Finset.mem_univ _, ?_⟩
    simp [e]

end Erdos993
