import Mathlib

open scoped BigOperators
open Polynomial

namespace Erdos993

universe u v

/-- A finite independent vertex set of a mathlib `SimpleGraph`.  This is a thin
counting type, not a second graph representation. -/
def IndepFinset {V : Type u} (G : SimpleGraph V) :=
  {s : Finset V // G.IsIndepSet (s : Set V)}

namespace IndepFinset

variable {V : Type u} {G : SimpleGraph V}

noncomputable instance [Fintype V] : Fintype (IndepFinset G) := by
  classical
  unfold IndepFinset
  infer_instance
noncomputable instance [DecidableEq V] : DecidableEq (IndepFinset G) := Classical.decEq _

@[simp] theorem card_mk (s : Finset V) (h) : (⟨s, h⟩ : IndepFinset G).val.card = s.card := rfl

/-- Package a mathlib-independent finite vertex set as the thin counting type. -/
def ofIsIndepSet (s : Finset V) (h : G.IsIndepSet (s : Set V)) : IndepFinset G :=
  ⟨s, h⟩

@[simp] theorem ofIsIndepSet_val (s : Finset V) (h : G.IsIndepSet (s : Set V)) :
    (ofIsIndepSet s h : IndepFinset G).val = s := rfl

/-- Exact conversion theorem: a `Finset` can be represented by the thin
counting subtype iff its coercion is a mathlib `SimpleGraph.IsIndepSet`.
Thus `IndepFinset` introduces no competing notion of graph independence. -/
theorem exists_indepFinset_iff_isIndepSet (s : Finset V) :
    (∃ t : IndepFinset G, t.val = s) ↔ G.IsIndepSet (s : Set V) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact t.property
  · intro h
    exact ⟨ofIsIndepSet s h, rfl⟩

/-- The empty vertex finset is independent. -/
def empty (G : SimpleGraph V) : IndepFinset G :=
  ⟨∅, by simp [SimpleGraph.isIndepSet_iff]⟩

@[simp] theorem empty_val (G : SimpleGraph V) : (empty G).val = ∅ := rfl
@[simp] theorem empty_card (G : SimpleGraph V) : (empty G).val.card = 0 := rfl

end IndepFinset

section Finite

variable {V : Type u} [Fintype V] (G : SimpleGraph V)

/-- The natural number of independent vertex finsets of cardinality `k`. -/
noncomputable def independenceCoeff (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun s : IndepFinset G => s.val.card = k).card

/-- The independence polynomial with natural counting coefficients. -/
noncomputable def independencePolynomial : Polynomial ℕ := by
  classical
  exact ∑ s : IndepFinset G, X ^ s.val.card

/-- The polynomial coefficient is exactly the number of independent vertex finsets
of that cardinality. -/
theorem coeff_independencePolynomial (k : ℕ) :
    (independencePolynomial G).coeff k = independenceCoeff G k := by
  classical
  simp [independencePolynomial, independenceCoeff, eq_comm]

/-- Expanded counting form of the independence polynomial. -/
theorem independencePolynomial_eq_sum :
    independencePolynomial G = ∑ s : IndepFinset G, X ^ s.val.card := by
  rfl

/-- Cast the natural counting polynomial to real coefficients. -/
noncomputable def independencePolynomialReal : Polynomial ℝ :=
  (independencePolynomial G).map (Nat.castRingHom ℝ)

/-- Real evaluation of the cast independence polynomial. -/
noncomputable def independenceEval (z : ℝ) : ℝ :=
  (independencePolynomialReal G).eval z

/-- Evaluation is the finite partition-function sum over independent vertex finsets. -/
theorem independenceEval_eq_sum (z : ℝ) :
    independenceEval G z = ∑ s : IndepFinset G, z ^ s.val.card := by
  classical
  rw [independenceEval, independencePolynomialReal, Polynomial.eval_map]
  change Polynomial.eval₂ (Nat.castRingHom ℝ) z
      (Finset.sum (Finset.univ : Finset (IndepFinset G)) (fun s => X ^ s.val.card)) = _
  rw [Polynomial.eval₂_finset_sum]
  simp

/-- Coefficients commute with the canonical natural-to-real cast. -/
theorem coeff_independencePolynomialReal (k : ℕ) :
    (independencePolynomialReal G).coeff k = (independenceCoeff G k : ℝ) := by
  simp [independencePolynomialReal, coeff_independencePolynomial]

/-- Evaluation of the cast polynomial agrees with `eval₂` on the natural polynomial. -/
theorem independenceEval_eq_eval₂ (z : ℝ) :
    independenceEval G z = Polynomial.eval₂ (Nat.castRingHom ℝ) z (independencePolynomial G) := by
  exact Polynomial.eval_map (Nat.castRingHom ℝ) z

/-- Strict positivity of the hard-core partition function at positive activity. -/
theorem independenceEval_pos {z : ℝ} (hz : 0 < z) : 0 < independenceEval G z := by
  classical
  rw [independenceEval_eq_sum]
  apply Finset.sum_pos
  · intro s hs
    exact pow_pos hz _
  · exact ⟨IndepFinset.empty G, Finset.mem_univ _⟩

end Finite

end Erdos993
