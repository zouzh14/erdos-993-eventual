import Erdos993.DisjointUnion
import Erdos993.GraphIso

open scoped BigOperators

namespace Erdos993

universe u v

private theorem independenceEval_iso_aux
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) :
    independenceEval G z = independenceEval H z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]

private theorem independenceEval_sum_aux
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) (z : ℝ) :
    independenceEval (G ⊕g H) z = independenceEval G z * independenceEval H z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_sum, Polynomial.map_mul, Polynomial.eval_mul]

private theorem independenceEval_isEmpty_aux
    {A : Type u} [Fintype A] [IsEmpty A] (G : SimpleGraph A) (z : ℝ) :
    independenceEval G z = 1 := by
  classical
  letI : Subsingleton (IndepFinset G) :=
    ⟨fun s t => by
      apply Subtype.ext
      exact Finset.eq_empty_of_isEmpty s.val |>.trans
        (Finset.eq_empty_of_isEmpty t.val).symm⟩
  rw [independenceEval_eq_sum]
  rw [Fintype.sum_subsingleton _ (IndepFinset.empty G)]
  simp

private noncomputable def induceFinsetUnionIso
    {A : Type u} [DecidableEq A] (G : SimpleGraph A) (a b : Finset A)
    (hd : Disjoint a b)
    (hcross : ∀ ⦃x y : A⦄, x ∈ a → y ∈ b → ¬ G.Adj x y) :
    G.induce (↑a : Set A) ⊕g G.induce (↑b : Set A) ≃g
      G.induce (↑(a ∪ b) : Set A) := by
  classical
  refine
    { toEquiv := Equiv.Finset.union a b hd
      map_rel_iff' := ?_ }
  rintro (x | x) (y | y)
  · simp
  · have hxy : ¬ G.Adj (x : A) (y : A) := hcross x.2 y.2
    simp [SimpleGraph.sum_adj, hxy]
  · have hxy : ¬ G.Adj (x : A) (y : A) := fun h => hcross y.2 x.2 h.symm
    simp [SimpleGraph.sum_adj, hxy]
  · simp

private theorem independenceEval_induceFinset_union_aux
    {A : Type u} [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (a b : Finset A)
    (hd : Disjoint a b)
    (hcross : ∀ ⦃x y : A⦄, x ∈ a → y ∈ b → ¬ G.Adj x y)
    (z : ℝ) :
    independenceEval (G.induce (↑(a ∪ b) : Set A)) z =
      independenceEval (G.induce (↑a : Set A)) z *
        independenceEval (G.induce (↑b : Set A)) z := by
  rw [← independenceEval_iso_aux (induceFinsetUnionIso G a b hd hcross) z]
  exact independenceEval_sum_aux _ _ z

/-- The hard-core partition function of a finite union of pairwise
vertex-disjoint, mutually nonadjacent induced graphs is the product of the
partition functions of the induced pieces. -/
theorem independenceEval_induceFinset_biUnion
    {ι : Type u} {A : Type v} [DecidableEq ι] [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : (↑s : Set ι).PairwiseDisjoint t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ ⦃x y : A⦄, x ∈ t i → y ∈ t j → ¬ G.Adj x y)
    (z : ℝ) :
    independenceEval (G.induce (↑(s.biUnion t) : Set A)) z =
      ∏ i ∈ s, independenceEval (G.induce (↑(t i) : Set A)) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      letI : IsEmpty {x : A // x ∈ ((∅ : Finset ι).biUnion t)} :=
        ⟨fun x => by
          obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp x.2
          exact Finset.notMem_empty i hi⟩
      exact independenceEval_isEmpty_aux
        (G.induce (↑((∅ : Finset ι).biUnion t) : Set A)) z
  | @insert i s hi ih =>
      have hi_mem : i ∈ insert i s := Finset.mem_insert_self i s
      have hdisj_i : Disjoint (t i) (s.biUnion t) := by
        rw [Finset.disjoint_left]
        intro x hxi hxunion
        simp only [Finset.mem_biUnion] at hxunion
        obtain ⟨j, hjs, hxj⟩ := hxunion
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hi hjs
        exact (Finset.disjoint_left.mp
          (hdisj (by simp) (by simp [hjs]) hij)) hxi hxj
      have hcross_i : ∀ ⦃x y : A⦄,
          x ∈ t i → y ∈ s.biUnion t → ¬ G.Adj x y := by
        intro x y hxi hyunion
        simp only [Finset.mem_biUnion] at hyunion
        obtain ⟨j, hjs, hyj⟩ := hyunion
        have hij : i ≠ j := by
          intro hij
          subst j
          exact hi hjs
        exact hcross i hi_mem j (Finset.mem_insert_of_mem hjs) hij hxi hyj
      have hdisj_s : (↑s : Set ι).PairwiseDisjoint t := by
        intro j hjs k hks hjk
        exact hdisj (by simp [hjs]) (by simp [hks]) hjk
      have hcross_s : ∀ j ∈ s, ∀ k ∈ s, j ≠ k →
          ∀ ⦃x y : A⦄, x ∈ t j → y ∈ t k → ¬ G.Adj x y := by
        intro j hjs k hks hjk x y hx hy
        exact hcross j (Finset.mem_insert_of_mem hjs)
          k (Finset.mem_insert_of_mem hks) hjk hx hy
      calc
        independenceEval (G.induce (↑((insert i s).biUnion t) : Set A)) z =
            independenceEval (G.induce (↑(t i) : Set A)) z *
              independenceEval (G.induce (↑(s.biUnion t) : Set A)) z := by
                rw [Finset.biUnion_insert]
                exact independenceEval_induceFinset_union_aux
                  G (t i) (s.biUnion t) hdisj_i hcross_i z
        _ = independenceEval (G.induce (↑(t i) : Set A)) z *
              ∏ j ∈ s, independenceEval (G.induce (↑(t j) : Set A)) z := by
                rw [ih hdisj_s hcross_s]
        _ = ∏ j ∈ insert i s,
              independenceEval (G.induce (↑(t j) : Set A)) z := by
                rw [Finset.prod_insert hi]

end Erdos993
