import Erdos993.Forest.CharacteristicTransfer

/-!
# Independent-component Fourier factorization for Appendix A

Exact finite product formulas for independence polynomials, hard-core
characteristic functions, characteristic moduli, and logarithmic losses over a
pairwise disjoint family of mutually nonadjacent induced subgraphs.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators ENNReal
open ActualRootedVariance
open ActualRootedVariance.ComponentRooting

universe u v

noncomputable local instance finiteSubtypeA6
    {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x : α // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Hard-core characteristic functions are invariant under graph isomorphism. -/
theorem hardCoreLaw_characteristic_iso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).characteristic θ =
      (hardCoreLaw H z hz).characteristic θ := by
  rw [hardCoreLaw_characteristic_eq_eval₂,
    hardCoreLaw_characteristic_eq_eval₂, independencePolynomial_iso e]
  congr 1
  simp only [independenceEval, independencePolynomialReal,
    independencePolynomial_iso e]

/-- Hard-core characteristic moduli are invariant under graph isomorphism. -/
theorem hardCoreLaw_characteristicModulus_iso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).characteristicModulus θ =
      (hardCoreLaw H z hz).characteristicModulus θ := by
  simp only [FiniteLatticeLaw.characteristicModulus,
    FiniteLatticeLaw.norm_centeredCharacteristic_eq]
  rw [hardCoreLaw_characteristic_iso e z θ hz]

/-- Hard-core logarithmic losses are invariant under graph isomorphism. -/
theorem hardCoreLaw_logarithmicLoss_iso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).logarithmicLoss θ =
      (hardCoreLaw H z hz).logarithmicLoss θ := by
  unfold FiniteLatticeLaw.logarithmicLoss
  rw [hardCoreLaw_characteristicModulus_iso e z θ hz]

private noncomputable def induceFinsetUnionIsoA6
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

private theorem independencePolynomial_isEmptyA6
    {A : Type u} [Fintype A] [IsEmpty A] (G : SimpleGraph A) :
    independencePolynomial G = 1 := by
  classical
  letI : Subsingleton (IndepFinset G) :=
    ⟨fun s t => by
      apply Subtype.ext
      exact Finset.eq_empty_of_isEmpty s.val |>.trans
        (Finset.eq_empty_of_isEmpty t.val).symm⟩
  rw [independencePolynomial_eq_sum]
  rw [Fintype.sum_subsingleton _ (IndepFinset.empty G)]
  simp

private theorem independencePolynomial_induceFinset_unionA6
    {A : Type u} [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (a b : Finset A)
    (hd : Disjoint a b)
    (hcross : ∀ ⦃x y : A⦄, x ∈ a → y ∈ b → ¬ G.Adj x y) :
    independencePolynomial (G.induce (↑(a ∪ b) : Set A)) =
      independencePolynomial (G.induce (↑a : Set A)) *
        independencePolynomial (G.induce (↑b : Set A)) := by
  rw [← independencePolynomial_iso (induceFinsetUnionIsoA6 G a b hd hcross)]
  exact independencePolynomial_sum _ _

/-- The independence polynomial of a finite union of mutually nonadjacent
induced pieces is the product of the piece polynomials. -/
theorem independencePolynomial_induceFinset_biUnion
    {ι : Type u} {A : Type v} [DecidableEq ι] [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : (↑s : Set ι).PairwiseDisjoint t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ ⦃x y : A⦄, x ∈ t i → y ∈ t j → ¬ G.Adj x y) :
    independencePolynomial (G.induce (↑(s.biUnion t) : Set A)) =
      ∏ i ∈ s, independencePolynomial (G.induce (↑(t i) : Set A)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      letI : IsEmpty {x : A // x ∈ ((∅ : Finset ι).biUnion t)} :=
        ⟨fun x => by
          obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp x.2
          exact Finset.notMem_empty i hi⟩
      exact independencePolynomial_isEmptyA6
        (G.induce (↑((∅ : Finset ι).biUnion t) : Set A))
  | @insert i s hi ih =>
      have hi_mem : i ∈ insert i s := Finset.mem_insert_self i s
      have hdisj_i : Disjoint (t i) (s.biUnion t) := by
        rw [Finset.disjoint_left]
        intro x hxi hxunion
        obtain ⟨j, hjs, hxj⟩ := Finset.mem_biUnion.mp hxunion
        have hij : i ≠ j := by rintro rfl; exact hi hjs
        exact (Finset.disjoint_left.mp
          (hdisj (by simp) (by simp [hjs]) hij)) hxi hxj
      have hcross_i : ∀ ⦃x y : A⦄,
          x ∈ t i → y ∈ s.biUnion t → ¬ G.Adj x y := by
        intro x y hxi hyunion
        obtain ⟨j, hjs, hyj⟩ := Finset.mem_biUnion.mp hyunion
        have hij : i ≠ j := by rintro rfl; exact hi hjs
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
        independencePolynomial
            (G.induce (↑((insert i s).biUnion t) : Set A)) =
            independencePolynomial (G.induce (↑(t i) : Set A)) *
              independencePolynomial
                (G.induce (↑(s.biUnion t) : Set A)) := by
                  rw [Finset.biUnion_insert]
                  exact independencePolynomial_induceFinset_unionA6
                    G (t i) (s.biUnion t) hdisj_i hcross_i
        _ = independencePolynomial (G.induce (↑(t i) : Set A)) *
              ∏ j ∈ s, independencePolynomial
                (G.induce (↑(t j) : Set A)) := by
                  rw [ih hdisj_s hcross_s]
        _ = ∏ j ∈ insert i s,
              independencePolynomial (G.induce (↑(t j) : Set A)) := by
                  rw [Finset.prod_insert hi]

/-- Exact characteristic product over mutually nonadjacent induced pieces. -/
theorem hardCoreLaw_characteristic_induceFinset_biUnion
    {ι : Type u} {A : Type v} [DecidableEq ι] [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : (↑s : Set ι).PairwiseDisjoint t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ ⦃x y : A⦄, x ∈ t i → y ∈ t j → ¬ G.Adj x y)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw (G.induce (↑(s.biUnion t) : Set A)) z hz).characteristic θ =
      ∏ i ∈ s,
        (hardCoreLaw (G.induce (↑(t i) : Set A)) z hz).characteristic θ := by
  classical
  rw [hardCoreLaw_characteristic_eq_eval₂,
    independencePolynomial_induceFinset_biUnion G s t hdisj hcross]
  have heval :
      Polynomial.eval₂ (Nat.castRingHom ℂ)
          ((z : ℂ) * FiniteLatticeLaw.phase θ 1)
          (∏ i ∈ s, independencePolynomial (G.induce (↑(t i) : Set A))) =
        ∏ i ∈ s, Polynomial.eval₂ (Nat.castRingHom ℂ)
          ((z : ℂ) * FiniteLatticeLaw.phase θ 1)
          (independencePolynomial (G.induce (↑(t i) : Set A))) := by
    simpa only [Polynomial.coe_eval₂RingHom] using
      (map_prod
        (Polynomial.eval₂RingHom (Nat.castRingHom ℂ)
          ((z : ℂ) * FiniteLatticeLaw.phase θ 1))
        (fun i => independencePolynomial (G.induce (↑(t i) : Set A))) s)
  rw [heval]
  rw [independenceEval_induceFinset_biUnion G s t hdisj hcross]
  push_cast
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hardCoreLaw_characteristic_eq_eval₂]

/-- Exact characteristic-modulus product over mutually nonadjacent induced
pieces. -/
theorem hardCoreLaw_characteristicModulus_induceFinset_biUnion
    {ι : Type u} {A : Type v} [DecidableEq ι] [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : (↑s : Set ι).PairwiseDisjoint t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ ⦃x y : A⦄, x ∈ t i → y ∈ t j → ¬ G.Adj x y)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw (G.induce (↑(s.biUnion t) : Set A)) z hz).characteristicModulus θ =
      ∏ i ∈ s,
        (hardCoreLaw (G.induce (↑(t i) : Set A)) z hz).characteristicModulus θ := by
  classical
  simp only [FiniteLatticeLaw.characteristicModulus,
    FiniteLatticeLaw.norm_centeredCharacteristic_eq]
  rw [hardCoreLaw_characteristic_induceFinset_biUnion G s t hdisj hcross]
  exact norm_prod _ _

private theorem neg_log_ofReal_prod_eq_sum
    {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) :
    -ENNReal.log (ENNReal.ofReal (∏ i ∈ s, m i)) =
      ∑ i ∈ s, (-ENNReal.log (ENNReal.ofReal (m i))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hmi : 0 ≤ m i := hm i (by simp)
      have hms : ∀ j ∈ s, 0 ≤ m j := fun j hj => hm j (by simp [hj])
      rw [Finset.prod_insert hi, ENNReal.ofReal_mul hmi,
        ENNReal.log_mul_add, Finset.sum_insert hi]
      have hlogprod : ENNReal.log (ENNReal.ofReal (∏ x ∈ s, m x)) ≠ ⊤ :=
        ne_of_lt (ENNReal.log_lt_top_iff.mpr ENNReal.ofReal_lt_top)
      have hlogi : ENNReal.log (ENNReal.ofReal (m i)) ≠ ⊤ :=
        ne_of_lt (ENNReal.log_lt_top_iff.mpr ENNReal.ofReal_lt_top)
      rw [EReal.neg_add (Or.inr hlogprod) (Or.inl hlogi), sub_eq_add_neg,
        ih hms]

/-- Exact additivity of the extended-real logarithmic loss over independent
pieces, including zero characteristic factors. -/
theorem hardCoreLaw_logarithmicLoss_induceFinset_biUnion
    {ι : Type u} {A : Type v} [DecidableEq ι] [Fintype A] [DecidableEq A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : (↑s : Set ι).PairwiseDisjoint t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ ⦃x y : A⦄, x ∈ t i → y ∈ t j → ¬ G.Adj x y)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw (G.induce (↑(s.biUnion t) : Set A)) z hz).logarithmicLoss θ =
      ∑ i ∈ s,
        (hardCoreLaw (G.induce (↑(t i) : Set A)) z hz).logarithmicLoss θ := by
  classical
  unfold FiniteLatticeLaw.logarithmicLoss
  rw [hardCoreLaw_characteristicModulus_induceFinset_biUnion
    G s t hdisj hcross]
  exact neg_log_ofReal_prod_eq_sum s
    (fun i => (hardCoreLaw (G.induce (↑(t i) : Set A)) z hz).characteristicModulus θ)
    (fun i hi => FiniteLatticeLaw.characteristicModulus_nonneg _ _)

private noncomputable def induceUnivIsoA6
    {A : Type u} [Fintype A] (G : SimpleGraph A) :
    G.induce ((Finset.univ : Finset A) : Set A) ≃g G := by
  classical
  let e : {x : A // x ∈ (Finset.univ : Finset A)} ≃ A :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; rfl }
  exact
    { toEquiv := e
      map_rel_iff' := by intro x y; rfl }

/-- Exact product of characteristic moduli over the connected components
selected by a component rooting. -/
theorem hardCoreLaw_characteristicModulus_eq_prod_componentRoots
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).characteristicModulus θ =
      ∏ r ∈ R.componentRoots (G := G),
        (hardCoreLaw (R.Subtree (G := G) r) z hz).characteristicModulus θ := by
  classical
  have hprod := hardCoreLaw_characteristicModulus_induceFinset_biUnion
    G (R.componentRoots (G := G))
      (fun r => R.descendants (G := G) r)
      (R.componentRoots_pairwiseDisjoint_descendants (G := G))
      (fun i hi j hj hij x y hx hy =>
        R.componentRoots_no_cross_edges (G := G)
          i hi j hj hij x hx y hy) z θ hz
  rw [R.componentRoots_biUnion_descendants (G := G)] at hprod
  calc
    (hardCoreLaw G z hz).characteristicModulus θ =
        (hardCoreLaw
          (G.induce ((Finset.univ : Finset V) : Set V)) z hz).characteristicModulus θ :=
      (hardCoreLaw_characteristicModulus_iso (induceUnivIsoA6 G) z θ hz).symm
    _ = _ := hprod

/-- Exact additivity of logarithmic loss over the connected components selected
by a component rooting. -/
theorem hardCoreLaw_logarithmicLoss_eq_sum_componentRoots
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).logarithmicLoss θ =
      ∑ r ∈ R.componentRoots (G := G),
        (hardCoreLaw (R.Subtree (G := G) r) z hz).logarithmicLoss θ := by
  classical
  have hsum := hardCoreLaw_logarithmicLoss_induceFinset_biUnion
    G (R.componentRoots (G := G))
      (fun r => R.descendants (G := G) r)
      (R.componentRoots_pairwiseDisjoint_descendants (G := G))
      (fun i hi j hj hij x y hx hy =>
        R.componentRoots_no_cross_edges (G := G)
          i hi j hj hij x hx y hy) z θ hz
  rw [R.componentRoots_biUnion_descendants (G := G)] at hsum
  calc
    (hardCoreLaw G z hz).logarithmicLoss θ =
        (hardCoreLaw
          (G.induce ((Finset.univ : Finset V) : Set V)) z hz).logarithmicLoss θ :=
      (hardCoreLaw_logarithmicLoss_iso (induceUnivIsoA6 G) z θ hz).symm
    _ = _ := hsum

/-- Exact product of characteristic moduli for the root-vacant law of a
rooted descendant subtree. -/
theorem hardCoreLaw_characteristicModulus_deleteSubtreeRoot_eq_prod_children
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).characteristicModulus θ =
      ∏ v ∈ R.children (G := G) u,
        (R.subtreeLawAt z hz v).characteristicModulus θ := by
  classical
  rw [hardCoreLaw_characteristicModulus_iso
    (R.deleteSubtreeRootIsoChildren (G := G) u) z θ hz]
  simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
    hardCoreLaw_characteristicModulus_induceFinset_biUnion
      G (R.children (G := G) u)
      (fun v => R.descendants (G := G) v)
      (R.children_pairwiseDisjoint_descendants (G := G) hG u)
      (fun i hi j hj hij x y hx hy =>
        R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u i).mp hi)
          ((R.mem_children (G := G) u j).mp hj) hij
          ((R.mem_descendants (G := G) i x).mp hx)
          ((R.mem_descendants (G := G) j y).mp hy)) z θ hz

/-- Exact additivity of logarithmic loss for the root-vacant law over the
child descendant subtrees. -/
theorem hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).logarithmicLoss θ =
      ∑ v ∈ R.children (G := G) u,
        (R.subtreeLawAt z hz v).logarithmicLoss θ := by
  classical
  rw [hardCoreLaw_logarithmicLoss_iso
    (R.deleteSubtreeRootIsoChildren (G := G) u) z θ hz]
  simpa only [ActualRootedVariance.ComponentRooting.subtreeLawAt] using
    hardCoreLaw_logarithmicLoss_induceFinset_biUnion
      G (R.children (G := G) u)
      (fun v => R.descendants (G := G) v)
      (R.children_pairwiseDisjoint_descendants (G := G) hG u)
      (fun i hi j hj hij x y hx hy =>
        R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u i).mp hi)
          ((R.mem_children (G := G) u j).mp hj) hij
          ((R.mem_descendants (G := G) i x).mp hx)
          ((R.mem_descendants (G := G) j y).mp hy)) z θ hz

end
end AppendixA
end Forest
end Erdos993
