import Erdos993.Forest.RootedVariance
import Erdos993.FiniteDisjointUnion
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open scoped BigOperators

namespace Erdos993

universe u

namespace ActualRootedVariance

open Forest

noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

private theorem eval_iso {A B : Type u} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) :
    independenceEval G z = independenceEval H z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]

private theorem mean_iso {A B : Type u} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).mean = (Forest.hardCoreLaw H z hz).mean := by
  unfold Forest.FiniteLatticeLaw.mean
  apply Fintype.sum_equiv (indepFinsetIsoEquiv e)
  intro s
  simp only [Forest.hardCoreLaw]
  rw [indepFinsetIsoEquiv_card, eval_iso e z]

private theorem second_iso {A B : Type u} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).secondMoment =
      (Forest.hardCoreLaw H z hz).secondMoment := by
  unfold Forest.FiniteLatticeLaw.secondMoment
  apply Fintype.sum_equiv (indepFinsetIsoEquiv e)
  intro s
  simp only [Forest.hardCoreLaw]
  rw [indepFinsetIsoEquiv_card, eval_iso e z]

private theorem variance_iso {A B : Type u} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).variance = (Forest.hardCoreLaw H z hz).variance := by
  rw [Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    mean_iso e z hz, second_iso e z hz]

/-- Public variance transport for homogeneous hard-core laws under a genuine
graph isomorphism. -/
theorem hardCoreLaw_variance_iso {A B : Type u} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).variance = (Forest.hardCoreLaw H z hz).variance :=
  variance_iso e z hz

private noncomputable def unionIso {A : Type u} [DecidableEq A]
    (G : SimpleGraph A) (a b : Finset A) (hd : Disjoint a b)
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

private theorem eval_sum {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) (z : ℝ) :
    independenceEval (G ⊕g H) z = independenceEval G z * independenceEval H z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_sum, Polynomial.map_mul, Polynomial.eval_mul]

private theorem sum_product_add {A B : Type u} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → ℝ) (g : B → ℝ) :
    (∑ a, ∑ b, (p a * q b) * (f a + g b)) =
      (∑ a, p a * f a) * (∑ b, q b) +
      (∑ a, p a) * (∑ b, q b * g b) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  ring

private theorem mean_sum {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G ⊕g H) z hz).mean =
      (Forest.hardCoreLaw G z hz).mean + (Forest.hardCoreLaw H z hz).mean := by
  unfold Forest.FiniteLatticeLaw.mean
  change (∑ s : IndepFinset (G ⊕g H), z ^ s.val.card /
      independenceEval (G ⊕g H) z * (s.val.card : ℝ)) = _
  rw [show (∑ s : IndepFinset (G ⊕g H), z ^ s.val.card /
      independenceEval (G ⊕g H) z * (s.val.card : ℝ)) =
      ∑ p : IndepFinset G × IndepFinset H,
        ((Forest.hardCoreLaw G z hz).probability p.1 *
          (Forest.hardCoreLaw H z hz).probability p.2) *
          ((p.1.val.card + p.2.val.card : ℕ) : ℝ) by
    apply Fintype.sum_equiv (indepFinsetSumEquiv G H)
    intro s
    rw [← indepFinsetSumEquiv_card G H s]
    simp only [Forest.hardCoreLaw]
    rw [pow_add, eval_sum]
    field_simp]
  rw [Fintype.sum_prod_type]
  simp only [Nat.cast_add]
  rw [sum_product_add]
  rw [(Forest.hardCoreLaw G z hz).probability_sum,
    (Forest.hardCoreLaw H z hz).probability_sum]
  simp only [Forest.hardCoreLaw]
  ring

private theorem sum_product_sq_add {A B : Type u} [Fintype A] [Fintype B]
    (p : A → ℝ) (q : B → ℝ) (f : A → ℝ) (g : B → ℝ) :
    (∑ a, ∑ b, (p a * q b) * (f a + g b) ^ 2) =
      (∑ a, p a * f a ^ 2) * (∑ b, q b) +
      (∑ a, p a) * (∑ b, q b * g b ^ 2) +
      2 * (∑ a, p a * f a) * (∑ b, q b * g b) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  rw [show 2 * (∑ a, p a * f a) * (∑ b, q b * g b) =
      (∑ a, 2 * (p a * f a)) * (∑ b, q b * g b) by
    rw [← Finset.mul_sum]]
  rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  ring_nf

private theorem second_sum {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G ⊕g H) z hz).secondMoment =
      (Forest.hardCoreLaw G z hz).secondMoment +
      (Forest.hardCoreLaw H z hz).secondMoment +
      2 * (Forest.hardCoreLaw G z hz).mean *
        (Forest.hardCoreLaw H z hz).mean := by
  unfold Forest.FiniteLatticeLaw.secondMoment Forest.FiniteLatticeLaw.mean
  change (∑ s : IndepFinset (G ⊕g H), z ^ s.val.card /
      independenceEval (G ⊕g H) z * (s.val.card : ℝ) ^ 2) = _
  rw [show (∑ s : IndepFinset (G ⊕g H), z ^ s.val.card /
      independenceEval (G ⊕g H) z * (s.val.card : ℝ) ^ 2) =
      ∑ p : IndepFinset G × IndepFinset H,
        ((Forest.hardCoreLaw G z hz).probability p.1 *
          (Forest.hardCoreLaw H z hz).probability p.2) *
          ((p.1.val.card + p.2.val.card : ℕ) : ℝ) ^ 2 by
    apply Fintype.sum_equiv (indepFinsetSumEquiv G H)
    intro s
    rw [← indepFinsetSumEquiv_card G H s]
    simp only [Forest.hardCoreLaw]
    rw [pow_add, eval_sum]
    field_simp]
  rw [Fintype.sum_prod_type]
  simp only [Nat.cast_add]
  rw [sum_product_sq_add]
  rw [(Forest.hardCoreLaw G z hz).probability_sum,
    (Forest.hardCoreLaw H z hz).probability_sum]
  simp only [Forest.hardCoreLaw]
  ring

private theorem variance_sum {A B : Type u} [Fintype A] [Fintype B]
    (G : SimpleGraph A) (H : SimpleGraph B) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G ⊕g H) z hz).variance =
      (Forest.hardCoreLaw G z hz).variance + (Forest.hardCoreLaw H z hz).variance := by
  rw [Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    mean_sum, second_sum]
  ring

private theorem mean_empty {A : Type u} [Fintype A] [IsEmpty A]
    (G : SimpleGraph A) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).mean = 0 := by
  unfold Forest.FiniteLatticeLaw.mean
  apply Finset.sum_eq_zero
  intro s hs
  have h : s.val = ∅ := Finset.eq_empty_of_isEmpty s.val
  simp [Forest.hardCoreLaw, h]

private theorem variance_empty {A : Type u} [Fintype A] [IsEmpty A]
    (G : SimpleGraph A) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).variance = 0 := by
  unfold Forest.FiniteLatticeLaw.variance
  rw [mean_empty]
  apply Finset.sum_eq_zero
  intro s hs
  have h : s.val = ∅ := Finset.eq_empty_of_isEmpty s.val
  simp [Forest.hardCoreLaw, h]

private theorem mean_biUnion {ι : Type*} {A : Type u} [DecidableEq A] [Fintype A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G.induce {x | x ∈ s.biUnion t}) z hz).mean =
      ∑ i ∈ s, (Forest.hardCoreLaw (G.induce {x | x ∈ t i}) z hz).mean := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      haveI : IsEmpty {x // x ∈ (∅ : Finset ι).biUnion t} :=
        ⟨fun x => by
          obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp x.property
          exact Finset.notMem_empty i hi⟩
      exact mean_empty (A := {x : A // x ∈ (∅ : Finset ι).biUnion t})
        (G.induce {x | x ∈ (∅ : Finset ι).biUnion t}) z hz
  | @insert a s ha ih =>
      have hd : Disjoint (t a) (s.biUnion t) := by
        rw [Finset.disjoint_biUnion_right]
        intro b hb
        exact hdisj (by simp) (by simp [hb]) (by intro h; subst b; exact ha hb)
      have hc : ∀ ⦃x y : A⦄, x ∈ t a → y ∈ s.biUnion t → ¬ G.Adj x y := by
        intro x y hx hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨b, hb, hyb⟩ := hy
        exact hcross a (by simp) b (by simp [hb]) (by intro h; subst b; exact ha hb) x hx y hyb
      have hd' : Set.PairwiseDisjoint (↑s : Set ι) t := fun i hi j hj hij =>
        hdisj (by simp [hi]) (by simp [hj]) hij
      have hc' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y := by
        intro i hi j hj hij
        exact hcross i (by simp [hi]) j (by simp [hj]) hij
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc
        (Forest.hardCoreLaw (G.induce {x | x ∈ t a ∪ s.biUnion t}) z hz).mean =
            (Forest.hardCoreLaw ((G.induce {x | x ∈ t a}) ⊕g
              (G.induce {x | x ∈ s.biUnion t})) z hz).mean :=
          (mean_iso (unionIso G (t a) (s.biUnion t) hd hc) z hz).symm
        _ = _ := by rw [mean_sum, ih hd' hc']

/-- The mean of a hard-core law on a finite union of pairwise disjoint,
mutually nonadjacent induced pieces is the sum of the piece means. -/
theorem hardCoreLaw_mean_induceFinset_biUnion
    {ι : Type*} {A : Type u} [DecidableEq A] [Fintype A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G.induce {x | x ∈ s.biUnion t}) z hz).mean =
      ∑ i ∈ s, (Forest.hardCoreLaw (G.induce {x | x ∈ t i}) z hz).mean :=
  mean_biUnion G s t hdisj hcross z hz

private theorem variance_biUnion {ι : Type*} {A : Type u} [DecidableEq A] [Fintype A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G.induce {x | x ∈ s.biUnion t}) z hz).variance =
      ∑ i ∈ s, (Forest.hardCoreLaw (G.induce {x | x ∈ t i}) z hz).variance := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      haveI : IsEmpty {x // x ∈ (∅ : Finset ι).biUnion t} :=
        ⟨fun x => by
          obtain ⟨i, hi, _⟩ := Finset.mem_biUnion.mp x.property
          exact Finset.notMem_empty i hi⟩
      exact variance_empty (A := {x : A // x ∈ (∅ : Finset ι).biUnion t})
        (G.induce {x | x ∈ (∅ : Finset ι).biUnion t}) z hz
  | @insert a s ha ih =>
      have hd : Disjoint (t a) (s.biUnion t) := by
        rw [Finset.disjoint_biUnion_right]
        intro b hb
        exact hdisj (by simp) (by simp [hb]) (by intro h; subst b; exact ha hb)
      have hc : ∀ ⦃x y : A⦄, x ∈ t a → y ∈ s.biUnion t → ¬ G.Adj x y := by
        intro x y hx hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨b, hb, hyb⟩ := hy
        exact hcross a (by simp) b (by simp [hb]) (by intro h; subst b; exact ha hb) x hx y hyb
      have hd' : Set.PairwiseDisjoint (↑s : Set ι) t := fun i hi j hj hij =>
        hdisj (by simp [hi]) (by simp [hj]) hij
      have hc' : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
          ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y := by
        intro i hi j hj hij
        exact hcross i (by simp [hi]) j (by simp [hj]) hij
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc
        (Forest.hardCoreLaw (G.induce {x | x ∈ t a ∪ s.biUnion t}) z hz).variance =
            (Forest.hardCoreLaw ((G.induce {x | x ∈ t a}) ⊕g
              (G.induce {x | x ∈ s.biUnion t})) z hz).variance :=
          (variance_iso (unionIso G (t a) (s.biUnion t) hd hc) z hz).symm
        _ = _ := by rw [variance_sum, ih hd' hc']

/-- Public variance additivity for a finite family of pairwise disjoint,
mutually nonadjacent induced hard-core components. -/
theorem hardCoreLaw_variance_induceFinset_biUnion
    {ι : Type*} {A : Type u} [DecidableEq A] [Fintype A]
    (G : SimpleGraph A) (s : Finset ι) (t : ι → Finset A)
    (hdisj : Set.PairwiseDisjoint (↑s : Set ι) t)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ∀ x ∈ t i, ∀ y ∈ t j, ¬ G.Adj x y)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw (G.induce {x | x ∈ s.biUnion t}) z hz).variance =
      ∑ i ∈ s, (Forest.hardCoreLaw (G.induce {x | x ∈ t i}) z hz).variance :=
  variance_biUnion G s t hdisj hcross z hz


private theorem hardCoreLaw_expectation_root
    {A : Type u} [Fintype A] (G : SimpleGraph A) (r : A)
    (z : ℝ) (hz : 0 < z) (f : ℕ → ℝ) :
    (∑ s : IndepFinset G, (Forest.hardCoreLaw G z hz).probability s * f s.val.card) =
      (independenceEval (deleteVertex G r) z / independenceEval G z) *
        (∑ s : IndepFinset (deleteVertex G r),
          (Forest.hardCoreLaw (deleteVertex G r) z hz).probability s * f s.val.card) +
      (z * independenceEval (deleteClosedNeighborhood G r) z /
        independenceEval G z) *
        (∑ s : IndepFinset (deleteClosedNeighborhood G r),
          (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability s *
            f (s.val.card + 1)) := by
  letI : Fintype (AvoidingIndepFinset G r) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset G r) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  simp only [Forest.hardCoreLaw]
  rw [show (∑ s : IndepFinset G,
      z ^ s.val.card / independenceEval G z * f s.val.card) =
      ∑ q : AvoidingIndepFinset G r ⊕ ContainingIndepFinset G r,
        Sum.elim
          (fun s => z ^ s.val.val.card / independenceEval G z * f s.val.val.card)
          (fun s => z ^ s.val.val.card / independenceEval G z * f s.val.val.card) q by
    apply Fintype.sum_equiv (indepFinsetPartitionEquiv G r)
    intro s
    by_cases h : r ∈ s.val <;> simp [indepFinsetPartitionEquiv, h]]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [show (∑ s : AvoidingIndepFinset G r,
      z ^ s.val.val.card / independenceEval G z * f s.val.val.card) =
      ∑ t : IndepFinset (deleteVertex G r),
        z ^ t.val.card / independenceEval G z * f t.val.card by
    symm
    apply Fintype.sum_equiv (avoidingEquiv G r)
    intro t
    rw [avoidingEquiv_card]]
  rw [show (∑ s : ContainingIndepFinset G r,
      z ^ s.val.val.card / independenceEval G z * f s.val.val.card) =
      ∑ t : IndepFinset (deleteClosedNeighborhood G r),
        z ^ (t.val.card + 1) / independenceEval G z * f (t.val.card + 1) by
    symm
    apply Fintype.sum_equiv (containingEquiv G r)
    intro t
    rw [containingEquiv_card]]
  simp only [pow_add, pow_one]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hQ : independenceEval (deleteVertex G r) z ≠ 0 :=
      (independenceEval_pos _ hz).ne'
    field_simp [hQ]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hC : independenceEval (deleteClosedNeighborhood G r) z ≠ 0 :=
      (independenceEval_pos _ hz).ne'
    field_simp [hC]

private theorem hardCoreLaw_mean_root
    {A : Type u} [Fintype A] (G : SimpleGraph A) (r : A)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).mean =
      (independenceEval (deleteVertex G r) z / independenceEval G z) *
        (Forest.hardCoreLaw (deleteVertex G r) z hz).mean +
      (z * independenceEval (deleteClosedNeighborhood G r) z /
        independenceEval G z) *
        (1 + (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).mean) := by
  rw [show (Forest.hardCoreLaw G z hz).mean =
      ∑ s : IndepFinset G, (Forest.hardCoreLaw G z hz).probability s *
        (s.val.card : ℝ) by rfl]
  rw [hardCoreLaw_expectation_root G r z hz (fun n => (n : ℝ))]
  congr 1
  rw [show (∑ s : IndepFinset (deleteClosedNeighborhood G r),
      (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability s *
        ((s.val.card + 1 : ℕ) : ℝ)) =
      (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).mean + 1 by
    simp only [Nat.cast_add, Nat.cast_one, mul_add, Finset.sum_add_distrib,
      mul_one]
    rw [(Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability_sum]
    rfl]
  ring

private theorem hardCoreLaw_secondMoment_root
    {A : Type u} [Fintype A] (G : SimpleGraph A) (r : A)
    (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw G z hz).secondMoment =
      (independenceEval (deleteVertex G r) z / independenceEval G z) *
        (Forest.hardCoreLaw (deleteVertex G r) z hz).secondMoment +
      (z * independenceEval (deleteClosedNeighborhood G r) z /
        independenceEval G z) *
        ((Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).secondMoment +
          2 * (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).mean + 1) := by
  rw [show (Forest.hardCoreLaw G z hz).secondMoment =
      ∑ s : IndepFinset G, (Forest.hardCoreLaw G z hz).probability s *
        (s.val.card : ℝ) ^ 2 by rfl]
  rw [hardCoreLaw_expectation_root G r z hz (fun n => (n : ℝ) ^ 2)]
  congr 1
  rw [show (∑ s : IndepFinset (deleteClosedNeighborhood G r),
      (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability s *
        ((s.val.card + 1 : ℕ) : ℝ) ^ 2) =
      (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).secondMoment +
        2 * (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).mean + 1 by
    simp only [Nat.cast_add, Nat.cast_one, add_sq, mul_add,
      Finset.sum_add_distrib, mul_one, one_pow]
    rw [show (∑ x : IndepFinset (deleteClosedNeighborhood G r),
        (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability x *
          (2 * (x.val.card : ℝ))) =
        2 * ∑ x : IndepFinset (deleteClosedNeighborhood G r),
          (Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability x *
            (x.val.card : ℝ) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring]
    rw [(Forest.hardCoreLaw (deleteClosedNeighborhood G r) z hz).probability_sum]
    rfl]


noncomputable local instance classicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

/-- A choice of one vertex in every connected component.  This is the exact
root datum used by the actual rooted construction. -/
structure ComponentRooting where
  root : G.ConnectedComponent → V
  root_mem : ∀ c, root c ∈ c

namespace ComponentRooting

/-- The root of the component containing `v`. -/
noncomputable def rootOf (R : ComponentRooting G) (v : V) : V :=
  R.root (G.connectedComponentMk v)

@[simp] theorem rootOf_mem_component (R : ComponentRooting G) (v : V) :
    R.rootOf (G := G) v ∈ (G.connectedComponentMk v).supp :=
  R.root_mem _

/-- An undirected edge oriented away from the selected component root. -/
def IsChild (R : ComponentRooting G) (u v : V) : Prop :=
  G.Adj u v ∧ G.dist (R.rootOf (G := G) v) v =
    G.dist (R.rootOf (G := G) v) u + 1

/-- The selected root reaches every vertex of its component. -/
theorem rootOf_reachable (R : ComponentRooting G) (v : V) :
    G.Reachable (R.rootOf (G := G) v) v := by
  let c := G.connectedComponentMk v
  exact c.reachable_of_mem_supp (R.root_mem c)
    SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- Root choices are constant along a reachable pair. -/
theorem rootOf_eq_of_reachable (R : ComponentRooting G) {u v : V}
    (h : G.Reachable u v) : R.rootOf (G := G) u = R.rootOf (G := G) v := by
  unfold rootOf
  rw [SimpleGraph.ConnectedComponent.sound h]

/-- Root choices are constant across an edge. -/
theorem rootOf_eq_of_adj (R : ComponentRooting G) {u v : V} (h : G.Adj u v) :
    R.rootOf (G := G) u = R.rootOf (G := G) v :=
  rootOf_eq_of_reachable (G := G) R h.reachable

/-- Applying `rootOf` twice is idempotent. -/
@[simp] theorem rootOf_rootOf (R : ComponentRooting G) (v : V) :
    R.rootOf (G := G) (R.rootOf (G := G) v) = R.rootOf (G := G) v := by
  unfold rootOf
  congr 1
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp (R.root_mem _)

/-- A shortest root-to-vertex path supplies a parent for every nonroot. -/
theorem exists_isChild_of_ne_root (R : ComponentRooting G) {v : V}
    (hv : v ≠ R.rootOf (G := G) v) : ∃ u, R.IsChild (G := G) u v := by
  let r := R.rootOf (G := G) v
  have hrv : G.Reachable r v := rootOf_reachable (G := G) R v
  obtain ⟨p, hpPath, hpLength⟩ := hrv.exists_path_of_dist
  have hpnn : ¬ p.Nil := SimpleGraph.Walk.not_nil_of_ne hv.symm
  have hprefix : p.dropLast.length = G.dist r p.penultimate :=
    SimpleGraph.length_eq_dist_of_subwalk hpLength
      ((SimpleGraph.Walk.isSubwalk_rfl p).dropLast)
  refine ⟨p.penultimate, p.adj_penultimate hpnn, ?_⟩
  change G.dist r v = G.dist r p.penultimate + 1
  calc
    G.dist r v = p.length := hpLength.symm
    _ = p.dropLast.length + 1 := (p.length_dropLast_add_one hpnn).symm
    _ = G.dist r p.penultimate + 1 := by rw [hprefix]

/-- No edge can point toward a selected root. -/
theorem not_isChild_of_eq_root (R : ComponentRooting G) {u v : V}
    (hv : v = R.rootOf (G := G) v) : ¬ R.IsChild (G := G) u v := by
  rintro ⟨_, hd⟩
  have hz : G.dist (R.rootOf (G := G) v) v = 0 := by rw [← hv]; simp
  omega

/-- In a forest the neighbour one level closer to the root is unique. -/
theorem isChild_unique (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u w v : V} (hu : R.IsChild (G := G) u v) (hw : R.IsChild (G := G) w v) :
    u = w := by
  let r := R.rootOf (G := G) v
  have hrv : G.Reachable r v := rootOf_reachable (G := G) R v
  have hru : G.Reachable r u := hrv.trans hu.1.symm.reachable
  have hrw : G.Reachable r w := hrv.trans hw.1.symm.reachable
  obtain ⟨pu, hpu⟩ := hru.exists_walk_length_eq_dist
  obtain ⟨pw, hpw⟩ := hrw.exists_walk_length_eq_dist
  have hpuv : (pu.concat hu.1).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by
      simpa [r, hpu] using hu.2.symm)
  have hpwv : (pw.concat hw.1).IsPath :=
    SimpleGraph.Walk.isPath_of_length_eq_dist _ (by
      simpa [r, hpw] using hw.2.symm)
  have heq :
      (⟨pu.concat hu.1, hpuv⟩ : G.Path r v) = ⟨pw.concat hw.1, hpwv⟩ :=
    hG.path_unique _ _
  have hpen := congrArg (fun q : G.Path r v => q.1.penultimate) heq
  simpa using hpen

/-- Every graph edge of a forest has exactly one outward orientation. -/
theorem adj_iff_isChild_or_reverse (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u v : V} : G.Adj u v ↔
      R.IsChild (G := G) u v ∨ R.IsChild (G := G) v u := by
  constructor
  · intro huv
    have hr : G.Reachable (R.rootOf (G := G) u) u :=
      rootOf_reachable (G := G) R u
    have hroots : R.rootOf (G := G) u = R.rootOf (G := G) v :=
      rootOf_eq_of_adj (G := G) R huv
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable
      (R.rootOf (G := G) u) huv hr with hdown | hup
    · right
      refine ⟨huv.symm, ?_⟩
      simpa [← hroots] using hdown
    · left
      refine ⟨huv, ?_⟩
      simpa [← hroots] using hup
  · rintro (h | h)
    · exact h.1
    · exact h.1.symm

/-- The two orientations of an edge cannot both hold. -/
theorem not_isChild_reverse (R : ComponentRooting G) {u v : V}
    (h : R.IsChild (G := G) u v) : ¬ R.IsChild (G := G) v u := by
  obtain ⟨hadj, hd⟩ := h
  rintro ⟨_, hd'⟩
  have hroots := rootOf_eq_of_adj (G := G) R hadj
  rw [← hroots] at hd
  omega

/-- Distance from the selected root; this is a genuine finite height on a component. -/
noncomputable def depth (R : ComponentRooting G) (v : V) : ℕ :=
  G.dist (R.rootOf (G := G) v) v

/-- Child edges increase root depth by exactly one. -/
theorem depth_child (R : ComponentRooting G) {u v : V}
    (h : R.IsChild (G := G) u v) : R.depth (G := G) v = R.depth (G := G) u + 1 := by
  have hr := rootOf_eq_of_adj (G := G) R h.1
  simpa [depth, hr] using h.2

/-- The selected root has depth zero. -/
@[simp] theorem depth_rootOf (R : ComponentRooting G) (v : V) :
    R.depth (G := G) (R.rootOf (G := G) v) = 0 := by
  simp [depth]

/-- The optional parent: roots have none, while a nonroot uses a shortest path. -/
noncomputable def parent (R : ComponentRooting G) (v : V) : Option V := by
  classical
  exact if h : v = R.rootOf (G := G) v then none
  else
    let c := G.connectedComponentMk v
    let hr : R.rootOf (G := G) v ∈ c.supp := R.root_mem c
    let hv : v ∈ c.supp := SimpleGraph.ConnectedComponent.connectedComponentMk_mem
    some (Classical.choose ((c.reachable_of_mem_supp hr hv).exists_path_of_dist)).penultimate

/-- Children as an actual finite set. -/
noncomputable def children (R : ComponentRooting G) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => R.IsChild (G := G) u v)

/-- A descendant is reached by zero or more child steps. -/
def IsDescendant (R : ComponentRooting G) (u v : V) : Prop :=
  Relation.ReflTransGen (fun x y => R.IsChild (G := G) x y) u v

/-- Actual finite descendant set. -/
noncomputable def descendants (R : ComponentRooting G) (u : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => R.IsDescendant (G := G) u v)

@[simp] theorem mem_children (R : ComponentRooting G) (u v : V) :
    v ∈ R.children (G := G) u ↔ R.IsChild (G := G) u v := by
  classical
  simp [children]

@[simp] theorem mem_descendants (R : ComponentRooting G) (u v : V) :
    v ∈ R.descendants (G := G) u ↔ R.IsDescendant (G := G) u v := by
  classical
  simp [descendants]

/-- Every vertex belongs to its own descendant set. -/
theorem self_mem_descendants (R : ComponentRooting G) (u : V) :
    u ∈ R.descendants (G := G) u := by
  rw [mem_descendants]
  exact Relation.ReflTransGen.refl

/-- Descendant steps are graph-reachable steps. -/
theorem isDescendant_reachable (R : ComponentRooting G) {u v : V}
    (h : R.IsDescendant (G := G) u v) : G.Reachable u v := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact h.mono (fun _ _ hc => hc.1)

/-- Descendant depth is monotone. -/
theorem depth_le_of_isDescendant (R : ComponentRooting G) {u v : V}
    (h : R.IsDescendant (G := G) u v) : R.depth (G := G) u ≤ R.depth (G := G) v := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact le_rfl
  | single h =>
      rw [depth_child (G := G) R h]
      omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A nontrivial descendant has strictly larger depth. -/
theorem depth_lt_of_isDescendant_of_ne (R : ComponentRooting G) {u v : V}
    (h : R.IsDescendant (G := G) u v) (hne : u ≠ v) :
    R.depth (G := G) u < R.depth (G := G) v := by
  rcases (Relation.ReflTransGen.cases_head_iff.mp h) with huv | ⟨w, huw, hwv⟩
  · exact (hne huv).elim
  · have hw := depth_le_of_isDescendant (G := G) R hwv
    rw [depth_child (G := G) R huw] at hw
    omega

/-- Equal-depth comparable vertices coincide. -/
theorem eq_of_isDescendant_of_depth_eq (R : ComponentRooting G) {u v : V}
    (h : R.IsDescendant (G := G) u v)
    (hd : R.depth (G := G) u = R.depth (G := G) v) : u = v := by
  by_contra hne
  have := depth_lt_of_isDescendant_of_ne (G := G) R h hne
  omega

/-- Two child branches in a forest cannot merge. -/
theorem child_eq_of_common_descendant (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u v w x : V} (huv : R.IsChild (G := G) u v)
    (huw : R.IsChild (G := G) u w)
    (hv : R.IsDescendant (G := G) v x)
    (hw : R.IsDescendant (G := G) w x) : v = w := by
  generalize hn : R.depth (G := G) x = n
  induction n using Nat.strong_induction_on generalizing x with
  | h n ih =>
      rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hv with hvx | ⟨pv, hvp, hpx⟩
      · subst x
        symm
        apply eq_of_isDescendant_of_depth_eq (G := G) R hw
        rw [depth_child (G := G) R huv, depth_child (G := G) R huw]
      · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hw with hwx | ⟨pw, hwp, hqx⟩
        · subst x
          apply eq_of_isDescendant_of_depth_eq (G := G) R hv
          rw [depth_child (G := G) R huv, depth_child (G := G) R huw]
        · have hpw : pv = pw := isChild_unique (G := G) hG R hpx hqx
          subst pw
          exact ih (R.depth (G := G) pv) (by
            have hd := depth_child (G := G) R hpx
            omega) hvp hwp rfl

/-- Distinct child subtrees are disjoint. -/
theorem disjoint_descendants_of_ne_children (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u v w : V} (hv : R.IsChild (G := G) u v) (hw : R.IsChild (G := G) u w)
    (hvw : v ≠ w) : Disjoint (R.descendants (G := G) v) (R.descendants (G := G) w) := by
  rw [Finset.disjoint_left]
  intro x hxv hxw
  have heq := child_eq_of_common_descendant (G := G) hG R hv hw
    ((mem_descendants (G := G) R v x).mp hxv)
    ((mem_descendants (G := G) R w x).mp hxw)
  exact hvw heq

/-- The child descendant family is pairwise disjoint. -/
theorem children_pairwiseDisjoint_descendants (hG : G.IsAcyclic)
    (R : ComponentRooting G) (u : V) :
    (↑(R.children (G := G) u) : Set V).PairwiseDisjoint
      (fun v => R.descendants (G := G) v) := by
  intro v hv w hw hvw
  exact disjoint_descendants_of_ne_children (G := G) hG R
    ((mem_children (G := G) R u v).mp hv)
    ((mem_children (G := G) R u w).mp hw) hvw

/-- A vertex is not contained in any proper child subtree. -/
theorem not_mem_descendants_child (R : ComponentRooting G) {u v : V}
    (h : R.IsChild (G := G) u v) : u ∉ R.descendants (G := G) v := by
  intro hu
  have hdesc := (mem_descendants (G := G) R v u).mp hu
  have hle := depth_le_of_isDescendant (G := G) R hdesc
  have hd := depth_child (G := G) R h
  omega

/-- Within a descendant subtree, the neighbours of its root are exactly its children. -/
theorem adj_of_descendant_iff_isChild (hG : G.IsAcyclic) (R : ComponentRooting G)
    {u v : V} (hv : R.IsDescendant (G := G) u v) :
    G.Adj u v ↔ R.IsChild (G := G) u v := by
  constructor
  · intro huv
    rcases (adj_iff_isChild_or_reverse (G := G) hG R).mp huv with h | h
    · exact h
    · have hle := depth_le_of_isDescendant (G := G) R hv
      have hd := depth_child (G := G) R h
      omega
  · exact fun h => h.1

/-- There are no edges between distinct child descendant subtrees. -/
theorem not_adj_of_distinct_child_descendants (hG : G.IsAcyclic)
    (R : ComponentRooting G) {u v w x y : V}
    (hv : R.IsChild (G := G) u v) (hw : R.IsChild (G := G) u w) (hvw : v ≠ w)
    (hx : R.IsDescendant (G := G) v x) (hy : R.IsDescendant (G := G) w y) :
    ¬ G.Adj x y := by
  intro hxy
  rcases (adj_iff_isChild_or_reverse (G := G) hG R).mp hxy with hchild | hchild
  · have hyv : R.IsDescendant (G := G) v y :=
      (Relation.ReflTransGen.trans hx (Relation.ReflTransGen.single hchild))
    exact hvw (child_eq_of_common_descendant (G := G) hG R hv hw hyv hy)
  · have hxw : R.IsDescendant (G := G) w x :=
      Relation.ReflTransGen.trans hy (Relation.ReflTransGen.single hchild)
    exact hvw (child_eq_of_common_descendant (G := G) hG R hv hw hx hxw)

theorem IsDescendant.trans (R : ComponentRooting G) {u v w : V}
    (huv : R.IsDescendant (G := G) u v)
    (hvw : R.IsDescendant (G := G) v w) : R.IsDescendant (G := G) u w :=
  Relation.ReflTransGen.trans huv hvw

/-- A child and all of its descendants are descendants of the parent. -/
theorem child_descendant (R : ComponentRooting G) {u v w : V}
    (huv : R.IsChild (G := G) u v)
    (hvw : R.IsDescendant (G := G) v w) : R.IsDescendant (G := G) u w :=
  (Relation.ReflTransGen.single huv).trans hvw

/-- Descendants split into the root and descendants of one first child. -/
theorem isDescendant_iff_eq_or_child_descendant (R : ComponentRooting G) (u v : V) :
    R.IsDescendant (G := G) u v ↔
      u = v ∨ ∃ w, R.IsChild (G := G) u w ∧ R.IsDescendant (G := G) w v := by
  simpa [IsDescendant] using
    (Relation.ReflTransGen.cases_head_iff
      (r := fun x y => R.IsChild (G := G) x y) (a := u) (b := v))

/-- The selected component root is an ancestor of each component vertex. -/
theorem root_isDescendant (R : ComponentRooting G) (v : V) :
    R.IsDescendant (G := G) (R.rootOf (G := G) v) v := by
  let r := R.rootOf (G := G) v
  suffices h : ∀ n : ℕ, ∀ w : V, G.dist r w = n →
      R.rootOf (G := G) w = r → R.IsDescendant (G := G) r w by
    exact h (G.dist r v) v rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hd hrw
      by_cases hwr : w = r
      · subst w
        exact Relation.ReflTransGen.refl
      · have hwnr : w ≠ R.rootOf (G := G) w := by simpa [hrw] using hwr
        obtain ⟨p, hp⟩ := exists_isChild_of_ne_root (G := G) R hwnr
        have hpr : R.rootOf (G := G) p = r :=
          (rootOf_eq_of_adj (G := G) R hp.1).trans hrw
        have hdepth : n = G.dist r p + 1 := by
          calc
            n = G.dist r w := hd.symm
            _ = G.dist r p + 1 := by simpa [hrw] using hp.2
        have hip := ih (G.dist r p) (by omega) p rfl hpr
        exact hip.tail hp

/-- Descendants of a component root are exactly that component's support. -/
theorem mem_descendants_rootOf_iff (R : ComponentRooting G) (v w : V) :
    w ∈ R.descendants (G := G) (R.rootOf (G := G) v) ↔
      w ∈ (G.connectedComponentMk v).supp := by
  constructor
  · intro hw
    have hreach : G.Reachable (R.rootOf (G := G) v) w :=
      isDescendant_reachable (G := G) R ((mem_descendants (G := G) R _ _).mp hw)
    have hrootcomp : G.connectedComponentMk (R.rootOf (G := G) v) =
        G.connectedComponentMk v := R.root_mem (G.connectedComponentMk v)
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.sound hreach).symm.trans hrootcomp
  · intro hw
    rw [mem_descendants]
    have hcomp : G.connectedComponentMk w = G.connectedComponentMk v :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp hw
    have hroot : R.rootOf (G := G) w = R.rootOf (G := G) v := by
      unfold rootOf
      rw [hcomp]
    simpa [hroot] using root_isDescendant (G := G) R w

section DescendantFinsets

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Descendant finsets decompose into the vertex and its child subtrees. -/
theorem descendants_eq_insert_biUnion_children (R : ComponentRooting G) (u : V) :
    R.descendants (G := G) u =
      insert u ((R.children (G := G) u).biUnion
        (fun w => R.descendants (G := G) w)) := by
  classical
  ext v
  simp only [mem_descendants, Finset.mem_insert, Finset.mem_biUnion, mem_children]
  simpa [eq_comm] using isDescendant_iff_eq_or_child_descendant (G := G) R u v

end DescendantFinsets

/-- The graph induced by one actual descendant set. -/
abbrev Subtree (R : ComponentRooting G) (u : V) :
    SimpleGraph {v // v ∈ R.descendants (G := G) u} :=
  G.induce {v | v ∈ R.descendants (G := G) u}

/-- The root vertex as an element of its own descendant subtree. -/
def subtreeRoot (R : ComponentRooting G) (u : V) :
    {v // v ∈ R.descendants (G := G) u} :=
  ⟨u, R.self_mem_descendants (G := G) u⟩

/-- Actual descendant-subtree partition function, at the original canonical activity. -/
noncomputable def rootedP (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  independenceEval (R.Subtree (G := G) u) C.activity

/-- Actual root-vacant descendant-subtree partition function. -/
noncomputable def rootedQ (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  independenceEval
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) C.activity

/-- Actual root-occupied descendant-subtree partition function (including the root weight). -/
noncomputable def rootedA (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  C.activity * independenceEval
    (deleteClosedNeighborhood (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity

private noncomputable def childVertexUnion
    (R : ComponentRooting G) (u : V) : Finset V := by
  classical
  exact (R.children (G := G) u).biUnion
    (fun w => R.descendants (G := G) w)

private noncomputable def deleteSubtreeRootIsoChildUnion
    (R : ComponentRooting G) (u : V) :
    deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ childVertexUnion (G := G) R u} := by
  classical
  have hdecomp : R.descendants (G := G) u =
      insert u (childVertexUnion (G := G) R u) := by
    simpa only [childVertexUnion] using
      R.descendants_eq_insert_biUnion_children (G := G) u
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u} ≃
      {x : V // x ∈ childVertexUnion (G := G) R u} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          have hmem : x.1.1 ∈
              insert u (childVertexUnion (G := G) R u) := by
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
              simpa only [childVertexUnion] using y.2
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
  refine
    { toEquiv := e
      map_rel_iff' := ?_ }
  intro x y
  rfl

/-- Public graph-isomorphism bridge: deleting a descendant-subtree root leaves
exactly the induced disjoint union of its child descendant subtrees. -/
noncomputable def deleteSubtreeRootIsoChildren
    (R : ComponentRooting G) (u : V) :
    deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ (R.children (G := G) u).biUnion
        (fun v => R.descendants (G := G) v)} := by
  simpa only [childVertexUnion] using
    deleteSubtreeRootIsoChildUnion (G := G) R u

/-- Deleting the root of a rooted subtree leaves the mutually nonadjacent
subtrees rooted at its children. -/
theorem rootedQ_eq_prod_rootedP
    (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    R.rootedQ (G := G) C u =
      ∏ v ∈ R.children (G := G) u,
        R.rootedP (G := G) C v := by
  classical
  unfold rootedQ rootedP
  calc
    independenceEval
        (deleteVertex (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) C.activity =
      independenceEval
        (G.induce {x | x ∈ childVertexUnion (G := G) R u}) C.activity := by
            simp only [independenceEval, independencePolynomialReal]
            rw [independencePolynomial_iso
              (deleteSubtreeRootIsoChildUnion (G := G) R u)]
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval (R.Subtree (G := G) v) C.activity := by
          apply independenceEval_induceFinset_biUnion G
            (R.children (G := G) u)
            (fun v => R.descendants (G := G) v)
            (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u)
          intro v hv w hw hvw x y hx hy
          exact R.not_adj_of_distinct_child_descendants (G := G) C.isForest
            ((R.mem_children (G := G) u v).mp hv)
            ((R.mem_children (G := G) u w).mp hw) hvw
            ((R.mem_descendants (G := G) v x).mp hx)
            ((R.mem_descendants (G := G) w y).mp hy)

/-- The exact two-state partition recurrence on every actual descendant subtree. -/
theorem rootedP_eq_rootedQ_add_rootedA (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    R.rootedP (G := G) C u = R.rootedQ (G := G) C u + R.rootedA (G := G) C u := by
  let H := R.Subtree (G := G) u
  let r := R.subtreeRoot (G := G) u
  have hrec := rooted_recurrence H r
  apply_fun fun p : Polynomial ℕ =>
    Polynomial.eval C.activity (p.map (Nat.castRingHom ℝ)) at hrec
  simpa [rootedP, rootedQ, rootedA, independenceEval, independencePolynomialReal,
    rootedAvoidingPolynomial, rootedOccupiedRemainder,
    Polynomial.map_add, Polynomial.map_mul] using hrec

/-- Proper descendants of a vertex (the vertex itself removed). -/
noncomputable def properDescendants
    (R : ComponentRooting G) (u : V) : Finset V :=
  (R.descendants (G := G) u).erase u

noncomputable def deleteSubtreeRootIsoProperDescendants
    (R : ComponentRooting G) (u : V) :
    deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ properDescendants (G := G) R u} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u} ≃
      {x : V // x ∈ properDescendants (G := G) R u} :=
    { toFun := fun x =>
        ⟨x.1.1, by
          rw [properDescendants, Finset.mem_erase]
          exact ⟨by
            intro h
            apply x.2
            apply Subtype.ext
            exact h, x.1.2⟩⟩
      invFun := fun y =>
        have hy : y.1 ∈ (R.descendants (G := G) u).erase u := by
          simpa only [properDescendants] using y.2
        ⟨⟨y.1, (Finset.mem_erase.mp hy).2⟩, by
          intro h
          exact (Finset.mem_erase.mp hy).1 (congrArg Subtype.val h)⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  rfl

private noncomputable def deleteClosedSubtreeRootIsoProperChildUnion
    (hG : G.IsAcyclic) (R : ComponentRooting G) (u : V) :
    deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ (R.children (G := G) u).biUnion
        (fun v => properDescendants (G := G) R v)} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u ∧
          ¬ (R.Subtree (G := G) u).Adj (R.subtreeRoot (G := G) u) x} ≃
      {x : V // x ∈ (R.children (G := G) u).biUnion
        (fun v => properDescendants (G := G) R v)} :=
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
              exact (R.not_mem_descendants_child (G := G) huv) (this ▸ (Finset.mem_erase.mp hy).2)
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
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro x y
  rfl

/-- Exact occupied-root partition recurrence `A_u = z * product Q_child`. -/
theorem rootedA_eq_activity_mul_prod_rootedQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.rootedA (G := G) C u = C.activity *
      ∏ v ∈ R.children (G := G) u, R.rootedQ (G := G) C v := by
  classical
  unfold rootedA rootedQ
  congr 1
  calc
    independenceEval
        (deleteClosedNeighborhood (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) C.activity =
      independenceEval
        (G.induce {x | x ∈ (R.children (G := G) u).biUnion
          (fun v => properDescendants (G := G) R v)}) C.activity :=
        eval_iso (deleteClosedSubtreeRootIsoProperChildUnion
          (G := G) C.isForest R u) C.activity
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval (G.induce {x | x ∈ properDescendants (G := G) R v})
          C.activity := by
      apply independenceEval_induceFinset_biUnion G
        (R.children (G := G) u)
        (fun v => properDescendants (G := G) R v)
      · intro v hv w hw hvw
        exact (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u
          hv hw hvw).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)
      · intro v hv w hw hvw x y hx hy
        exact R.not_adj_of_distinct_child_descendants (G := G) C.isForest
          ((R.mem_children (G := G) _ _).mp hv) ((R.mem_children (G := G) _ _).mp hw) hvw
          ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hx).2)
          ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2)
    _ = ∏ v ∈ R.children (G := G) u,
        independenceEval
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) C.activity := by
      apply Finset.prod_congr rfl
      intro v hv
      exact (eval_iso (deleteSubtreeRootIsoProperDescendants
        (G := G) R v) C.activity).symm

/-- The actual subtree partition function is strictly positive. -/
theorem rootedP_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : 0 < R.rootedP (G := G) C u :=
  independenceEval_pos _ C.activity_pos

/-- The actual root-vacant partition function is strictly positive. -/
theorem rootedQ_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : 0 < R.rootedQ (G := G) C u :=
  independenceEval_pos _ C.activity_pos

/-- The actual root-occupied partition function is strictly positive. -/
theorem rootedA_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : 0 < R.rootedA (G := G) C u := by
  exact mul_pos C.activity_pos (independenceEval_pos _ C.activity_pos)

/-- Conditional root occupation probability in the actual descendant subtree. -/
noncomputable def occupationProbability (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  R.rootedA (G := G) C u / R.rootedP (G := G) C u

/-- Conditional root vacancy probability in the actual descendant subtree. -/
noncomputable def vacancyProbability (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  R.rootedQ (G := G) C u / R.rootedP (G := G) C u

/-- Occupation and vacancy are complementary. -/
theorem occupationProbability_add_vacancyProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupationProbability (G := G) C u + R.vacancyProbability (G := G) C u = 1 := by
  rw [occupationProbability, vacancyProbability, ← add_div,
    add_comm, ← rootedP_eq_rootedQ_add_rootedA (G := G) C R u]
  exact div_self (ne_of_gt (rootedP_pos (G := G) C R u))

/-- The actual conditional occupation probability is nonnegative. -/
theorem occupationProbability_nonneg (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    0 ≤ R.occupationProbability (G := G) C u :=
  (div_pos (rootedA_pos (G := G) C R u) (rootedP_pos (G := G) C R u)).le

/-- The actual conditional occupation probability is at most one. -/
theorem occupationProbability_le_one (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    R.occupationProbability (G := G) C u ≤ 1 := by
  have hq := (div_pos (rootedQ_pos (G := G) C R u)
    (rootedP_pos (G := G) C R u)).le
  have hq' : 0 ≤ R.vacancyProbability (G := G) C u := by
    simpa [vacancyProbability] using hq
  rw [← occupationProbability_add_vacancyProbability (G := G) C R u]
  exact le_add_of_nonneg_right hq'

/-- The actual hard-core law on a descendant subtree, at exactly `C.activity`. -/
noncomputable def subtreeLaw (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    FiniteLatticeLaw (IndepFinset (R.Subtree (G := G) u)) :=
  hardCoreLaw (R.Subtree (G := G) u) C.activity C.activity_pos

/-- Conditional mean given that the subtree root is absent. -/
noncomputable def vacantMean (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos).mean

/-- Conditional mean given that the subtree root is occupied. -/
noncomputable def occupiedMean (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  1 + (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos).mean

/-- The actual occupied-minus-vacant conditional mean displacement. -/
noncomputable def conditionalMeanDifference (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  R.occupiedMean (G := G) C u - R.vacantMean (G := G) C u

/-- Actual conditional subtree variance. -/
noncomputable def subtreeVariance (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  (R.subtreeLaw (G := G) C u).variance


/-- Second moment of the count conditional on a vacant subtree root. -/
noncomputable def vacantSecondMoment (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos).secondMoment

/-- Second moment of the full count conditional on an occupied subtree root. -/
noncomputable def occupiedSecondMoment (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  let L := hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos
  L.secondMoment + 2 * L.mean + 1

/-- Conditional variance given that the subtree root is vacant. -/
noncomputable def vacantVariance (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos).variance

/-- Conditional variance given that the subtree root is occupied. -/
noncomputable def occupiedVariance (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    C.activity C.activity_pos).variance

private theorem children_hcross (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    ∀ i ∈ R.children (G := G) u, ∀ j ∈ R.children (G := G) u, i ≠ j →
      ∀ x ∈ R.descendants (G := G) i, ∀ y ∈ R.descendants (G := G) j,
        ¬ G.Adj x y := by
  intro i hi j hj hij x hx y hy
  exact R.not_adj_of_distinct_child_descendants (G := G) C.isForest
    ((R.mem_children (G := G) _ _).mp hi) ((R.mem_children (G := G) _ _).mp hj) hij
    ((R.mem_descendants (G := G) _ _).mp hx) ((R.mem_descendants (G := G) _ _).mp hy)

/-- Exact Q-law conditional first-moment recurrence. -/
theorem vacantMean_eq_sum_subtreeMean
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vacantMean (G := G) C u =
      ∑ v ∈ R.children (G := G) u, (R.subtreeLaw (G := G) C v).mean := by
  classical
  unfold vacantMean subtreeLaw
  rw [mean_iso (deleteSubtreeRootIsoChildUnion (G := G) R u)]
  exact mean_biUnion G (R.children (G := G) u)
    (fun v => R.descendants (G := G) v)
    (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u)
    (children_hcross (G := G) C R u) C.activity C.activity_pos

/-- Exact Q-law conditional variance recurrence. -/
theorem vacantVariance_eq_sum_subtreeVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vacantVariance (G := G) C u =
      ∑ v ∈ R.children (G := G) u, R.subtreeVariance (G := G) C v := by
  classical
  unfold vacantVariance subtreeVariance subtreeLaw
  rw [variance_iso (deleteSubtreeRootIsoChildUnion (G := G) R u)]
  exact variance_biUnion G (R.children (G := G) u)
    (fun v => R.descendants (G := G) v)
    (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u)
    (children_hcross (G := G) C R u) C.activity C.activity_pos

/-- Exact Q-law conditional second-moment recurrence. -/
theorem vacantSecondMoment_eq_sum
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.vacantSecondMoment (G := G) C u =
      (∑ v ∈ R.children (G := G) u,
        ((R.subtreeLaw (G := G) C v).secondMoment -
          (R.subtreeLaw (G := G) C v).mean ^ 2)) +
      (∑ v ∈ R.children (G := G) u,
        (R.subtreeLaw (G := G) C v).mean) ^ 2 := by
  rw [show R.vacantSecondMoment (G := G) C u =
      R.vacantVariance (G := G) C u + R.vacantMean (G := G) C u ^ 2 by
    unfold vacantSecondMoment vacantVariance vacantMean
    rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]
    ring]
  rw [vacantVariance_eq_sum_subtreeVariance, vacantMean_eq_sum_subtreeMean]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro v hv
  unfold subtreeVariance
  rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]

private theorem proper_children_hdisj (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    Set.PairwiseDisjoint (↑(R.children (G := G) u) : Set V)
      (fun v => properDescendants (G := G) R v) := by
  intro v hv w hw hvw
  exact (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u
    hv hw hvw).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)

private theorem proper_children_hcross (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    ∀ i ∈ R.children (G := G) u, ∀ j ∈ R.children (G := G) u, i ≠ j →
      ∀ x ∈ properDescendants (G := G) R i,
      ∀ y ∈ properDescendants (G := G) R j, ¬ G.Adj x y := by
  intro i hi j hj hij x hx y hy
  exact R.not_adj_of_distinct_child_descendants (G := G) C.isForest
    ((R.mem_children (G := G) _ _).mp hi) ((R.mem_children (G := G) _ _).mp hj) hij
    ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hx).2)
    ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2)

/-- Exact R-law conditional first-moment recurrence. -/
theorem occupiedMean_eq_one_add_sum_vacantMean
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupiedMean (G := G) C u =
      1 + ∑ v ∈ R.children (G := G) u, R.vacantMean (G := G) C v := by
  classical
  unfold occupiedMean vacantMean
  congr 1
  rw [mean_iso (deleteClosedSubtreeRootIsoProperChildUnion
    (G := G) C.isForest R u)]
  rw [mean_biUnion G (R.children (G := G) u)
    (fun v => properDescendants (G := G) R v)
    (proper_children_hdisj (G := G) C R u)
    (proper_children_hcross (G := G) C R u)]
  apply Finset.sum_congr rfl
  intro v hv
  exact (mean_iso (deleteSubtreeRootIsoProperDescendants (G := G) R v)
    C.activity C.activity_pos).symm

/-- Exact R-law conditional variance recurrence. -/
theorem occupiedVariance_eq_sum_vacantVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupiedVariance (G := G) C u =
      ∑ v ∈ R.children (G := G) u, R.vacantVariance (G := G) C v := by
  classical
  unfold occupiedVariance vacantVariance
  rw [variance_iso (deleteClosedSubtreeRootIsoProperChildUnion
    (G := G) C.isForest R u)]
  rw [variance_biUnion G (R.children (G := G) u)
    (fun v => properDescendants (G := G) R v)
    (proper_children_hdisj (G := G) C R u)
    (proper_children_hcross (G := G) C R u)]
  apply Finset.sum_congr rfl
  intro v hv
  exact (variance_iso (deleteSubtreeRootIsoProperDescendants (G := G) R v)
    C.activity C.activity_pos).symm

/-- Exact R-law conditional second-moment recurrence. -/
theorem occupiedSecondMoment_eq_sum
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.occupiedSecondMoment (G := G) C u =
      (∑ v ∈ R.children (G := G) u,
        (R.vacantSecondMoment (G := G) C v -
          R.vacantMean (G := G) C v ^ 2)) +
      (1 + ∑ v ∈ R.children (G := G) u,
        R.vacantMean (G := G) C v) ^ 2 := by
  rw [show R.occupiedSecondMoment (G := G) C u =
      R.occupiedVariance (G := G) C u + R.occupiedMean (G := G) C u ^ 2 by
    unfold occupiedSecondMoment occupiedVariance occupiedMean
    dsimp only
    rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]
    ring]
  rw [occupiedVariance_eq_sum_vacantVariance,
    occupiedMean_eq_one_add_sum_vacantMean]
  apply congrArg₂ (· + ·) ?_ rfl
  apply Finset.sum_congr rfl
  intro v hv
  unfold vacantVariance vacantSecondMoment vacantMean
  rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]

/-- Exact P-law conditional first-moment recurrence (root mixture). -/
theorem subtreeMean_eq_root_mixture
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (R.subtreeLaw (G := G) C u).mean =
      R.vacancyProbability (G := G) C u * R.vacantMean (G := G) C u +
      R.occupationProbability (G := G) C u * R.occupiedMean (G := G) C u := by
  simpa [subtreeLaw, vacancyProbability, occupationProbability, rootedP, rootedQ,
    rootedA, vacantMean, occupiedMean] using
    hardCoreLaw_mean_root (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u) C.activity C.activity_pos

/-- Exact P-law conditional second-moment recurrence (root mixture). -/
theorem subtreeSecondMoment_eq_root_mixture
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    (R.subtreeLaw (G := G) C u).secondMoment =
      R.vacancyProbability (G := G) C u * R.vacantSecondMoment (G := G) C u +
      R.occupationProbability (G := G) C u *
        R.occupiedSecondMoment (G := G) C u := by
  simpa [subtreeLaw, vacancyProbability, occupationProbability, rootedP, rootedQ,
    rootedA, vacantSecondMoment, occupiedSecondMoment] using
    hardCoreLaw_secondMoment_root (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u) C.activity C.activity_pos

/-- Law of total variance for the actual P/Q/R conditional laws. -/
theorem subtreeVariance_law_total_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.subtreeVariance (G := G) C u =
      R.vacancyProbability (G := G) C u * R.vacantVariance (G := G) C u +
      R.occupationProbability (G := G) C u * R.occupiedVariance (G := G) C u +
      R.occupationProbability (G := G) C u *
        R.vacancyProbability (G := G) C u *
          R.conditionalMeanDifference (G := G) C u ^ 2 := by
  unfold subtreeVariance
  rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    subtreeSecondMoment_eq_root_mixture, subtreeMean_eq_root_mixture]
  rw [show R.vacantVariance (G := G) C u =
      R.vacantSecondMoment (G := G) C u -
        R.vacantMean (G := G) C u ^ 2 by
    unfold vacantVariance vacantSecondMoment vacantMean
    exact FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean _]
  rw [show R.occupiedVariance (G := G) C u =
      R.occupiedSecondMoment (G := G) C u -
        R.occupiedMean (G := G) C u ^ 2 by
    unfold occupiedVariance occupiedSecondMoment occupiedMean
    dsimp only
    rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]
    ring]
  unfold conditionalMeanDifference
  have hsum := R.occupationProbability_add_vacancyProbability (G := G) C u
  have hq : R.vacancyProbability (G := G) C u =
      1 - R.occupationProbability (G := G) C u := by linarith
  rw [hq]
  ring

/-- Exact rooted displacement recurrence. -/
theorem conditionalMeanDifference_eq_one_sub_sum
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.conditionalMeanDifference (G := G) C u =
      1 - ∑ v ∈ R.children (G := G) u,
        R.occupationProbability (G := G) C v *
          R.conditionalMeanDifference (G := G) C v := by
  unfold conditionalMeanDifference
  rw [occupiedMean_eq_one_add_sum_vacantMean,
    vacantMean_eq_sum_subtreeMean]
  have hsummeans : (∑ v ∈ R.children (G := G) u,
      (R.subtreeLaw (G := G) C v).mean) =
      ∑ v ∈ R.children (G := G) u,
        (R.vacantMean (G := G) C v +
          R.occupationProbability (G := G) C v *
            R.conditionalMeanDifference (G := G) C v) := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [R.subtreeMean_eq_root_mixture (G := G) C v]
    have hpq := R.occupationProbability_add_vacancyProbability (G := G) C v
    have hq : R.vacancyProbability (G := G) C v =
        1 - R.occupationProbability (G := G) C v := by linarith
    rw [hq]
    unfold conditionalMeanDifference
    ring
  rw [hsummeans, Finset.sum_add_distrib]
  simp only [conditionalMeanDifference]
  ring

/-- The unique parent selected for a nonroot vertex. -/
noncomputable def selectedParent (R : ComponentRooting G) (v : V)
    (hv : v ≠ R.rootOf (G := G) v) : V :=
  Classical.choose (R.exists_isChild_of_ne_root (G := G) hv)

/-- The selected parent is an actual inward-oriented neighbour. -/
theorem selectedParent_isChild (R : ComponentRooting G) (v : V)
    (hv : v ≠ R.rootOf (G := G) v) :
    R.IsChild (G := G) (R.selectedParent (G := G) v hv) v :=
  Classical.choose_spec (R.exists_isChild_of_ne_root (G := G) hv)

/-- In a forest the selected parent agrees with every proved parent. -/
theorem selectedParent_eq_of_isChild (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) {u v : V} (huv : R.IsChild (G := G) u v)
    (hv : v ≠ R.rootOf (G := G) v) :
    R.selectedParent (G := G) v hv = u :=
  R.isChild_unique (G := G) C.isForest
    (R.selectedParent_isChild (G := G) v hv) huv

/-- No edge crosses from a descendant subtree to the complement after its
unique parent edge is removed. -/
private theorem not_adj_descendant_outside_of_child
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u x y : V} (hpu : R.IsChild (G := G) p u)
    (hx : x ∈ R.descendants (G := G) u)
    (hy : y ∉ R.descendants (G := G) u) (hyp : y ≠ p) :
    ¬ G.Adj x y := by
  intro hxy
  have hxd := (R.mem_descendants (G := G) u x).mp hx
  rcases (R.adj_iff_isChild_or_reverse (G := G) C.isForest).mp hxy with hdown | hup
  · exact hy ((R.mem_descendants (G := G) u y).mpr
      (hxd.tail hdown))
  · by_cases hxu : x = u
    · subst x
      have hyp' : y = p := R.isChild_unique (G := G) C.isForest hup hpu
      exact hyp hyp'
    · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hxd with hux | ⟨q, huq, hqx⟩
      · exact hxu hux
      · have hyq : y = q := R.isChild_unique (G := G) C.isForest hup hqx
        exact hy ((R.mem_descendants (G := G) u y).mpr (hyq ▸ huq))

private noncomputable def outsideDescendants
    (R : ComponentRooting G) (p u : V) : Finset V :=
  ((Finset.univ : Finset V).erase p) \ R.descendants (G := G) u

private noncomputable def closedAvoiders (H : SimpleGraph V) (u : V) : Finset V := by
  classical
  exact (Finset.univ : Finset V).filter (fun x => x ≠ u ∧ ¬ H.Adj u x)

private noncomputable def closedDescendants
    (R : ComponentRooting G) (u : V) : Finset V := by
  classical
  exact (R.descendants (G := G) u).filter (fun x => x ≠ u ∧ ¬ G.Adj u x)

private noncomputable def deleteVertexIsoErase (p : V) :
    deleteVertex G p ≃g G.induce {x | x ∈ (Finset.univ : Finset V).erase p} := by
  classical
  let e : {x : V // x ≠ p} ≃ {x : V // x ∈ (Finset.univ : Finset V).erase p} :=
    { toFun := fun x => ⟨x.1, Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩⟩
      invFun := fun x => ⟨x.1, (Finset.mem_erase.mp x.2).1⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

private noncomputable def deleteClosedIsoFilter (u : V) :
    deleteClosedNeighborhood G u ≃g G.induce {x | x ∈ closedAvoiders G u} := by
  classical
  let e : {x : V // x ≠ u ∧ ¬ G.Adj u x} ≃
      {x : V // x ∈ closedAvoiders G u} :=
    { toFun := fun x => ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩
      invFun := fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

private noncomputable def deleteClosedSubtreeIsoClosedDescendants
    (R : ComponentRooting G) (u : V) :
    deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) ≃g
      G.induce {x | x ∈ closedDescendants (G := G) R u} := by
  classical
  let e :
      {x : {v // v ∈ R.descendants (G := G) u} //
        x ≠ R.subtreeRoot (G := G) u ∧
          ¬ (R.Subtree (G := G) u).Adj (R.subtreeRoot (G := G) u) x} ≃
      {x : V // x ∈ closedDescendants (G := G) R u} :=
    { toFun := fun x => ⟨x.1.1, by
          change x.1.1 ∈ (R.descendants (G := G) u).filter
            (fun y => y ≠ u ∧ ¬ G.Adj u y)
          exact Finset.mem_filter.mpr ⟨x.1.2, by
            constructor
            · intro h
              exact x.2.1 (Subtype.ext h)
            · exact x.2.2⟩⟩
      invFun := fun x => by
        have hxmem : x.1 ∈ (R.descendants (G := G) u).filter
            (fun y => y ≠ u ∧ ¬ G.Adj u y) := by
          simpa only [closedDescendants] using x.2
        have hx := Finset.mem_filter.mp hxmem
        exact ⟨⟨x.1, hx.1⟩, by
          constructor
          · intro h
            exact hx.2.1 (congrArg Subtype.val h)
          · exact hx.2.2⟩
      left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

private theorem descendants_union_outside
    (R : ComponentRooting G) {p u : V} (hpu : R.IsChild (G := G) p u) :
    R.descendants (G := G) u ∪ R.outsideDescendants (G := G) p u =
      (Finset.univ : Finset V).erase p := by
  classical
  ext x
  simp only [outsideDescendants, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (hx | ⟨hxp, _⟩)
    · intro h
      subst x
      exact R.not_mem_descendants_child (G := G) hpu hx
    · exact hxp
  · intro hxp
    by_cases hx : x ∈ R.descendants (G := G) u
    · exact Or.inl hx
    · exact Or.inr ⟨hxp, hx⟩

private theorem closedDescendants_union_outside
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    R.closedDescendants (G := G) u ∪ R.outsideDescendants (G := G) p u =
      closedAvoiders G u := by
  classical
  ext x
  simp only [closedDescendants, closedAvoiders, outsideDescendants,
    Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, Finset.mem_erase, and_assoc]
  constructor
  · rintro (⟨hxD, hxu, hxadj⟩ | ⟨hxp, hxD⟩)
    · exact ⟨hxu, hxadj⟩
    · have huD := R.self_mem_descendants (G := G) u
      exact ⟨by intro h; subst x; exact hxD huD,
        R.not_adj_descendant_outside_of_child (G := G) C hpu huD hxD hxp⟩
  · rintro ⟨hxu, hxadj⟩
    by_cases hxD : x ∈ R.descendants (G := G) u
    · exact Or.inl ⟨hxD, hxu, hxadj⟩
    · have hxp : x ≠ p := by
        intro h
        subst x
        exact hxadj hpu.1.symm
      exact Or.inr ⟨hxp, hxD⟩

/-- No edge crosses between a rooted component and its complement. -/
private theorem not_adj_descendant_outside_of_root
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {r x y : V} (hr : r = R.rootOf (G := G) r)
    (hx : x ∈ R.descendants (G := G) r)
    (hy : y ∉ R.descendants (G := G) r) : ¬ G.Adj x y := by
  intro hxy
  have hxd := (R.mem_descendants (G := G) r x).mp hx
  rcases (R.adj_iff_isChild_or_reverse (G := G) C.isForest).mp hxy with hdown | hup
  · exact hy ((R.mem_descendants (G := G) r y).mpr (hxd.tail hdown))
  · by_cases hxr : x = r
    · subst x
      exact R.not_isChild_of_eq_root (G := G) hr hup
    · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hxd with hrx | ⟨q, hrq, hqx⟩
      · exact hxr hrx
      · have hyq : y = q := R.isChild_unique (G := G) C.isForest hup hqx
        exact hy ((R.mem_descendants (G := G) r y).mpr (hyq ▸ hrq))

private noncomputable def outsideComponent
    (R : ComponentRooting G) (r : V) : Finset V :=
  (Finset.univ : Finset V) \ R.descendants (G := G) r

private theorem descendants_union_outsideComponent
    (R : ComponentRooting G) (r : V) :
    R.descendants (G := G) r ∪ R.outsideComponent (G := G) r = Finset.univ := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

private theorem closedDescendants_union_outsideComponent
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {r : V} (hr : r = R.rootOf (G := G) r) :
    R.closedDescendants (G := G) r ∪ R.outsideComponent (G := G) r =
      closedAvoiders G r := by
  classical
  ext x
  simp only [closedDescendants, outsideComponent, closedAvoiders,
    Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  constructor
  · rintro (⟨hxD, hxr, hxadj⟩ | hxD)
    · exact ⟨hxr, hxadj⟩
    · have hrD := R.self_mem_descendants (G := G) r
      exact ⟨by intro h; subst x; exact hxD hrD,
        R.not_adj_descendant_outside_of_root (G := G) C hr hrD hxD⟩
  · rintro ⟨hxr, hxadj⟩
    by_cases hxD : x ∈ R.descendants (G := G) r
    · exact Or.inl ⟨hxD, hxr, hxadj⟩
    · exact Or.inr hxD

/-- Removing the parent separates a child descendant subtree from the
remainder of a forest, so the partition function factors. -/
private theorem independenceEval_deleteVertex_child_factor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    independenceEval (deleteVertex G p) C.activity =
      independenceEval (R.Subtree (G := G) u) C.activity *
        independenceEval
          (G.induce {x | x ∈ R.outsideDescendants (G := G) p u}) C.activity := by
  classical
  let D := R.descendants (G := G) u
  let O := R.outsideDescendants (G := G) p u
  have hd : Disjoint D O := by
    rw [Finset.disjoint_left]
    intro x hxD hxO
    exact (Finset.mem_sdiff.mp hxO).2 hxD
  have hc : ∀ ⦃x y : V⦄, x ∈ D → y ∈ O → ¬ G.Adj x y := by
    intro x y hx hy
    exact R.not_adj_descendant_outside_of_child (G := G) C hpu hx
      (Finset.mem_sdiff.mp hy).2 (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).1
  calc
    independenceEval (deleteVertex G p) C.activity =
        independenceEval
          (G.induce {x | x ∈ (Finset.univ : Finset V).erase p}) C.activity :=
      eval_iso (deleteVertexIsoErase (G := G) p) C.activity
    _ = independenceEval (G.induce {x | x ∈ D ∪ O}) C.activity := by
      rw [R.descendants_union_outside (G := G) hpu]
    _ = independenceEval
          ((G.induce {x | x ∈ D}) ⊕g (G.induce {x | x ∈ O})) C.activity :=
      (eval_iso (unionIso G D O hd hc) C.activity).symm
    _ = independenceEval (G.induce {x | x ∈ D}) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity :=
      eval_sum _ _ _
    _ = _ := rfl

/-- Removing the closed neighbourhood of a child has the same outside factor
as removing its parent. -/
private theorem independenceEval_deleteClosed_child_factor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    independenceEval (deleteClosedNeighborhood G u) C.activity =
      independenceEval
          (deleteClosedNeighborhood (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) C.activity *
        independenceEval
          (G.induce {x | x ∈ R.outsideDescendants (G := G) p u}) C.activity := by
  classical
  let D := R.closedDescendants (G := G) u
  let O := R.outsideDescendants (G := G) p u
  have hd : Disjoint D O := by
    rw [Finset.disjoint_left]
    intro x hxD hxO
    exact (Finset.mem_sdiff.mp hxO).2 (Finset.mem_filter.mp hxD).1
  have hc : ∀ ⦃x y : V⦄, x ∈ D → y ∈ O → ¬ G.Adj x y := by
    intro x y hx hy
    exact R.not_adj_descendant_outside_of_child (G := G) C hpu
      (Finset.mem_filter.mp hx).1 (Finset.mem_sdiff.mp hy).2
      (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).1
  calc
    independenceEval (deleteClosedNeighborhood G u) C.activity =
        independenceEval (G.induce {x | x ∈ closedAvoiders G u}) C.activity :=
      eval_iso (deleteClosedIsoFilter (G := G) u) C.activity
    _ = independenceEval (G.induce {x | x ∈ D ∪ O}) C.activity := by
      rw [R.closedDescendants_union_outside (G := G) C hpu]
    _ = independenceEval
          ((G.induce {x | x ∈ D}) ⊕g (G.induce {x | x ∈ O})) C.activity :=
      (eval_iso (unionIso G D O hd hc) C.activity).symm
    _ = independenceEval (G.induce {x | x ∈ D}) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity :=
      eval_sum _ _ _
    _ = independenceEval
          (deleteClosedNeighborhood (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity := by
      rw [eval_iso (R.deleteClosedSubtreeIsoClosedDescendants (G := G) u)
        C.activity]
    _ = _ := rfl

private noncomputable def induceUnivIso :
    G.induce {x | x ∈ (Finset.univ : Finset V)} ≃g G := by
  classical
  let e : {x : V // x ∈ (Finset.univ : Finset V)} ≃ V :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, Finset.mem_univ x⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; rfl }
  exact { toEquiv := e, map_rel_iff' := by intro x y; rfl }

/-- The partition function factors between a rooted component and all other
components. -/
private theorem independenceEval_root_factor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {r : V} (hr : r = R.rootOf (G := G) r) :
    independenceEval G C.activity =
      independenceEval (R.Subtree (G := G) r) C.activity *
        independenceEval
          (G.induce {x | x ∈ R.outsideComponent (G := G) r}) C.activity := by
  classical
  let D := R.descendants (G := G) r
  let O := R.outsideComponent (G := G) r
  have hd : Disjoint D O := by
    rw [Finset.disjoint_left]
    intro x hxD hxO
    exact (Finset.mem_sdiff.mp hxO).2 hxD
  have hc : ∀ ⦃x y : V⦄, x ∈ D → y ∈ O → ¬ G.Adj x y := by
    intro x y hx hy
    exact R.not_adj_descendant_outside_of_root (G := G) C hr hx
      (Finset.mem_sdiff.mp hy).2
  calc
    independenceEval G C.activity =
        independenceEval
          (G.induce {x | x ∈ (Finset.univ : Finset V)}) C.activity :=
      (eval_iso (induceUnivIso (G := G)) C.activity).symm
    _ = independenceEval (G.induce {x | x ∈ D ∪ O}) C.activity := by
      rw [R.descendants_union_outsideComponent (G := G) r]
    _ = independenceEval
          ((G.induce {x | x ∈ D}) ⊕g (G.induce {x | x ∈ O})) C.activity :=
      (eval_iso (unionIso G D O hd hc) C.activity).symm
    _ = independenceEval (G.induce {x | x ∈ D}) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity := eval_sum _ _ _
    _ = _ := rfl

/-- Closed-neighbourhood deletion at a component root preserves the same
outside-component factor. -/
private theorem independenceEval_deleteClosed_root_factor
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {r : V} (hr : r = R.rootOf (G := G) r) :
    independenceEval (deleteClosedNeighborhood G r) C.activity =
      independenceEval
          (deleteClosedNeighborhood (R.Subtree (G := G) r)
            (R.subtreeRoot (G := G) r)) C.activity *
        independenceEval
          (G.induce {x | x ∈ R.outsideComponent (G := G) r}) C.activity := by
  classical
  let D := R.closedDescendants (G := G) r
  let O := R.outsideComponent (G := G) r
  have hd : Disjoint D O := by
    rw [Finset.disjoint_left]
    intro x hxD hxO
    exact (Finset.mem_sdiff.mp hxO).2 (Finset.mem_filter.mp hxD).1
  have hc : ∀ ⦃x y : V⦄, x ∈ D → y ∈ O → ¬ G.Adj x y := by
    intro x y hx hy
    exact R.not_adj_descendant_outside_of_root (G := G) C hr
      (Finset.mem_filter.mp hx).1 (Finset.mem_sdiff.mp hy).2
  calc
    independenceEval (deleteClosedNeighborhood G r) C.activity =
        independenceEval (G.induce {x | x ∈ closedAvoiders G r}) C.activity :=
      eval_iso (deleteClosedIsoFilter (G := G) r) C.activity
    _ = independenceEval (G.induce {x | x ∈ D ∪ O}) C.activity := by
      rw [R.closedDescendants_union_outsideComponent (G := G) C hr]
    _ = independenceEval
          ((G.induce {x | x ∈ D}) ⊕g (G.induce {x | x ∈ O})) C.activity :=
      (eval_iso (unionIso G D O hd hc) C.activity).symm
    _ = independenceEval (G.induce {x | x ∈ D}) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity := eval_sum _ _ _
    _ = independenceEval
          (deleteClosedNeighborhood (R.Subtree (G := G) r)
            (R.subtreeRoot (G := G) r)) C.activity *
          independenceEval (G.induce {x | x ∈ O}) C.activity := by
      rw [eval_iso (R.deleteClosedSubtreeIsoClosedDescendants (G := G) r)
        C.activity]
    _ = _ := rfl

/-- Under the canonical hard-core law, the event that a vertex is absent
has mass `I(G-v)/I(G)`. -/
private theorem sum_law_probability_if_not_mem_eq
    (C : CanonicalFirstRecoveryState G) (p : V) :
    (∑ s : IndepFinset G, if p ∉ s.val then C.law.probability s else 0) =
      independenceEval (deleteVertex G p) C.activity /
        independenceEval G C.activity := by
  classical
  letI : Fintype (AvoidingIndepFinset G p) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset G p) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  calc
    (∑ s : IndepFinset G, if p ∉ s.val then C.law.probability s else 0) =
        ∑ q : AvoidingIndepFinset G p ⊕ ContainingIndepFinset G p,
          Sum.elim
            (fun s => C.activity ^ s.val.val.card /
              independenceEval G C.activity)
            (fun _ => 0) q := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv G p)
      intro s
      by_cases h : p ∈ s.val <;>
        simp [indepFinsetPartitionEquiv, h,
          Forest.CanonicalFirstRecoveryState.law, Forest.hardCoreLaw]
    _ = ∑ s : AvoidingIndepFinset G p,
          C.activity ^ s.val.val.card / independenceEval G C.activity := by
      rw [Fintype.sum_sum_type]
      simp
    _ = ∑ t : IndepFinset (deleteVertex G p),
          C.activity ^ t.val.card / independenceEval G C.activity := by
      symm
      apply Fintype.sum_equiv (avoidingEquiv G p)
      intro t
      rw [avoidingEquiv_card]
    _ = (∑ t : IndepFinset (deleteVertex G p),
          C.activity ^ t.val.card) / independenceEval G C.activity := by
      rw [Finset.sum_div]
    _ = independenceEval (deleteVertex G p) C.activity /
          independenceEval G C.activity := by
      congr 1
      exact (independenceEval_eq_sum (G := deleteVertex G p) C.activity).symm

/-- Evaluation form of the vertex-deletion recurrence. -/
private theorem independenceEval_deleteVertex_recurrence
    (H : SimpleGraph V) (z : ℝ) (v : V) :
    independenceEval H z = independenceEval (deleteVertex H v) z +
      z * independenceEval (deleteClosedNeighborhood H v) z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_deleteVertex (G := H) (v := v)]
  simp [Polynomial.eval_add, Polynomial.eval_mul]

/-- The **actual global-law marginal** that the parent of `u` is absent.
For a component root the optional parent is virtual and absent surely; otherwise
this is literally the `C.law` event sum over global independent finsets. -/
noncomputable def parentAbsentProbability (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  if hu : u = R.rootOf (G := G) u then 1
  else
    ∑ s : IndepFinset G,
      if R.selectedParent (G := G) u hu ∉ s.val then C.law.probability s else 0

/-- Public identification of `parentAbsentProbability` with the explicit
`C.law` parent-absence event at every non-root vertex. -/
theorem parentAbsentProbability_eq_globalLaw_event
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) {u : V}
    (hu : u ≠ R.rootOf (G := G) u) :
    R.parentAbsentProbability (G := G) C u =
      ∑ s : IndepFinset G,
        if R.selectedParent (G := G) u hu ∉ s.val then C.law.probability s else 0 := by
  simp [parentAbsentProbability, hu]

/-- At a non-root vertex the actual marginal is the usual hard-core
vertex-deletion ratio for its selected parent. -/
theorem parentAbsentProbability_eq_deleteVertex_ratio
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) {u : V}
    (hu : u ≠ R.rootOf (G := G) u) :
    R.parentAbsentProbability (G := G) C u =
      independenceEval
          (deleteVertex G (R.selectedParent (G := G) u hu)) C.activity /
        independenceEval G C.activity := by
  rw [R.parentAbsentProbability_eq_globalLaw_event (G := G) C hu]
  exact sum_law_probability_if_not_mem_eq (G := G) C _

/-- A component root has its virtual parent absent with probability one. -/
@[simp] theorem parentAbsentProbability_rootOf
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    R.parentAbsentProbability (G := G) C (R.rootOf (G := G) v) = 1 := by
  simp [parentAbsentProbability]

/-- Parent-absence probability is nonnegative. -/
theorem parentAbsentProbability_nonneg (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    0 ≤ R.parentAbsentProbability (G := G) C u := by
  classical
  unfold parentAbsentProbability
  split
  · norm_num
  · apply Finset.sum_nonneg
    intro s hs
    split
    · exact C.law.probability_nonneg s
    · norm_num

/-- Parent-absence probability is at most one. -/
theorem parentAbsentProbability_le_one (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) :
    R.parentAbsentProbability (G := G) C u ≤ 1 := by
  classical
  unfold parentAbsentProbability
  split
  · exact le_rfl
  · calc
      (∑ s : IndepFinset G,
          if R.selectedParent (G := G) u ‹_› ∉ s.val then C.law.probability s else 0) ≤
          ∑ s : IndepFinset G, C.law.probability s := by
            apply Finset.sum_le_sum
            intro s hs
            split
            · exact le_rfl
            · exact C.law.probability_nonneg s
      _ = 1 := C.law.probability_sum
/-- The actual global probability that `u` is occupied factors as the
actual parent-absence marginal times the rooted conditional occupation
probability. -/
theorem parentAbsentProbability_mul_occupationProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u =
      C.activity * independenceEval (deleteClosedNeighborhood G u) C.activity /
        independenceEval G C.activity := by
  classical
  by_cases hu : u = R.rootOf (G := G) u
  · have hG := R.independenceEval_root_factor (G := G) C hu
    have hD := R.independenceEval_deleteClosed_root_factor (G := G) C hu
    simp only [parentAbsentProbability, dif_pos hu, one_mul]
    unfold occupationProbability rootedP rootedA
    rw [hG, hD]
    field_simp [ne_of_gt (independenceEval_pos _ C.activity_pos)]
  · let p := R.selectedParent (G := G) u hu
    have hpu : R.IsChild (G := G) p u :=
      R.selectedParent_isChild (G := G) u hu
    have hA := R.independenceEval_deleteVertex_child_factor (G := G) C hpu
    have hD := R.independenceEval_deleteClosed_child_factor (G := G) C hpu
    rw [R.parentAbsentProbability_eq_deleteVertex_ratio (G := G) C hu]
    unfold occupationProbability rootedP rootedA
    rw [hA, hD]
    field_simp [ne_of_gt (independenceEval_pos _ C.activity_pos)]

/-- Exact parent-state recursion along every child edge, now proved for the
explicit global-law marginal. -/
theorem parentAbsentProbability_child
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    R.parentAbsentProbability (G := G) C v =
      1 - R.parentAbsentProbability (G := G) C u *
        R.occupationProbability (G := G) C u := by
  have hv : v ≠ R.rootOf (G := G) v := by
    intro h
    exact R.not_isChild_of_eq_root (G := G) h huv
  rw [R.parentAbsentProbability_eq_deleteVertex_ratio (G := G) C hv]
  rw [R.selectedParent_eq_of_isChild (G := G) C huv hv]
  rw [R.parentAbsentProbability_mul_occupationProbability (G := G) C u]
  have hrec := independenceEval_deleteVertex_recurrence G C.activity u
  have hpos := (independenceEval_pos G C.activity_pos).ne'
  field_simp
  linarith


noncomputable def subtreeOrder (R : ComponentRooting G) (u : V) : ℕ :=
  (R.descendants (G := G) u).card

/-- Every descendant subtree contains its root vertex. -/
theorem subtreeOrder_pos (R : ComponentRooting G) (u : V) :
    0 < R.subtreeOrder (G := G) u := by
  rw [subtreeOrder, Finset.card_pos]
  exact ⟨u, R.self_mem_descendants (G := G) u⟩

/-- Every descendant subtree is bounded by the ambient vertex set. -/
theorem subtreeOrder_le_card (R : ComponentRooting G) (u : V) :
    R.subtreeOrder (G := G) u ≤ Fintype.card V := by
  rw [subtreeOrder, ← Finset.card_univ]
  exact Finset.card_le_card (Finset.subset_univ _)

/-- The induced descendant graph is acyclic whenever the ambient graph is. -/
theorem subtree_isAcyclic (R : ComponentRooting G) (hG : G.IsAcyclic) (u : V) :
    (R.Subtree (G := G) u).IsAcyclic := by
  exact hG.induce _


/-- The actual vertex variance contribution `g(u)`. -/
noncomputable def vertexVarianceContribution (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  R.parentAbsentProbability (G := G) C u *
    R.occupationProbability (G := G) C u *
    R.vacancyProbability (G := G) C u *
    R.conditionalMeanDifference (G := G) C u ^ 2

/-- The actual subtree variance mass `E(u)`. -/
noncomputable def subtreeVarianceMass (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : V) : ℝ :=
  R.parentAbsentProbability (G := G) C u * R.subtreeVariance (G := G) C u +
    (1 - R.parentAbsentProbability (G := G) C u) *
      R.vacantVariance (G := G) C u

/-- Exact recursive variance decomposition `E(u)=g(u)+sum_child E(v)`. -/
theorem subtreeVarianceMass_eq_vertexContribution_add_sum_children
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.subtreeVarianceMass (G := G) C u =
      R.vertexVarianceContribution (G := G) C u +
      ∑ v ∈ R.children (G := G) u,
        R.subtreeVarianceMass (G := G) C v := by
  classical
  let a := R.parentAbsentProbability (G := G) C u
  let p := R.occupationProbability (G := G) C u
  let q := R.vacancyProbability (G := G) C u
  let vp := R.subtreeVariance (G := G) C u
  let vq := R.vacantVariance (G := G) C u
  let vr := R.occupiedVariance (G := G) C u
  let d := R.conditionalMeanDifference (G := G) C u
  have hvp : vp = q * vq + p * vr + p * q * d ^ 2 := by
    exact R.subtreeVariance_law_total_variance (G := G) C u
  have hvq : vq = ∑ v ∈ R.children (G := G) u,
      R.subtreeVariance (G := G) C v := by
    exact R.vacantVariance_eq_sum_subtreeVariance (G := G) C u
  have hvr : vr = ∑ v ∈ R.children (G := G) u,
      R.vacantVariance (G := G) C v := by
    exact R.occupiedVariance_eq_sum_vacantVariance (G := G) C u
  have hchild : (∑ v ∈ R.children (G := G) u,
      R.subtreeVarianceMass (G := G) C v) =
      (1 - a * p) * vq + (a * p) * vr := by
    rw [hvq, hvr, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    unfold subtreeVarianceMass
    rw [show R.parentAbsentProbability (G := G) C v = 1 - a * p by
      exact R.parentAbsentProbability_child (G := G) C
        ((R.mem_children (G := G) u v).mp hv)]
    dsimp only [a, p]
    ring
  change a * vp + (1 - a) * vq =
    a * p * q * d ^ 2 +
      ∑ v ∈ R.children (G := G) u,
        R.subtreeVarianceMass (G := G) C v
  rw [hchild, hvp]
  have hpq := R.occupationProbability_add_vacancyProbability (G := G) C u
  have hq : q = 1 - p := by
    change p + q = 1 at hpq
    linarith
  rw [hq]
  ring


/-- A child subtree is strictly smaller than its parent's subtree. -/
theorem subtreeOrder_child_lt (R : ComponentRooting G) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    R.subtreeOrder (G := G) v < R.subtreeOrder (G := G) u := by
  unfold subtreeOrder
  apply Finset.card_lt_card
  constructor
  · intro x hx
    rw [mem_descendants] at hx ⊢
    exact R.child_descendant (G := G) huv hx
  · intro hrev
    have hu : u ∈ R.descendants (G := G) v :=
      hrev (R.self_mem_descendants (G := G) u)
    exact R.not_mem_descendants_child (G := G) huv hu

/-- Component-rooted telescope on one actual descendant subtree. -/
theorem subtreeVarianceMass_eq_sum_descendants
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (u : V) :
    R.subtreeVarianceMass (G := G) C u =
      ∑ x ∈ R.descendants (G := G) u,
        R.vertexVarianceContribution (G := G) C x := by
  classical
  induction horder : R.subtreeOrder (G := G) u using Nat.strong_induction_on generalizing u with
  | h n ih =>
      rw [R.subtreeVarianceMass_eq_vertexContribution_add_sum_children (G := G) C u]
      have hsum : (∑ v ∈ R.children (G := G) u,
          R.subtreeVarianceMass (G := G) C v) =
          ∑ v ∈ R.children (G := G) u,
            ∑ x ∈ R.descendants (G := G) v,
              R.vertexVarianceContribution (G := G) C x := by
        apply Finset.sum_congr rfl
        intro v hv
        apply ih (R.subtreeOrder (G := G) v)
        · rw [← horder]
          exact R.subtreeOrder_child_lt (G := G)
            ((R.mem_children (G := G) u v).mp hv)
        · rfl
      rw [hsum]
      rw [← Finset.sum_biUnion
        (R.children_pairwiseDisjoint_descendants (G := G) C.isForest u)]
      rw [← Finset.sum_insert]
      · rw [← R.descendants_eq_insert_biUnion_children (G := G) u]
      · rw [Finset.mem_biUnion]
        push_neg
        intro v hv
        exact R.not_mem_descendants_child (G := G)
          ((R.mem_children (G := G) u v).mp hv)


/-- The selected component roots as a finite subset of the vertex set. -/
noncomputable def componentRoots (R : ComponentRooting G) : Finset V :=
  Finset.univ.filter (fun v => v = R.rootOf (G := G) v)

@[simp] theorem mem_componentRoots (R : ComponentRooting G) (v : V) :
    v ∈ R.componentRoots (G := G) ↔ v = R.rootOf (G := G) v := by
  simp [componentRoots]

/-- Distinct component-root descendant sets are disjoint. -/
theorem componentRoots_pairwiseDisjoint_descendants
    (R : ComponentRooting G) :
    (↑(R.componentRoots (G := G)) : Set V).PairwiseDisjoint
      (fun r => R.descendants (G := G) r) := by
  intro r hr s hs hrs
  change Disjoint (R.descendants (G := G) r) (R.descendants (G := G) s)
  rw [Finset.disjoint_left]
  intro x hxr hxs
  have hrx := R.rootOf_eq_of_reachable (G := G)
    (R.isDescendant_reachable (G := G)
      ((R.mem_descendants (G := G) r x).mp hxr))
  have hsx := R.rootOf_eq_of_reachable (G := G)
    (R.isDescendant_reachable (G := G)
      ((R.mem_descendants (G := G) s x).mp hxs))
  apply hrs
  calc
    r = R.rootOf (G := G) r := (R.mem_componentRoots (G := G) r).mp hr
    _ = R.rootOf (G := G) x := hrx
    _ = R.rootOf (G := G) s := hsx.symm
    _ = s := ((R.mem_componentRoots (G := G) s).mp hs).symm

/-- There are no edges between distinct rooted components. -/
theorem componentRoots_no_cross_edges (R : ComponentRooting G) :
    ∀ r ∈ R.componentRoots (G := G), ∀ s ∈ R.componentRoots (G := G), r ≠ s →
      ∀ x ∈ R.descendants (G := G) r, ∀ y ∈ R.descendants (G := G) s,
        ¬ G.Adj x y := by
  intro r hr s hs hrs x hx y hy hxy
  have hrx := R.rootOf_eq_of_reachable (G := G)
    (R.isDescendant_reachable (G := G)
      ((R.mem_descendants (G := G) r x).mp hx))
  have hsy := R.rootOf_eq_of_reachable (G := G)
    (R.isDescendant_reachable (G := G)
      ((R.mem_descendants (G := G) s y).mp hy))
  have hxyroot := R.rootOf_eq_of_adj (G := G) hxy
  apply hrs
  calc
    r = R.rootOf (G := G) r := (R.mem_componentRoots (G := G) r).mp hr
    _ = R.rootOf (G := G) x := hrx
    _ = R.rootOf (G := G) y := hxyroot
    _ = R.rootOf (G := G) s := hsy.symm
    _ = s := ((R.mem_componentRoots (G := G) s).mp hs).symm

/-- The component-root descendant sets partition the whole vertex set. -/
theorem componentRoots_biUnion_descendants (R : ComponentRooting G) :
    (R.componentRoots (G := G)).biUnion
      (fun r => R.descendants (G := G) r) = Finset.univ := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
  refine ⟨R.rootOf (G := G) x, ?_, ?_⟩
  · rw [R.mem_componentRoots (G := G)]
    exact (R.rootOf_rootOf (G := G) x).symm
  · rw [R.mem_descendants (G := G)]
    exact R.root_isDescendant (G := G) x

/-- The canonical variance is the sum of actual component-root subtree variances. -/
theorem variance_eq_sum_componentRoot_subtreeVariance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    C.variance = ∑ r ∈ R.componentRoots (G := G),
      R.subtreeVariance (G := G) C r := by
  classical
  have hcomponents := variance_biUnion G (R.componentRoots (G := G))
    (fun r => R.descendants (G := G) r)
    (R.componentRoots_pairwiseDisjoint_descendants (G := G))
    (R.componentRoots_no_cross_edges (G := G)) C.activity C.activity_pos
  rw [R.componentRoots_biUnion_descendants (G := G)] at hcomponents
  calc
    C.variance = (hardCoreLaw G C.activity C.activity_pos).variance := rfl
    _ = (hardCoreLaw (G.induce ((Finset.univ : Finset V) : Set V))
        C.activity C.activity_pos).variance := by
      let e : {x : V // x ∈ (Finset.univ : Finset V)} ≃ V :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, Finset.mem_univ x⟩
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro x; rfl }
      have hIso : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
        { toEquiv := e
          map_rel_iff' := by intro x y; rfl }
      exact (variance_iso hIso C.activity C.activity_pos).symm
    _ = ∑ r ∈ R.componentRoots (G := G),
        R.subtreeVariance (G := G) C r := by
      change (hardCoreLaw (G.induce ((Finset.univ : Finset V) : Set V))
        C.activity C.activity_pos).variance = _
      exact hcomponents

/-- At a component root, the variance mass is exactly its subtree variance. -/
theorem subtreeVarianceMass_componentRoot
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) {r : V}
    (hr : r ∈ R.componentRoots (G := G)) :
    R.subtreeVarianceMass (G := G) C r =
      R.subtreeVariance (G := G) C r := by
  have ha : R.parentAbsentProbability (G := G) C r = 1 := by
    rw [(R.mem_componentRoots (G := G) r).mp hr]
    exact R.parentAbsentProbability_rootOf (G := G) C r
  unfold subtreeVarianceMass
  rw [ha]
  ring

/-- Global exact telescope: the sum of actual rooted contributions is the
canonical variance. -/
theorem sum_vertexVarianceContribution_eq_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    (∑ v, R.vertexVarianceContribution (G := G) C v) = C.variance := by
  classical
  rw [R.variance_eq_sum_componentRoot_subtreeVariance (G := G) C]
  calc
    ∑ v, R.vertexVarianceContribution (G := G) C v =
        ∑ v ∈ (R.componentRoots (G := G)).biUnion
          (fun r => R.descendants (G := G) r),
          R.vertexVarianceContribution (G := G) C v := by
      rw [R.componentRoots_biUnion_descendants (G := G)]
    _ = ∑ r ∈ R.componentRoots (G := G),
        ∑ v ∈ R.descendants (G := G) r,
          R.vertexVarianceContribution (G := G) C v :=
      Finset.sum_biUnion
        (R.componentRoots_pairwiseDisjoint_descendants (G := G))
    _ = ∑ r ∈ R.componentRoots (G := G),
        R.subtreeVarianceMass (G := G) C r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (R.subtreeVarianceMass_eq_sum_descendants (G := G) C r).symm
    _ = ∑ r ∈ R.componentRoots (G := G),
        R.subtreeVariance (G := G) C r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact R.subtreeVarianceMass_componentRoot (G := G) C hr

/-- The project vacancy convention agrees with `1-p`. -/
theorem vacancyProbability_eq_one_sub_occupationProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    R.vacancyProbability (G := G) C v =
      1 - R.occupationProbability (G := G) C v := by
  linarith [R.occupationProbability_add_vacancyProbability (G := G) C v]

/-- Actual observables associated with one component rooting.  Its
`variance_decomposition` field is discharged by the global telescope above. -/
noncomputable def observables (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) : RootedForestObservables C where
  occupationProbability := R.occupationProbability (G := G) C
  parentAbsentProbability := R.parentAbsentProbability (G := G) C
  conditionalMeanDifference := R.conditionalMeanDifference (G := G) C
  subtreeOrder := R.subtreeOrder (G := G)
  occupationProbability_nonneg := R.occupationProbability_nonneg (G := G) C
  occupationProbability_le_one := R.occupationProbability_le_one (G := G) C
  parentAbsentProbability_nonneg := R.parentAbsentProbability_nonneg (G := G) C
  parentAbsentProbability_le_one := R.parentAbsentProbability_le_one (G := G) C
  subtreeOrder_pos := R.subtreeOrder_pos (G := G)
  subtreeOrder_le_order := by
    intro v
    exact R.subtreeOrder_le_card (G := G) v
  variance_decomposition := by
    simpa only [vertexVarianceContribution,
      vacancyProbability_eq_one_sub_occupationProbability] using
      R.sum_vertexVarianceContribution_eq_variance (G := G) C

end ComponentRooting

/-- There is a component-root choice because every quotient component has a
nonempty support.  No nonemptiness is assumed. -/
noncomputable def defaultComponentRooting : ComponentRooting G where
  root c := c.nonempty_supp.some
  root_mem c := c.nonempty_supp.some_mem

/-- Every finite graph, in particular every finite forest, admits a component rooting. -/
theorem nonempty_componentRooting : Nonempty (ComponentRooting G) :=
  ⟨defaultComponentRooting G⟩

/-- A realization of a canonical forest state is exactly one root per actual component. -/
abbrev Realization {W : Type u} [Fintype W] {H : SimpleGraph W}
    (_C : CanonicalFirstRecoveryState H) : Type u := ComponentRooting H

/-- Every canonical forest state has an actual component-rooting realization. -/
theorem nonempty_realization {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) : Nonempty (Realization C) :=
  nonempty_componentRooting (G := H)

/-- The compiled actual rooted-forest family.  Realizations are precisely
choices of one root in every connected component, and the observables carry
the proved (rather than postulated) variance telescope. -/
noncomputable def actualRootedForestFamily : RootedForestFamily.{u} where
  Realization := fun {_W} [_] {H} _C => ComponentRooting H
  observables := fun {_W} [_] {H} C R =>
    ComponentRooting.observables (G := H) C R

/-- The family realization type is definitionally the component-rooting type. -/
theorem actualRootedForestFamily_realization_eq
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) :
    actualRootedForestFamily.Realization C = ComponentRooting H := rfl

/-- Every canonical state has a realization in the compiled actual family. -/
theorem actualRootedForestFamily_nonempty
    {W : Type u} [Fintype W] {H : SimpleGraph W}
    (C : CanonicalFirstRecoveryState H) :
    Nonempty (actualRootedForestFamily.Realization C) :=
  nonempty_componentRooting (G := H)

/-! ## Arbitrary-activity conditional means and exact displacement -/

namespace ComponentRooting

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Descendant-subtree hard-core law at an arbitrary unchanged global activity. -/
noncomputable def subtreeLawAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : FiniteLatticeLaw (IndepFinset (R.Subtree (G := G) u)) :=
  hardCoreLaw (R.Subtree (G := G) u) z hz

/-- Root occupation probability in the descendant-subtree law at activity `z`. -/
noncomputable def occupationProbabilityAt (R : ComponentRooting G) (z : ℝ)
    (u : V) : ℝ :=
  (z * independenceEval
    (deleteClosedNeighborhood (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u)) z) /
    independenceEval (R.Subtree (G := G) u) z

/-- Root vacancy probability in the descendant-subtree law at activity `z`. -/
noncomputable def vacancyProbabilityAt (R : ComponentRooting G) (z : ℝ)
    (u : V) : ℝ :=
  independenceEval
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z /
    independenceEval (R.Subtree (G := G) u) z

/-- Conditional count mean given a vacant subtree root at activity `z`. -/
noncomputable def vacantMeanAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z hz).mean

/-- Conditional count mean given an occupied subtree root at activity `z`. -/
noncomputable def occupiedMeanAt (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (u : V) : ℝ :=
  1 + (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u)) z hz).mean

/-- Occupied-minus-vacant conditional count displacement at activity `z`. -/
noncomputable def conditionalMeanDifferenceAt (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) : ℝ :=
  occupiedMeanAt R z hz u - vacantMeanAt R z hz u

/-- The arbitrary-activity descendant partition recurrence. -/
theorem independenceEval_subtree_eq_delete_add_occupiedAt
    (R : ComponentRooting G) (z : ℝ) (u : V) :
    independenceEval (R.Subtree (G := G) u) z =
      independenceEval
        (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z +
      z * independenceEval
        (deleteClosedNeighborhood (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) z := by
  let H := R.Subtree (G := G) u
  let r := R.subtreeRoot (G := G) u
  have hrec := rooted_recurrence H r
  apply_fun fun p : Polynomial ℕ =>
    Polynomial.eval z (p.map (Nat.castRingHom ℝ)) at hrec
  simpa [independenceEval, independencePolynomialReal,
    rootedAvoidingPolynomial, rootedOccupiedRemainder,
    Polynomial.map_add, Polynomial.map_mul] using hrec

/-- Root occupation and vacancy probabilities at `z` sum to one. -/
theorem occupationProbabilityAt_add_vacancyProbabilityAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    occupationProbabilityAt R z u + vacancyProbabilityAt R z u = 1 := by
  rw [occupationProbabilityAt, vacancyProbabilityAt, ← add_div, add_comm]
  rw [← independenceEval_subtree_eq_delete_add_occupiedAt R z u]
  exact div_self (ne_of_gt (independenceEval_pos _ hz))

private theorem children_hcrossAt (hG : G.IsAcyclic)
    (R : ComponentRooting G) (u : V) :
    ∀ i ∈ R.children (G := G) u, ∀ j ∈ R.children (G := G) u, i ≠ j →
      ∀ x ∈ R.descendants (G := G) i, ∀ y ∈ R.descendants (G := G) j,
        ¬ G.Adj x y := by
  intro i hi j hj hij x hx y hy
  exact R.not_adj_of_distinct_child_descendants (G := G) hG
    ((R.mem_children (G := G) _ _).mp hi) ((R.mem_children (G := G) _ _).mp hj) hij
    ((R.mem_descendants (G := G) _ _).mp hx) ((R.mem_descendants (G := G) _ _).mp hy)

/-- Vacant-root conditional mean is the sum of child subtree means. -/
theorem vacantMeanAt_eq_sum_subtreeMeanAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    vacantMeanAt R z hz u =
      ∑ v ∈ R.children (G := G) u, (subtreeLawAt R z hz v).mean := by
  classical
  unfold vacantMeanAt subtreeLawAt
  rw [mean_iso (deleteSubtreeRootIsoChildUnion (G := G) R u)]
  exact mean_biUnion G (R.children (G := G) u)
    (fun v => R.descendants (G := G) v)
    (R.children_pairwiseDisjoint_descendants (G := G) hG u)
    (children_hcrossAt hG R u) z hz

private theorem proper_children_hdisjAt (hG : G.IsAcyclic)
    (R : ComponentRooting G) (u : V) :
    Set.PairwiseDisjoint (↑(R.children (G := G) u) : Set V)
      (fun v => properDescendants (G := G) R v) := by
  intro v hv w hw hvw
  exact (R.children_pairwiseDisjoint_descendants (G := G) hG u
    hv hw hvw).mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)

private theorem proper_children_hcrossAt (hG : G.IsAcyclic)
    (R : ComponentRooting G) (u : V) :
    ∀ i ∈ R.children (G := G) u, ∀ j ∈ R.children (G := G) u, i ≠ j →
      ∀ x ∈ properDescendants (G := G) R i,
      ∀ y ∈ properDescendants (G := G) R j, ¬ G.Adj x y := by
  intro i hi j hj hij x hx y hy
  exact R.not_adj_of_distinct_child_descendants (G := G) hG
    ((R.mem_children (G := G) _ _).mp hi) ((R.mem_children (G := G) _ _).mp hj) hij
    ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hx).2)
    ((R.mem_descendants (G := G) _ _).mp (Finset.mem_erase.mp hy).2)

/-- Occupied-root conditional mean is one plus the sum of child-vacant means. -/
theorem occupiedMeanAt_eq_one_add_sum_vacantMeanAt
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    occupiedMeanAt R z hz u =
      1 + ∑ v ∈ R.children (G := G) u, vacantMeanAt R z hz v := by
  classical
  unfold occupiedMeanAt vacantMeanAt
  congr 1
  rw [mean_iso (deleteClosedSubtreeRootIsoProperChildUnion (G := G) hG R u)]
  rw [mean_biUnion G (R.children (G := G) u)
    (fun v => properDescendants (G := G) R v)
    (proper_children_hdisjAt hG R u)
    (proper_children_hcrossAt hG R u)]
  apply Finset.sum_congr rfl
  intro v hv
  exact (mean_iso (deleteSubtreeRootIsoProperDescendants (G := G) R v) z hz).symm

/-- Child subtree mean is vacant mean plus occupation probability times displacement. -/
theorem subtreeMeanAt_eq_vacantMeanAt_add_occupation_mul_differenceAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    (subtreeLawAt R z hz u).mean =
      vacantMeanAt R z hz u +
        occupationProbabilityAt R z u * conditionalMeanDifferenceAt R z hz u := by
  have hmix : (subtreeLawAt R z hz u).mean =
      vacancyProbabilityAt R z u * vacantMeanAt R z hz u +
      occupationProbabilityAt R z u * occupiedMeanAt R z hz u := by
    simpa [subtreeLawAt, vacancyProbabilityAt, occupationProbabilityAt,
      vacantMeanAt, occupiedMeanAt] using
      hardCoreLaw_mean_root (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) z hz
  rw [hmix]
  have hpq := occupationProbabilityAt_add_vacancyProbabilityAt R z hz u
  have hq : vacancyProbabilityAt R z u = 1 - occupationProbabilityAt R z u := by
    linarith
  rw [hq]
  unfold conditionalMeanDifferenceAt
  ring

/-- Exact arbitrary-activity displacement recurrence, equation (A.9). -/
theorem conditionalMeanDifferenceAt_eq_one_sub_sum
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    conditionalMeanDifferenceAt R z hz u =
      1 - ∑ v ∈ R.children (G := G) u,
        occupationProbabilityAt R z v * conditionalMeanDifferenceAt R z hz v := by
  unfold conditionalMeanDifferenceAt
  rw [occupiedMeanAt_eq_one_add_sum_vacantMeanAt hG,
    vacantMeanAt_eq_sum_subtreeMeanAt hG]
  have hsummeans : (∑ v ∈ R.children (G := G) u,
      (subtreeLawAt R z hz v).mean) =
      ∑ v ∈ R.children (G := G) u,
        (vacantMeanAt R z hz v +
          occupationProbabilityAt R z v * conditionalMeanDifferenceAt R z hz v) := by
    apply Finset.sum_congr rfl
    intro v hv
    exact subtreeMeanAt_eq_vacantMeanAt_add_occupation_mul_differenceAt R z hz v
  rw [hsummeans, Finset.sum_add_distrib]
  simp only [conditionalMeanDifferenceAt]
  ring

/-! ## Arbitrary-activity conditional variances -/

/-- Conditional variance given that the descendant-subtree root is vacant,
at an arbitrary unchanged global activity. -/
noncomputable def vacantVarianceAt (R : ComponentRooting G) (z : ℝ)
    (hz : 0 < z) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u)) z hz).variance

/-- Conditional variance given that the descendant-subtree root is occupied,
at an arbitrary unchanged global activity.  The deterministic contribution of
the occupied root does not affect this variance. -/
noncomputable def occupiedVarianceAt (R : ComponentRooting G) (z : ℝ)
    (hz : 0 < z) (u : V) : ℝ :=
  (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u)) z hz).variance

/-- Exact arbitrary-activity Q-law variance recurrence: after conditioning the
root vacant, the child descendant subtrees are independent components. -/
theorem vacantVarianceAt_eq_sum_subtreeVarianceAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    vacantVarianceAt R z hz u =
      ∑ v ∈ R.children (G := G) u, (subtreeLawAt R z hz v).variance := by
  classical
  unfold vacantVarianceAt subtreeLawAt
  rw [variance_iso (deleteSubtreeRootIsoChildUnion (G := G) R u)]
  exact variance_biUnion G (R.children (G := G) u)
    (fun v => R.descendants (G := G) v)
    (R.children_pairwiseDisjoint_descendants (G := G) hG u)
    (children_hcrossAt hG R u) z hz

/-- Exact arbitrary-activity R-law variance recurrence: after conditioning the
root occupied, every child root is forced vacant and the resulting proper-child
forests are independent components. -/
theorem occupiedVarianceAt_eq_sum_vacantVarianceAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    occupiedVarianceAt R z hz u =
      ∑ v ∈ R.children (G := G) u, vacantVarianceAt R z hz v := by
  classical
  unfold occupiedVarianceAt vacantVarianceAt
  rw [variance_iso (deleteClosedSubtreeRootIsoProperChildUnion
    (G := G) hG R u)]
  rw [variance_biUnion G (R.children (G := G) u)
    (fun v => properDescendants (G := G) R v)
    (proper_children_hdisjAt hG R u)
    (proper_children_hcrossAt hG R u)]
  apply Finset.sum_congr rfl
  intro v hv
  exact (variance_iso (deleteSubtreeRootIsoProperDescendants (G := G) R v)
    z hz).symm

/-- Exact arbitrary-activity law of total variance for the P/Q/R root split.
This is equation (A.27) in the Appendix-A notation. -/
theorem subtreeVarianceAt_law_total_variance
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    (subtreeLawAt R z hz u).variance =
      vacancyProbabilityAt R z u * vacantVarianceAt R z hz u +
      occupationProbabilityAt R z u * occupiedVarianceAt R z hz u +
      occupationProbabilityAt R z u * vacancyProbabilityAt R z u *
        conditionalMeanDifferenceAt R z hz u ^ 2 := by
  have hmean : (subtreeLawAt R z hz u).mean =
      vacancyProbabilityAt R z u * vacantMeanAt R z hz u +
      occupationProbabilityAt R z u * occupiedMeanAt R z hz u := by
    simpa [subtreeLawAt, vacancyProbabilityAt, occupationProbabilityAt,
      vacantMeanAt, occupiedMeanAt] using
      hardCoreLaw_mean_root (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) z hz
  have hsecond : (subtreeLawAt R z hz u).secondMoment =
      vacancyProbabilityAt R z u *
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) z hz).secondMoment +
      occupationProbabilityAt R z u *
        ((hardCoreLaw
          (deleteClosedNeighborhood (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) z hz).secondMoment +
          2 * (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).mean + 1) := by
    simpa [subtreeLawAt, vacancyProbabilityAt, occupationProbabilityAt] using
      hardCoreLaw_secondMoment_root (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u) z hz
  rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean, hsecond, hmean]
  rw [show vacantVarianceAt R z hz u =
      (hardCoreLaw
        (deleteVertex (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) z hz).secondMoment -
      vacantMeanAt R z hz u ^ 2 by
    unfold vacantVarianceAt vacantMeanAt
    exact FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean _]
  rw [show occupiedVarianceAt R z hz u =
      ((hardCoreLaw
        (deleteClosedNeighborhood (R.Subtree (G := G) u)
          (R.subtreeRoot (G := G) u)) z hz).secondMoment +
        2 * (hardCoreLaw
          (deleteClosedNeighborhood (R.Subtree (G := G) u)
            (R.subtreeRoot (G := G) u)) z hz).mean + 1) -
      occupiedMeanAt R z hz u ^ 2 by
    unfold occupiedVarianceAt occupiedMeanAt
    rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean]
    ring]
  unfold conditionalMeanDifferenceAt
  have hpq := occupationProbabilityAt_add_vacancyProbabilityAt R z hz u
  have hq : vacancyProbabilityAt R z u =
      1 - occupationProbabilityAt R z u := by linarith
  rw [hq]
  ring

/-- At arbitrary positive activity, global forest variance is exactly the sum
of the variances of its rooted connected components. -/
theorem variance_eq_sum_componentRoot_subtreeVarianceAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).variance =
      ∑ r ∈ R.componentRoots (G := G), (R.subtreeLawAt z hz r).variance := by
  classical
  have hcomponents := variance_biUnion G (R.componentRoots (G := G))
    (fun r => R.descendants (G := G) r)
    (R.componentRoots_pairwiseDisjoint_descendants (G := G))
    (R.componentRoots_no_cross_edges (G := G)) z hz
  rw [R.componentRoots_biUnion_descendants (G := G)] at hcomponents
  calc
    (hardCoreLaw G z hz).variance =
        (hardCoreLaw (G.induce ((Finset.univ : Finset V) : Set V)) z hz).variance := by
      let e : {x : V // x ∈ (Finset.univ : Finset V)} ≃ V :=
        { toFun := Subtype.val
          invFun := fun x => ⟨x, Finset.mem_univ x⟩
          left_inv := by intro x; apply Subtype.ext; rfl
          right_inv := by intro x; rfl }
      have hIso : G.induce ((Finset.univ : Finset V) : Set V) ≃g G :=
        { toEquiv := e
          map_rel_iff' := by intro x y; rfl }
      exact (variance_iso hIso z hz).symm
    _ = _ := hcomponents

/-! ## Arbitrary-activity child/outside polynomial factorization -/

/-- Vertices outside a child descendant subtree after its parent is removed. -/
noncomputable def childOutsideAt (R : ComponentRooting G) (p u : V) : Finset V :=
  ((Finset.univ : Finset V).erase p) \ R.descendants (G := G) u

/-- No forest edge crosses from a child descendant subtree to its outside
complement once the unique parent endpoint is deleted. -/
theorem not_adj_descendant_childOutsideAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u x y : V} (hpu : R.IsChild (G := G) p u)
    (hx : x ∈ R.descendants (G := G) u)
    (hy : y ∈ childOutsideAt (G := G) R p u) :
    ¬ G.Adj x y := by
  intro hxy
  have hxd := (R.mem_descendants (G := G) u x).mp hx
  have hyout : y ∉ R.descendants (G := G) u := (Finset.mem_sdiff.mp hy).2
  have hyp : y ≠ p := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hy).1).1
  rcases (R.adj_iff_isChild_or_reverse (G := G) hG).mp hxy with hdown | hup
  · exact hyout ((R.mem_descendants (G := G) u y).mpr (hxd.tail hdown))
  · by_cases hxu : x = u
    · subst x
      have hyp' : y = p := R.isChild_unique (G := G) hG hup hpu
      exact hyp hyp'
    · rcases (Relation.ReflTransGen.cases_tail_iff _ _ _).mp hxd with hux | ⟨q, huq, hqx⟩
      · exact hxu hux
      · have hyq : y = q := R.isChild_unique (G := G) hG hup hqx
        exact hyout ((R.mem_descendants (G := G) u y).mpr (hyq ▸ huq))

/-- The child descendants and their outside complement partition the
parent-deleted vertex set. -/
theorem descendants_union_childOutsideAt
    (R : ComponentRooting G) {p u : V} (hpu : R.IsChild (G := G) p u) :
    R.descendants (G := G) u ∪ childOutsideAt (G := G) R p u =
      (Finset.univ : Finset V).erase p := by
  classical
  ext x
  simp only [childOutsideAt, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (hx | ⟨hxp, _⟩)
    · intro h
      subst x
      exact R.not_mem_descendants_child (G := G) hpu hx
    · exact hxp
  · intro hxp
    by_cases hx : x ∈ R.descendants (G := G) u
    · exact Or.inl hx
    · exact Or.inr ⟨hxp, hx⟩

/-- At every coefficient ring, removing a parent factors into the chosen child
subtree and the outside forest.  This is the polynomial form of the conditional
independence used in (A.33). -/
theorem independencePolynomial_deleteVertex_child_factorAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    independencePolynomial (deleteVertex G p) =
      independencePolynomial (R.Subtree (G := G) u) *
        independencePolynomial
          (G.induce {x | x ∈ childOutsideAt (G := G) R p u}) := by
  classical
  let D := R.descendants (G := G) u
  let O := childOutsideAt (G := G) R p u
  have hd : Disjoint D O := by
    rw [Finset.disjoint_left]
    intro x hxD hxO
    exact (Finset.mem_sdiff.mp hxO).2 hxD
  have hc : ∀ ⦃x y : V⦄, x ∈ D → y ∈ O → ¬ G.Adj x y := by
    intro x y hx hy
    exact not_adj_descendant_childOutsideAt hG R hpu hx hy
  calc
    independencePolynomial (deleteVertex G p) =
        independencePolynomial
          (G.induce {x | x ∈ (Finset.univ : Finset V).erase p}) :=
      independencePolynomial_iso (deleteVertexIsoErase (G := G) p)
    _ = independencePolynomial (G.induce {x | x ∈ D ∪ O}) := by
      rw [R.descendants_union_childOutsideAt (G := G) hpu]
    _ = independencePolynomial
          ((G.induce {x | x ∈ D}) ⊕g (G.induce {x | x ∈ O})) :=
      (independencePolynomial_iso (unionIso G D O hd hc)).symm
    _ = independencePolynomial (G.induce {x | x ∈ D}) *
          independencePolynomial (G.induce {x | x ∈ O}) :=
      independencePolynomial_sum _ _
    _ = _ := rfl

end ComponentRooting

end ActualRootedVariance

end Erdos993
