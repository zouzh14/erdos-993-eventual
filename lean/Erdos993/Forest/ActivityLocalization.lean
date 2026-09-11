import Erdos993.Forest.FirstRecovery
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Activity localization for finite forests

This module proves the finite counting chain that places every first-recovery index strictly below
the hard-core mean at activity `27`.  It stops at that strict mean barrier.

The inspected mathlib graph API has finite matchings and vertex covers, but no maximum-matching
number or König equality.  The sole external graph-theoretic input is therefore the narrowly named
`ForestKonigCertificate`: an explicitly represented matching of size `|V| - α(G)`.
All counting and analytic consequences of that certificate are proved below.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)

/-- Addable vertices in one color class. -/
private noncomputable def sideAdditions (c : G.Coloring (Fin 2)) (j : Fin 2)
    (A : IndepFinset G) : Finset V := by
  classical
  exact Finset.univ.filter fun v ↦
    c v = j ∧ v ∉ A.val ∧ ∀ w ∈ A.val, ¬G.Adj v w

/-- Adding one available vertex from either side of a fixed two-coloring. -/
private def IsSideAddition (c : G.Coloring (Fin 2)) (A B : IndepFinset G) : Prop :=
  ∃ (j : Fin 2) (v : V), v ∈ sideAdditions G c j A ∧ B.val = insert v A.val

/-- Total extension operation, used only on vertices for which the inserted finset is independent. -/
private noncomputable def addIndep (A : IndepFinset G) (v : V) : IndepFinset G := by
  classical
  by_cases h : G.IsIndepSet ((insert v A.val : Finset V) : Set V)
  · exact ⟨insert v A.val, h⟩
  · exact A

private theorem addIndep_val_of_mem_sideAdditions
    (c : G.Coloring (Fin 2)) (j : Fin 2) (A : IndepFinset G) {v : V}
    (hv : v ∈ sideAdditions G c j A) :
    (addIndep G A v).val = insert v A.val := by
  classical
  have hd := (Finset.mem_filter.mp hv).2
  have hi : G.IsIndepSet (((insert v A.val) : Finset V) : Set V) := by
    apply (SimpleGraph.isIndepSet_iff G).2
    intro x hx y hy hxy
    change x ∈ insert v A.val at hx
    change y ∈ insert v A.val at hy
    simp only [Finset.mem_insert] at hx hy
    rcases hx with rfl | hxA <;> rcases hy with rfl | hyA
    · exact (hxy rfl).elim
    · exact hd.2.2 y hyA
    · intro hadj
      exact hd.2.2 x hxA hadj.symm
    · exact (SimpleGraph.isIndepSet_iff G).1 A.property hxA hyA hxy
  rw [addIndep]
  split
  · rfl
  · contradiction

private theorem sideAdditions_card_le
    (c : G.Coloring (Fin 2)) (j : Fin 2) (A : IndepFinset G) :
    (sideAdditions G c j A).card ≤ G.indepNum - A.val.card := by
  classical
  let S := sideAdditions G c j A
  have hS_indep : G.IsIndepSet (S : Set V) := by
    apply (SimpleGraph.isIndepSet_iff G).2
    intro v hv w hw hvw
    have hvc : c v = j := (Finset.mem_filter.mp hv).2.1
    have hwc : c w = j := (Finset.mem_filter.mp hw).2.1
    intro hadj
    exact (c.valid hadj) (hvc.trans hwc.symm)
  have hdisj : Disjoint S A.val := by
    rw [Finset.disjoint_left]
    intro v hvS hvA
    exact (Finset.mem_filter.mp hvS).2.2.1 hvA
  have hunion_indep : G.IsIndepSet ((S ∪ A.val : Finset V) : Set V) := by
    apply (SimpleGraph.isIndepSet_iff G).2
    intro v hv w hw hvw
    change v ∈ S ∪ A.val at hv
    change w ∈ S ∪ A.val at hw
    simp only [Finset.mem_union] at hv hw
    rcases hv with hvS | hvA <;> rcases hw with hwS | hwA
    · exact (SimpleGraph.isIndepSet_iff G).1 hS_indep hvS hwS hvw
    · exact (Finset.mem_filter.mp hvS).2.2.2 w hwA
    · intro hadj
      exact (Finset.mem_filter.mp hwS).2.2.2 v hvA hadj.symm
    · exact (SimpleGraph.isIndepSet_iff G).1 A.property hvA hwA hvw
  have hcardUnion : (S ∪ A.val).card ≤ G.indepNum :=
    SimpleGraph.IsIndepSet.card_le_indepNum hunion_indep
  have hcardEq : (S ∪ A.val).card = S.card + A.val.card :=
    Finset.card_union_of_disjoint hdisj
  have hcard : S.card + A.val.card ≤ G.indepNum := by
    rw [← hcardEq]
    exact hcardUnion
  exact Nat.le_sub_of_add_le (by simpa [S] using hcard)

/-- For a bipartite finite graph, double-counting one-vertex additions on its two color classes
proves `(k+1) i_(k+1) ≤ 2 (alpha-k) i_k`. -/
theorem addition_double_count_of_bipartite
    (hBip : G.IsBipartite) (k : ℕ) :
    (k + 1) * independenceCoeff G (k + 1) ≤
      2 * (G.indepNum - k) * independenceCoeff G k := by
  classical
  let c : G.Coloring (Fin 2) := Classical.choice hBip
  let L : Finset (IndepFinset G) := Finset.univ.filter fun A ↦ A.val.card = k
  let R : Finset (IndepFinset G) := Finset.univ.filter fun B ↦ B.val.card = k + 1
  let rel : IndepFinset G → IndepFinset G → Prop := IsSideAddition G c
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow rel (s := L) (t := R)
  have habove : ∀ A ∈ L,
      (Finset.bipartiteAbove rel R A).card ≤ 2 * (G.indepNum - k) := by
    intro A hAL
    let S0 := sideAdditions G c 0 A
    let S1 := sideAdditions G c 1 A
    let f : V → IndepFinset G := addIndep G A
    have hsub : Finset.bipartiteAbove rel R A ⊆ S0.image f ∪ S1.image f := by
      intro B hB
      have hrel := (Finset.mem_bipartiteAbove rel).1 hB |>.2
      obtain ⟨j, v, hv, hval⟩ := hrel
      have hBf : B = f v := by
        apply Subtype.ext
        change B.val = (addIndep G A v).val
        rw [addIndep_val_of_mem_sideAdditions G c j A hv]
        exact hval
      subst B
      fin_cases j
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    have hAcard : A.val.card = k := (Finset.mem_filter.mp hAL).2
    calc
      (Finset.bipartiteAbove rel R A).card ≤ (S0.image f ∪ S1.image f).card :=
        Finset.card_le_card hsub
      _ ≤ (S0.image f).card + (S1.image f).card := Finset.card_union_le _ _
      _ ≤ S0.card + S1.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ (G.indepNum - A.val.card) + (G.indepNum - A.val.card) :=
        Nat.add_le_add (sideAdditions_card_le G c 0 A) (sideAdditions_card_le G c 1 A)
      _ = 2 * (G.indepNum - k) := by rw [hAcard]; omega
  have hbelow : ∀ B ∈ R,
      (Finset.bipartiteBelow rel L B).card = k + 1 := by
    intro B hBR
    let eraseIndep : V → IndepFinset G := fun v ↦
      ⟨B.val.erase v, B.property.mono (Finset.erase_subset v B.val)⟩
    have herase_val (v : V) : (eraseIndep v).val = B.val.erase v := rfl
    have hset : Finset.bipartiteBelow rel L B = B.val.image eraseIndep := by
      ext A
      constructor
      · intro hA
        have hrel := (Finset.mem_bipartiteBelow rel).1 hA |>.2
        obtain ⟨j, v, hv, hval⟩ := hrel
        have hvnotA : v ∉ A.val := (Finset.mem_filter.mp hv).2.2.1
        have hvB : v ∈ B.val := by
          rw [hval]
          exact Finset.mem_insert_self v A.val
        apply Finset.mem_image.mpr
        refine ⟨v, hvB, ?_⟩
        apply Subtype.ext
        change B.val.erase v = A.val
        rw [hval, Finset.erase_insert hvnotA]
      · intro hA
        obtain ⟨v, hvB, rfl⟩ := Finset.mem_image.mp hA
        apply (Finset.mem_bipartiteBelow rel).2
        have hBcard : B.val.card = k + 1 := (Finset.mem_filter.mp hBR).2
        have heraseCard : (B.val.erase v).card = k := by
          rw [Finset.card_erase_of_mem hvB, hBcard]
          omega
        have heraseIndepCard : (eraseIndep v).val.card = k := by
          rw [herase_val]
          exact heraseCard
        refine ⟨by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, heraseIndepCard⟩, ?_⟩
        refine ⟨c v, v, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, rfl, ?_⟩
          constructor
          · change v ∉ B.val.erase v
            intro hv
            exact (Finset.mem_erase.mp hv).1 rfl
          · intro w hw
            change w ∈ B.val.erase v at hw
            exact (SimpleGraph.isIndepSet_iff G).1 B.property hvB
              (Finset.mem_of_mem_erase hw)
              (by
                intro hvw
                subst w
                have hmem : v ∈ B.val.erase v := hw
                simp only [Finset.mem_erase, ne_eq, not_true_eq_false,
                  false_and] at hmem)
        · change B.val = insert v (B.val.erase v)
          exact (Finset.insert_erase hvB).symm
    rw [hset]
    have hinj : Set.InjOn eraseIndep (B.val : Set V) := by
      intro x hx y hy hxy
      apply Finset.erase_injOn B.val hx hy
      exact congrArg Subtype.val hxy
    rw [Finset.card_image_iff.mpr hinj]
    exact (Finset.mem_filter.mp hBR).2
  have hL : L.card = independenceCoeff G k := by rfl
  have hR : R.card = independenceCoeff G (k + 1) := by rfl
  have hfiberSum :
      (∑ B ∈ R, (Finset.bipartiteBelow rel L B).card) = R.card * (k + 1) :=
    Finset.sum_const_nat hbelow
  calc
    (k + 1) * independenceCoeff G (k + 1) = R.card * (k + 1) := by
      simp [hR, Nat.mul_comm]
    _ = ∑ B ∈ R, (Finset.bipartiteBelow rel L B).card := hfiberSum.symm
    _ = ∑ A ∈ L, (Finset.bipartiteAbove rel R A).card := hdc.symm
    _ ≤ ∑ _A ∈ L, 2 * (G.indepNum - k) := by
      exact Finset.sum_le_sum fun A hA ↦ habove A hA
    _ = 2 * (G.indepNum - k) * independenceCoeff G k := by
      simp [hL, mul_comm]

/-- The addition double count specialized to forests. -/
theorem addition_double_count
    (hForest : G.IsAcyclic) (k : ℕ) :
    (k + 1) * independenceCoeff G (k + 1) ≤
      2 * (G.indepNum - k) * independenceCoeff G k :=
  addition_double_count_of_bipartite G hForest.isBipartite k

/-- A strict rise in the independence sequence can occur only at the two-thirds threshold. -/
theorem strict_rise_index_le_two_thirds
    (hForest : G.IsAcyclic) {k : ℕ}
    (hRise : independenceCoefficients G k < independenceCoefficients G (k + 1)) :
    k ≤ (2 * G.indepNum - 2) / 3 := by
  have hRiseNat : independenceCoeff G k < independenceCoeff G (k + 1) := by
    change (independenceCoeff G k : ℝ) < (independenceCoeff G (k + 1) : ℝ) at hRise
    exact_mod_cast hRise
  have hsuccPos : 0 < independenceCoeff G (k + 1) := by omega
  have hpos : 0 < independenceCoeff G k :=
    independenceCoeff_pos_of_succ_pos G k hsuccPos
  have hdc := addition_double_count G hForest k
  have hprod : (k + 1) * independenceCoeff G k <
      2 * (G.indepNum - k) * independenceCoeff G k := by
    calc
      (k + 1) * independenceCoeff G k <
          (k + 1) * independenceCoeff G (k + 1) :=
        (Nat.mul_lt_mul_left (by omega : 0 < k + 1)).2 hRiseNat
      _ ≤ 2 * (G.indepNum - k) * independenceCoeff G k := hdc
  have hfactor : k + 1 < 2 * (G.indepNum - k) := by
    apply (Nat.mul_lt_mul_right hpos).1
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
  omega

/-- Every first-recovery index obeys the same two-thirds bound. -/
theorem firstRecoveryIndex_le_two_thirds
    (hForest : G.IsAcyclic) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    s ≤ (2 * G.indepNum - 2) / 3 :=
  strict_rise_index_le_two_thirds G hForest hs.isRecovery.2

/-! ## A narrow König certificate and the forest partition estimate -/

/-- An explicit König certificate, isolated as the only graph-theoretic input absent from the
pinned API: a matching of size `ν = |V| - α(G)`.  This states no partition-function or hard-core
conclusion. -/
structure ForestKonigCertificate where
  nu : ℕ
  left : Fin nu → V
  right : Fin nu → V
  edge : ∀ i, G.Adj (left i) (right i)
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  cross_disjoint : ∀ i j, left i ≠ right j
  order_eq : Fintype.card V = G.indepNum + nu

private theorem fin_two_eq_of_ne_of_ne {a b d : Fin 2} (ha : a ≠ d) (hb : b ≠ d) : a = b := by
  fin_cases a <;> fin_cases b <;> fin_cases d <;> simp_all

/-- Every finite forest has an explicit matching of size `|V| - α(G)`. -/
theorem forestKonigCertificate_nonempty (hForest : G.IsAcyclic) :
    Nonempty (ForestKonigCertificate G) := by
  classical
  let c : G.Coloring (Fin 2) := Classical.choice hForest.isBipartite
  obtain ⟨A, hA⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  let C : Finset V := Finset.univ \ A
  let Cj (j : Fin 2) : Type u := {x : V // x ∈ C ∧ c x = j}
  let nbr (j : Fin 2) (x : Cj j) : Finset V :=
    Finset.univ.filter fun y ↦ y ∈ A ∧ G.Adj x y
  have hHall (j : Fin 2) (S : Finset (Cj j)) :
      S.card ≤ (S.biUnion (nbr j)).card := by
    let T : Finset V := S.biUnion (nbr j)
    let U : Finset V := Finset.image (fun x : Cj j ↦ (x : V)) S
    have hTsub : T ⊆ A := by
      intro y hy
      obtain ⟨x, hxS, hyx⟩ := Finset.mem_biUnion.mp hy
      exact (Finset.mem_filter.mp hyx).2.1
    have hUsub : U ⊆ C := by
      intro x hx
      change x ∈ S.image (fun z : Cj j ↦ (z : V)) at hx
      obtain ⟨x', hx'S, hx'eq⟩ := Finset.mem_image.mp hx
      subst x
      exact x'.property.1
    have hdisj : Disjoint (A \ T) U := by
      rw [Finset.disjoint_left]
      intro x hxAT hxU
      have hxA : x ∈ A := (Finset.mem_sdiff.mp hxAT).1
      have hxC : x ∈ C := hUsub hxU
      exact (Finset.mem_sdiff.mp hxC).2 hxA
    have hUindep : G.IsIndepSet (U : Set V) := by
      apply (SimpleGraph.isIndepSet_iff G).2
      intro x hx y hy hxy
      change x ∈ S.image (fun z : Cj j ↦ (z : V)) at hx
      change y ∈ S.image (fun z : Cj j ↦ (z : V)) at hy
      obtain ⟨x', hx'S, hx'eq⟩ := Finset.mem_image.mp hx
      obtain ⟨y', hy'S, hy'eq⟩ := Finset.mem_image.mp hy
      subst x
      subst y
      intro hadj
      exact (c.valid hadj) (x'.property.2.trans y'.property.2.symm)
    have hBindep : G.IsIndepSet (((A \ T) ∪ U : Finset V) : Set V) := by
      apply (SimpleGraph.isIndepSet_iff G).2
      intro x hx y hy hxy
      change x ∈ (A \ T) ∪ U at hx
      change y ∈ (A \ T) ∪ U at hy
      rw [Finset.mem_union] at hx hy
      rcases hx with hxAT | hxU <;> rcases hy with hyAT | hyU
      · exact (SimpleGraph.isIndepSet_iff G).1
          (hA.isIndepSet.mono (Finset.sdiff_subset : A \ T ⊆ A)) hxAT hyAT hxy
      · intro hadj
        change y ∈ S.image (fun z : Cj j ↦ (z : V)) at hyU
        obtain ⟨y', hy'S, hy'eq⟩ := Finset.mem_image.mp hyU
        subst y
        have hxA : x ∈ A := (Finset.mem_sdiff.mp hxAT).1
        have hxT : x ∈ T := by
          apply Finset.mem_biUnion.mpr
          refine ⟨y', hy'S, ?_⟩
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hxA, hadj.symm⟩
        exact (Finset.mem_sdiff.mp hxAT).2 hxT
      · intro hadj
        change x ∈ S.image (fun z : Cj j ↦ (z : V)) at hxU
        obtain ⟨x', hx'S, hx'eq⟩ := Finset.mem_image.mp hxU
        subst x
        have hyA : y ∈ A := (Finset.mem_sdiff.mp hyAT).1
        have hyT : y ∈ T := by
          apply Finset.mem_biUnion.mpr
          refine ⟨x', hx'S, ?_⟩
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hyA, hadj⟩
        exact (Finset.mem_sdiff.mp hyAT).2 hyT
      · exact (SimpleGraph.isIndepSet_iff G).1 hUindep hxU hyU hxy
    have hUcard : U.card = S.card := by
      change (S.image (fun x : Cj j ↦ (x : V))).card = S.card
      exact Finset.card_image_of_injective S Subtype.val_injective
    have hBcard : ((A \ T) ∪ U).card = A.card - T.card + S.card := by
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hTsub, hUcard]
    have hBle : ((A \ T) ∪ U).card ≤ G.indepNum :=
      SimpleGraph.IsIndepSet.card_le_indepNum hBindep
    have hTle : T.card ≤ G.indepNum := by
      rw [← hA.card_eq]
      exact Finset.card_le_card hTsub
    rw [hBcard, hA.card_eq] at hBle
    change S.card ≤ T.card
    omega
  have hMatches : ∀ j : Fin 2, ∃ f : Cj j → V,
      Function.Injective f ∧ ∀ x, f x ∈ nbr j x := by
    intro j
    exact (Finset.all_card_le_biUnion_card_iff_existsInjective' (nbr j)).1 (hHall j)
  choose f hf_inj hf_mem using hMatches
  let Ctype : Type u := {x : V // x ∈ C}
  let leftC : Ctype → V := fun x ↦ x
  let fTotal (j : Fin 2) (x : V) : V :=
    if hx : x ∈ C ∧ c x = j then f j ⟨x, hx⟩ else x
  let rightC : Ctype → V := fun x ↦ fTotal (c x) x
  have hright_mem (x : Ctype) :
      rightC x ∈ nbr (c x) ⟨x, x.property, rfl⟩ := by
    simpa [rightC, fTotal, x.property] using
      (hf_mem (c x) ⟨x, x.property, rfl⟩)
  have hedgeC (x : Ctype) : G.Adj (leftC x) (rightC x) := by
    exact (Finset.mem_filter.mp (hright_mem x)).2.2
  have hleftC : Function.Injective leftC := Subtype.val_injective
  have hrightC : Function.Injective rightC := by
    intro x y hxy
    have hxne : c x ≠ c (rightC x) := c.valid (hedgeC x)
    have hyne : c y ≠ c (rightC y) := c.valid (hedgeC y)
    have hcolor : c x = c y := by
      apply fin_two_eq_of_ne_of_ne hxne
      simpa [hxy] using hyne
    have hxy' : fTotal (c x) x = fTotal (c y) y := hxy
    rw [← hcolor] at hxy'
    have hff : f (c x) ⟨(x : V), x.property, rfl⟩ =
        f (c x) ⟨(y : V), y.property, hcolor.symm⟩ := by
      simpa [fTotal, x.property, y.property, hcolor.symm] using hxy'
    have hdep := hf_inj (c x) hff
    have hv : (x : V) = (y : V) :=
      congrArg (fun z : Cj (c x) ↦ (z : V)) hdep
    exact Subtype.ext hv
  have hcrossC (x y : Ctype) : leftC x ≠ rightC y := by
    intro hEq
    have hxC : (x : V) ∈ C := x.property
    have hxnotA : (x : V) ∉ A := (Finset.mem_sdiff.mp hxC).2
    have hyA : rightC y ∈ A :=
      (Finset.mem_filter.mp (hright_mem y)).2.1
    change (x : V) = rightC y at hEq
    rw [hEq] at hxnotA
    exact hxnotA hyA
  let e : Fin (Fintype.card Ctype) ≃ Ctype := (Fintype.equivFin Ctype).symm
  refine ⟨{
    nu := Fintype.card Ctype
    left := fun i ↦ leftC (e i)
    right := fun i ↦ rightC (e i)
    edge := fun i ↦ hedgeC (e i)
    left_injective := hleftC.comp e.injective
    right_injective := hrightC.comp e.injective
    cross_disjoint := fun i j ↦ hcrossC (e i) (e j)
    order_eq := ?_ }⟩
  have hCcard : Fintype.card Ctype = C.card := by
    exact Fintype.card_coe C
  have hAsub : A ⊆ (Finset.univ : Finset V) := Finset.subset_univ A
  rw [hCcard]
  dsimp [C]
  rw [Finset.card_sdiff_of_subset hAsub, Finset.card_univ, hA.card_eq]
  have hAle : G.indepNum ≤ Fintype.card V := by
    rw [← hA.card_eq, ← Finset.card_univ]
    exact Finset.card_le_card hAsub
  omega

namespace ForestKonigCertificate

variable {G : SimpleGraph V}

/-- The endpoints of the represented matching. -/
def endpoints (K : ForestKonigCertificate G) : Finset V :=
  Finset.univ.image K.left ∪ Finset.univ.image K.right

/-- Code an independent set by its choices on the matching edges and its free choices outside the
matching. -/
private def encode (K : ForestKonigCertificate G) (S : IndepFinset G) :
    (Fin K.nu → Fin 3) × (↥(Finset.univ \ K.endpoints) → Bool) :=
  (fun i ↦ if K.left i ∈ S.val then 1 else if K.right i ∈ S.val then 2 else 0,
    fun v ↦ decide ((v : V) ∈ S.val))

private theorem encode_injective (K : ForestKonigCertificate G) :
    Function.Injective K.encode := by
  intro S T hST
  apply Subtype.ext
  ext v
  by_cases hE : v ∈ K.endpoints
  · rw [endpoints, Finset.mem_union] at hE
    rcases hE with hL | hR
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hL
      subst v
      have hcode := congrFun (congrArg Prod.fst hST) i
      by_cases hSi : K.left i ∈ S.val
      · have hTi : K.left i ∈ T.val := by
          by_contra hnot
          by_cases hTright : K.right i ∈ T.val <;>
            simp [encode, hSi, hnot, hTright] at hcode
        simp [hSi, hTi]
      · have hTi : K.left i ∉ T.val := by
          intro hmem
          by_cases hSright : K.right i ∈ S.val <;>
            simp [encode, hSi, hmem, hSright] at hcode
        simp [hSi, hTi]
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hR
      subst v
      have hcode := congrFun (congrArg Prod.fst hST) i
      by_cases hSright : K.right i ∈ S.val <;> by_cases hTright : K.right i ∈ T.val
      · simp [hSright, hTright]
      · have hSleft : K.left i ∉ S.val := by
          intro hmem
          exact ((SimpleGraph.isIndepSet_iff G).1 S.property hmem hSright (K.edge i).ne)
            (K.edge i)
        by_cases hTleft : K.left i ∈ T.val <;>
          simp [encode, hSleft, hTleft, hSright, hTright] at hcode
      · have hTleft : K.left i ∉ T.val := by
          intro hmem
          exact ((SimpleGraph.isIndepSet_iff G).1 T.property hmem hTright (K.edge i).ne)
            (K.edge i)
        by_cases hSleft : K.left i ∈ S.val <;>
          simp [encode, hSleft, hTleft, hSright, hTright] at hcode
      · simp [hSright, hTright]
  · let v' : ↥(Finset.univ \ K.endpoints) := ⟨v, by simp [hE]⟩
    have hcode := congrFun (congrArg Prod.snd hST) v'
    simpa [encode, v'] using hcode

private theorem endpoints_card (K : ForestKonigCertificate G) :
    K.endpoints.card = 2 * K.nu := by
  have hdisj : Disjoint (Finset.univ.image K.left) (Finset.univ.image K.right) := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hvL
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hvR
    subst v
    exact K.cross_disjoint i j hj.symm
  rw [endpoints, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ K.left_injective,
    Finset.card_image_of_injective _ K.right_injective, Finset.card_univ,
    Fintype.card_fin]
  omega

private theorem nu_le_indepNum (K : ForestKonigCertificate G) : K.nu ≤ G.indepNum := by
  have horder : K.nu + K.nu ≤ G.indepNum + K.nu := by
    rw [← K.order_eq]
    calc
      K.nu + K.nu = K.endpoints.card := by rw [K.endpoints_card]; omega
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ K.endpoints)
      _ = Fintype.card V := Finset.card_univ
  omega

/-- Three choices on every matching edge and two choices at every remaining vertex bound the
number of independent sets. -/
theorem card_indepFinset_le (K : ForestKonigCertificate G) :
    Fintype.card (IndepFinset G) ≤ 3 ^ K.nu * 2 ^ (G.indepNum - K.nu) := by
  have hinj := Fintype.card_le_of_injective K.encode K.encode_injective
  have hcardOutside : (Finset.univ \ K.endpoints).card = G.indepNum - K.nu := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ K.endpoints),
      Finset.card_univ, K.endpoints_card, K.order_eq]
    omega
  calc
    Fintype.card (IndepFinset G) ≤
        Fintype.card ((Fin K.nu → Fin 3) × (↥(Finset.univ \ K.endpoints) → Bool)) := hinj
    _ = 3 ^ K.nu * 2 ^ (G.indepNum - K.nu) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, Fintype.card_coe,
        hcardOutside]

/-- At activity one, the partition function obeys the direct matching-encoding bound. -/
theorem independenceEval_one_le_matching_bound (K : ForestKonigCertificate G) :
    independenceEval G 1 ≤
      (3 : ℝ) ^ K.nu * 2 ^ (G.indepNum - K.nu) := by
  have hcard := K.card_indepFinset_le
  have heval : independenceEval G 1 = (Fintype.card (IndepFinset G) : ℝ) := by
    rw [independenceEval_eq_sum]
    simp
  rw [heval]
  exact_mod_cast hcard

/-- Replacing every free binary choice by a ternary choice gives the second half of the
partition-function estimate. -/
theorem matching_bound_le_three_pow (K : ForestKonigCertificate G) :
    (3 : ℝ) ^ K.nu * 2 ^ (G.indepNum - K.nu) ≤
      3 ^ G.indepNum := by
  have hnu : K.nu ≤ G.indepNum := K.nu_le_indepNum
  have hpow : 2 ^ (G.indepNum - K.nu) ≤ 3 ^ (G.indepNum - K.nu) :=
    Nat.pow_le_pow_left (by omega) _
  have hnat : 3 ^ K.nu * 2 ^ (G.indepNum - K.nu) ≤ 3 ^ G.indepNum := by
    calc
      3 ^ K.nu * 2 ^ (G.indepNum - K.nu) ≤
          3 ^ K.nu * 3 ^ (G.indepNum - K.nu) := Nat.mul_le_mul_left _ hpow
      _ = 3 ^ G.indepNum := by
        rw [← pow_add, Nat.add_sub_of_le hnu]
  exact_mod_cast hnat

/-- The forest partition estimate at activity one, derived from the explicit matching certificate. -/
theorem independenceEval_one_le_three_pow (K : ForestKonigCertificate G) :
    independenceEval G 1 ≤ (3 : ℝ) ^ G.indepNum := by
  have hnu : K.nu ≤ G.indepNum := K.nu_le_indepNum
  have hcard := K.card_indepFinset_le
  have hpow : 2 ^ (G.indepNum - K.nu) ≤ 3 ^ (G.indepNum - K.nu) :=
    Nat.pow_le_pow_left (by omega) _
  have hnat : Fintype.card (IndepFinset G) ≤ 3 ^ G.indepNum := by
    calc
      Fintype.card (IndepFinset G) ≤ 3 ^ K.nu * 2 ^ (G.indepNum - K.nu) := hcard
      _ ≤ 3 ^ K.nu * 3 ^ (G.indepNum - K.nu) := Nat.mul_le_mul_left _ hpow
      _ = 3 ^ G.indepNum := by
        rw [← pow_add, Nat.add_sub_of_le hnu]
  have heval : independenceEval G 1 = (Fintype.card (IndepFinset G) : ℝ) := by
    rw [independenceEval_eq_sum]
    simp
  rw [heval]
  exact_mod_cast hnat

end ForestKonigCertificate

/-! ## The modulo-three estimate -/

private theorem pow_twentySeven (r : ℕ) : (27 : ℕ) ^ r = 3 ^ (3 * r) := by
  rw [show (27 : ℕ) = 3 ^ 3 by norm_num, pow_mul]

/-- In the residue-zero case, the normalized positive term is `27(r+1)`. -/
theorem modulo_three_normalized_zero (r : ℕ) (hr : 0 < r) :
    let alpha := 3 * r
    let b := (2 * alpha - 2) / 3
    let d := alpha - b
    b = 2 * r - 1 ∧ d = r + 1 ∧
      d * 27 ^ d = (27 * (r + 1)) * 3 ^ alpha ∧
      b < 27 * (r + 1) := by
  dsimp only
  have hb : (2 * (3 * r) - 2) / 3 = 2 * r - 1 := by omega
  have hd : 3 * r - (2 * r - 1) = r + 1 := by omega
  rw [hb, hd]
  refine ⟨rfl, rfl, ?_, by omega⟩
  rw [pow_succ, pow_twentySeven]
  ring

/-- In the residue-one case, the normalized positive term is `9(r+1)`. -/
theorem modulo_three_normalized_one (r : ℕ) :
    let alpha := 3 * r + 1
    let b := (2 * alpha - 2) / 3
    let d := alpha - b
    b = 2 * r ∧ d = r + 1 ∧
      d * 27 ^ d = (9 * (r + 1)) * 3 ^ alpha ∧
      b < 9 * (r + 1) := by
  dsimp only
  have hb : (2 * (3 * r + 1) - 2) / 3 = 2 * r := by omega
  have hd : 3 * r + 1 - 2 * r = r + 1 := by omega
  rw [hb, hd]
  refine ⟨rfl, rfl, ?_, by omega⟩
  rw [pow_succ, pow_twentySeven, pow_succ]
  ring

/-- In the residue-two case, the normalized positive term is `81(r+2)`. -/
theorem modulo_three_normalized_two (r : ℕ) :
    let alpha := 3 * r + 2
    let b := (2 * alpha - 2) / 3
    let d := alpha - b
    b = 2 * r ∧ d = r + 2 ∧
      d * 27 ^ d = (81 * (r + 2)) * 3 ^ alpha ∧
      b < 81 * (r + 2) := by
  dsimp only
  have hb : (2 * (3 * r + 2) - 2) / 3 = 2 * r := by omega
  have hd : 3 * r + 2 - 2 * r = r + 2 := by omega
  rw [hb, hd]
  refine ⟨rfl, rfl, ?_, by omega⟩
  rw [show r + 2 = (r + 1) + 1 by omega, pow_succ, pow_succ,
    pow_twentySeven, show 3 * r + 2 = (3 * r + 1) + 1 by omega,
    pow_succ, pow_succ]
  ring

/-- The arithmetic core of the localization proof, split into the three residue classes of `α`. -/
theorem modulo_three_strict_estimate (alpha : ℕ) (halpha : 0 < alpha) :
    let b := (2 * alpha - 2) / 3
    let d := alpha - b
    b * 3 ^ alpha < d * 27 ^ d := by
  let r := alpha / 3
  have hdecomp : alpha = 3 * r + alpha % 3 := by
    dsimp [r]
    omega
  have hmod : alpha % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hrem : alpha % 3
  · have hr : 0 < r := by omega
    have halpha' : alpha = 3 * r := by omega
    rw [halpha']
    simp only
    have hb : (2 * (3 * r) - 2) / 3 = 2 * r - 1 := by omega
    have hd : 3 * r - (2 * r - 1) = r + 1 := by omega
    rw [hb, hd]
    have hright : (r + 1) * 27 ^ (r + 1) =
        (27 * (r + 1)) * 3 ^ (3 * r) := by
      rw [pow_succ, pow_twentySeven]
      ring
    rw [hright]
    exact (Nat.mul_lt_mul_right (pow_pos (by norm_num : (0 : ℕ) < 3) _)).2 (by omega)
  · have halpha' : alpha = 3 * r + 1 := by omega
    rw [halpha']
    simp only
    have hb : (2 * (3 * r + 1) - 2) / 3 = 2 * r := by omega
    have hd : 3 * r + 1 - 2 * r = r + 1 := by omega
    rw [hb, hd]
    have hleft : 2 * r * 3 ^ (3 * r + 1) = (6 * r) * 3 ^ (3 * r) := by
      rw [pow_succ]
      ring
    have hright : (r + 1) * 27 ^ (r + 1) =
        (27 * (r + 1)) * 3 ^ (3 * r) := by
      rw [pow_succ, pow_twentySeven]
      ring
    rw [hleft, hright]
    exact (Nat.mul_lt_mul_right (pow_pos (by norm_num : (0 : ℕ) < 3) _)).2 (by omega)
  · have halpha' : alpha = 3 * r + 2 := by omega
    rw [halpha']
    simp only
    have hb : (2 * (3 * r + 2) - 2) / 3 = 2 * r := by omega
    have hd : 3 * r + 2 - 2 * r = r + 2 := by omega
    rw [hb, hd]
    have hleft : 2 * r * 3 ^ (3 * r + 2) = (18 * r) * 3 ^ (3 * r) := by
      rw [show 3 * r + 2 = 3 * r + 2 by rfl, pow_add]
      norm_num
      ring
    have hright : (r + 2) * 27 ^ (r + 2) =
        (729 * (r + 2)) * 3 ^ (3 * r) := by
      rw [show r + 2 = r + 2 by rfl, pow_add, pow_twentySeven]
      norm_num
      ring
    rw [hleft, hright]
    exact (Nat.mul_lt_mul_right (pow_pos (by norm_num : (0 : ℕ) < 3) _)).2 (by omega)

/-! ## Weighted partition lower bound and the strict mean barrier -/

omit [DecidableEq V] in
private theorem mean_gap_sum_twentySeven (b : ℕ) :
    independenceEval G 27 * ((hardCoreLaw G 27 (by norm_num)).mean - (b : ℝ)) =
      ∑ S : IndepFinset G, ((S.val.card : ℝ) - (b : ℝ)) * 27 ^ S.val.card := by
  have hm : independenceEval G 27 * (hardCoreLaw G 27 (by norm_num)).mean =
      ∑ S : IndepFinset G, (S.val.card : ℝ) * 27 ^ S.val.card := by
    have hZ : independenceEval G 27 ≠ 0 :=
      (independenceEval_pos G (by norm_num)).ne'
    rw [FiniteLatticeLaw.mean, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    simp only [hardCoreLaw]
    field_simp
  rw [mul_sub, hm, independenceEval_eq_sum, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S hS
  ring

private theorem weighted_term_lower_twentySeven (n b : ℕ) :
    -((b : ℝ) * 27 ^ b) ≤ ((n : ℝ) - b) * 27 ^ n := by
  by_cases h : b ≤ n
  · have hnb : (0 : ℝ) ≤ (n : ℝ) - b := sub_nonneg.mpr (by exact_mod_cast h)
    have hnonneg : 0 ≤ ((n : ℝ) - b) * 27 ^ n :=
      mul_nonneg hnb (pow_nonneg (by norm_num) _)
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 27 by norm_num) b]
  · have hn : n ≤ b := by omega
    have hp : (27 : ℝ) ^ n ≤ 27 ^ b := pow_le_pow_right₀ (by norm_num) hn
    have hbn : (b : ℝ) - n ≤ b := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hprod : ((b : ℝ) - n) * 27 ^ n ≤ b * 27 ^ b :=
      mul_le_mul hbn hp (pow_nonneg (by norm_num) _) hb0
    nlinarith

/-- Keeping one maximum independent-set term and bounding every other term below proves the
weighted partition-function estimate used in the activity localization argument. -/
theorem partition_mean_gap_lower_bound (b : ℕ) (hb : b ≤ G.indepNum) :
    (27 : ℝ) ^ b *
        (((G.indepNum - b : ℕ) : ℝ) * 27 ^ (G.indepNum - b) -
          (b : ℝ) * independenceEval G 1) ≤
      independenceEval G 27 * ((hardCoreLaw G 27 (by norm_num)).mean - (b : ℝ)) := by
  obtain ⟨Aset, hA⟩ := SimpleGraph.exists_isNIndepSet_indepNum (G := G)
  let A : IndepFinset G := ⟨Aset, hA.isIndepSet⟩
  have hAcard : A.val.card = G.indepNum := hA.card_eq
  let f : IndepFinset G → ℝ := fun S =>
    ((S.val.card : ℝ) - (b : ℝ)) * 27 ^ S.val.card
  let M : ℝ := (b : ℝ) * 27 ^ b
  have hpoint : ∀ S : IndepFinset G, -M ≤ f S := by
    intro S
    simpa [M, f] using weighted_term_lower_twentySeven S.val.card b
  have hA_mem : A ∈ (Finset.univ : Finset (IndepFinset G)) := Finset.mem_univ A
  have herase : ((Finset.univ.erase A).card : ℝ) * (-M) ≤
      ∑ S ∈ Finset.univ.erase A, f S := by
    simpa [nsmul_eq_mul] using
      (Finset.card_nsmul_le_sum (Finset.univ.erase A) f (-M)
        (fun S hS => hpoint S))
  have hcard : (Finset.univ.erase A).card ≤ Fintype.card (IndepFinset G) := by
    rw [Fintype.card]
    exact Finset.card_le_card (Finset.erase_subset A Finset.univ)
  have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)
  have herase' : -(Fintype.card (IndepFinset G) : ℝ) * M ≤
      ∑ S ∈ Finset.univ.erase A, f S := by
    have hcardR : ((Finset.univ.erase A).card : ℝ) ≤
        Fintype.card (IndepFinset G) := by exact_mod_cast hcard
    calc
      -(Fintype.card (IndepFinset G) : ℝ) * M ≤
          -((Finset.univ.erase A).card : ℝ) * M := by nlinarith
      _ = ((Finset.univ.erase A).card : ℝ) * (-M) := by ring
      _ ≤ _ := herase
  have hsum : -(Fintype.card (IndepFinset G) : ℝ) * M + f A ≤
      ∑ S : IndepFinset G, f S := by
    rw [← Finset.sum_erase_add (Finset.univ : Finset (IndepFinset G)) f hA_mem]
    linarith
  have hcardEval : (Fintype.card (IndepFinset G) : ℝ) = independenceEval G 1 := by
    rw [independenceEval_eq_sum]
    simp
  rw [mean_gap_sum_twentySeven G b]
  calc
    (27 : ℝ) ^ b *
        (((G.indepNum - b : ℕ) : ℝ) * 27 ^ (G.indepNum - b) -
          (b : ℝ) * independenceEval G 1) =
        -(Fintype.card (IndepFinset G) : ℝ) * M + f A := by
      rw [hcardEval]
      simp only [M, f, hAcard]
      rw [← Nat.cast_sub hb,
        show (27 : ℝ) ^ G.indepNum = 27 ^ b * 27 ^ (G.indepNum - b) by
          rw [← pow_add, Nat.add_sub_of_le hb]]
      ring
    _ ≤ ∑ S : IndepFinset G, f S := hsum
    _ = ∑ S : IndepFinset G,
        ((S.val.card : ℝ) - (b : ℝ)) * 27 ^ S.val.card := by rfl

/-- The partition estimate and the modulo-three inequality make the explicit lower bound strictly
positive.  This is the formal version of
`I_F(27) (K₁(I_F;27)-b) ≥ 27^b (d 27^d-b I_F(1)) > 0`. -/
theorem partition_mean_gap_strict_lower_bound
    (K : ForestKonigCertificate G) (ha : 0 < G.indepNum) :
    let b := (2 * G.indepNum - 2) / 3
    let d := G.indepNum - b
    0 < (27 : ℝ) ^ b *
        ((d : ℝ) * 27 ^ d - (b : ℝ) * independenceEval G 1) ∧
      (27 : ℝ) ^ b *
          ((d : ℝ) * 27 ^ d - (b : ℝ) * independenceEval G 1) ≤
        independenceEval G 27 *
          ((hardCoreLaw G 27 (by norm_num)).mean - (b : ℝ)) := by
  dsimp only
  let alpha := G.indepNum
  let b := (2 * alpha - 2) / 3
  let d := alpha - b
  have hb : b ≤ alpha := by
    dsimp [b, alpha]
    omega
  have harithNat : b * 3 ^ alpha < d * 27 ^ d := by
    simpa [alpha, b, d] using
      modulo_three_strict_estimate alpha (by simpa [alpha] using ha)
  have harith : (b : ℝ) * 3 ^ alpha < (d : ℝ) * 27 ^ d := by
    exact_mod_cast harithNat
  have hEval := K.independenceEval_one_le_three_pow
  have hbracket :
      0 < (d : ℝ) * 27 ^ d - (b : ℝ) * independenceEval G 1 := by
    have hmul : (b : ℝ) * independenceEval G 1 ≤ (b : ℝ) * 3 ^ alpha :=
      mul_le_mul_of_nonneg_left hEval (Nat.cast_nonneg b)
    linarith
  have hpow : 0 < (27 : ℝ) ^ b := pow_pos (by norm_num) _
  have hlower := partition_mean_gap_lower_bound G b hb
  change 0 < (27 : ℝ) ^ b *
        ((d : ℝ) * 27 ^ d - (b : ℝ) * independenceEval G 1) ∧
      (27 : ℝ) ^ b *
          ((d : ℝ) * 27 ^ d - (b : ℝ) * independenceEval G 1) ≤
        independenceEval G 27 *
          ((hardCoreLaw G 27 (by norm_num)).mean - (b : ℝ))
  exact ⟨mul_pos hpow hbracket, hlower⟩

/-- Under the explicit matching/König certificate, the hard-core mean at activity `27` lies
strictly above the two-thirds threshold. -/
theorem hardCoreLaw_mean_twentySeven_gt_two_thirds
    (K : ForestKonigCertificate G) (ha : 0 < G.indepNum) :
    (hardCoreLaw G 27 (by norm_num)).mean >
      ((2 * G.indepNum - 2) / 3 : ℕ) := by
  obtain ⟨hpositive, hlower⟩ := partition_mean_gap_strict_lower_bound G K ha
  have hprod : 0 < independenceEval G 27 *
      ((hardCoreLaw G 27 (by norm_num)).mean -
        (((2 * G.indepNum - 2) / 3 : ℕ) : ℝ)) :=
    lt_of_lt_of_le hpositive hlower
  exact sub_pos.mp (pos_of_mul_pos_right hprod
    (independenceEval_pos G (by norm_num)).le)

/-- Final Unit 3 barrier: every first-recovery index of a finite forest is strictly below the
hard-core mean at activity `27`.  No canonical activity is used. -/
theorem hardCoreLaw_mean_twentySeven_gt_firstRecoveryIndex
    (hForest : G.IsAcyclic) (K : ForestKonigCertificate G) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    (hardCoreLaw G 27 (by norm_num)).mean > s := by
  have hsBound := firstRecoveryIndex_le_two_thirds G hForest hs
  have ha : 0 < G.indepNum := by
    by_contra hnot
    have hzero : G.indepNum = 0 := by omega
    rw [hzero] at hsBound
    have hspos := hs.index_pos
    omega
  have hm := hardCoreLaw_mean_twentySeven_gt_two_thirds G K ha
  exact lt_of_le_of_lt (by exact_mod_cast hsBound) hm


/-- Every first-recovery index of a finite forest is strictly below the hard-core mean at
activity `27`; the matching/König certificate is constructed internally from acyclicity. -/
theorem hardCoreLaw_mean_twentySeven_gt_firstRecoveryIndex_of_isAcyclic
    (hForest : G.IsAcyclic) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    (hardCoreLaw G 27 (by norm_num)).mean > s := by
  let K : ForestKonigCertificate G :=
    Classical.choice (forestKonigCertificate_nonempty G hForest)
  exact hardCoreLaw_mean_twentySeven_gt_firstRecoveryIndex G hForest K hs

end
end Forest
end Erdos993
