import Erdos993.Forest.CanonicalLaw
import Erdos993.Forest.FirstRecovery
import Erdos993.Forest.Interfaces
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Index and variance localization for finite forests

This file proves the finite-graph part of Proposition 2.1 with its exact
constants.  It develops the low-degree independent set, coefficient and
canonical-activity estimates, an explicit finite conditioning decomposition of
the hard-core law, the erase/intersection avoidance bound, the forest variance
lower bound, and the final `IndexVarianceSizeLocalized` interface inhabitant.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- A finite acyclic graph has at most as many edges as vertices. -/
theorem SimpleGraph.IsAcyclic.card_edgeFinset_le_card
    [DecidableRel G.Adj] (hG : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V := by
  classical
  cases isEmpty_or_nonempty V with
  | inl hV =>
      letI : IsEmpty V := hV
      have hbot : G = ⊥ := by
        ext v
        exact isEmptyElim v
      simp [hbot]
  | inr hV =>
      letI : Nonempty V := hV
      obtain ⟨T, hGT, hTmax⟩ :=
        SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
          (G := (⊤ : SimpleGraph V)) (H := G) (by simp) hG
      have hTmax' : Maximal SimpleGraph.IsAcyclic T := by
        simpa only [le_top, true_and] using hTmax
      have hTtree : T.IsTree :=
        SimpleGraph.maximal_isAcyclic_iff_isTree.mp hTmax'
      have hcard : G.edgeFinset.card ≤ T.edgeFinset.card :=
        Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
      have hTcard : T.edgeFinset.card + 1 = Fintype.card V :=
        hTtree.card_edgeFinset
      omega

/-- The sharp edge bound for a nonempty finite forest. -/
theorem SimpleGraph.IsAcyclic.card_edgeFinset_add_one_le_card
    [DecidableRel G.Adj] [Nonempty V] (hG : G.IsAcyclic) :
    G.edgeFinset.card + 1 ≤ Fintype.card V := by
  classical
  obtain ⟨T, hGT, hTmax⟩ :=
    SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
      (G := (⊤ : SimpleGraph V)) (H := G) (by simp) hG
  have hTmax' : Maximal SimpleGraph.IsAcyclic T := by
    simpa only [le_top, true_and] using hTmax
  have hTtree : T.IsTree :=
    SimpleGraph.maximal_isAcyclic_iff_isTree.mp hTmax'
  have hcard : G.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  have hTcard : T.edgeFinset.card + 1 = Fintype.card V :=
    hTtree.card_edgeFinset
  omega

/-- Double-count incidences between a finite vertex set and all graph edges. -/
private lemma incidence_sum_on_eq [DecidableEq V] [DecidableRel G.Adj]
    (H : Finset V) :
    (∑ v ∈ H, G.degree v) =
      ∑ e ∈ G.edgeFinset, (H.filter (fun v => v ∈ e)).card := by
  classical
  calc
    (∑ v ∈ H, G.degree v) =
        ∑ v ∈ H, (G.incidenceFinset v).card := by
          apply Finset.sum_congr rfl
          intro v hv
          exact (G.card_incidenceFinset_eq_degree v).symm
    _ = ∑ v ∈ H, ∑ e ∈ G.edgeFinset,
          if e ∈ G.incidenceFinset v then (1 : ℕ) else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          rw [Finset.sum_boole (R := ℕ)]
          apply congrArg Finset.card
          ext e
          simp only [Finset.mem_filter]
          constructor
          · intro he
            exact ⟨G.incidenceFinset_subset v he, he⟩
          · exact fun he => he.2
    _ = ∑ e ∈ G.edgeFinset, ∑ v ∈ H,
          if e ∈ G.incidenceFinset v then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ e ∈ G.edgeFinset, (H.filter (fun v => v ∈ e)).card := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext v
          simp only [Finset.mem_filter]
          have hedge : e ∈ G.edgeSet := SimpleGraph.mem_edgeFinset.mp he
          rw [G.mem_incidenceFinset]
          simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq, hedge, true_and]

/-- An edge contributes at most one incidence, plus one more exactly when both
of its endpoints lie in the chosen vertex set. -/
private lemma edge_contrib_on_le [DecidableEq V]
    (H : Finset V) (e : Sym2 V) :
    (H.filter (fun v => v ∈ e)).card ≤
      1 + if e ∈ H.sym2 then 1 else 0 := by
  induction e using Sym2.inductionOn with
  | _ v w =>
      by_cases hv : v ∈ H
      · by_cases hw : w ∈ H
        · have hsym : s(v, w) ∈ H.sym2 := by
            rw [Finset.mem_sym2_iff]
            intro a ha
            rcases Sym2.mem_iff.mp ha with rfl | rfl
            · exact hv
            · exact hw
          rw [if_pos hsym]
          calc
            (H.filter (fun x => x ∈ s(v, w))).card ≤ ({v, w} : Finset V).card :=
              Finset.card_le_card (by
                intro x hx
                simp only [Finset.mem_filter, Sym2.mem_iff,
                  Finset.mem_insert, Finset.mem_singleton] at hx ⊢
                exact hx.2)
            _ ≤ 2 := by
              simpa using Finset.card_insert_le v ({w} : Finset V)
        · have hsym : s(v, w) ∉ H.sym2 := by
            intro h
            rw [Finset.mem_sym2_iff] at h
            exact hw (h w (by simp))
          rw [if_neg hsym, add_zero]
          have hsub : H.filter (fun x => x ∈ s(v, w)) ⊆ ({v} : Finset V) := by
            intro x hx
            simp only [Finset.mem_filter, Sym2.mem_iff,
              Finset.mem_singleton] at hx ⊢
            rcases hx.2 with rfl | rfl
            · rfl
            · exact (hw hx.1).elim
          simpa using Finset.card_le_card hsub
      · have hsym : s(v, w) ∉ H.sym2 := by
          intro h
          rw [Finset.mem_sym2_iff] at h
          exact hv (h v (by simp))
        rw [if_neg hsym, add_zero]
        have hsub : H.filter (fun x => x ∈ s(v, w)) ⊆ ({w} : Finset V) := by
          intro x hx
          simp only [Finset.mem_filter, Sym2.mem_iff,
            Finset.mem_singleton] at hx ⊢
          rcases hx.2 with rfl | rfl
          · exact (hv hx.1).elim
          · rfl
        simpa using Finset.card_le_card hsub

/-- Restricted incidence bound for a finite forest: incidences at a vertex set
are bounded by all edges plus the number of selected vertices. -/
theorem SimpleGraph.IsAcyclic.sum_degrees_on_le_card_edges_add_card
    [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (H : Finset V) :
    (∑ v ∈ H, G.degree v) ≤ G.edgeFinset.card + H.card := by
  classical
  rw [incidence_sum_on_eq H]
  calc
    (∑ e ∈ G.edgeFinset, (H.filter (fun v => v ∈ e)).card) ≤
        ∑ e ∈ G.edgeFinset, (1 + if e ∈ H.sym2 then 1 else 0) := by
          exact Finset.sum_le_sum fun e he => edge_contrib_on_le H e
    _ = G.edgeFinset.card + (G.edgeFinset ∩ H.sym2).card := by
          rw [Finset.sum_add_distrib]
          rw [show (∑ _e ∈ G.edgeFinset, (1 : ℕ)) = G.edgeFinset.card by simp]
          rw [Finset.sum_boole (R := ℕ)]
          have hf : G.edgeFinset.filter (fun e => e ∈ H.sym2) =
              G.edgeFinset ∩ H.sym2 := by
            ext e
            simp
          rw [hf]
          simp
    _ ≤ G.edgeFinset.card + H.card := by
          apply Nat.add_le_add_left
          let s : Set V := (H : Set V)
          letI : Fintype s := Subtype.fintype (Membership.mem s)
          let T : Finset V := s.toFinset
          have hT : T = H := by
            ext v
            simp [T, s]
          have hi := SimpleGraph.map_edgeFinset_induce (G := G) (s := s)
          have hc := congrArg Finset.card hi
          simp only [Finset.card_map] at hc
          have hb := SimpleGraph.IsAcyclic.card_edgeFinset_le_card
            (G := G.induce s) (hG.induce s)
          have hs : Fintype.card s = T.card := by simp [T]
          calc
            (G.edgeFinset ∩ H.sym2).card =
                (G.edgeFinset ∩ T.sym2).card := by rw [hT]
            _ = (G.induce s).edgeFinset.card := by
              simpa only [T] using hc.symm
            _ ≤ Fintype.card s := hb
            _ = T.card := hs
            _ = H.card := congrArg Finset.card hT

/-- At least half the vertices of a finite forest have degree at most two. -/
theorem SimpleGraph.IsAcyclic.card_le_two_mul_card_degree_le_two
    [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    Fintype.card V ≤
      2 * (Finset.univ.filter (fun v => G.degree v ≤ 2)).card := by
  classical
  let H : Finset V := Finset.univ.filter (fun v => 3 ≤ G.degree v)
  let L : Finset V := Finset.univ.filter (fun v => G.degree v ≤ 2)
  have hthree : 3 * H.card ≤ ∑ v ∈ H, G.degree v := by
    calc
      3 * H.card = ∑ _v ∈ H, 3 := by simp [mul_comm]
      _ ≤ ∑ v ∈ H, G.degree v := by
        exact Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
  have hrestricted :=
    SimpleGraph.IsAcyclic.sum_degrees_on_le_card_edges_add_card (G := G) hG H
  have hedge := SimpleGraph.IsAcyclic.card_edgeFinset_le_card (G := G) hG
  have hhigh : 2 * H.card ≤ Fintype.card V := by omega
  have hpart : L.card + H.card = Fintype.card V := by
    have hp := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (p := fun v => G.degree v ≤ 2)
    simpa only [L, H, Finset.card_univ, Nat.not_le, Nat.lt_iff_add_one_le] using hp
  change Fintype.card V ≤ 2 * L.card
  omega

/-- Restricting the canonical two-coloring of a forest to any finite vertex set
produces an independent subset containing at least half of that set. -/
theorem SimpleGraph.IsAcyclic.exists_indepFinset_subset_two_mul_card
    [DecidableEq V] (hG : G.IsAcyclic) (L : Finset V) :
    ∃ S : Finset V,
      S ⊆ L ∧ G.IsIndepSet (S : Set V) ∧ L.card ≤ 2 * S.card := by
  classical
  let c : G.Coloring (Fin 2) := hG.coloringTwo
  let A : Finset V := L.filter (fun v => c v = 0)
  let B : Finset V := L.filter (fun v => c v ≠ 0)
  have hsplit : A.card + B.card = L.card := by
    simpa [A, B] using
      (Finset.card_filter_add_card_filter_not (s := L) (p := fun v => c v = 0))
  have hAsub : A ⊆ L := Finset.filter_subset _ _
  have hBsub : B ⊆ L := Finset.filter_subset _ _
  have hAindep : G.IsIndepSet (A : Set V) := by
    apply (c.isIndepSet_colorClass 0).mono
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hBindep : G.IsIndepSet (B : Set V) := by
    intro v hv w hw hvw hadj
    have hcv : c v ≠ 0 := (Finset.mem_filter.mp hv).2
    have hcw : c w ≠ 0 := (Finset.mem_filter.mp hw).2
    apply c.valid hadj
    apply Fin.ext
    have hvpos : 0 < (c v).val :=
      Nat.pos_of_ne_zero (fun hzero => hcv (Fin.ext hzero))
    have hwpos : 0 < (c w).val :=
      Nat.pos_of_ne_zero (fun hzero => hcw (Fin.ext hzero))
    omega
  by_cases hAB : B.card ≤ A.card
  · exact ⟨A, hAsub, hAindep, by omega⟩
  · exact ⟨B, hBsub, hBindep, by omega⟩

/-- Once a set containing at least half the vertices is supplied, forest
bipartiteness extracts an independent subset containing at least one quarter
of all vertices.  This is the exact downstream use of the missing low-degree
count; it does not assume the requested localization conclusion. -/
theorem SimpleGraph.IsAcyclic.exists_indepFinset_of_card_le_two_mul
    [DecidableEq V] (hG : G.IsAcyclic) (L : Finset V)
    (hL : Fintype.card V ≤ 2 * L.card) :
    ∃ S : Finset V,
      S ⊆ L ∧ G.IsIndepSet (S : Set V) ∧ Fintype.card V ≤ 4 * S.card := by
  obtain ⟨S, hSL, hS, hcard⟩ :=
    SimpleGraph.IsAcyclic.exists_indepFinset_subset_two_mul_card hG L
  exact ⟨S, hSL, hS, by omega⟩

/-- A finite forest has an independent finset of degree-at-most-two vertices
containing at least one quarter of all vertices. -/
theorem SimpleGraph.IsAcyclic.exists_indepFinset_degree_le_two
    [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) :
    ∃ S : Finset V,
      G.IsIndepSet (S : Set V) ∧
      (∀ v ∈ S, G.degree v ≤ 2) ∧
      Fintype.card V ≤ 4 * S.card := by
  classical
  let L : Finset V := Finset.univ.filter (fun v => G.degree v ≤ 2)
  have hL : Fintype.card V ≤ 2 * L.card := by
    simpa only [L] using
      (SimpleGraph.IsAcyclic.card_le_two_mul_card_degree_le_two (G := G) hG)
  obtain ⟨S, hSL, hSindep, hcard⟩ :=
    SimpleGraph.IsAcyclic.exists_indepFinset_of_card_le_two_mul hG L hL
  refine ⟨S, hSindep, ?_, hcard⟩
  intro v hv
  exact (Finset.mem_filter.mp (hSL hv)).2

/-! ## Low-rank coefficient growth and the first-recovery index bound -/

private def vertexKSets' (k : ℕ) : Finset (Finset V) :=
  Finset.univ.powersetCard k

private def independentVertexKSets' (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact (vertexKSets' (V := V) k).filter (fun s : Finset V => G.IsIndepSet (s : Set V))

private def nonindependentVertexKSets' (G : SimpleGraph V) (k : ℕ) : Finset (Finset V) := by
  classical
  exact (vertexKSets' (V := V) k).filter (fun s : Finset V => ¬G.IsIndepSet (s : Set V))

private theorem coeff_count (G : SimpleGraph V) (k : ℕ) :
    independenceCoeff G k = (independentVertexKSets' G k).card := by
  classical
  rw [independenceCoeff]
  apply Finset.card_bij (fun s _ => s.val)
  · intro s hs
    have hscard := (Finset.mem_filter.mp hs).2
    simp only [independentVertexKSets', Finset.mem_filter]
    refine ⟨?_, s.property⟩
    simp [vertexKSets', Finset.mem_powersetCard, hscard]
  · intro a₁ ha₁ a₂ ha₂ heq
    exact Subtype.ext heq
  · intro s hs
    simp only [independentVertexKSets', vertexKSets', Finset.mem_filter,
      Finset.mem_powersetCard, Finset.subset_univ, true_and] at hs
    let a : IndepFinset G := ⟨s, hs.2⟩
    refine ⟨a, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs.1⟩

private theorem partition_count (G : SimpleGraph V) (k : ℕ) :
    (independentVertexKSets' G k).card +
      (nonindependentVertexKSets' G k).card = (Fintype.card V).choose k := by
  classical
  simpa [independentVertexKSets', nonindependentVertexKSets', vertexKSets'] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ.powersetCard k)
      (fun s : Finset V => G.IsIndepSet (s : Set V)))


private def containingKSets' [DecidableEq V] (k : ℕ) (e : Sym2 V) :
    Finset (Finset V) :=
  (vertexKSets' (V := V) k).filter (fun s => e.toFinset ⊆ s)

private lemma coeff_le_choose (G : SimpleGraph V) (k : ℕ) :
    independenceCoeff G k ≤ (Fintype.card V).choose k := by
  classical
  rw [coeff_count]
  calc
    (independentVertexKSets' G k).card ≤ (vertexKSets' (V := V) k).card :=
      Finset.card_filter_le _ _
    _ = (Fintype.card V).choose k := by simp [vertexKSets']

private lemma card_containingKSets_le
    (G : SimpleGraph V) [DecidableEq V] (k : ℕ) {e : Sym2 V}
    (he : e ∈ G.edgeSet) :
    (containingKSets' (V := V) k e).card ≤ (Fintype.card V).choose (k - 2) := by
  classical
  have hE : e.toFinset.card = 2 := by
    have hnot : ¬ e.IsDiag := by
      simpa only [Set.mem_compl_iff, Sym2.mem_diagSet] using
        G.edgeSet_subset_compl_diagSet he
    simp [Sym2.card_toFinset, hnot]
  calc
    (containingKSets' (V := V) k e).card ≤ (vertexKSets' (V := V) (k - 2)).card := by
      refine Finset.card_le_card_of_injOn
        (s := containingKSets' (V := V) k e) (t := vertexKSets' (V := V) (k - 2))
        (fun s => s \ e.toFinset) ?_ ?_
      · intro s hs
        have hs' : s ∈ vertexKSets' (V := V) k ∧ e.toFinset ⊆ s := by
          rw [containingKSets'] at hs
          exact Finset.mem_filter.mp hs
        rcases hs' with ⟨hsall, hsub⟩
        have hcard : s.card = k := (Finset.mem_powersetCard.mp hsall).2
        apply Finset.mem_powersetCard.mpr
        refine ⟨Finset.subset_univ _, ?_⟩
        rw [Finset.card_sdiff_of_subset hsub, hcard, hE]
      · intro s₁ hs₁ s₂ hs₂ heq
        have hs₁' : s₁ ∈ vertexKSets' (V := V) k ∧ e.toFinset ⊆ s₁ := by
          rw [containingKSets'] at hs₁
          exact Finset.mem_filter.mp hs₁
        have hs₂' : s₂ ∈ vertexKSets' (V := V) k ∧ e.toFinset ⊆ s₂ := by
          rw [containingKSets'] at hs₂
          exact Finset.mem_filter.mp hs₂
        have h₁ := hs₁'.2
        have h₂ := hs₂'.2
        calc
          s₁ = e.toFinset ∪ (s₁ \ e.toFinset) :=
            (Finset.union_sdiff_of_subset h₁).symm
          _ = e.toFinset ∪ (s₂ \ e.toFinset) := by
            simpa only using congrArg (fun t => e.toFinset ∪ t) heq
          _ = s₂ := Finset.union_sdiff_of_subset h₂
    _ = (Fintype.card V).choose (k - 2) := by simp [vertexKSets']

private lemma nonindependentVertexKSets_subset_edgeCover (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj] (k : ℕ) :
    nonindependentVertexKSets' G k ⊆
      G.edgeFinset.biUnion (containingKSets' (V := V) k) := by
  classical
  intro s hs
  have hs' : s ∈ vertexKSets' (V := V) k ∧
      ¬ G.IsIndepSet (s : Set V) := by
    simpa only [nonindependentVertexKSets', Finset.mem_filter] using hs
  rcases hs' with ⟨hsall, hnot⟩
  rw [SimpleGraph.isIndepSet_iff] at hnot
  simp only [Set.Pairwise, Finset.mem_coe, Classical.not_forall,
    Decidable.not_not] at hnot
  rcases hnot with ⟨v, hv, w, hw, hvw, hadj⟩
  have he : s(v,w) ∈ G.edgeFinset := by simpa using hadj
  apply Finset.mem_biUnion.mpr
  refine ⟨s(v,w), he, ?_⟩
  change s ∈ (vertexKSets' (V := V) k).filter
    (fun s => s(v,w).toFinset ⊆ s)
  apply Finset.mem_filter.mpr
  refine ⟨hsall, ?_⟩
  intro x hx
  simp only [Sym2.mem_toFinset, Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact hv
  · exact hw

private lemma nonindependent_count_le (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (k : ℕ) :
    (nonindependentVertexKSets' G k).card ≤
      Fintype.card V * (Fintype.card V).choose (k - 2) := by
  classical
  calc
    (nonindependentVertexKSets' G k).card ≤
        (G.edgeFinset.biUnion (containingKSets' (V := V) k)).card :=
      Finset.card_le_card (nonindependentVertexKSets_subset_edgeCover G k)
    _ ≤ ∑ e ∈ G.edgeFinset, (containingKSets' (V := V) k e).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ G.edgeFinset,
        (Fintype.card V).choose (k - 2) :=
      Finset.sum_le_sum (fun e he =>
        card_containingKSets_le G k (SimpleGraph.mem_edgeFinset.mp he))
    _ = G.edgeFinset.card * (Fintype.card V).choose (k - 2) := by simp
    _ ≤ Fintype.card V * (Fintype.card V).choose (k - 2) :=
      Nat.mul_le_mul_right _
        (SimpleGraph.IsAcyclic.card_edgeFinset_le_card (G := G) hG)

private lemma choose_prev_add_error_lt
    {n k : ℕ} (hk : 2 ≤ k) (hsize : (2 * k)^2 ≤ n) :
    n.choose (k - 1) + n * n.choose (k - 2) < n.choose k := by
  let A := n.choose k
  let B := n.choose (k - 1)
  let C := n.choose (k - 2)
  have hkm2 : k - 2 + 1 = k - 1 := by omega
  have hkm1 : k - 1 + 1 = k := by omega
  have hrecC : B * (k - 1) = C * (n - (k - 2)) := by
    dsimp [B, C]
    simpa only [hkm2] using Nat.choose_succ_right_eq n (k - 2)
  have hrecB : A * k = B * (n - (k - 1)) := by
    dsimp [A, B]
    simpa only [hkm1] using Nat.choose_succ_right_eq n (k - 1)
  have h2kn : 2 * k ≤ n :=
    (Nat.le_pow (a := 2 * k) (b := 2) (by omega)).trans hsize
  have hdouble : n ≤ 2 * (n - (k - 2)) := by omega
  have hratio : (2 * k) * k < n - (k - 1) := by
    rw [Nat.lt_sub_iff_add_lt]
    have hsmall : (2 * k) * k + (k - 1) < (2 * k)^2 := by
      nlinarith
    exact hsmall.trans_le hsize
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.choose_pos (by omega)
  have hbadTerm : n * C ≤ 2 * (k - 1) * B := by
    calc
      n * C ≤ (2 * (n - (k - 2))) * C :=
        Nat.mul_le_mul_right C hdouble
      _ = 2 * (C * (n - (k - 2))) := by ring
      _ = 2 * (B * (k - 1)) := by rw [← hrecC]
      _ = 2 * (k - 1) * B := by ring
  have hsum : B + n * C ≤ (2 * k) * B := by
    calc
      B + n * C ≤ B + 2 * (k - 1) * B := Nat.add_le_add_left hbadTerm B
      _ = (1 + 2 * (k - 1)) * B := by ring
      _ ≤ (2 * k) * B := Nat.mul_le_mul_right B (by omega)
  have hscaled : ((2 * k) * B) * k < A * k := by
    calc
      ((2 * k) * B) * k = B * ((2 * k) * k) := by ring
      _ < B * (n - (k - 1)) := Nat.mul_lt_mul_of_pos_left hratio hBpos
      _ = A * k := hrecB.symm
  have hdom : (2 * k) * B < A := Nat.lt_of_mul_lt_mul_right hscaled
  exact hsum.trans_lt hdom

private lemma isIndepSet_of_card_le_one
    (G : SimpleGraph V) {s : Finset V} (hs : s.card ≤ 1) :
    G.IsIndepSet (s : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro v hv w hw hvw
  exact (hvw (Finset.card_le_one.mp hs v hv w hw)).elim

private lemma independenceCoeff_zero (G : SimpleGraph V) :
    independenceCoeff G 0 = 1 := by
  classical
  rw [coeff_count]
  have hfilter : independentVertexKSets' G 0 = vertexKSets' (V := V) 0 := by
    unfold independentVertexKSets'
    apply Finset.filter_eq_self.2
    intro s hs
    exact isIndepSet_of_card_le_one G (by
      have hcard := (Finset.mem_powersetCard.mp hs).2
      omega)
  rw [hfilter]
  simp [vertexKSets']

private lemma independenceCoeff_one (G : SimpleGraph V) :
    independenceCoeff G 1 = Fintype.card V := by
  classical
  rw [coeff_count]
  have hfilter : independentVertexKSets' G 1 = vertexKSets' (V := V) 1 := by
    unfold independentVertexKSets'
    apply Finset.filter_eq_self.2
    intro s hs
    exact isIndepSet_of_card_le_one G
      ((Finset.mem_powersetCard.mp hs).2.le)
  rw [hfilter]
  simp [vertexKSets']

/-- Forest independence coefficients strictly increase at every positive rank
whose doubled square still fits inside the vertex count.  The proof counts
nonindependent `k`-sets by a containing edge and then applies the two adjacent
binomial recurrences. -/
theorem independenceCoeff_strict_step_of_sq_le_card
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (k : ℕ)
    (hk : 1 ≤ k) (hsize : (2 * k)^2 ≤ Fintype.card V) :
    independenceCoeff G (k - 1) < independenceCoeff G k := by
  classical
  by_cases hk1 : k = 1
  · subst k
    norm_num at hsize
    change independenceCoeff G 0 < independenceCoeff G 1
    rw [independenceCoeff_zero, independenceCoeff_one]
    omega
  have hk2 : 2 ≤ k := by omega
  have hprev := coeff_le_choose (G := G) (k := k - 1)
  have hbad := nonindependent_count_le G hG k
  have harith := choose_prev_add_error_lt
    (n := Fintype.card V) (k := k) hk2 hsize
  have hpart : independenceCoeff G k + (nonindependentVertexKSets' G k).card =
      (Fintype.card V).choose k := by
    calc
      independenceCoeff G k + (nonindependentVertexKSets' G k).card =
          (independentVertexKSets' G k).card +
            (nonindependentVertexKSets' G k).card := by rw [coeff_count]
      _ = (Fintype.card V).choose k := partition_count G k
  have hsum : independenceCoeff G (k - 1) +
      (nonindependentVertexKSets' G k).card < (Fintype.card V).choose k :=
    (Nat.add_le_add hprev hbad).trans_lt harith
  rw [← hpart] at hsum
  exact Nat.lt_of_add_lt_add_right hsum

/-- A canonical first recovery lies strictly beyond the low-rank square
window in natural-number form. -/
theorem CanonicalFirstRecoveryState.order_lt_four_mul_index_sq
    {G : SimpleGraph V} (C : CanonicalFirstRecoveryState G) :
    C.order < (2 * C.index)^2 := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel _
  by_contra hnot
  have hsize : (2 * C.index)^2 ≤ C.order := Nat.le_of_not_gt hnot
  have hgrowth := independenceCoeff_strict_step_of_sq_le_card
    G C.isForest C.index C.firstRecovery.index_pos hsize
  have hprevReal := C.firstRecovery.prev_ge
  have hprevNat : independenceCoeff G C.index ≤
      independenceCoeff G (C.index - 1) := by
    change (independenceCoeff G C.index : ℝ) ≤
      (independenceCoeff G (C.index - 1) : ℝ) at hprevReal
    exact_mod_cast hprevReal
  exact (not_lt_of_ge hprevNat) hgrowth

/-- Every canonical first-recovery index is strictly larger than one half of
the square root of the forest order. -/
theorem CanonicalFirstRecoveryState.sqrt_order_div_two_lt_index
    {G : SimpleGraph V} (C : CanonicalFirstRecoveryState G) :
    Real.sqrt (C.order : ℝ) / 2 < (C.index : ℝ) := by
  have hsqNat := C.order_lt_four_mul_index_sq
  have hsqReal : (C.order : ℝ) < (2 * (C.index : ℝ)) ^ 2 := by
    exact_mod_cast hsqNat
  have hsqrt : Real.sqrt (C.order : ℝ) < 2 * (C.index : ℝ) :=
    (Real.sqrt_lt (Nat.cast_nonneg _) (by positivity)).2 hsqReal
  linarith


/-- Every hard-core vertex marginal is at most `z/(1+z)`. -/
theorem hardCoreLaw_vertex_marginal_le
    [DecidableEq V] (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) (v : V) :
    (∑ s ∈ Finset.univ.filter
        (fun s : IndepFinset G => v ∈ s.val),
      (hardCoreLaw G z hz).probability s) ≤ z / (1 + z) := by
  classical
  let μ := hardCoreLaw G z hz
  let C : Finset (IndepFinset G) :=
    Finset.univ.filter (fun s => v ∈ s.val)
  let A : Finset (IndepFinset G) :=
    Finset.univ.filter (fun s => v ∉ s.val)
  let eraseV : IndepFinset G → IndepFinset G := fun s =>
    ⟨s.val.erase v, s.property.mono (Finset.erase_subset v s.val)⟩
  change (∑ s ∈ C, μ.probability s) ≤ z / (1 + z)
  have himage : C.image eraseV ⊆ A := by
    intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp ht
    simp [A, eraseV]
  have hinj : Set.InjOn eraseV (C : Set (IndepFinset G)) := by
    intro s hs t ht hst
    have hvs : v ∈ s.val := by simpa [C] using hs
    have hvt : v ∈ t.val := by simpa [C] using ht
    have herase := congrArg (fun q : IndepFinset G => q.val) hst
    change s.val.erase v = t.val.erase v at herase
    apply Subtype.ext
    calc
      s.val = insert v (s.val.erase v) := (Finset.insert_erase hvs).symm
      _ = insert v (t.val.erase v) := congrArg (insert v) herase
      _ = t.val := Finset.insert_erase hvt
  have hweight : ∀ s ∈ C,
      μ.probability s = z * μ.probability (eraseV s) := by
    intro s hs
    have hvs : v ∈ s.val := by simpa [C] using hs
    change z ^ s.val.card / independenceEval G z =
      z * (z ^ (s.val.erase v).card / independenceEval G z)
    rw [← Finset.card_erase_add_one hvs, pow_succ]
    ring
  have hraw :
      (∑ s ∈ C, μ.probability s) ≤
        z * ∑ t ∈ A, μ.probability t := by
    calc
      (∑ s ∈ C, μ.probability s) =
          ∑ s ∈ C, z * μ.probability (eraseV s) :=
        Finset.sum_congr rfl hweight
      _ = ∑ t ∈ C.image eraseV, z * μ.probability t := by
        symm
        apply Finset.sum_image
        intro s hs t ht hst
        exact hinj hs ht hst
      _ ≤ ∑ t ∈ A, z * μ.probability t := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro i hiA hiImage
        exact mul_nonneg hz.le (μ.probability_nonneg i)
      _ = z * ∑ t ∈ A, μ.probability t := by
        rw [Finset.mul_sum]
  have hpart :
      (∑ t ∈ A, μ.probability t) +
          (∑ s ∈ C, μ.probability s) = 1 := by
    calc
      _ = ∑ s : IndepFinset G, μ.probability s := by
        simpa only [A, C] using
          (Finset.sum_filter_not_add_sum_filter
            (Finset.univ : Finset (IndepFinset G))
            (fun s : IndepFinset G => v ∈ s.val) μ.probability)
      _ = 1 := μ.probability_sum
  apply (le_div_iff₀ (by linarith : 0 < 1 + z)).2
  nlinarith [hraw, hpart]

/-- The hard-core mean occupation is at most the corresponding product-law
mean. -/
theorem hardCoreLaw_mean_le
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean ≤
      (Fintype.card V : ℝ) * z / (1 + z) := by
  classical
  let μ := hardCoreLaw G z hz
  have hmean :
      μ.mean = ∑ v : V,
        ∑ s ∈ Finset.univ.filter
          (fun s : IndepFinset G => v ∈ s.val), μ.probability s := by
    unfold FiniteLatticeLaw.mean
    change (∑ s : IndepFinset G,
      μ.probability s * (s.val.card : ℝ)) = _
    calc
      _ = ∑ s : IndepFinset G, μ.probability s *
            ∑ v : V, if v ∈ s.val then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        apply congrArg (fun x : ℝ => μ.probability s * x)
        symm
        simpa using
          (Finset.sum_boole (R := ℝ)
            (fun v : V => v ∈ s.val) (Finset.univ : Finset V))
      _ = ∑ s : IndepFinset G, ∑ v : V,
            if v ∈ s.val then μ.probability s else 0 := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        by_cases h : v ∈ s.val <;> simp [h]
      _ = ∑ v : V, ∑ s : IndepFinset G,
            if v ∈ s.val then μ.probability s else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ v : V,
            ∑ s ∈ Finset.univ.filter
              (fun s : IndepFinset G => v ∈ s.val), μ.probability s := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [Finset.sum_filter]
  calc
    μ.mean = _ := hmean
    _ ≤ ∑ _v : V, z / (1 + z) :=
      Finset.sum_le_sum (fun v _ => hardCoreLaw_vertex_marginal_le G z hz v)
    _ = (Fintype.card V : ℝ) * z / (1 + z) := by
      simp [div_eq_mul_inv, mul_assoc]

/-- The canonical activity is strictly above the reciprocal square-root
scale. -/
theorem CanonicalFirstRecoveryState.one_div_two_sqrt_order_lt_activity
    {G : SimpleGraph V} (C : CanonicalFirstRecoveryState G) :
    1 / (2 * Real.sqrt (C.order : ℝ)) < C.activity := by
  classical
  have hmean := hardCoreLaw_mean_le G C.activity C.activity_pos
  rw [C.mean_eq_index] at hmean
  have hindex_pos : 0 < (C.index : ℝ) := by
    exact_mod_cast C.firstRecovery.index_pos
  have hprod_pos :
      0 < (C.order : ℝ) * C.activity / (1 + C.activity) :=
    lt_of_lt_of_le hindex_pos hmean
  have hden_pos : 0 < 1 + C.activity := by linarith [C.activity_pos]
  have hnz_pos : 0 < (C.order : ℝ) * C.activity := by
    rcases (div_pos_iff.mp hprod_pos) with h | h
    · exact h.1
    · nlinarith [hden_pos, h.2]
  have hn_pos : 0 < (C.order : ℝ) := by
    nlinarith [C.activity_pos]
  have hsqrt_pos : 0 < Real.sqrt (C.order : ℝ) := Real.sqrt_pos.2 hn_pos
  have hsqrt_sq : Real.sqrt (C.order : ℝ) ^ 2 = (C.order : ℝ) :=
    Real.sq_sqrt hn_pos.le
  have hfrac_le :
      (C.order : ℝ) * C.activity / (1 + C.activity) ≤
        (C.order : ℝ) * C.activity := by
    apply (div_le_iff₀ hden_pos).2
    nlinarith [mul_nonneg hn_pos.le C.activity_pos.le]
  have hmain :
      Real.sqrt (C.order : ℝ) / 2 <
        (C.order : ℝ) * C.activity :=
    lt_of_lt_of_le C.sqrt_order_div_two_lt_index (hmean.trans hfrac_le)
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hsqrt_pos)).2
  nlinarith [hsqrt_sq]


/-! ## Exact hard-core variance localization -/

lemma weightedPowerset {V : Type u} [DecidableEq V]
    (A : Finset V) (z : ℝ) :
    (∑ t ∈ A.powerset, z ^ t.card) = (1 + z) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hsecond :
          (∑ t ∈ A.powerset, z ^ (insert a t).card) =
            z * ∑ t ∈ A.powerset, z ^ t.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [Finset.card_insert_of_notMem hat, pow_succ]
        ring
      rw [hsecond, ih, Finset.card_insert_of_notMem ha, pow_succ]
      ring

lemma weightedPowersetSq {V : Type u} [DecidableEq V]
    (A : Finset V) (z x : ℝ) (hz1 : 1 + z ≠ 0) :
    (∑ t ∈ A.powerset,
      z ^ t.card * (x + (t.card : ℝ)) ^ 2) =
      (1 + z) ^ A.card *
        ((x + (A.card : ℝ) * z / (1 + z)) ^ 2 +
          (A.card : ℝ) * z / (1 + z) ^ 2) := by
  induction A using Finset.induction_on generalizing x with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hsecond :
          (∑ t ∈ A.powerset,
            z ^ (insert a t).card *
              (x + ((insert a t).card : ℝ)) ^ 2) =
          z * ∑ t ∈ A.powerset,
            z ^ t.card * ((x + 1) + (t.card : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [Finset.card_insert_of_notMem hat, pow_succ]
        push_cast
        ring
      rw [hsecond, ih x, ih (x + 1),
          Finset.card_insert_of_notMem ha, pow_succ]
      push_cast
      field_simp [hz1]
      ring

lemma weightedPowersetSq_lower {V : Type u} [DecidableEq V]
    (A : Finset V) (z x : ℝ) (hz : 0 < z) :
    (1 + z) ^ A.card * ((A.card : ℝ) * z / (1 + z)^2) ≤
      ∑ t ∈ A.powerset, z ^ t.card * (x + (t.card : ℝ))^2 := by
  rw [weightedPowersetSq A z x (by linarith)]
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left (sq_nonneg _))
    (pow_nonneg (by linarith) _)

def OutsideConfig {V : Type u} [Fintype V]
    (G : SimpleGraph V) (S : Finset V) :=
  {b : Finset V // Disjoint b S ∧ G.IsIndepSet (b : Set V)}

def outsidePart {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (I : IndepFinset G) :
    OutsideConfig G S :=
  ⟨I.val \ S,
    Finset.disjoint_left.mpr (by
      intro x hx hS
      exact (Finset.mem_sdiff.mp hx).2 hS),
    I.property.mono (by
      intro x hx
      exact (Finset.mem_sdiff.mp hx).1)⟩

def freeInside {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (b : OutsideConfig G S) : Finset V :=
  S.filter fun v => Disjoint b.val (G.neighborFinset v)

def Fiber {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (b : OutsideConfig G S) :=
  {I : IndepFinset G // outsidePart G S I = b}

def PowerConfig {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (b : OutsideConfig G S) :=
  {t : Finset V // t ⊆ freeInside G S b}

def fiberEquivPowerset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (b : OutsideConfig G S) :
    Fiber G S b ≃ PowerConfig G S b where
  toFun I := ⟨I.val.val ∩ S, by
    intro v hv
    have hvI : v ∈ I.val.val := (Finset.mem_inter.mp hv).1
    have hvS : v ∈ S := (Finset.mem_inter.mp hv).2
    rw [freeInside, Finset.mem_filter]
    refine ⟨hvS, Finset.disjoint_left.mpr ?_⟩
    intro w hwb hwn
    have hwout : w ∈ I.val.val \ S := by
      change w ∈ (outsidePart G S I.val).val
      rw [I.property]
      exact hwb
    have hwI : w ∈ I.val.val := (Finset.mem_sdiff.mp hwout).1
    have hadj : G.Adj v w := by simpa using hwn
    have hvw : v ≠ w := hadj.ne
    exact I.val.property hvI hwI hvw hadj⟩
  invFun t := ⟨⟨b.val ∪ t.val, by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_union] at hx hy
    rcases hx with hxb | hxt <;> rcases hy with hyb | hyt
    · exact b.property.2 hxb hyb hxy
    · have hyS : y ∈ S := by
        exact (Finset.mem_filter.mp (t.property hyt)).1
      have hfree := (Finset.mem_filter.mp (t.property hyt)).2
      intro hadj
      exact (Finset.disjoint_left.mp hfree) hxb (by simpa using G.symm hadj)
    · have hxS : x ∈ S := by
        exact (Finset.mem_filter.mp (t.property hxt)).1
      have hfree := (Finset.mem_filter.mp (t.property hxt)).2
      intro hadj
      exact (Finset.disjoint_left.mp hfree) hyb (by simpa using hadj)
    · exact hS (by
        exact (Finset.mem_filter.mp (t.property hxt)).1)
        (by exact (Finset.mem_filter.mp (t.property hyt)).1) hxy⟩,
    by
      apply Subtype.ext
      ext x
      constructor
      · intro hx
        have hxu := Finset.mem_sdiff.mp hx
        rcases Finset.mem_union.mp hxu.1 with hxb | hxt
        · exact hxb
        · exact False.elim (hxu.2 ((Finset.mem_filter.mp (t.property hxt)).1))
      · intro hxb
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_union_left _ hxb, ?_⟩
        exact fun hxS => (Finset.disjoint_left.mp b.property.1) hxb hxS⟩
  left_inv I := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have hb : b.val = I.val.val \ S :=
      congrArg Subtype.val I.property.symm
    rw [hb]
    exact Finset.sdiff_union_inter I.val.val S
  right_inv t := by
    apply Subtype.ext
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxb | hxt, hxS⟩
      · exact False.elim ((Finset.disjoint_left.mp b.property.1) hxb hxS)
      · exact hxt
    · intro hxt
      exact ⟨Or.inr hxt, (Finset.mem_filter.mp (t.property hxt)).1⟩

noncomputable def fiberFinset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (b : OutsideConfig G S) :
    Finset (IndepFinset G) := by
  classical
  exact Finset.univ.filter (fun I => outsidePart G S I = b)

def hardCoreAvoidWeight {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (T : Finset V) : ℝ :=
  ∑ I : IndepFinset G, if Disjoint I.val T then z ^ I.val.card else 0

/-- Exact first missing fiber identity in the conditional-variance proof.
The RHS is the unnormalized second-moment numerator restricted to one outside
fiber; the LHS is that fiber's product-Bernoulli conditional variance. -/
theorem fiber_weighted_sq_lower {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (b : OutsideConfig G S) (z μ : ℝ) (hz : 0 < z) :
    z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
        ((freeInside G S b).card * z / (1 + z)^2) ≤
      ∑ I ∈ fiberFinset G S b,
        z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 := by
  classical
  let F := freeInside G S b
  have hsum :
      (∑ I ∈ fiberFinset G S b,
        z ^ I.val.card * ((I.val.card : ℝ) - μ)^2) =
      ∑ t ∈ F.powerset,
        z ^ b.val.card *
          (z ^ t.card * (((b.val.card : ℝ) - μ) + (t.card : ℝ))^2) := by
    apply Finset.sum_bij (fun I hI => I.val ∩ S)
    · intro I hI
      have hIb : outsidePart G S I = b := by
        simpa [fiberFinset] using hI
      let Ifib : Fiber G S b := ⟨I, hIb⟩
      exact Finset.mem_powerset.mpr
        ((fiberEquivPowerset G S hS b Ifib).property)
    · intro I₁ hI₁ I₂ hI₂ heq
      have hb₁ : outsidePart G S I₁ = b := by
        simpa [fiberFinset] using hI₁
      have hb₂ : outsidePart G S I₂ = b := by
        simpa [fiberFinset] using hI₂
      apply Subtype.ext
      have hout : I₁.val \ S = I₂.val \ S := by
        have := congrArg Subtype.val (hb₁.trans hb₂.symm)
        exact this
      calc
        I₁.val = (I₁.val \ S) ∪ (I₁.val ∩ S) :=
          (Finset.sdiff_union_inter I₁.val S).symm
        _ = (I₂.val \ S) ∪ (I₂.val ∩ S) := by rw [hout, heq]
        _ = I₂.val := Finset.sdiff_union_inter I₂.val S
    · intro t ht
      let T : PowerConfig G S b := ⟨t, Finset.mem_powerset.mp ht⟩
      let I : IndepFinset G := ((fiberEquivPowerset G S hS b).symm T).val
      refine ⟨I, ?_, ?_⟩
      · show I ∈ fiberFinset G S b
        simp [I, fiberFinset]
        exact ((fiberEquivPowerset G S hS b).symm T).property
      · have hr := (fiberEquivPowerset G S hS b).right_inv T
        exact congrArg Subtype.val hr
    · intro I hI
      have hIb : outsidePart G S I = b := by
        simpa [fiberFinset] using hI
      have hout : I.val \ S = b.val := congrArg Subtype.val hIb
      have hdisj : Disjoint b.val (I.val ∩ S) := by
        apply Finset.disjoint_left.mpr
        intro x hxb hx
        exact (Finset.disjoint_left.mp b.property.1) hxb
          (Finset.mem_inter.mp hx).2
      have hval : I.val = b.val ∪ (I.val ∩ S) := by
        calc
          I.val = (I.val \ S) ∪ (I.val ∩ S) :=
            (Finset.sdiff_union_inter I.val S).symm
          _ = _ := by rw [hout]
      have hcard : I.val.card = b.val.card + (I.val ∩ S).card := by
        calc
          I.val.card = ((I.val \ S) ∪ (I.val ∩ S)).card := by
            rw [Finset.sdiff_union_inter]
          _ = (I.val \ S).card + (I.val ∩ S).card := by
            rw [Finset.card_union_of_disjoint]
            exact Finset.disjoint_left.mpr (by
              intro x hx₁ hx₂
              exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hx₂).2)
          _ = _ := by rw [hout]
      calc
        z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 =
            z ^ (b.val.card + (I.val ∩ S).card) *
              (((b.val.card : ℝ) + ((I.val ∩ S).card : ℝ)) - μ)^2 := by
          rw [hcard]
          push_cast
          rfl
        _ = z ^ b.val.card *
              (z ^ (I.val ∩ S).card *
                (((b.val.card : ℝ) - μ) + ((I.val ∩ S).card : ℝ))^2) := by
          rw [pow_add]
          ring
  rw [hsum, ← Finset.mul_sum]
  simpa only [F, mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (weightedPowersetSq_lower F z ((b.val.card : ℝ) - μ) hz)
      (pow_nonneg hz.le b.val.card))

noncomputable local instance outsideConfigFintype {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    Fintype (OutsideConfig G S) := by
  classical
  let B : Finset (Finset V) :=
    (Finset.univ : Finset V).powerset.filter
      (fun b => Disjoint b S ∧ G.IsIndepSet (b : Set V))
  let e : {b // b ∈ B} ↪ OutsideConfig G S :=
    ⟨fun b => ⟨b.val, (Finset.mem_filter.mp b.property).2⟩,
      by
        intro a b h
        have hv : a.val = b.val :=
          congrArg (fun q : OutsideConfig G S => q.val) h
        exact Subtype.ext hv⟩
  refine ⟨B.attach.map e, ?_⟩
  intro b
  apply Finset.mem_map.mpr
  let a : {q // q ∈ B} := ⟨b.val, by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), b.property⟩⟩
  exact ⟨a, Finset.mem_attach _ _, by rfl⟩

lemma fiber_weight_sum {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (b : OutsideConfig G S) (z : ℝ) :
    (∑ I ∈ fiberFinset G S b, z ^ I.val.card) =
      z ^ b.val.card * (1 + z) ^ (freeInside G S b).card := by
  classical
  let F := freeInside G S b
  calc
    _ = ∑ t ∈ F.powerset, z ^ b.val.card * z ^ t.card := by
      apply Finset.sum_bij (fun I hI => I.val ∩ S)
      · intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        let Ifib : Fiber G S b := ⟨I, hIb⟩
        exact Finset.mem_powerset.mpr ((fiberEquivPowerset G S hS b Ifib).property)
      · intro I₁ hI₁ I₂ hI₂ heq
        have hb₁ : outsidePart G S I₁ = b := by simpa [fiberFinset] using hI₁
        have hb₂ : outsidePart G S I₂ = b := by simpa [fiberFinset] using hI₂
        apply Subtype.ext
        have hout : I₁.val \ S = I₂.val \ S :=
          congrArg Subtype.val (hb₁.trans hb₂.symm)
        calc
          I₁.val = (I₁.val \ S) ∪ (I₁.val ∩ S) :=
            (Finset.sdiff_union_inter I₁.val S).symm
          _ = (I₂.val \ S) ∪ (I₂.val ∩ S) := by rw [hout, heq]
          _ = I₂.val := Finset.sdiff_union_inter I₂.val S
      · intro t ht
        let T : PowerConfig G S b := ⟨t, Finset.mem_powerset.mp ht⟩
        let I : IndepFinset G := ((fiberEquivPowerset G S hS b).symm T).val
        refine ⟨I, ?_, ?_⟩
        · show I ∈ fiberFinset G S b
          simp [I, fiberFinset]
          exact ((fiberEquivPowerset G S hS b).symm T).property
        · exact congrArg Subtype.val ((fiberEquivPowerset G S hS b).right_inv T)
      · intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        have hout : I.val \ S = b.val := congrArg Subtype.val hIb
        have hcard : I.val.card = b.val.card + (I.val ∩ S).card := by
          calc
            I.val.card = ((I.val \ S) ∪ (I.val ∩ S)).card := by
              rw [Finset.sdiff_union_inter]
            _ = (I.val \ S).card + (I.val ∩ S).card := by
              rw [Finset.card_union_of_disjoint]
              exact Finset.disjoint_left.mpr (by
                intro x hx₁ hx₂
                exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hx₂).2)
            _ = _ := by rw [hout]
        rw [hcard, pow_add]
    _ = z ^ b.val.card * (1 + z) ^ F.card := by
      rw [← Finset.mul_sum, weightedPowerset]
    _ = _ := rfl

lemma sum_fiberFinset {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (f : IndepFinset G → ℝ) :
    (∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b, f I) =
      ∑ I : IndepFinset G, f I := by
  classical
  simp only [fiberFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

lemma fiber_free_iff_avoid {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (v : V) (hvS : v ∈ S) (b : OutsideConfig G S)
    (I : IndepFinset G) (hIb : outsidePart G S I = b) :
    v ∈ freeInside G S b ↔ Disjoint I.val (G.neighborFinset v) := by
  classical
  have hout : I.val \ S = b.val := congrArg Subtype.val hIb
  constructor
  · intro hvfree
    have hbdisj := (Finset.mem_filter.mp hvfree).2
    apply Finset.disjoint_left.mpr
    intro x hxI hxN
    by_cases hxS : x ∈ S
    · have hvx : v ≠ x := by
        intro h
        subst x
        exact G.notMem_neighborFinset_self v hxN
      exact (hS hvS hxS hvx) (by simpa using hxN)
    · have hxb : x ∈ b.val := by
        rw [← hout]
        exact Finset.mem_sdiff.mpr ⟨hxI, hxS⟩
      exact (Finset.disjoint_left.mp hbdisj) hxb hxN
  · intro havoid
    apply Finset.mem_filter.mpr
    refine ⟨hvS, Finset.disjoint_left.mpr ?_⟩
    intro x hxb hxN
    apply (Finset.disjoint_left.mp havoid) ?_ hxN
    have : x ∈ I.val \ S := by rw [hout]; exact hxb
    exact (Finset.mem_sdiff.mp this).1

lemma outsideFreeWeightSum_eq_avoid {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (v : V) (hvS : v ∈ S) (z : ℝ) :
    (∑ b : OutsideConfig G S,
      if v ∈ freeInside G S b then
        z ^ b.val.card * (1 + z) ^ (freeInside G S b).card else 0) =
      hardCoreAvoidWeight G z (G.neighborFinset v) := by
  classical
  rw [hardCoreAvoidWeight]
  calc
    _ = ∑ b : OutsideConfig G S,
        if v ∈ freeInside G S b then
          ∑ I ∈ fiberFinset G S b, z ^ I.val.card else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : v ∈ freeInside G S b
      · simp only [h, if_true]
        exact (fiber_weight_sum G S hS b z).symm
      · simp [h]
    _ = ∑ b : OutsideConfig G S,
        ∑ I ∈ fiberFinset G S b,
          if Disjoint I.val (G.neighborFinset v) then z ^ I.val.card else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases h : v ∈ freeInside G S b
      · simp only [h, if_true]
        apply Finset.sum_congr rfl
        intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        have hd : Disjoint I.val (G.neighborFinset v) :=
          (fiber_free_iff_avoid G S hS v hvS b I hIb).mp h
        simp [hd]
      · simp only [h, if_false]
        symm
        apply Finset.sum_eq_zero
        intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        have hn : ¬ Disjoint I.val (G.neighborFinset v) := by
          intro hd
          exact h ((fiber_free_iff_avoid G S hS v hvS b I hIb).mpr hd)
        simp [hn]
    _ = _ := sum_fiberFinset G S _

lemma sum_fiberVariance_eq_sum_avoid {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (z : ℝ) :
    (∑ b : OutsideConfig G S,
      z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
        ((freeInside G S b).card * z / (1 + z)^2)) =
      z / (1 + z)^2 *
        ∑ v ∈ S, hardCoreAvoidWeight G z (G.neighborFinset v) := by
  classical
  calc
    _ = ∑ b : OutsideConfig G S, ∑ v ∈ S,
        if v ∈ freeInside G S b then
          z / (1 + z)^2 *
            (z ^ b.val.card * (1 + z) ^ (freeInside G S b).card)
        else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      have hc : ((freeInside G S b).card : ℝ) =
          ∑ v ∈ S, if v ∈ freeInside G S b then (1 : ℝ) else 0 := by
        simp [freeInside]
        congr 1
        ext x
        simp
      calc
        _ = (∑ v ∈ S, if v ∈ freeInside G S b then (1 : ℝ) else 0) *
            (z / (1 + z)^2 *
              (z ^ b.val.card * (1 + z) ^ (freeInside G S b).card)) := by
          rw [← hc]
          ring
        _ = ∑ v ∈ S,
            (if v ∈ freeInside G S b then (1 : ℝ) else 0) *
              (z / (1 + z)^2 *
                (z ^ b.val.card * (1 + z) ^ (freeInside G S b).card)) := by
          rw [Finset.sum_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v hv
          by_cases h : v ∈ freeInside G S b <;> simp [h]
    _ = ∑ v ∈ S, ∑ b : OutsideConfig G S,
        if v ∈ freeInside G S b then
          z / (1 + z)^2 *
            (z ^ b.val.card * (1 + z) ^ (freeInside G S b).card)
        else 0 := by rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      calc
        (∑ b : OutsideConfig G S,
          if v ∈ freeInside G S b then
            z / (1 + z)^2 *
              (z ^ b.val.card * (1 + z) ^ (freeInside G S b).card)
          else 0) =
            z / (1 + z)^2 *
              ∑ b : OutsideConfig G S,
                if v ∈ freeInside G S b then
                  z ^ b.val.card * (1 + z) ^ (freeInside G S b).card
                else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b hb
          by_cases h : v ∈ freeInside G S b <;> simp [h]
        _ = _ := by rw [outsideFreeWeightSum_eq_avoid G S hS v hv z]

theorem independenceEval_le_mul_hardCoreAvoidWeight {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (T : Finset V) :
    independenceEval G z ≤
      (1 + z) ^ T.card * hardCoreAvoidWeight G z T := by
  classical
  let eraseT : IndepFinset G → IndepFinset G := fun I =>
    ⟨I.val \ T, I.property.mono (Finset.sdiff_subset)⟩
  let enc : IndepFinset G ↪ (IndepFinset G × Finset V) :=
    ⟨fun I => (eraseT I, I.val ∩ T), by
      intro I J h
      apply Subtype.ext
      have hbase : I.val \ T = J.val \ T := by
        have := congrArg (fun p : IndepFinset G × Finset V => p.1) h
        exact congrArg Subtype.val this
      have hins : I.val ∩ T = J.val ∩ T :=
        congrArg (fun p : IndepFinset G × Finset V => p.2) h
      calc
        I.val = (I.val \ T) ∪ (I.val ∩ T) :=
          (Finset.sdiff_union_inter I.val T).symm
        _ = (J.val \ T) ∪ (J.val ∩ T) := by rw [hbase, hins]
        _ = J.val := Finset.sdiff_union_inter J.val T⟩
  let A : Finset (IndepFinset G) :=
    Finset.univ.filter (fun J => Disjoint J.val T)
  let P : Finset (Finset V) := T.powerset
  have himage : (Finset.univ.image enc) ⊆ A.product P := by
    intro p hp
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hp
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, Finset.disjoint_left.mpr ?_⟩
      intro x hx hT
      exact (Finset.mem_sdiff.mp hx).2 hT
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
  have hweight : ∀ I : IndepFinset G,
      z ^ I.val.card = z ^ (eraseT I).val.card * z ^ (I.val ∩ T).card := by
    intro I
    have hc : I.val.card = (I.val \ T).card + (I.val ∩ T).card := by
      calc
        I.val.card = ((I.val \ T) ∪ (I.val ∩ T)).card := by
          rw [Finset.sdiff_union_inter]
        _ = _ := by
          rw [Finset.card_union_of_disjoint]
          exact Finset.disjoint_left.mpr (by
            intro x hx₁ hx₂
            exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hx₂).2)
    rw [hc, pow_add]
  calc
    independenceEval G z = ∑ I : IndepFinset G, z ^ I.val.card :=
      independenceEval_eq_sum G z
    _ = ∑ p ∈ Finset.univ.image enc,
        z ^ p.1.val.card * z ^ p.2.card := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro I hI
        exact hweight I
      · intro I hI J hJ h
        exact enc.injective h
    _ ≤ ∑ p ∈ A.product P, z ^ p.1.val.card * z ^ p.2.card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro p hpA hpim
      exact mul_nonneg (pow_nonneg hz.le _) (pow_nonneg hz.le _)
    _ = ∑ J ∈ A, ∑ t ∈ P, z ^ J.val.card * z ^ t.card := by
      exact Finset.sum_product A P
        (fun p : IndepFinset G × Finset V =>
          z ^ p.1.val.card * z ^ p.2.card)
    _ = (∑ J ∈ A, z ^ J.val.card) * (∑ t ∈ P, z ^ t.card) := by
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_mul]
    _ = hardCoreAvoidWeight G z T * (1 + z) ^ T.card := by
      congr 1
      · exact Finset.sum_filter
          (fun J : IndepFinset G => Disjoint J.val T)
          (fun J : IndepFinset G => z ^ J.val.card)
      · exact weightedPowerset T z
    _ = (1 + z) ^ T.card * hardCoreAvoidWeight G z T := mul_comm _ _

lemma hardCoreAvoidWeight_nonneg {V : Type u} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (T : Finset V) : 0 ≤ hardCoreAvoidWeight G z T := by
  unfold hardCoreAvoidWeight
  apply Finset.sum_nonneg
  intro I hI
  split <;> positivity

lemma independenceEval_div_sq_le_avoid_of_card_le_two
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z)
    (T : Finset V) (hT : T.card ≤ 2) :
    independenceEval G z / (1 + z)^2 ≤ hardCoreAvoidWeight G z T := by
  have hA := hardCoreAvoidWeight_nonneg G z hz T
  have hE := independenceEval_le_mul_hardCoreAvoidWeight G z hz T
  have hp : (1 + z) ^ T.card ≤ (1 + z)^2 := by
    rcases (show T.card = 0 ∨ T.card = 1 ∨ T.card = 2 by omega) with h | h | h
    · rw [h, pow_zero]
      nlinarith [sq_nonneg z]
    · rw [h, pow_one]
      nlinarith [sq_nonneg z]
    · rw [h]
  have hE' : independenceEval G z ≤
      (1 + z)^2 * hardCoreAvoidWeight G z T :=
    le_trans hE (mul_le_mul_of_nonneg_right hp hA)
  have hE'' : independenceEval G z ≤
      hardCoreAvoidWeight G z T * (1 + z)^2 := by
    simpa [mul_comm] using hE'
  exact (div_le_iff₀ (by positivity : 0 < (1 + z)^2)).2 hE''

theorem SimpleGraph.IsAcyclic.hardCoreLaw_variance_ge
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (z : ℝ) (hz : 0 < z) :
    (Fintype.card V : ℝ) * z / (4 * (1 + z)^4) ≤
      (hardCoreLaw G z hz).variance := by
  classical
  obtain ⟨S, hS, hdeg, hcard⟩ :=
    SimpleGraph.IsAcyclic.exists_indepFinset_degree_le_two (G := G) hG
  let E := independenceEval G z
  let μ := (hardCoreLaw G z hz).mean
  have hE : 0 < E := independenceEval_pos G hz
  have hav : (S.card : ℝ) * (E / (1 + z)^2) ≤
      ∑ v ∈ S, hardCoreAvoidWeight G z (G.neighborFinset v) := by
    calc
      _ = ∑ v ∈ S, E / (1 + z)^2 := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v hv =>
        independenceEval_div_sq_le_avoid_of_card_le_two
          G z hz (G.neighborFinset v) (by simpa using hdeg v hv))
  have hfac : 0 ≤ z / (1 + z)^2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hav hfac
  have hglobal :
      (∑ b : OutsideConfig G S,
        z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
          ((freeInside G S b).card * z / (1 + z)^2)) ≤
        ∑ I : IndepFinset G,
          z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 := by
    calc
      _ ≤ ∑ b : OutsideConfig G S,
          ∑ I ∈ fiberFinset G S b,
            z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 :=
        Finset.sum_le_sum (fun b _ => fiber_weighted_sq_lower G S hS b z μ hz)
      _ = _ := sum_fiberFinset G S _
  have hnum :
      (S.card : ℝ) * E * z / (1 + z)^4 ≤
        ∑ I : IndepFinset G, z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 := by
    calc
      _ = z / (1 + z)^2 * ((S.card : ℝ) * (E / (1 + z)^2)) := by
        field_simp <;> ring
      _ ≤ z / (1 + z)^2 *
          ∑ v ∈ S, hardCoreAvoidWeight G z (G.neighborFinset v) := hmul
      _ = ∑ b : OutsideConfig G S,
          z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
            ((freeInside G S b).card * z / (1 + z)^2) :=
        (sum_fiberVariance_eq_sum_avoid G S hS z).symm
      _ ≤ _ := hglobal
  have hcardR : (Fintype.card V : ℝ) ≤ 4 * (S.card : ℝ) := by
    exact_mod_cast hcard
  have htarget :
      (Fintype.card V : ℝ) * E * z / (4 * (1 + z)^4) ≤
        ∑ I : IndepFinset G, z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 := by
    have hscale : 0 ≤ E * z / (4 * (1 + z)^4) := by positivity
    have := mul_le_mul_of_nonneg_right hcardR hscale
    calc
      _ = (Fintype.card V : ℝ) * (E * z / (4 * (1 + z)^4)) := by ring
      _ ≤ (4 * (S.card : ℝ)) * (E * z / (4 * (1 + z)^4)) := this
      _ = (S.card : ℝ) * E * z / (1 + z)^4 := by field_simp <;> ring
      _ ≤ _ := hnum
  unfold FiniteLatticeLaw.variance
  change (Fintype.card V : ℝ) * z / (4 * (1 + z)^4) ≤
    ∑ I : IndepFinset G,
      (z ^ I.val.card / E) * ((I.val.card : ℝ) - μ)^2
  have hsum :
      (∑ I : IndepFinset G,
        (z ^ I.val.card / E) * ((I.val.card : ℝ) - μ)^2) =
      (∑ I : IndepFinset G,
        z ^ I.val.card * ((I.val.card : ℝ) - μ)^2) / E := by
    calc
      _ = ∑ I : IndepFinset G,
          (z ^ I.val.card * ((I.val.card : ℝ) - μ)^2) / E := by
        apply Finset.sum_congr rfl
        intro I hI
        field_simp <;> ring
      _ = _ := (Finset.sum_div _ _ _).symm
  rw [hsum]
  apply (le_div_iff₀ hE).2
  convert htarget using 1 <;> ring

theorem CanonicalFirstRecoveryState.indexVarianceSizeLocalized
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (Z : ℝ)
    (hCZ : C.activity ≤ Z) : IndexVarianceSizeLocalized C Z := by
  classical
  constructor
  · exact C.sqrt_order_div_two_lt_index
  · let n : ℝ := C.order
    let s : ℝ := Real.sqrt n
    let z : ℝ := C.activity
    have hz : 0 < z := C.activity_pos
    have hZ : 0 < Z := lt_of_lt_of_le hz hCZ
    have hm := hardCoreLaw_mean_le G C.activity C.activity_pos
    rw [C.mean_eq_index] at hm
    have hi : 0 < (C.index : ℝ) := by exact_mod_cast C.firstRecovery.index_pos
    have hprod : 0 < n * z / (1 + z) := by
      exact lt_of_lt_of_le hi hm
    have hn : 0 < n := by
      have hden : 0 < 1 + z := by linarith
      rcases (div_pos_iff.mp hprod) with h | h
      · nlinarith [h.1, hz]
      · nlinarith [hden, h.2]
    have hs : 0 < s := Real.sqrt_pos.2 hn
    have hs2 : s ^ 2 = n := Real.sq_sqrt hn.le
    have ha := C.one_div_two_sqrt_order_lt_activity
    change 1 / (2 * s) < z at ha
    have ha' : 1 < z * (2 * s) :=
      (div_lt_iff₀ (by positivity : 0 < 2 * s)).mp ha
    have hamul := mul_lt_mul_of_pos_left ha' hs
    have hscale : s / 8 < n * z / 4 := by
      nlinarith [hs2, hamul]
    have hpow : (1 + z)^4 ≤ (1 + Z)^4 := by
      have : 1 + z ≤ 1 + Z := by linarith
      gcongr
    have hleft : s / (8 * (1 + Z)^4) ≤ s / (8 * (1 + z)^4) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 8 * (1 + Z)^4)
        (by positivity : 0 < 8 * (1 + z)^4)).2
      gcongr
    have hmid : s / (8 * (1 + z)^4) ≤
        n * z / (4 * (1 + z)^4) := by
      have hd : 0 < (1 + z)^4 := by positivity
      have hh := div_lt_div_of_pos_right hscale hd
      simpa only [div_div] using hh.le
    have hv := SimpleGraph.IsAcyclic.hardCoreLaw_variance_ge
      (G := G) C.isForest C.activity C.activity_pos
    change n * z / (4 * (1 + z)^4) ≤ C.variance at hv
    exact hleft.trans (hmid.trans hv)

/-- The Proposition 2.1 theorem in the exact shape of the localization interface. -/
theorem index_variance_size :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V},
      (C : CanonicalFirstRecoveryState G) → ∀ Z : ℝ,
        C.activity ≤ Z → IndexVarianceSizeLocalized C Z := by
  intro V _ G C Z hCZ
  exact C.indexVarianceSizeLocalized Z hCZ

lemma sum_fiber_weighted_sq_lower {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (z μ : ℝ) (hz : 0 < z) :
    (∑ b : OutsideConfig G S,
      z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
        ((freeInside G S b).card * z / (1 + z)^2)) ≤
      ∑ I : IndepFinset G,
        z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 := by
  calc
    _ ≤ ∑ b : OutsideConfig G S,
        ∑ I ∈ fiberFinset G S b,
          z ^ I.val.card * ((I.val.card : ℝ) - μ)^2 :=
      Finset.sum_le_sum (fun b _ => fiber_weighted_sq_lower G S hS b z μ hz)
    _ = _ := sum_fiberFinset G S _
end
end Forest
end Erdos993
