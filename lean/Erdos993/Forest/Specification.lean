import Erdos993.Evaluation
import Erdos993.TiltedTuran

/-!
# Phase 0 vocabulary for eventual forest unimodality

This file contains only finite definitions and elementary proved facts.  In
particular, the analytic inputs from the manuscript appendices do not occur
here as theorems.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

/-! ## Finite coefficient sequences -/

/-- A nonnegative real sequence with a specified finite support bound. -/
structure FiniteNonnegativeSequence where
  coeff : ℕ → ℝ
  cutoff : ℕ
  coeff_nonneg : ∀ k, 0 ≤ coeff k
  coeff_eq_zero_of_cutoff_lt : ∀ {k}, cutoff < k → coeff k = 0

namespace FiniteNonnegativeSequence

/-- Every real polynomial with nonnegative coefficients gives a finite
nonnegative coefficient sequence. -/
def ofPolynomial (P : Polynomial ℝ) (hP : ∀ k, 0 ≤ P.coeff k) :
    FiniteNonnegativeSequence where
  coeff := P.coeff
  cutoff := P.natDegree
  coeff_nonneg := hP
  coeff_eq_zero_of_cutoff_lt := fun hk => Polynomial.coeff_eq_zero_of_natDegree_lt hk

end FiniteNonnegativeSequence

/-- The real-valued coefficient sequence of the independence polynomial. -/
def independenceCoefficients {V : Type u} [Fintype V] (G : SimpleGraph V) : ℕ → ℝ :=
  fun k => (independenceCoeff G k : ℝ)

/-- The independence coefficients, packaged with finite support and
nonnegativity. -/
def independenceCoefficientSequence {V : Type u} [Fintype V] (G : SimpleGraph V) :
    FiniteNonnegativeSequence :=
  FiniteNonnegativeSequence.ofPolynomial (independencePolynomialReal G) (by
    intro k
    rw [coeff_independencePolynomialReal]
    exact Nat.cast_nonneg _)

/-! ## Weak unimodality and first recovery -/

/-- There was a strict fall somewhere before `k`. -/
def HasStrictDropBefore (a : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ j, j < k ∧ a (j + 1) < a j

/-- Index `k` is a recovery: the sequence rises at `k` after an earlier fall. -/
def IsRecoveryIndex (a : ℕ → ℝ) (k : ℕ) : Prop :=
  HasStrictDropBefore a k ∧ a k < a (k + 1)

/-- Weak unimodality in the manuscript's exact sense: no strict rise occurs
after a strict fall.  Plateaux are allowed. -/
def WeaklyUnimodal (a : ℕ → ℝ) : Prop :=
  ∀ k, ¬IsRecoveryIndex a k

/-- `s` is the least index at which a strict rise follows an earlier fall. -/
def IsFirstRecovery (a : ℕ → ℝ) (s : ℕ) : Prop :=
  IsRecoveryIndex a s ∧ ∀ k, IsRecoveryIndex a k → s ≤ k

/-- A sequence is nonunimodal exactly when it has a first recovery. -/
theorem exists_firstRecovery_iff (a : ℕ → ℝ) :
    (∃ s, IsFirstRecovery a s) ↔ ¬WeaklyUnimodal a := by
  classical
  constructor
  · rintro ⟨s, hs, hmin⟩ huni
    exact huni s hs
  · intro hnot
    have hex : ∃ k, IsRecoveryIndex a k := by
      by_contra hnone
      apply hnot
      intro k hk
      exact hnone ⟨k, hk⟩
    let s := Nat.find hex
    refine ⟨s, Nat.find_spec hex, ?_⟩
    intro k hk
    exact Nat.find_min' hex hk

theorem IsFirstRecovery.isRecovery {a : ℕ → ℝ} {s : ℕ}
    (h : IsFirstRecovery a s) : IsRecoveryIndex a s :=
  h.1

theorem IsFirstRecovery.index_pos {a : ℕ → ℝ} {s : ℕ}
    (h : IsFirstRecovery a s) : 0 < s := by
  obtain ⟨j, hj, _⟩ := h.isRecovery.1
  omega

/-- Minimality forces the step immediately before a first recovery to be
nonincreasing. -/
theorem IsFirstRecovery.prev_ge {a : ℕ → ℝ} {s : ℕ}
    (h : IsFirstRecovery a s) : a s ≤ a (s - 1) := by
  by_contra hlt
  have hrise : a (s - 1) < a ((s - 1) + 1) := by
    simpa [Nat.sub_add_cancel h.index_pos] using lt_of_not_ge hlt
  obtain ⟨j, hjs, hdrop⟩ := h.isRecovery.1
  have hj : j < s - 1 := by
    have hjne : j ≠ s - 1 := by
      intro heq
      subst j
      exact lt_asymm hdrop hrise
    omega
  have hrecovery : IsRecoveryIndex a (s - 1) :=
    ⟨⟨j, hj, hdrop⟩, hrise⟩
  have hmin := h.2 (s - 1) hrecovery
  omega

/-- The central Turán minor, with the sign convention used in the manuscript. -/
def centralTuranMinor (a : ℕ → ℝ) (s : ℕ) : ℝ :=
  a s * a s - a (s - 1) * a (s + 1)

/-- A first recovery with positive central coefficient has strictly negative
central Turán minor. -/
theorem centralTuranMinor_neg_of_firstRecovery {a : ℕ → ℝ} {s : ℕ}
    (h : IsFirstRecovery a s) (hpos : 0 < a s) :
    centralTuranMinor a s < 0 := by
  have hrise := h.isRecovery.2
  have hleft : a s * a s < a s * a (s + 1) :=
    mul_lt_mul_of_pos_left hrise hpos
  have hright_nonneg : 0 ≤ a (s + 1) := le_trans hpos.le hrise.le
  have hright : a s * a (s + 1) ≤ a (s - 1) * a (s + 1) :=
    mul_le_mul_of_nonneg_right h.prev_ge hright_nonneg
  exact sub_neg.mpr (lt_of_lt_of_le hleft hright)

/-- Downward closure of graph independence ensures that a positive coefficient
at rank `k+1` forces a positive coefficient at rank `k`. -/
theorem independenceCoeff_pos_of_succ_pos {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) (hpos : 0 < independenceCoeff G (k + 1)) :
    0 < independenceCoeff G k := by
  classical
  rw [independenceCoeff] at hpos ⊢
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  have hscard : s.val.card = k + 1 := (Finset.mem_filter.mp hs).2
  have hsne : s.val.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hsne
  let t : IndepFinset G :=
    ⟨s.val.erase v, s.property.mono (Finset.erase_subset v s.val)⟩
  apply Finset.card_pos.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  dsimp [t]
  rw [Finset.card_erase_of_mem hv, hscard]
  omega

/-! ## Finite lattice laws and the hard-core specialization -/

/-- A normalized probability law on a finite type, together with a
natural-valued lattice statistic. -/
structure FiniteLatticeLaw (α : Type u) [Fintype α] where
  stat : α → ℕ
  probability : α → ℝ
  probability_nonneg : ∀ a, 0 ≤ probability a
  probability_sum : ∑ a, probability a = 1

namespace FiniteLatticeLaw

variable {α : Type u} [Fintype α]

/-- Probability mass at lattice rank `k`. -/
def rankMass (L : FiniteLatticeLaw α) (k : ℕ) : ℝ :=
  (Finset.univ.filter (fun a => L.stat a = k)).sum L.probability

/-- Mean of the lattice statistic. -/
def mean (L : FiniteLatticeLaw α) : ℝ :=
  ∑ a, L.probability a * (L.stat a : ℝ)

/-- Second moment of the lattice statistic. -/
def secondMoment (L : FiniteLatticeLaw α) : ℝ :=
  ∑ a, L.probability a * (L.stat a : ℝ) ^ 2

/-- Variance of the lattice statistic. -/
def variance (L : FiniteLatticeLaw α) : ℝ :=
  ∑ a, L.probability a * ((L.stat a : ℝ) - L.mean) ^ 2

theorem rankMass_nonneg (L : FiniteLatticeLaw α) (k : ℕ) :
    0 ≤ L.rankMass k := by
  apply Finset.sum_nonneg
  intro a ha
  exact L.probability_nonneg a

theorem mean_nonneg (L : FiniteLatticeLaw α) : 0 ≤ L.mean := by
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (L.probability_nonneg a) (Nat.cast_nonneg _)

theorem variance_nonneg (L : FiniteLatticeLaw α) : 0 ≤ L.variance := by
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (L.probability_nonneg a) (sq_nonneg _)

theorem rankMass_eq_sum_probability (L : FiniteLatticeLaw α) (k : ℕ) :
    L.rankMass k = ∑ a, if L.stat a = k then L.probability a else 0 := by
  unfold rankMass
  rw [Finset.sum_filter]

theorem variance_eq_secondMoment_sub_sq_mean (L : FiniteLatticeLaw α) :
    L.variance = L.secondMoment - L.mean ^ 2 := by
  rw [variance, secondMoment]
  calc
    (∑ a, L.probability a * ((L.stat a : ℝ) - L.mean) ^ 2) =
        ∑ a, (L.probability a * (L.stat a : ℝ) ^ 2 -
          2 * L.mean * (L.probability a * (L.stat a : ℝ)) +
          L.mean ^ 2 * L.probability a) := by
      apply Finset.sum_congr rfl
      intro a ha
      ring
    _ = (∑ a, L.probability a * (L.stat a : ℝ) ^ 2) -
        2 * L.mean * (∑ a, L.probability a * (L.stat a : ℝ)) +
        L.mean ^ 2 * (∑ a, L.probability a) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ = L.secondMoment - L.mean ^ 2 := by
      rw [L.probability_sum]
      simp only [secondMoment, mean]
      ring

end FiniteLatticeLaw

/-- The hard-core law on actual independent vertex finsets at activity `z`. -/
def hardCoreLaw {V : Type u} [Fintype V] (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) : FiniteLatticeLaw (IndepFinset G) where
  stat s := s.val.card
  probability s := z ^ s.val.card / independenceEval G z
  probability_nonneg s :=
    div_nonneg (pow_nonneg hz.le _) (independenceEval_pos G hz).le
  probability_sum := by
    have hEval : (∑ s : IndepFinset G, z ^ s.val.card) = independenceEval G z :=
      (independenceEval_eq_sum G z).symm
    rw [← Finset.sum_div, hEval]
    exact div_self (independenceEval_pos G hz).ne'

/-- The rank law of the hard-core model is the normalized tilt of the
independence coefficients. -/
theorem hardCoreLaw_rankMass_eq {V : Type u} [Fintype V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) (k : ℕ) :
    (hardCoreLaw G z hz).rankMass k =
      tiltedMass (independenceCoefficients G) z (independenceEval G z) k := by
  rw [FiniteLatticeLaw.rankMass_eq_sum_probability]
  simp only [hardCoreLaw]
  rw [← Finset.sum_filter, ← Finset.sum_div]
  have hsum :
      (Finset.univ.filter (fun a : IndepFinset G => a.val.card = k)).sum
          (fun a => z ^ a.val.card) =
        ((Finset.univ.filter
          (fun a : IndepFinset G => a.val.card = k)).card : ℝ) * z ^ k := by
    calc
      _ = ((Finset.univ.filter
          (fun a : IndepFinset G => a.val.card = k)).card : ℕ) • z ^ k :=
        Finset.sum_eq_card_nsmul (s := Finset.univ.filter
          (fun a : IndepFinset G => a.val.card = k)) (f := fun a => z ^ a.val.card)
          (b := z ^ k) (by
            intro a ha
            exact congrArg (fun n : ℕ => z ^ n) (Finset.mem_filter.mp ha).2)
      _ = ((Finset.univ.filter
          (fun a : IndepFinset G => a.val.card = k)).card : ℝ) * z ^ k := by
        rw [nsmul_eq_mul]
  rw [hsum]
  rfl

/-- Positive tilting also preserves the strict reverse Turán inequality. -/
theorem tilted_strict_reverse_turan_iff (a : ℕ → ℝ) (z Z : ℝ) (s : ℕ)
    (hs : 1 ≤ s) (hz : 0 < z) (hZ : Z ≠ 0) :
    tiltedMass a z Z s * tiltedMass a z Z s <
        tiltedMass a z Z (s - 1) * tiltedMass a z Z (s + 1) ↔
      a s * a s < a (s - 1) * a (s + 1) := by
  have he : (s - 1) + (s + 1) = s + s := by omega
  have hp : z ^ (s - 1) * z ^ (s + 1) = z ^ s * z ^ s := by
    rw [← pow_add, he, pow_add]
  let c : ℝ := z ^ (s + s) / (Z * Z)
  have hc : 0 < c := div_pos (pow_pos hz _) (mul_self_pos.mpr hZ)
  have hneighbors :
      tiltedMass a z Z (s - 1) * tiltedMass a z Z (s + 1) =
        c * (a (s - 1) * a (s + 1)) := by
    simp only [tiltedMass, c, div_eq_mul_inv]
    calc
      _ = (a (s - 1) * a (s + 1) * (Z⁻¹ * Z⁻¹)) *
            (z ^ (s - 1) * z ^ (s + 1)) := by ring
      _ = (a (s - 1) * a (s + 1) * (Z⁻¹ * Z⁻¹)) *
            (z ^ s * z ^ s) := by rw [hp]
      _ = _ := by rw [← pow_add]; ring
  have hcenter :
      tiltedMass a z Z s * tiltedMass a z Z s = c * (a s * a s) := by
    simp only [tiltedMass, c, div_eq_mul_inv]
    rw [pow_add]
    ring
  rw [hcenter, hneighbors]
  constructor <;> intro h <;> nlinarith

/-! ## Canonical first-recovery data -/

/-- The finite data of one canonical first-recovery state.  The field
`mean_eq_index` records the saddle-point equation; existence and uniqueness of
that activity are deliberately not claimed in this specification file. -/
structure CanonicalFirstRecoveryState {V : Type u} [Fintype V]
    (G : SimpleGraph V) where
  isForest : G.IsAcyclic
  index : ℕ
  firstRecovery : IsFirstRecovery (independenceCoefficients G) index
  activity : ℝ
  activity_pos : 0 < activity
  mean_eq_index :
    (hardCoreLaw G activity activity_pos).mean = (index : ℝ)

namespace CanonicalFirstRecoveryState

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The canonical hard-core law carried by a first-recovery state. -/
def law (C : CanonicalFirstRecoveryState G) : FiniteLatticeLaw (IndepFinset G) :=
  hardCoreLaw G C.activity C.activity_pos

/-- Number of vertices in the underlying forest. -/
def order (_C : CanonicalFirstRecoveryState G) : ℕ := Fintype.card V

/-- Variance of the global hard-core occupation count. -/
def variance (C : CanonicalFirstRecoveryState G) : ℝ := C.law.variance

theorem center_coeff_pos (C : CanonicalFirstRecoveryState G) :
    0 < independenceCoefficients G C.index := by
  have hrise := C.firstRecovery.isRecovery.2
  have hcenter_nonneg : 0 ≤ independenceCoefficients G C.index := Nat.cast_nonneg _
  have hsucc_real : 0 < independenceCoefficients G (C.index + 1) :=
    lt_of_le_of_lt hcenter_nonneg hrise
  have hsucc_nat : 0 < independenceCoeff G (C.index + 1) := by
    change (0 : ℝ) < (independenceCoeff G (C.index + 1) : ℝ) at hsucc_real
    exact_mod_cast hsucc_real
  have hcenter_nat := independenceCoeff_pos_of_succ_pos G C.index hsucc_nat
  change (0 : ℝ) < (independenceCoeff G C.index : ℝ)
  exact_mod_cast hcenter_nat

/-- Exact finite first-recovery implication (1.1). -/
theorem centralTuranMinor_neg (C : CanonicalFirstRecoveryState G) :
    centralTuranMinor (independenceCoefficients G) C.index < 0 :=
  centralTuranMinor_neg_of_firstRecovery C.firstRecovery C.center_coeff_pos

/-- Exact conversion of (1.1) into the reverse log-concavity inequality (1.2)
for the three central hard-core probabilities. -/
theorem central_rankMass_strict_reverse_turan (C : CanonicalFirstRecoveryState G) :
    C.law.rankMass C.index * C.law.rankMass C.index <
      C.law.rankMass (C.index - 1) * C.law.rankMass (C.index + 1) := by
  rw [law, hardCoreLaw_rankMass_eq, hardCoreLaw_rankMass_eq,
    hardCoreLaw_rankMass_eq, tilted_strict_reverse_turan_iff]
  · exact sub_neg.mp C.centralTuranMinor_neg
  · exact C.firstRecovery.index_pos
  · exact C.activity_pos
  · exact (independenceEval_pos G C.activity_pos).ne'

end CanonicalFirstRecoveryState

end
end Forest
end Erdos993
