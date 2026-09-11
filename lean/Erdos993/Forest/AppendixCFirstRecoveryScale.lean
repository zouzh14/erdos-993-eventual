import Erdos993.Forest.AppendixCActivityFloor
import Erdos993.Forest.ProbabilityAtMean
import Erdos993.Forest.UniformBinomialMass
import Erdos993.Forest.Interfaces

open scoped BigOperators Topology
open Filter

namespace Erdos993.Forest.AppendixC

open ProbabilityAtMean UniformBinomialMass

noncomputable section

noncomputable local instance finiteColorEnvironment
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (P : FiniteBipartition G) (c : BipartitionSide) :
    Fintype (ColorEnvironment P c) :=
  Fintype.ofInjective (fun E : ColorEnvironment P c => E.occupied) (by
    intro E₁ E₂ h
    cases E₁ with
    | mk o₁ h₁ =>
      cases E₂ with
      | mk o₂ h₂ =>
        cases h
        rfl)

/-- A covering finite bipartition obtained from the canonical two-coloring of a forest. -/
noncomputable def finiteBipartitionOfForest {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) : FiniteBipartition G := by
  classical
  let col : G.Coloring (Fin 2) := hG.coloringTwo
  let L : Finset V := Finset.univ.filter (fun v => col v = 0)
  let R : Finset V := Finset.univ.filter (fun v => col v ≠ 0)
  refine { left := L, right := R, crosses := ?_, cover := ?_ }
  · refine ⟨?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hvL hvR
      have hv0 : col v = 0 := by simpa [L] using hvL
      have hvn0 : col v ≠ 0 := by simpa [R] using hvR
      exact hvn0 hv0
    · intro v w hvw
      have hne := col.valid hvw
      by_cases hv : col v = 0
      · left
        constructor
        · simpa [L, hv]
        · have hw : col w ≠ 0 := by
            intro hw
            exact hne (hv.trans hw.symm)
          simpa [R, hw]
      · by_cases hw : col w = 0
        · right
          constructor
          · simpa [R, hv]
          · simpa [L, hw]
        · exfalso
          apply hne
          rw [Fin.eq_one_of_ne_zero (col v) hv, Fin.eq_one_of_ne_zero (col w) hw]
  · ext v
    by_cases h : col v = 0 <;> simp [L, R, h]

lemma sideOccupationExpectation_add
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (z : ℝ) (hz : 0 < z) :
    sideOccupationExpectation G P .left z hz +
        sideOccupationExpectation G P .right z hz =
      (hardCoreLaw G z hz).mean := by
  rw [← sum_singleSiteOccupationProbability_eq_mean (G := G) z hz]
  unfold sideOccupationExpectation
  change (∑ v ∈ P.left, singleSiteOccupationProbability G z hz v) +
      (∑ v ∈ P.right, singleSiteOccupationProbability G z hz v) = _
  have hd : Disjoint P.left P.right := by
    simpa only [FiniteBipartition.side, FiniteBipartition.other] using
      (P.disjoint_side_other .left)
  rw [← Finset.sum_union hd, P.cover]

lemma exists_reveal_side_opposite_occupation_half
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (z : ℝ) (hz : 0 < z) :
    ∃ c : BipartitionSide,
      (hardCoreLaw G z hz).mean / 2 ≤
        sideOccupationExpectation G P c.opposite z hz := by
  have hsum := sideOccupationExpectation_add G P z hz
  by_cases h : (hardCoreLaw G z hz).mean / 2 ≤
      sideOccupationExpectation G P .right z hz
  · exact ⟨.left, by simpa using h⟩
  · refine ⟨.right, ?_⟩
    simp only [not_le] at h
    simp only [BipartitionSide.opposite_right]
    linarith

lemma expectedConditionalVariance_gt_index_div_56
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide)
    (hopp : (C.index : ℝ) / 2 ≤
      sideOccupationExpectation G P c.opposite C.activity C.activity_pos)
    (hz27 : C.activity < 27) :
    (C.index : ℝ) / 56 <
      expectedConditionalVariance G P c C.activity C.activity_pos := by
  rw [C43_expectedConditionalVariance, one_sub_hardCoreTheta C.activity_pos]
  have hq : (1 : ℝ) / 28 < 1 / (1 + C.activity) := by
    apply one_div_lt_one_div_of_lt
    · linarith [C.activity_pos]
    · linarith
  have hs : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
  nlinarith

lemma conditionalVarianceGivenRestriction_nonneg
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    0 ≤ conditionalVarianceGivenRestriction G P c z hz s := by
  unfold conditionalVarianceGivenRestriction
  rw [C41_actual_conditionalVariance]
  unfold hardCoreTheta
  have hden : 0 < 1 + z := by linarith
  have htheta0 : 0 ≤ z / (1 + z) := (div_pos hz hden).le
  have htheta1 : z / (1 + z) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  exact mul_nonneg (mul_nonneg htheta0 (sub_nonneg.mpr htheta1)) (by positivity)

lemma conditionalVarianceGivenRestriction_le_order_div_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    conditionalVarianceGivenRestriction G P c z hz s ≤
      (Fintype.card V : ℝ) / 4 := by
  unfold conditionalVarianceGivenRestriction
  rw [C41_actual_conditionalVariance]
  let θ := hardCoreTheta z
  have hθ0 : 0 ≤ θ := by
    dsimp [θ, hardCoreTheta]
    positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ, hardCoreTheta]
    apply (div_le_one (by linarith)).2
    linarith
  have hquad : θ * (1 - θ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have haN : ((restrictionEnvironment G P c s).available.card : ℝ) ≤
      (Fintype.card V : ℝ) := by
    exact_mod_cast (Finset.card_le_univ (restrictionEnvironment G P c s).available)
  have ha0 : (0 : ℝ) ≤ (restrictionEnvironment G P c s).available.card := by positivity
  nlinarith

/-- Probability mass of a decidable event under the original global canonical law. -/
noncomputable def canonicalEventMass
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (p : IndepFinset G → Prop) : ℝ := by
  classical
  exact ∑ s : IndepFinset G, if p s then C.law.probability s else 0

lemma canonicalEventMass_nonneg
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G) (p : IndepFinset G → Prop) :
    0 ≤ canonicalEventMass C p := by
  classical
  unfold canonicalEventMass
  apply Finset.sum_nonneg
  intro s hs
  split
  · exact C.law.probability_nonneg s
  · exact le_rfl

/-- C.57 in literal global-state form. -/
lemma high_conditional_variance_event_mass_gt
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide)
    (hexp : (C.index : ℝ) / 56 <
      expectedConditionalVariance G P c C.activity C.activity_pos)
    (horder : (C.order : ℝ) < (3304 / 3 : ℝ) * C.index) :
    (1 : ℝ) / (28 * (3304 / 3 : ℝ)) <
      canonicalEventMass C (fun s =>
        (C.index : ℝ) / 112 ≤
          conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s) := by
  classical
  let q := canonicalEventMass C (fun s =>
    (C.index : ℝ) / 112 ≤
      conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s)
  have hsum : expectedConditionalVariance G P c C.activity C.activity_pos ≤
      (C.index : ℝ) / 112 + (C.order : ℝ) / 4 * q := by
    unfold expectedConditionalVariance
    calc
      (∑ s : IndepFinset G, C.law.probability s *
          conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s) ≤
          ∑ s : IndepFinset G,
            (C.law.probability s * ((C.index : ℝ) / 112) +
              if (C.index : ℝ) / 112 ≤
                  conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s then
                C.law.probability s * ((C.order : ℝ) / 4) else 0) := by
        apply Finset.sum_le_sum
        intro s hs
        have hp := C.law.probability_nonneg s
        have hW := conditionalVarianceGivenRestriction_le_order_div_four
          G P c C.activity C.activity_pos s
        change _ ≤ (C.order : ℝ) / 4 at hW
        by_cases hevent : (C.index : ℝ) / 112 ≤
            conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s
        · rw [if_pos hevent]
          have hs0 : (0 : ℝ) ≤ C.index := by positivity
          nlinarith
        · rw [if_neg hevent]
          simp only [not_le] at hevent
          simpa using (mul_le_mul_of_nonneg_left hevent.le hp)
      _ = (C.index : ℝ) / 112 * (∑ s : IndepFinset G, C.law.probability s) +
          (C.order : ℝ) / 4 * q := by
        rw [Finset.sum_add_distrib]
        congr 1
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        · unfold q canonicalEventMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          split <;> ring
      _ = (C.index : ℝ) / 112 + (C.order : ℝ) / 4 * q := by
        rw [C.law.probability_sum]
        ring
  have hq0 : 0 ≤ q := canonicalEventMass_nonneg C _
  have hs0 : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
  have hscaled : (C.order : ℝ) / 4 * q ≤
      ((3304 / 3 : ℝ) * C.index) / 4 * q := by
    exact mul_le_mul_of_nonneg_right (by linarith [horder]) hq0
  have hmain : (C.index : ℝ) / 56 <
      (C.index : ℝ) / 112 + ((3304 / 3 : ℝ) * C.index) / 4 * q := by
    have hadd : (C.index : ℝ) / 112 + (C.order : ℝ) / 4 * q ≤
        (C.index : ℝ) / 112 + ((3304 / 3 : ℝ) * C.index) / 4 * q := by
      linarith
    exact lt_of_lt_of_le (hexp.trans_le hsum) hadd
  change (1 : ℝ) / (28 * (3304 / 3 : ℝ)) < q
  nlinarith

/-- Original-law mass of an event on exact conditioning environments. -/
noncomputable def canonicalEnvironmentEventMass
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) (p : ColorEnvironment P c → Prop) : ℝ := by
  classical
  exact ∑ E : ColorEnvironment P c,
    if p E then actualFiberMass G P c C.activity C.activity_pos E else 0

lemma canonicalEventMass_restriction_eq_environmentMass
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) (p : ColorEnvironment P c → Prop) :
    canonicalEventMass C (fun s => p (restrictionEnvironment G P c s)) =
      canonicalEnvironmentEventMass C P c p := by
  classical
  unfold canonicalEventMass canonicalEnvironmentEventMass
  rw [sum_global_eq_sum_fiberSigma (G := G) P c]
  apply Finset.sum_congr rfl
  intro E hE
  change (∑ t : E.FiberState,
      if p (restrictionEnvironment G P c (E.extension t)) then
        actualFiberWeight G P c C.activity C.activity_pos E t else 0) =
    (if p E then actualFiberMass G P c C.activity C.activity_pos E else 0)
  simp [restrictionEnvironment_extension_eq' (G := G) c E, actualFiberMass]

lemma canonicalEnvironmentEventMass_nonneg
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) (p : ColorEnvironment P c → Prop) :
    0 ≤ canonicalEnvironmentEventMass C P c p := by
  classical
  unfold canonicalEnvironmentEventMass
  apply Finset.sum_nonneg
  intro E hE
  split
  · exact (actualFiberMass_pos G P c C.activity C.activity_pos E).le
  · exact le_rfl

lemma canonical_rankMass_eq_environment_conditionalRankMass
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) :
    C.law.rankMass C.index =
      ∑ E : ColorEnvironment P c,
        actualFiberMass G P c C.activity C.activity_pos E *
          actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index := by
  classical
  rw [C.law.rankMass_eq_sum_probability]
  rw [sum_global_eq_sum_fiberSigma (G := G) P c]
  apply Finset.sum_congr rfl
  intro E hE
  unfold actualConditionalRankMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hfactor : C.law.probability (E.extension t) =
      actualFiberMass G P c C.activity C.activity_pos E *
        actualConditionalProbability G P c C.activity C.activity_pos E t := by
    change actualFiberWeight G P c C.activity C.activity_pos E t = _
    unfold actualConditionalProbability
    have hne : actualFiberMass G P c C.activity C.activity_pos E ≠ 0 :=
      (actualFiberMass_pos G P c C.activity C.activity_pos E).ne'
    rw [← mul_div_assoc]
    exact (eq_div_iff hne).2 (by ring)
  by_cases hcard : (E.extension t).val.card = C.index
  · change (if (E.extension t).val.card = C.index then
        C.law.probability (E.extension t) else 0) = _
    rw [if_pos hcard, if_pos hcard]
    exact hfactor
  · change (if (E.extension t).val.card = C.index then
        C.law.probability (E.extension t) else 0) = _
    simp [hcard]

/-- C.6 transferred to the literal conditional rank mass in a C.40 fiber. -/
lemma actualConditionalRankMass_uniform_lower
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) (s : ℕ)
    (H M W : ℝ)
    (hθlo : (3 : ℝ) / 5 ≤ hardCoreTheta z)
    (hθhi : hardCoreTheta z ≤ (27 : ℝ) / 28)
    (hH : 1 ≤ H)
    (hM : M = (E.occupied.val.card : ℝ) +
      (E.available.card : ℝ) * hardCoreTheta z)
    (hW : W = (E.available.card : ℝ) * hardCoreTheta z *
      (1 - hardCoreTheta z))
    (hWH : 4 * H ≤ W) (hclose : (M - (s : ℝ)) ^ 2 ≤ H * W) :
    (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W * Real.exp (-H) ≤
      actualConditionalRankMass (G := G) z hz E s := by
  have hlocal := uniformBinomialMassLowerBound_explicit
    E.available.card (Int.ofNat E.occupied.val.card) (Int.ofNat s)
    (hardCoreTheta z) H M W hθlo hθhi hH (by
      simpa [mul_comm] using hM) hW hWH hclose
  have hinter := interior_rank_bounds
    E.available.card (Int.ofNat E.occupied.val.card) (Int.ofNat s)
    (hardCoreTheta z) H M W hθlo hθhi hH (by
      simpa [mul_comm] using hM) hW hWH hclose
  let k : ℕ := (Int.ofNat s - Int.ofNat E.occupied.val.card).toNat
  have hdiffpos : (0 : ℤ) < Int.ofNat s - Int.ofNat E.occupied.val.card := by
    have hreal := hinter.2.1
    have ha : (0 : ℝ) < E.available.card := by
      exact_mod_cast hinter.1
    have hzreal : (0 : ℝ) <
        ((Int.ofNat s - Int.ofNat E.occupied.val.card : ℤ) : ℝ) := by
      have := (le_div_iff₀ ha).mp hreal
      nlinarith
    exact_mod_cast hzreal
  have hKs : E.occupied.val.card ≤ s := by
    by_contra hnot
    have hslt : s < E.occupied.val.card := Nat.lt_of_not_ge hnot
    have hint : Int.ofNat s < Int.ofNat E.occupied.val.card := Int.ofNat_lt.mpr hslt
    omega
  have hkNat0 : k = s - E.occupied.val.card := by
    dsimp [k]
    rw [← Int.ofNat_sub hKs]
    simp
  have hkNat : E.occupied.val.card + k = s := by
    rw [hkNat0]
    omega
  calc
    (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W * Real.exp (-H) ≤
        shiftedBinomialMass E.available.card (Int.ofNat E.occupied.val.card)
          (Int.ofNat s) (hardCoreTheta z) := hlocal
    _ = binomialMass E.available.card k (hardCoreTheta z) := by
      unfold shiftedBinomialMass
      have hsupp := (interior_rank_bounds
        E.available.card (Int.ofNat E.occupied.val.card) (Int.ofNat s)
        (hardCoreTheta z) H M W hθlo hθhi hH (by
          simpa [mul_comm] using hM) hW hWH hclose)
      have hkpos : 0 ≤ Int.ofNat s - Int.ofNat E.occupied.val.card := hdiffpos.le
      have hkle : Int.ofNat s - Int.ofNat E.occupied.val.card ≤
          (E.available.card : ℤ) := by
        have hreal := hsupp.2.2
        have ha : (0 : ℝ) < E.available.card := by exact_mod_cast hsupp.1
        have hlt : ((Int.ofNat s - Int.ofNat E.occupied.val.card : ℤ) : ℝ) <
            (E.available.card : ℝ) := by
          apply (div_lt_one₀ ha).mp
          exact lt_of_le_of_lt hreal (by norm_num)
        exact_mod_cast hlt.le
      rw [if_pos ⟨hkpos, hkle⟩]
    _ = actualConditionalTotalRankMass G P c z hz E k := by
      symm
      simpa [binomialMass] using C40_actual_conditional_totalRankMass G P c z hz E k
    _ = actualConditionalRankMass (G := G) z hz E s := by
      unfold actualConditionalTotalRankMass actualConditionalRankMass
      apply Finset.sum_congr rfl
      intro t ht
      rw [hkNat]

lemma hardCoreTheta_bounds_of_activity
    {z : ℝ} (hz : 0 < z) (hzlo : (3 : ℝ) / 2 < z) (hzhi : z < 27) :
    (3 : ℝ) / 5 ≤ hardCoreTheta z ∧ hardCoreTheta z ≤ (27 : ℝ) / 28 := by
  unfold hardCoreTheta
  have hd : 0 < 1 + z := by linarith
  constructor
  · apply (le_div_iff₀ hd).2
    linarith
  · apply (div_le_iff₀ hd).2
    linarith

lemma actualConditionalVariance_le_order_div_four
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) :
    actualConditionalVariance G P c z hz E ≤ (Fintype.card V : ℝ) / 4 := by
  rw [C41_actual_conditionalVariance]
  let θ := hardCoreTheta z
  have hθ0 : 0 ≤ θ := by dsimp [θ, hardCoreTheta]; positivity
  have hθ1 : θ ≤ 1 := by
    dsimp [θ, hardCoreTheta]
    apply (div_le_one (by linarith)).2
    linarith
  have hquad : θ * (1 - θ) ≤ 1 / 4 := by
    nlinarith [sq_nonneg (θ - 1 / 2)]
  have haN : (E.available.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast (Finset.card_le_univ E.available)
  have ha0 : (0 : ℝ) ≤ E.available.card := by positivity
  nlinarith

/-- C.59 with a deliberately weaker `1/(C_*s)` prefactor, sufficient for C.60. -/
lemma near_center_environment_mass_times_atom_le_rankMass
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) (H : ℝ)
    (hH : 1 ≤ H) (hzlo : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (horder : (C.order : ℝ) < (3304 / 3 : ℝ) * C.index) :
    ((1 / (3 * (Real.exp 1) ^ 2)) /
        ((3304 / 3 : ℝ) * C.index) * Real.exp (-H)) *
      canonicalEnvironmentEventMass C P c (fun E =>
        4 * H ≤ actualConditionalVariance G P c C.activity C.activity_pos E ∧
        (actualConditionalMean G P c C.activity C.activity_pos E - (C.index : ℝ)) ^ 2 ≤
          H * actualConditionalVariance G P c C.activity C.activity_pos E) ≤
      C.law.rankMass C.index := by
  classical
  rw [canonical_rankMass_eq_environment_conditionalRankMass G C P c]
  unfold canonicalEnvironmentEventMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro E hE
  let W := actualConditionalVariance G P c C.activity C.activity_pos E
  let M := actualConditionalMean G P c C.activity C.activity_pos E
  by_cases hB : 4 * H ≤ W ∧ (M - (C.index : ℝ)) ^ 2 ≤ H * W
  · rw [if_pos hB]
    have hθ := hardCoreTheta_bounds_of_activity C.activity_pos hzlo hz27
    have hlocal : (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W *
          Real.exp (-H) ≤
        actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index := by
      apply actualConditionalRankMass_uniform_lower G P c C.activity C.activity_pos E C.index H M W
      · exact hθ.1
      · exact hθ.2
      · exact hH
      · dsimp [M]
        simpa [mul_comm] using C41_actual_conditionalMean G P c C.activity C.activity_pos E
      · dsimp [W]
        rw [C41_actual_conditionalVariance]
        ring
      · exact hB.1
      · exact hB.2
    have hW4 : 4 ≤ W := by nlinarith [hB.1, hH]
    have hW0 : 0 < W := by linarith
    have hsqrt0 : 0 < Real.sqrt W := Real.sqrt_pos.2 hW0
    have hsqrtW : Real.sqrt W ≤ W := by
      rw [Real.sqrt_le_iff]
      constructor
      · exact hW0.le
      · nlinarith
    have hWle := actualConditionalVariance_le_order_div_four
      G P c C.activity C.activity_pos E
    have hN : (Fintype.card V : ℝ) / 4 <
        ((3304 / 3 : ℝ) * C.index) / 4 := by
      change (C.order : ℝ) / 4 < _
      linarith [horder]
    have hWupper : W < ((3304 / 3 : ℝ) * C.index) / 4 :=
      hWle.trans_lt hN
    have hs0 : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
    have hden : Real.sqrt W ≤ (3304 / 3 : ℝ) * C.index := by
      nlinarith [hsqrtW, hWupper]
    have hfrac : (1 / (3 * (Real.exp 1) ^ 2)) /
          ((3304 / 3 : ℝ) * C.index) ≤
        (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W := by
      exact div_le_div_of_nonneg_left (by positivity) hsqrt0 hden
    have hatom : (1 / (3 * (Real.exp 1) ^ 2)) /
          ((3304 / 3 : ℝ) * C.index) * Real.exp (-H) ≤
        actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index :=
      (mul_le_mul_of_nonneg_right hfrac (Real.exp_pos _).le).trans hlocal
    simpa [mul_comm] using (mul_le_mul_of_nonneg_left hatom
      (actualFiberMass_pos G P c C.activity C.activity_pos E).le)
  · rw [if_neg hB]
    have hr : 0 ≤ actualConditionalRankMass (G := G)
        C.activity C.activity_pos E C.index := by
      unfold actualConditionalRankMass
      apply Finset.sum_nonneg
      intro t ht
      split
      · exact actualConditionalProbability_nonneg
          (G := G) C.activity C.activity_pos E t
      · exact le_rfl
    simpa only [mul_zero] using (mul_nonneg
      (actualFiberMass_pos G P c C.activity C.activity_pos E).le hr)

lemma weighted_sq_decomposition {α : Type*} [Fintype α]
    (p x : α → ℝ) (m a : ℝ)
    (hp : ∑ i, p i = 1) (hm : m = ∑ i, p i * x i) :
    (∑ i, p i * (x i - a) ^ 2) =
      (∑ i, p i * (x i - m) ^ 2) + (m - a) ^ 2 := by
  have hcenter : ∑ i, p i * (x i - m) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have hpm : (∑ i, p i * m) = m := by
      rw [← Finset.sum_mul, hp, one_mul]
    rw [hpm, ← hm]
    ring
  have hcross : (∑ i, p i * (2 * (x i - m) * (m - a))) =
      2 * (m - a) * (∑ i, p i * (x i - m)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hconst : (∑ i, p i * (m - a) ^ 2) =
      (m - a) ^ 2 * (∑ i, p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    (∑ i, p i * (x i - a) ^ 2) =
        ∑ i, p i * ((x i - m) + (m - a)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 2 <;> ring
    _ = (∑ i, p i * (x i - m) ^ 2) +
        (∑ i, p i * (2 * (x i - m) * (m - a))) +
        (∑ i, p i * (m - a) ^ 2) := by
      simp_rw [add_sq, mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = _ := by rw [hcross, hconst, hcenter, hp]; ring

lemma environment_conditionalMean_sq_le_variance
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) :
    (∑ E : ColorEnvironment P c,
      actualFiberMass G P c C.activity C.activity_pos E *
        (actualConditionalMean G P c C.activity C.activity_pos E - (C.index : ℝ)) ^ 2) ≤
      C.variance := by
  classical
  unfold CanonicalFirstRecoveryState.variance FiniteLatticeLaw.variance
  rw [C.law_mean]
  rw [sum_global_eq_sum_fiberSigma (G := G) P c]
  apply Finset.sum_le_sum
  intro E hE
  have hfactor (t : E.FiberState) : C.law.probability (E.extension t) =
      actualFiberMass G P c C.activity C.activity_pos E *
        actualConditionalProbability G P c C.activity C.activity_pos E t := by
    change actualFiberWeight G P c C.activity C.activity_pos E t = _
    unfold actualConditionalProbability
    have hne := (actualFiberMass_pos G P c C.activity C.activity_pos E).ne'
    rw [← mul_div_assoc]
    exact (eq_div_iff hne).2 (by ring)
  change actualFiberMass G P c C.activity C.activity_pos E *
      (actualConditionalMean G P c C.activity C.activity_pos E - (C.index : ℝ)) ^ 2 ≤
    ∑ t : E.FiberState, C.law.probability (E.extension t) *
      (((E.extension t).val.card : ℝ) - (C.index : ℝ)) ^ 2
  simp_rw [hfactor, mul_assoc]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _
    (actualFiberMass_pos G P c C.activity C.activity_pos E).le
  have hdecomp := weighted_sq_decomposition
    (fun t : E.FiberState => actualConditionalProbability G P c C.activity C.activity_pos E t)
    (fun t : E.FiberState => ((E.extension t).val.card : ℝ))
    (actualConditionalMean G P c C.activity C.activity_pos E) (C.index : ℝ)
    (C40_actual_conditional_probability_sum G P c C.activity C.activity_pos E) rfl
  rw [hdecomp]
  have hvar : 0 ≤ actualConditionalVariance G P c C.activity C.activity_pos E := by
    unfold actualConditionalVariance
    apply Finset.sum_nonneg
    intro t ht
    exact mul_nonneg
      (actualConditionalProbability_nonneg (G := G) C.activity C.activity_pos E t)
      (sq_nonneg _)
  change _ ≤ actualConditionalVariance G P c C.activity C.activity_pos E + _
  linarith

abbrev scaleCstar : ℝ := 3304 / 3
abbrev scaleGamma0 : ℝ := 1 / (25088 * scaleCstar)
abbrev scaleGamma : ℝ := min (scaleGamma0 / 2) (1 / 448)
abbrev scaleDelta : ℝ := 1 / (28 * scaleCstar)
abbrev scaleCb : ℝ := 1 / (3 * (Real.exp 1) ^ 2)

lemma scaleGamma_pos : 0 < scaleGamma := by
  apply lt_min <;> norm_num [scaleGamma, scaleGamma0, scaleCstar]

lemma scaleDelta_pos : 0 < scaleDelta := by norm_num [scaleDelta, scaleCstar]
lemma scaleCb_pos : 0 < scaleCb := by positivity
lemma scaleGamma_le : scaleGamma ≤ (1 : ℝ) / 448 := min_le_right _ _

/-- C.56--C.62 once the two explicit scalar large-index inequalities hold. -/
lemma variance_quadratic_lower_of_scalar_bounds
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableEq V] [DecidableRel G.Adj]
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide)
    (hopp : (C.index : ℝ) / 2 ≤
      sideOccupationExpectation G P c.opposite C.activity C.activity_pos)
    (hzlo : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (hH : 1 ≤ scaleGamma * (C.index : ℝ))
    (hscalar : 12 * scaleCstar * Real.exp (-(C.index : ℝ) /
          (25088 * scaleCstar)) ≤
      (scaleCb / (scaleCstar * (C.index : ℝ)) *
          Real.exp (-(scaleGamma * (C.index : ℝ)))) * (scaleDelta / 2)) :
    scaleDelta * scaleGamma / 224 * (C.index : ℝ) ^ 2 ≤ C.variance := by
  classical
  let H : ℝ := scaleGamma * (C.index : ℝ)
  let W : ColorEnvironment P c → ℝ := fun E =>
    actualConditionalVariance G P c C.activity C.activity_pos E
  let M : ColorEnvironment P c → ℝ := fun E =>
    actualConditionalMean G P c C.activity C.activity_pos E
  let high : ColorEnvironment P c → Prop := fun E => (C.index : ℝ) / 112 ≤ W E
  let near : ColorEnvironment P c → Prop := fun E =>
    4 * H ≤ W E ∧ (M E - (C.index : ℝ)) ^ 2 ≤ H * W E
  let far : ColorEnvironment P c → Prop := fun E =>
    high E ∧ ¬((M E - (C.index : ℝ)) ^ 2 ≤ H * W E)
  have h39 := C39_order_and_variance_lt (G := G) C hzlo hz27
  have hexp := expectedConditionalVariance_gt_index_div_56 G C P c hopp hz27
  have hhighGlobal := high_conditional_variance_event_mass_gt
    G C P c hexp h39.1
  have hbridge := canonicalEventMass_restriction_eq_environmentMass
    G C P c high
  have hrest (s : IndepFinset G) :
      high (restrictionEnvironment G P c s) ↔
        (C.index : ℝ) / 112 ≤
          conditionalVarianceGivenRestriction G P c C.activity C.activity_pos s := by
    rfl
  have hhigh : scaleDelta < canonicalEnvironmentEventMass C P c high := by
    rw [← hbridge]
    simpa [high, W, scaleDelta, scaleCstar] using hhighGlobal
  have hatom := near_center_environment_mass_times_atom_le_rankMass
    G C P c H (by simpa [H] using hH) hzlo hz27 h39.1
  have hcenter := ProbabilityAtMean.C44_probability_at_mean_finite
    (G := G) C P C.firstRecovery.index_pos hzlo hz27
  have hnear : canonicalEnvironmentEventMass C P c near ≤ scaleDelta / 2 := by
    have hchain : (scaleCb / (scaleCstar * (C.index : ℝ)) * Real.exp (-H)) *
          canonicalEnvironmentEventMass C P c near ≤
        12 * scaleCstar * Real.exp (-(C.index : ℝ) /
          (25088 * scaleCstar)) := by
      exact hatom.trans hcenter
    have hA : 0 < scaleCb / (scaleCstar * (C.index : ℝ)) * Real.exp (-H) := by
      have hs : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
      positivity
    apply (le_of_mul_le_mul_left _ hA)
    calc
      (scaleCb / (scaleCstar * (C.index : ℝ)) * Real.exp (-H)) *
          canonicalEnvironmentEventMass C P c near ≤
          12 * scaleCstar * Real.exp (-(C.index : ℝ) /
            (25088 * scaleCstar)) := hchain
      _ ≤ (scaleCb / (scaleCstar * (C.index : ℝ)) * Real.exp (-H)) *
          (scaleDelta / 2) := by simpa [H] using hscalar
  have hthreshold : 4 * H ≤ (C.index : ℝ) / 112 := by
    have hs : (0 : ℝ) ≤ C.index := by positivity
    dsimp [H]
    nlinarith [scaleGamma_le]
  have hsplit : canonicalEnvironmentEventMass C P c high ≤
      canonicalEnvironmentEventMass C P c near +
        canonicalEnvironmentEventMass C P c far := by
    unfold canonicalEnvironmentEventMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro E hE
    have hm := (actualFiberMass_pos G P c C.activity C.activity_pos E).le
    by_cases hh : high E
    · have h4 : 4 * H ≤ W E := hthreshold.trans hh
      by_cases hc : (M E - (C.index : ℝ)) ^ 2 ≤ H * W E
      · have hnotlt : ¬ H * W E < (M E - (C.index : ℝ)) ^ 2 := not_lt_of_ge hc
        simp [high, near, far, hh, h4, hc, hnotlt, hm]
      · have hc' : H * W E < (M E - (C.index : ℝ)) ^ 2 := lt_of_not_ge hc
        simp [high, near, far, hh, h4, hc, hc']
    · rw [if_neg hh]
      positivity
  have hfar : scaleDelta / 2 < canonicalEnvironmentEventMass C P c far := by
    by_contra hn
    have hfarle := le_of_not_gt hn
    have hadd : canonicalEnvironmentEventMass C P c near +
        canonicalEnvironmentEventMass C P c far ≤ scaleDelta := by
      have ht := add_le_add hnear hfarle
      convert ht using 1 <;> ring
    have hlt : scaleDelta < scaleDelta := hhigh.trans_le (hsplit.trans hadd)
    linarith
  have hsquare :
      (H * ((C.index : ℝ) / 112)) * canonicalEnvironmentEventMass C P c far ≤
        ∑ E : ColorEnvironment P c,
          actualFiberMass G P c C.activity C.activity_pos E *
            (M E - (C.index : ℝ)) ^ 2 := by
    unfold canonicalEnvironmentEventMass
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro E hE
    by_cases hf : far E
    · rw [if_pos hf]
      have hm := (actualFiberMass_pos G P c C.activity C.activity_pos E).le
      have hsq : H * ((C.index : ℝ) / 112) ≤
          (M E - (C.index : ℝ)) ^ 2 := by
        exact le_trans (mul_le_mul_of_nonneg_left hf.1 (by positivity))
          (le_of_not_ge hf.2)
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hsq hm
    · rw [if_neg hf]
      have hm := (actualFiberMass_pos G P c C.activity C.activity_pos E).le
      simpa only [mul_zero] using mul_nonneg hm (sq_nonneg _)
  have hbetween := environment_conditionalMean_sq_le_variance G C P c
  have hs : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
  have hlower : (scaleDelta / 2) * (H * ((C.index : ℝ) / 112)) ≤ C.variance := by
    have hT : 0 < H * ((C.index : ℝ) / 112) := by
      dsimp [H]
      positivity
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hfar.le hT.le).trans (hsquare.trans hbetween)
  dsimp [H] at hlower
  nlinarith

lemma scaleGamma_lt_gamma0 : scaleGamma < scaleGamma0 := by
  have hp : 0 < scaleGamma0 := by norm_num [scaleGamma0, scaleCstar]
  exact (min_le_left (scaleGamma0 / 2) ((1 : ℝ) / 448)).trans_lt (by linarith)

lemma exists_scale_scalar_threshold :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ s : ℝ, S ≤ s →
      1 ≤ scaleGamma * s ∧
      12 * scaleCstar * Real.exp (-s / (25088 * scaleCstar)) ≤
        (scaleCb / (scaleCstar * s) * Real.exp (-(scaleGamma * s))) *
          (scaleDelta / 2) := by
  let α : ℝ := scaleGamma0 - scaleGamma
  have hα : 0 < α := by dsimp [α]; linarith [scaleGamma_lt_gamma0]
  have hlin : Filter.Tendsto (fun s : ℝ => α * s) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hα
  have hg0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hgcomp := hg0.comp hlin
  have hg : Filter.Tendsto (fun s : ℝ => s * Real.exp (-α * s)) Filter.atTop (𝓝 0) := by
    have ht := hgcomp.const_mul (1 / α)
    convert ht using 1
    · funext s
      simp [Function.comp_def]
      field_simp
    · simp
  let K : ℝ := 24 * scaleCstar ^ 2 / (scaleCb * scaleDelta)
  have hKg : Filter.Tendsto (fun s : ℝ => K * (s * Real.exp (-α * s))) Filter.atTop (𝓝 0) := by
    simpa using hg.const_mul K
  have hev : ∀ᶠ s : ℝ in Filter.atTop, K * (s * Real.exp (-α * s)) < 1 :=
    (tendsto_order.1 hKg).2 1 (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨a, ha⟩ := hev
  refine ⟨max 0 (max a (1 / scaleGamma)), le_max_left _ _, ?_⟩
  intro s hs
  have hs0 : 0 < s := by
    have hgpos := scaleGamma_pos
    have hsg : 1 / scaleGamma ≤ s := (le_max_right a _).trans (le_max_right 0 _ |>.trans hs)
    have : 0 < 1 / scaleGamma := by positivity
    linarith
  have hH : 1 ≤ scaleGamma * s := by
    have hsg : 1 / scaleGamma ≤ s :=
      (le_max_right a _).trans (le_max_right 0 _ |>.trans hs)
    simpa [mul_comm] using (div_le_iff₀ scaleGamma_pos).1 hsg
  refine ⟨hH, ?_⟩
  have hsmall := ha s ((le_max_left a (1 / scaleGamma)).trans
    ((le_max_right 0 (max a (1 / scaleGamma))).trans hs))
  have hden : 0 < scaleCb * scaleDelta := mul_pos scaleCb_pos scaleDelta_pos
  have hbase : 24 * scaleCstar ^ 2 * (s * Real.exp (-α * s)) ≤
      scaleCb * scaleDelta := by
    have hsmall' : (24 * scaleCstar ^ 2 * (s * Real.exp (-α * s))) /
        (scaleCb * scaleDelta) < 1 := by
      dsimp [K] at hsmall
      convert hsmall using 1 <;> ring
    have h := (div_lt_iff₀ hden).1 hsmall'
    nlinarith
  have hexp : Real.exp (-s / (25088 * scaleCstar)) =
      Real.exp (-α * s) * Real.exp (-(scaleGamma * s)) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [α, scaleGamma0]
    field_simp [show scaleCstar ≠ 0 by norm_num [scaleCstar]]
    ring
  rw [hexp]
  let q : ℝ := Real.exp (-(scaleGamma * s)) / (2 * scaleCstar * s)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hmul := mul_le_mul_of_nonneg_right hbase hq
  calc
    12 * scaleCstar * (Real.exp (-α * s) * Real.exp (-(scaleGamma * s))) =
        (24 * scaleCstar ^ 2 * (s * Real.exp (-α * s))) * q := by
          dsimp [q]
          field_simp
          ring
    _ ≤ (scaleCb * scaleDelta) * q := hmul
    _ = (scaleCb / (scaleCstar * s) * Real.exp (-(scaleGamma * s))) *
          (scaleDelta / 2) := by
          dsimp [q]
          field_simp

universe u

/-- The genuine finite-forest C.7 threshold theorem, with all conditioning
    performed on the original global canonical state. -/
theorem exists_appendixC7_varianceThreshold :
    ∃ threshold : ℝ, 0 ≤ threshold ∧
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G),
        C.activity < 27 → threshold ≤ C.variance →
          FirstRecoveryScaleAt C
            (scaleDelta * scaleGamma / 224) scaleCstar 1 scaleCstar := by
  obtain ⟨T, hT, hfloor⟩ := exists_uniform_activity_floor
  obtain ⟨S, hS, hscalar⟩ := exists_scale_scalar_threshold
  let threshold : ℝ := max T (scaleCstar * (S + 1) ^ 2)
  refine ⟨threshold, ?_, ?_⟩
  · dsimp [threshold]
    exact le_max_of_le_left hT
  intro V instV G C hz27 hvar
  classical
  have hzlo : (3 : ℝ) / 2 < C.activity :=
    hfloor G C hz27 ((le_max_left T (scaleCstar * (S + 1) ^ 2)).trans hvar)
  have h39 := C39_order_and_variance_lt (G := G) C hzlo hz27
  have hCstar : 0 < scaleCstar := by norm_num [scaleCstar]
  have hspos : (0 : ℝ) < C.index := by exact_mod_cast C.firstRecovery.index_pos
  have hthreshold : scaleCstar * (S + 1) ^ 2 ≤ C.variance :=
    (le_max_right T (scaleCstar * (S + 1) ^ 2)).trans hvar
  have hsq : scaleCstar * (S + 1) ^ 2 <
      scaleCstar * (C.index : ℝ) ^ 2 := hthreshold.trans_lt h39.2
  have hSindex : S ≤ (C.index : ℝ) := by
    have hSp : 0 < S + 1 := by linarith
    have hsquares : (S + 1) ^ 2 < (C.index : ℝ) ^ 2 := by
      nlinarith
    have : S + 1 < (C.index : ℝ) := by
      nlinarith [sq_nonneg ((C.index : ℝ) + (S + 1))]
    linarith
  have hnum := hscalar (C.index : ℝ) hSindex
  let P : FiniteBipartition G := finiteBipartitionOfForest G C.isForest
  obtain ⟨c, hopp⟩ := exists_reveal_side_opposite_occupation_half
    G P C.activity C.activity_pos
  have hopp' : (C.index : ℝ) / 2 ≤
      sideOccupationExpectation G P c.opposite C.activity C.activity_pos := by
    rw [← C.mean_eq_index]
    exact hopp
  have hlow := variance_quadratic_lower_of_scalar_bounds
    G C P c hopp' hzlo hz27 hnum.1 hnum.2
  have horderlow : (C.index : ℝ) ≤ (C.order : ℝ) := by
    rw [← C.mean_eq_index]
    exact hardCoreLaw_mean_le_order G C.activity C.activity_pos
  unfold FirstRecoveryScaleAt
  exact ⟨hlow, h39.2.le, by simpa using horderlow, h39.1.le⟩

/-- A selected finite C.7 threshold for universe `u`. -/
noncomputable def appendixC7VarianceThreshold : ℝ :=
  Classical.choose (exists_appendixC7_varianceThreshold.{u})

theorem appendixC7VarianceThreshold_spec :
    0 ≤ appendixC7VarianceThreshold.{u} ∧
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G),
        C.activity < 27 → appendixC7VarianceThreshold.{u} ≤ C.variance →
          FirstRecoveryScaleAt C
            (scaleDelta * scaleGamma / 224) scaleCstar 1 scaleCstar :=
  Classical.choose_spec (exists_appendixC7_varianceThreshold.{u})

/-- Concrete C.7 interface with definitionally explicit positive constants. -/
noncomputable def appendixC7FirstRecoveryScaleInterface :
    FirstRecoveryScaleInterface.{u} where
  cV := scaleDelta * scaleGamma / 224
  CV := scaleCstar
  cN := 1
  CN := scaleCstar
  varianceThreshold := appendixC7VarianceThreshold.{u}
  cV_pos := by positivity
  CV_pos := by norm_num [scaleCstar]
  cN_pos := by norm_num
  CN_pos := by norm_num [scaleCstar]
  varianceThreshold_nonneg := appendixC7VarianceThreshold_spec.{u} |>.1
  conclusion := appendixC7VarianceThreshold_spec.{u} |>.2

theorem appendixC7FirstRecoveryScaleInterface_nonempty :
    Nonempty FirstRecoveryScaleInterface.{u} :=
  ⟨appendixC7FirstRecoveryScaleInterface.{u}⟩

/-- Theorem C.7 in direct existential form. -/
theorem exists_appendixC7_firstRecoveryScaleInterface :
    Nonempty FirstRecoveryScaleInterface.{u} :=
  appendixC7FirstRecoveryScaleInterface_nonempty.{u}
