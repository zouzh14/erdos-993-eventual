import Erdos993.Forest.CanonicalActivityFloor
import Erdos993.Forest.ProbabilityAtMean
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Canonical exact-center decay (Appendix D.38--D.39)

This module derives the exponentially small probability at the canonical mean
for genuine finite forests.  The lower activity bound is supplied by
`CanonicalActivityFloor`, where it is proved from the actual low-activity CLT
and strict reverse Turán; it is not assumed here.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos993.Forest

noncomputable section

universe u

/-- Every finite acyclic simple graph admits the concrete finite bipartition
needed by the finite probability-at-the-mean estimate. -/
theorem nonempty_finiteBipartitionOfAcyclic
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) : Nonempty (FiniteBipartition G) := by
  classical
  obtain ⟨c, hc⟩ := hG.isBipartite
  let L : Finset V := Finset.univ.filter (fun v => c v = 0)
  let R : Finset V := Finset.univ.filter (fun v => c v ≠ 0)
  refine ⟨⟨L, R, ?_, ?_⟩⟩
  · constructor
    · simp [L, R, Set.disjoint_left]
    · intro v w hvw
      have hne : c v ≠ c w := by simpa using hc hvw
      by_cases hv : c v = 0
      · left
        constructor
        · change v ∈ L
          simp [L, hv]
        · change w ∈ R
          simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
          intro hw
          exact hne (hv.trans hw.symm)
      · right
        constructor
        · change v ∈ R
          simp [R, hv]
        · change w ∈ L
          simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
          apply Fin.ext
          have hvlt := (c v).isLt
          have hwlt := (c w).isLt
          simp only at hne ⊢
          omega
  · ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    by_cases hv : c v = 0
    · left
      simp [L, hv]
    · right
      simp [R, hv]

/-- A selected finite bipartition of an acyclic graph. -/
noncomputable def finiteBipartitionOfAcyclic
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) : FiniteBipartition G :=
  Classical.choice (nonempty_finiteBipartitionOfAcyclic hG)

namespace CanonicalCompactnessWrapper.CanonicalSequence

/-- Reindex a canonical sequence along a strictly increasing map. -/
noncomputable def subsequence (S : CanonicalSequence) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) : CanonicalSequence where
  order := S.order ∘ φ
  graph := fun n => S.graph (φ n)
  state := fun n => S.state (φ n)
  activity_lt := fun n => S.activity_lt (φ n)
  variance_pos := fun n => S.variance_pos (φ n)
  variance_tendsto := S.variance_tendsto.comp hφ.tendsto_atTop

@[simp] theorem subsequence_standardizedLaw (S : CanonicalSequence)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subsequence φ hφ).standardizedLaw n = S.standardizedLaw (φ n) := rfl

@[simp] theorem subsequence_characteristic (S : CanonicalSequence)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subsequence φ hφ).characteristic n = S.characteristic (φ n) := rfl

@[simp] theorem subsequence_zeroExtendedCharacteristic (S : CanonicalSequence)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (n : ℕ) :
    (S.subsequence φ hφ).zeroExtendedCharacteristic n =
      S.zeroExtendedCharacteristic (φ n) := rfl

lemma centeredMass_zero_eq_rankMass (S : CanonicalSequence) (n : ℕ) :
    S.centeredMass n 0 = (S.state n).law.rankMass (S.state n).index := by
  unfold centeredMass
  rw [if_pos]
  · simp
  · omega

/-- D.38: the canonical first-recovery index tends to infinity whenever the
canonical variance does. -/
lemma index_tendsto_atTop_D38 (S : CanonicalSequence) :
    Tendsto (fun n => ((S.state n).index : ℝ)) atTop atTop := by
  classical
  letI : ∀ n, DecidableEq (Fin (S.order n)) := fun n => Classical.decEq _
  letI : ∀ n, DecidableRel (S.graph n).Adj := fun n => Classical.decRel _
  rw [tendsto_atTop]
  intro b
  have hfloor := S.eventually_activity_gt_three_halves
  have hvar := tendsto_atTop.1 S.variance_tendsto
    ((3304 / 3 : ℝ) * (max b 0 + 1) ^ 2)
  filter_upwards [hfloor, hvar] with n hz hn
  have hupp := (C39_order_and_variance_lt (S.state n) hz (S.activity_lt n)).2
  have hi : 0 < ((S.state n).index : ℝ) := by
    exact_mod_cast (S.state n).firstRecovery.index_pos
  have hK : 0 < (3304 / 3 : ℝ) := by norm_num
  have hmax : 0 ≤ max b 0 + 1 := by positivity
  have hlt : max b 0 + 1 < ((S.state n).index : ℝ) := by
    by_contra hnot
    have hsle : ((S.state n).index : ℝ) ≤ max b 0 + 1 := le_of_not_gt hnot
    have hsq : ((S.state n).index : ℝ) ^ 2 ≤ (max b 0 + 1) ^ 2 := by
      rw [sq_le_sq₀ hi.le hmax]
      exact hsle
    have hmul := mul_le_mul_of_nonneg_left hsq hK.le
    nlinarith
  exact le_trans (le_max_left b 0)
    (by linarith : max b 0 ≤ ((S.state n).index : ℝ))

/-- D.38--D.39: the exact canonical-center mass, multiplied by the lattice
scale, tends to zero.  The lower activity bound is derived, not assumed. -/
theorem centeredMass_zero_scaled_tendsto_zero_D39 (S : CanonicalSequence) :
    Tendsto (fun n => Real.sqrt (S.V n) * S.centeredMass n 0)
      atTop (𝓝 0) := by
  classical
  letI : ∀ n, DecidableEq (Fin (S.order n)) := fun n => Classical.decEq _
  letI : ∀ n, DecidableRel (S.graph n).Adj := fun n => Classical.decRel _
  let K : ℝ := 3304 / 3
  let d : ℝ := 25088 * K
  let c : ℝ := 12 * K
  have hidx := S.index_tendsto_atTop_D38
  have hbase : Tendsto (fun x : ℝ => x * Real.exp (-x / d)) atTop (𝓝 0) := by
    have hd : 0 < d := by norm_num [d, K]
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (1 / d)
      (by positivity : 0 < 1 / d)
    simpa [Real.rpow_one, div_eq_mul_inv, mul_comm] using h
  have hdecay : Tendsto
      (fun n => c * Real.sqrt K *
        (((S.state n).index : ℝ) *
          Real.exp (-((S.state n).index : ℝ) / d))) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => c * Real.sqrt K) atTop
        (𝓝 (c * Real.sqrt K)) := tendsto_const_nhds
    simpa [Function.comp_def] using hc.mul (hbase.comp hidx)
  apply squeeze_zero'
    (f := fun n => Real.sqrt (S.V n) * S.centeredMass n 0)
    (g := fun n => c * Real.sqrt K *
      (((S.state n).index : ℝ) * Real.exp (-((S.state n).index : ℝ) / d)))
  · filter_upwards with n
    rw [S.centeredMass_zero_eq_rankMass n]
    exact mul_nonneg (Real.sqrt_nonneg _) ((S.state n).law.rankMass_nonneg _)
  · filter_upwards [S.eventually_activity_gt_three_halves] with n hz
    have hmass := ProbabilityAtMean.C44_probability_at_mean_finite (S.state n)
      (finiteBipartitionOfAcyclic (S.state n).isForest)
      (S.state n).firstRecovery.index_pos hz (S.activity_lt n)
    have hvar := (C39_order_and_variance_lt (S.state n) hz (S.activity_lt n)).2.le
    have hsqrt : Real.sqrt (S.V n) ≤ Real.sqrt K * ((S.state n).index : ℝ) := by
      have hi : 0 ≤ ((S.state n).index : ℝ) := by positivity
      have hK : 0 ≤ K := by norm_num [K]
      rw [← Real.sqrt_sq hi]
      rw [← Real.sqrt_mul hK]
      exact Real.sqrt_le_sqrt (by simpa [V, K, mul_assoc] using hvar)
    rw [S.centeredMass_zero_eq_rankMass n]
    have hmnon := (S.state n).law.rankMass_nonneg (S.state n).index
    change (S.state n).law.rankMass (S.state n).index ≤
      c * Real.exp (-((S.state n).index : ℝ) / d) at hmass
    have hleft : 0 ≤ Real.sqrt K * ((S.state n).index : ℝ) :=
      mul_nonneg (Real.sqrt_nonneg _) (by positivity)
    calc
      Real.sqrt (S.V n) * (S.state n).law.rankMass (S.state n).index ≤
          (Real.sqrt K * ((S.state n).index : ℝ)) *
            (S.state n).law.rankMass (S.state n).index :=
        mul_le_mul_of_nonneg_right hsqrt hmnon
      _ ≤ (Real.sqrt K * ((S.state n).index : ℝ)) *
          (c * Real.exp (-((S.state n).index : ℝ) / d)) :=
        mul_le_mul_of_nonneg_left hmass hleft
      _ = c * Real.sqrt K * (((S.state n).index : ℝ) *
          Real.exp (-((S.state n).index : ℝ) / d)) := by ring
  · exact hdecay

end CanonicalCompactnessWrapper.CanonicalSequence

end

end Erdos993.Forest
