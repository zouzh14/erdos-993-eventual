import Erdos993.Forest.CanonicalLaw
import Erdos993.Forest.FirstRecovery

/-!
# Canonical hard-core activity

This module closes the elementary analytic gap left explicit in
`Forest.CanonicalLaw`.  The hard-core mean is represented by one rational
function of finite partition sums.  Its derivative is the variance divided by
activity, and it is strictly increasing whenever the graph has a vertex.  The
finite endpoint estimates then give the unique positive activity at every
first-recovery rank.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

universe u

variable {V : Type u} [Fintype V]

/-- Unnormalized first occupation moment of the hard-core partition sum. -/
def hardCoreFirstMomentSum (G : SimpleGraph V) (z : ℝ) : ℝ :=
  ∑ s : IndepFinset G, (s.val.card : ℝ) * z ^ s.val.card

/-- Unnormalized second occupation moment of the hard-core partition sum. -/
def hardCoreSecondMomentSum (G : SimpleGraph V) (z : ℝ) : ℝ :=
  ∑ s : IndepFinset G, (s.val.card : ℝ) ^ 2 * z ^ s.val.card

/-- The hard-core mean as a rational function, independent of a positivity
proof argument. -/
def hardCoreMean (G : SimpleGraph V) (z : ℝ) : ℝ :=
  hardCoreFirstMomentSum G z / independenceEval G z

/-- The hard-core variance as the corresponding rational second central
moment, independent of a positivity proof argument. -/
def hardCoreVariance (G : SimpleGraph V) (z : ℝ) : ℝ :=
  hardCoreSecondMomentSum G z / independenceEval G z - (hardCoreMean G z) ^ 2

/-- The structure-valued hard-core mean agrees with the rational finite-sum
function. -/
theorem hardCoreLaw_mean_eq_hardCoreMean (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean = hardCoreMean G z := by
  rw [hardCoreMean, hardCoreFirstMomentSum]
  calc
    (∑ s : IndepFinset G,
        (z ^ s.val.card / independenceEval G z) * (s.val.card : ℝ)) =
      ∑ s : IndepFinset G,
        ((s.val.card : ℝ) * z ^ s.val.card) / independenceEval G z := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
    _ = (∑ s : IndepFinset G, (s.val.card : ℝ) * z ^ s.val.card) /
        independenceEval G z := (Finset.sum_div ..).symm

/-- Auditable rational finite-sum formula for the tilted mean. -/
theorem hardCoreMean_eq_finite_sum (G : SimpleGraph V) (z : ℝ) :
    hardCoreMean G z =
      (∑ s : IndepFinset G, (s.val.card : ℝ) * z ^ s.val.card) /
        (∑ s : IndepFinset G, z ^ s.val.card) := by
  rw [hardCoreMean, hardCoreFirstMomentSum, independenceEval_eq_sum]

/-- The structure-valued second moment agrees with the rational finite-sum
second moment. -/
theorem hardCoreLaw_secondMoment_eq_ratio (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).secondMoment =
      hardCoreSecondMomentSum G z / independenceEval G z := by
  rw [hardCoreSecondMomentSum]
  calc
    (∑ s : IndepFinset G,
        (z ^ s.val.card / independenceEval G z) * (s.val.card : ℝ) ^ 2) =
      ∑ s : IndepFinset G,
        ((s.val.card : ℝ) ^ 2 * z ^ s.val.card) / independenceEval G z := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
    _ = (∑ s : IndepFinset G, (s.val.card : ℝ) ^ 2 * z ^ s.val.card) /
        independenceEval G z := (Finset.sum_div ..).symm

/-- The structure-valued hard-core variance agrees with the rational variance
function. -/
theorem hardCoreLaw_variance_eq_hardCoreVariance (G : SimpleGraph V)
    (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).variance = hardCoreVariance G z := by
  rw [FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    hardCoreVariance, hardCoreLaw_secondMoment_eq_ratio G z hz,
    hardCoreLaw_mean_eq_hardCoreMean G z hz]

/-- Auditable rational finite-sum formula for the tilted variance. -/
theorem hardCoreVariance_eq_finite_sum (G : SimpleGraph V) (z : ℝ) :
    hardCoreVariance G z =
      (∑ s : IndepFinset G, (s.val.card : ℝ) ^ 2 * z ^ s.val.card) /
          (∑ s : IndepFinset G, z ^ s.val.card) -
        ((∑ s : IndepFinset G, (s.val.card : ℝ) * z ^ s.val.card) /
          (∑ s : IndepFinset G, z ^ s.val.card)) ^ 2 := by
  rw [hardCoreVariance, hardCoreMean, hardCoreFirstMomentSum,
    hardCoreSecondMomentSum, independenceEval_eq_sum]

/-- Differentiating the partition sum produces the first moment divided by
activity. -/
theorem hasDerivAt_independenceEval (G : SimpleGraph V) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (independenceEval G) (hardCoreFirstMomentSum G z / z) z := by
  rw [show independenceEval G =
      (fun x : ℝ => ∑ s : IndepFinset G, x ^ s.val.card) by
        funext x
        exact independenceEval_eq_sum G x]
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ s : IndepFinset G, x ^ s.val.card)
      (∑ s : IndepFinset G, (s.val.card : ℝ) * z ^ (s.val.card - 1)) z := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun (s : IndepFinset G) _ =>
      hasDerivAt_pow s.val.card z)
  convert hsum using 1
  rw [hardCoreFirstMomentSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  push_cast
  by_cases hcard : s.val.card = 0
  · simp [hcard]
  · field_simp [hz.ne']
    rw [← pow_sub_one_mul hcard]
    ring

/-- Differentiating the unnormalized first moment produces the unnormalized
second moment divided by activity. -/
theorem hasDerivAt_hardCoreFirstMomentSum (G : SimpleGraph V) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (hardCoreFirstMomentSum G)
      (hardCoreSecondMomentSum G z / z) z := by
  change HasDerivAt
    (fun x : ℝ => ∑ s : IndepFinset G,
      (s.val.card : ℝ) * x ^ s.val.card)
    ((∑ s : IndepFinset G, (s.val.card : ℝ) ^ 2 * z ^ s.val.card) / z) z
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ s : IndepFinset G,
        (s.val.card : ℝ) * x ^ s.val.card)
      (∑ s : IndepFinset G,
        (s.val.card : ℝ) * ((s.val.card : ℝ) * z ^ (s.val.card - 1))) z := by
    exact HasDerivAt.fun_sum (u := Finset.univ) (fun (s : IndepFinset G) _ =>
      (hasDerivAt_pow s.val.card z).const_mul (s.val.card : ℝ))
  convert hsum using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  push_cast
  by_cases hcard : s.val.card = 0
  · simp [hcard]
  · field_simp [hz.ne']
    rw [← pow_sub_one_mul hcard]
    ring

/-- The rational hard-core mean is continuous at every positive activity. -/
theorem hardCoreMean_continuousAt (G : SimpleGraph V) {z : ℝ} (hz : 0 < z) :
    ContinuousAt (hardCoreMean G) z := by
  exact ((hasDerivAt_hardCoreFirstMomentSum G hz).fun_div
    (hasDerivAt_independenceEval G hz) (independenceEval_pos G hz).ne').continuousAt

/-- The rational hard-core mean is continuous on positive activities. -/
theorem hardCoreMean_continuousOn (G : SimpleGraph V) :
    ContinuousOn (hardCoreMean G) (Set.Ioi 0) := by
  intro z hz
  exact (hardCoreMean_continuousAt G hz).continuousWithinAt

/-- The exact fluctuation identity: the derivative of the hard-core mean at a
positive activity is variance divided by activity. -/
theorem hasDerivAt_hardCoreMean (G : SimpleGraph V) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (hardCoreMean G) (hardCoreVariance G z / z) z := by
  change HasDerivAt
    (fun x : ℝ => hardCoreFirstMomentSum G x / independenceEval G x)
    ((hardCoreSecondMomentSum G z / independenceEval G z -
      (hardCoreFirstMomentSum G z / independenceEval G z) ^ 2) / z) z
  have hZ := independenceEval_pos G hz
  convert (hasDerivAt_hardCoreFirstMomentSum G hz).fun_div
    (hasDerivAt_independenceEval G hz) hZ.ne' using 1 <;>
      field_simp <;> ring

/-- Named derivative equality form of the fluctuation identity. -/
theorem deriv_hardCoreMean_eq_variance_div (G : SimpleGraph V)
    {z : ℝ} (hz : 0 < z) :
    deriv (hardCoreMean G) z = hardCoreVariance G z / z :=
  (hasDerivAt_hardCoreMean G hz).deriv

/-- At every positive activity on a nonempty vertex type, the hard-core
variance is strictly positive.  The empty and singleton independent sets give
two distinct occupied-cardinality values of positive mass. -/
theorem hardCoreVariance_pos (G : SimpleGraph V) [Nonempty V]
    {z : ℝ} (hz : 0 < z) : 0 < hardCoreVariance G z := by
  let e : IndepFinset G := IndepFinset.empty G
  let v : V := Classical.choice ‹Nonempty V›
  let q : IndepFinset G :=
    ⟨{v}, by simp [SimpleGraph.isIndepSet_iff]⟩
  have heprob : 0 < (hardCoreLaw G z hz).probability e := by
    change 0 < z ^ e.val.card / independenceEval G z
    exact div_pos (pow_pos hz _) (independenceEval_pos G hz)
  have hqprob : 0 < (hardCoreLaw G z hz).probability q := by
    change 0 < z ^ q.val.card / independenceEval G z
    exact div_pos (pow_pos hz _) (independenceEval_pos G hz)
  have hene : ((e.val.card : ℝ) - (hardCoreLaw G z hz).mean) ≠ 0 ∨
      ((q.val.card : ℝ) - (hardCoreLaw G z hz).mean) ≠ 0 := by
    by_contra h
    push_neg at h
    have : (e.val.card : ℝ) = q.val.card := by linarith [h.1, h.2]
    simp [e, q] at this
  rw [← hardCoreLaw_variance_eq_hardCoreVariance G z hz,
    FiniteLatticeLaw.variance]
  apply Finset.sum_pos'
  · intro a ha
    exact mul_nonneg ((hardCoreLaw G z hz).probability_nonneg a) (sq_nonneg _)
  · rcases hene with he | hq
    · refine ⟨e, Finset.mem_univ _, mul_pos heprob ?_⟩
      exact sq_pos_of_ne_zero he
    · refine ⟨q, Finset.mem_univ _, mul_pos hqprob ?_⟩
      exact sq_pos_of_ne_zero hq

/-- The hard-core mean is strictly increasing on positive activities for every
nonempty finite graph. -/
theorem hardCoreMean_strictMonoOn (G : SimpleGraph V) [Nonempty V] :
    StrictMonoOn (hardCoreMean G) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0) (hardCoreMean_continuousOn G)
  intro z hz
  have hzpos : 0 < z := by simpa only [interior_Ioi] using hz
  rw [deriv_hardCoreMean_eq_variance_div G hzpos]
  exact div_pos (hardCoreVariance_pos G hzpos) hzpos

/-- At a first-recovery rank, the ambient vertex type is nonempty. -/
theorem nonempty_vertex_of_firstRecovery (G : SimpleGraph V) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) : Nonempty V := by
  have hsorder : s ≤ Fintype.card V := by
    have hcoeff : 0 < independenceCoeff G s := by
      have hc := hs.independence_center_pos
      change (0 : ℝ) < (independenceCoeff G s : ℝ) at hc
      exact_mod_cast hc
    rw [independenceCoeff] at hcoeff
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hcoeff
    have hcard : q.val.card = s := (Finset.mem_filter.mp hq).2
    rw [← hcard]
    exact Finset.card_le_univ q.val
  exact Fintype.card_pos_iff.mp (lt_of_lt_of_le hs.index_pos hsorder)

/-- The canonical target rank is strictly below the graph order. -/
theorem firstRecovery_lt_order (G : SimpleGraph V) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    s < Fintype.card V := by
  have hsucc : 0 < independenceCoeff G (s + 1) := by
    have hrise := hs.isRecovery.2
    have hnonneg : 0 ≤ independenceCoefficients G s := Nat.cast_nonneg _
    have hreal : 0 < independenceCoefficients G (s + 1) := lt_of_le_of_lt hnonneg hrise
    change (0 : ℝ) < (independenceCoeff G (s + 1) : ℝ) at hreal
    exact_mod_cast hreal
  rw [independenceCoeff] at hsucc
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hsucc
  have hcard : q.val.card = s + 1 := (Finset.mem_filter.mp hq).2
  have hle : s + 1 ≤ Fintype.card V := by
    rw [← hcard]
    exact Finset.card_le_univ q.val
  omega

/-- Explicit small-activity endpoint: at this positive activity the hard-core
mean is below any positive natural target rank. -/
theorem exists_pos_hardCoreMean_lt_nat (G : SimpleGraph V) (s : ℕ) (hs : 0 < s) :
    ∃ a : ℝ, 0 < a ∧ hardCoreMean G a < (s : ℝ) := by
  let n := Fintype.card (IndepFinset G)
  let a : ℝ := 1 / (2 * n * n)
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨IndepFinset.empty G⟩
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have haOne : a ≤ 1 := by
    dsimp [a]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (1 : ℝ) ≤ 2 * n * n := by nlinarith
    exact (div_le_one (by positivity : (0 : ℝ) < 2 * n * n)).2 hden
  have hnum : hardCoreFirstMomentSum G a < 1 := by
    calc
      hardCoreFirstMomentSum G a =
          ∑ q : IndepFinset G, (q.val.card : ℝ) * a ^ q.val.card := rfl
      _ ≤ ∑ q : IndepFinset G, (n : ℝ) * a := by
        apply Finset.sum_le_sum
        intro q hq
        by_cases hzero : q.val.card = 0
        · simp only [hzero, Nat.cast_zero, zero_mul]
          exact mul_nonneg (Nat.cast_nonneg _) ha.le
        · have hcard : (q.val.card : ℝ) ≤ n := by
            have hcardNat : q.val.card ≤ Fintype.card V := Finset.card_le_univ q.val
            have hVle : Fintype.card V ≤ n := by
              classical
              let f : V → IndepFinset G := fun v =>
                ⟨{v}, by simp [SimpleGraph.isIndepSet_iff]⟩
              exact Fintype.card_le_of_injective f (by
                intro v w hvw
                simpa [f] using congrArg Subtype.val hvw)
            exact_mod_cast le_trans hcardNat hVle
          have hpow : a ^ q.val.card ≤ a := by
            have hone : 1 ≤ q.val.card := Nat.one_le_iff_ne_zero.mpr hzero
            simpa using pow_le_pow_of_le_one ha.le haOne hone
          exact mul_le_mul hcard hpow (pow_nonneg ha.le _) (Nat.cast_nonneg _)
      _ = (n : ℝ) * ((n : ℝ) * a) := by
        simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
      _ ≤ 1 / 2 := by
        dsimp [a]
        have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
        rw [div_eq_mul_inv]
        field_simp
        nlinarith
      _ < 1 := by norm_num
  have hZge : 1 ≤ independenceEval G a := by
    rw [independenceEval_eq_sum]
    let e : IndepFinset G := IndepFinset.empty G
    calc
      1 = a ^ e.val.card := by simp [e]
      _ ≤ ∑ q : IndepFinset G, a ^ q.val.card := by
        have hnonneg : ∀ q ∈ (Finset.univ : Finset (IndepFinset G)),
            0 ≤ a ^ q.val.card := by
          intro q hq
          exact pow_nonneg ha.le _
        exact Finset.single_le_sum hnonneg (Finset.mem_univ e)
  refine ⟨a, ha, ?_⟩
  rw [hardCoreMean]
  have hmeanlt : hardCoreFirstMomentSum G a / independenceEval G a < 1 := by
    have hnumNonneg : 0 ≤ hardCoreFirstMomentSum G a := by
      rw [hardCoreFirstMomentSum]
      positivity
    have := div_le_self hnumNonneg hZge
    exact lt_of_le_of_lt this hnum
  exact lt_of_lt_of_le hmeanlt (by exact_mod_cast hs)

/-- Explicit large-activity endpoint: whenever rank `s+1` is realized, at a
large positive activity the hard-core mean is above `s`. -/
theorem exists_pos_nat_lt_hardCoreMean_of_succ_coefficient_pos
    (G : SimpleGraph V) (s : ℕ) (hsucc : 0 < independenceCoeff G (s + 1)) :
    ∃ b : ℝ, 0 < b ∧ (s : ℝ) < hardCoreMean G b := by
  rw [independenceCoeff] at hsucc
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hsucc
  have hqcard : q.val.card = s + 1 := (Finset.mem_filter.mp hq).2
  let n := Fintype.card (IndepFinset G)
  let b : ℝ := 2 * n * (s + 1)
  have hn : 0 < n := Fintype.card_pos_iff.mpr ⟨IndepFinset.empty G⟩
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hbOne : 1 ≤ b := by
    dsimp [b]
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsnonneg : (0 : ℝ) ≤ s := Nat.cast_nonneg _
    have hsreal : (1 : ℝ) ≤ s + 1 := by linarith
    nlinarith
  have hqterm : 0 < b ^ q.val.card := pow_pos hb _
  have hbadUpper :
      (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
        ((s : ℝ) - r.val.card) * b ^ r.val.card) ≤
        (n : ℝ) * (s : ℝ) * b ^ s := by
    calc
      _ ≤ ∑ _r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
          (s : ℝ) * b ^ s := by
        apply Finset.sum_le_sum
        intro r hr
        have hrs : r.val.card ≤ s := (Finset.mem_filter.mp hr).2
        have hdiff : (s : ℝ) - r.val.card ≤ s := by
          have : (0 : ℝ) ≤ r.val.card := Nat.cast_nonneg _
          linarith
        have hpow : b ^ r.val.card ≤ b ^ s := pow_le_pow_right₀ hbOne hrs
        have hdiffNonneg : (0 : ℝ) ≤ (s : ℝ) - r.val.card := by
          exact sub_nonneg.mpr (by exact_mod_cast hrs)
        have hsnonneg : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        exact mul_le_mul hdiff hpow (pow_nonneg hb.le _) hsnonneg
      _ = (((Finset.univ.filter
          (fun r : IndepFinset G => r.val.card ≤ s)).card : ℕ) : ℝ) *
            ((s : ℝ) * b ^ s) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) * ((s : ℝ) * b ^ s) := by
        gcongr
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (n : ℝ) * (s : ℝ) * b ^ s := by ring
  have hdistinguished :
      (n : ℝ) * (s : ℝ) * b ^ s <
        ((q.val.card : ℝ) - s) * b ^ q.val.card := by
    rw [hqcard, Nat.cast_add, Nat.cast_one]
    have hdiff : (s : ℝ) + 1 - (s : ℝ) = 1 := by ring
    rw [hdiff, one_mul, pow_succ]
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := Nat.cast_nonneg _
    have hbase : (n : ℝ) * (s : ℝ) < b := by
      dsimp [b]
      nlinarith
    have hp : 0 < b ^ s := pow_pos hb _
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      (mul_lt_mul_of_pos_right hbase hp)
  have hbadLtGood :
      (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
        ((s : ℝ) - r.val.card) * b ^ r.val.card) <
      ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
        ((r.val.card : ℝ) - s) * b ^ r.val.card := by
    refine lt_of_le_of_lt hbadUpper (lt_of_lt_of_le hdistinguished ?_)
    have hnonnegGood :
        ∀ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
          0 ≤ ((r.val.card : ℝ) - s) * b ^ r.val.card := by
      intro r hr
      have hrs : s < r.val.card := (Finset.mem_filter.mp hr).2
      exact mul_nonneg (sub_nonneg.mpr (by exact_mod_cast hrs.le))
        (pow_nonneg hb.le _)
    exact Finset.single_le_sum hnonnegGood
      (Finset.mem_filter.mpr ⟨Finset.mem_univ q, by omega⟩)
  have hratio : (s : ℝ) * independenceEval G b < hardCoreFirstMomentSum G b := by
    rw [independenceEval_eq_sum, hardCoreFirstMomentSum]
    have hpartition :
        ∑ r : IndepFinset G, b ^ r.val.card =
          (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
            b ^ r.val.card) +
          ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
            b ^ r.val.card := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun r : IndepFinset G => r.val.card ≤ s)
        (fun r : IndepFinset G => b ^ r.val.card)
      have hfilter :
          Finset.univ.filter (fun r : IndepFinset G => ¬ r.val.card ≤ s) =
            Finset.univ.filter (fun r : IndepFinset G => s < r.val.card) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      calc
        _ = (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
              b ^ r.val.card) +
            ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => ¬ r.val.card ≤ s),
              b ^ r.val.card := hsplit.symm
        _ = _ := by rw [hfilter]
    have hpartitionMoment :
        ∑ r : IndepFinset G, (r.val.card : ℝ) * b ^ r.val.card =
          (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
            (r.val.card : ℝ) * b ^ r.val.card) +
          ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
            (r.val.card : ℝ) * b ^ r.val.card := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun r : IndepFinset G => r.val.card ≤ s)
        (fun r : IndepFinset G => (r.val.card : ℝ) * b ^ r.val.card)
      have hfilter :
          Finset.univ.filter (fun r : IndepFinset G => ¬ r.val.card ≤ s) =
            Finset.univ.filter (fun r : IndepFinset G => s < r.val.card) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      calc
        _ = (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
              (r.val.card : ℝ) * b ^ r.val.card) +
            ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => ¬ r.val.card ≤ s),
              (r.val.card : ℝ) * b ^ r.val.card := hsplit.symm
        _ = _ := by rw [hfilter]
    rw [hpartition, hpartitionMoment]
    have hbadIdentity :
        (s : ℝ) *
            (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
              b ^ r.val.card) -
          (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
            (r.val.card : ℝ) * b ^ r.val.card) =
          ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => r.val.card ≤ s),
            ((s : ℝ) - r.val.card) * b ^ r.val.card := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hgoodIdentity :
        (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
            (r.val.card : ℝ) * b ^ r.val.card) -
          (s : ℝ) *
            (∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
              b ^ r.val.card) =
          ∑ r ∈ Finset.univ.filter (fun r : IndepFinset G => s < r.val.card),
            ((r.val.card : ℝ) - s) * b ^ r.val.card := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    linarith
  refine ⟨b, hb, ?_⟩
  rw [hardCoreMean, lt_div_iff₀ (independenceEval_pos G hb)]
  simpa [mul_comm] using hratio

/-- Existence and uniqueness of canonical activity at every first-recovery
rank.  This is an unconditional finite-graph theorem. -/
theorem existsUnique_pos_hardCoreMean_eq_firstRecovery
    (G : SimpleGraph V) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    ∃! z : ℝ, 0 < z ∧ hardCoreMean G z = (s : ℝ) := by
  letI : Nonempty V := nonempty_vertex_of_firstRecovery G hs
  obtain ⟨a, ha, hbelow⟩ := exists_pos_hardCoreMean_lt_nat G s hs.index_pos
  have hsucc : 0 < independenceCoeff G (s + 1) := by
    have hrise := hs.isRecovery.2
    have hnonneg : 0 ≤ independenceCoefficients G s := Nat.cast_nonneg _
    have hreal : 0 < independenceCoefficients G (s + 1) := lt_of_le_of_lt hnonneg hrise
    change (0 : ℝ) < (independenceCoeff G (s + 1) : ℝ) at hreal
    exact_mod_cast hreal
  obtain ⟨b, hb, habove⟩ :=
    exists_pos_nat_lt_hardCoreMean_of_succ_coefficient_pos G s hsucc
  have hab : a < b := by
    by_contra hba
    have hble : b ≤ a := le_of_not_gt hba
    have hmono := (hardCoreMean_strictMonoOn G).monotoneOn hb ha hble
    linarith
  have hIcc : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  obtain ⟨z, hzab, hzeq⟩ :=
    intermediate_value_Icc hab.le
      ((hardCoreMean_continuousOn G).mono hIcc)
      ⟨hbelow.le, habove.le⟩
  refine ⟨z, ⟨lt_of_lt_of_le ha hzab.1, hzeq⟩, ?_⟩
  intro y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hzy | hyz
  · have := (hardCoreMean_strictMonoOn G) hy.1 (lt_of_lt_of_le hy.1 hzy.le) hzy
    linarith [hy.2, hzeq]
  · have := (hardCoreMean_strictMonoOn G) (lt_of_lt_of_le ha hzab.1) hy.1 hyz
    linarith [hy.2, hzeq]

/-- Structure-valued form of canonical activity existence and uniqueness. -/
theorem existsUnique_pos_hardCoreLaw_mean_eq_firstRecovery
    (G : SimpleGraph V) {s : ℕ}
    (hs : IsFirstRecovery (independenceCoefficients G) s) :
    ∃! z : ℝ, ∃ hz : 0 < z,
      (hardCoreLaw G z hz).mean = (s : ℝ) := by
  obtain ⟨z, hz, huniq⟩ := existsUnique_pos_hardCoreMean_eq_firstRecovery G hs
  refine ⟨z, ⟨hz.1, ?_⟩, ?_⟩
  · simpa [hardCoreLaw_mean_eq_hardCoreMean G z hz.1] using hz.2
  · intro y hy
    obtain ⟨hypos, hymean⟩ := hy
    apply huniq y
    refine ⟨hypos, ?_⟩
    simpa [hardCoreLaw_mean_eq_hardCoreMean G y hypos] using hymean

/-- Direct construction of canonical first-recovery data from acyclicity and
coefficient nonunimodality.  No activity-existence premise is required. -/
theorem exists_canonicalFirstRecoveryState_of_nonunimodal
    (G : SimpleGraph V) (hforest : G.IsAcyclic)
    (hnonunimodal : ¬WeaklyUnimodal (independenceCoefficients G)) :
    Nonempty (CanonicalFirstRecoveryState G) := by
  obtain ⟨s, hs⟩ :=
    (exists_firstRecovery_iff (independenceCoefficients G)).2 hnonunimodal
  obtain ⟨z, hz, _⟩ := existsUnique_pos_hardCoreLaw_mean_eq_firstRecovery G hs
  obtain ⟨hzpos, hmean⟩ := hz
  exact ⟨{
    isForest := hforest
    index := s
    firstRecovery := hs
    activity := z
    activity_pos := hzpos
    mean_eq_index := hmean
  }⟩

/-- A selected canonical first-recovery state under exactly the forest and
nonunimodality hypotheses. -/
def canonicalFirstRecoveryStateOfNonunimodal
    (G : SimpleGraph V) (hforest : G.IsAcyclic)
    (hnonunimodal : ¬WeaklyUnimodal (independenceCoefficients G)) :
    CanonicalFirstRecoveryState G :=
  Classical.choice
    (exists_canonicalFirstRecoveryState_of_nonunimodal G hforest hnonunimodal)

end
end Forest
end Erdos993
