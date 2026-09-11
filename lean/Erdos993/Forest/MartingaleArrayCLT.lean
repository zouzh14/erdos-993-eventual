import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Finite martingale-difference arrays on varying probability spaces

This module develops the finite-row layer needed before a martingale triangular-array CLT.
Rows may live on unrelated types, measures, and filtrations.  The final CLT is recorded only
as a proposition-valued specification; it is not asserted here.
-/

namespace Erdos993
namespace Forest
namespace MartingaleArrayCLT

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology ENNReal NNReal

universe u

/-- Data of a finite triangular array.  The dependent family `Omega` permits unrelated
sample types in different rows; `probability` and `filtration` also vary with the row. -/
structure ArrayData (Omega : Nat → Type u)
    [mOmega : ∀ n, MeasurableSpace (Omega n)] where
  probability : (n : Nat) → Measure (Omega n)
  rowLength : Nat → Nat
  filtration : (n : Nat) → Filtration Nat (mOmega n)
  increment : (n : Nat) → Fin (rowLength n) → Omega n → Real

variable {Omega : Nat → Type u} [mOmega : ∀ n, MeasurableSpace (Omega n)]

namespace ArrayData

variable (A : ArrayData Omega)

/-- Extend a finite row by zero to a natural-number-indexed process. -/
def paddedIncrement (n k : Nat) (omega : Omega n) : Real :=
  if hk : k < A.rowLength n then A.increment n ⟨k, hk⟩ omega else 0

/-- Partial sums of the zero-padded row. -/
def partialSum (n j : Nat) (omega : Omega n) : Real :=
  ∑ k ∈ Finset.range j, A.paddedIncrement n k omega

/-- Terminal sum of row `n`. -/
def rowSum (n : Nat) (omega : Omega n) : Real :=
  ∑ k, A.increment n k omega

/-- The terminal finite sum agrees with the zero-padded natural partial sum. -/
theorem rowSum_eq_partialSum_rowLength (n : Nat) :
    A.rowSum n = A.partialSum n (A.rowLength n) := by
  funext omega
  simp [rowSum, partialSum, paddedIncrement, ← Fin.sum_univ_eq_sum_range]

/-- The predictable conditional second moment of one increment. -/
def conditionalVariance (n : Nat) (k : Fin (A.rowLength n)) (omega : Omega n) : Real :=
  ((A.probability n)[fun x => (A.increment n k x) ^ 2 |
    A.filtration n k.val]) omega

/-- Predictable quadratic variation of one row. -/
def predictableQuadraticVariation (n : Nat) (omega : Omega n) : Real :=
  ∑ k, A.conditionalVariance n k omega

/-- Conditional Lindeberg sum at cutoff `epsilon`. -/
def conditionalLindebergSum (epsilon : Real) (n : Nat) (omega : Omega n) : Real :=
  ∑ k, ((A.probability n)[fun x =>
    if epsilon < |A.increment n k x| then (A.increment n k x) ^ 2 else 0 |
      A.filtration n k.val]) omega

/-- Square-integrable martingale-difference hypotheses, row by row. -/
structure IsMartingaleDifferenceArray : Prop where
  stronglyMeasurable : ∀ n k,
    StronglyMeasurable[A.filtration n (k.val + 1)] (A.increment n k)
  memLp_two : ∀ n k, MemLp (A.increment n k) 2 (A.probability n)
  condExp_zero : ∀ n k,
    (A.probability n)[A.increment n k | A.filtration n k.val] =ᵐ[A.probability n] 0

end ArrayData

/-! ## Varying-space convergence notions -/

/-- Convergence in probability for random variables whose source type and measure may vary
with the index.  This is the direct dependent-space analogue of `TendstoInMeasure` for a
constant real target. -/
def TendstoInProbabilityVarying {ι : Type*} (Omega' : ι → Type*)
    [∀ i, MeasurableSpace (Omega' i)] (mu : (i : ι) → Measure (Omega' i))
    (X : (i : ι) → Omega' i → Real) (l : Filter ι) (c : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    Tendsto (fun i => mu i {omega | epsilon ≤ |X i omega - c|}) l (nhds 0)

/-- Real-valued form of varying-space convergence in probability. -/
def TendstoInProbabilityVaryingReal {ι : Type*} (Omega' : ι → Type*)
    [∀ i, MeasurableSpace (Omega' i)] (mu : (i : ι) → Measure (Omega' i))
    (X : (i : ι) → Omega' i → Real) (l : Filter ι) (c : Real) : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    Tendsto (fun i => (mu i).real {omega | epsilon ≤ |X i omega - c|}) l (nhds 0)

/-- A uniformly bounded nonnegative family that converges to zero in probability on
varying probability spaces also converges to zero in `L¹`.  This is the elementary
bounded-convergence localization estimate: split the integral at `epsilon / 2` and use
an indicator of the exceptional level set. -/
theorem tendsto_integral_of_tendstoInProbabilityVarying_of_nonneg_bounded
    {Omega' : Nat → Type u} [∀ n, MeasurableSpace (Omega' n)]
    (mu : (n : Nat) → Measure (Omega' n)) [∀ n, IsProbabilityMeasure (mu n)]
    (X : (n : Nat) → Omega' n → Real) (C : Real)
    (hX : ∀ n, Measurable (X n))
    (h0 : ∀ n omega, 0 ≤ X n omega)
    (hC0 : 0 ≤ C)
    (hC : ∀ n omega, X n omega ≤ C)
    (hprob : TendstoInProbabilityVarying Omega' mu X atTop 0) :
    Tendsto (fun n => ∫ omega, X n omega ∂(mu n)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  let delta : Real := epsilon / 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    linarith
  have hpENN : Tendsto
      (fun i => mu i {omega | delta ≤ |X i omega|}) atTop (nhds 0) := by
    simpa only [sub_zero] using hprob delta hdelta
  have hpReal : Tendsto
      (fun n => (mu n).real {omega | delta ≤ |X n omega|}) atTop (nhds 0) := by
    simpa only [MeasureTheory.measureReal_def, Function.comp_apply] using
      (Filter.Tendsto.comp
        (show Tendsto ENNReal.toReal (nhds (0 : ENNReal)) (nhds (0 : Real)) from
          ENNReal.continuousAt_toReal ENNReal.zero_ne_top)
        hpENN)
  rw [Metric.tendsto_atTop] at hpReal
  have hden : 0 < 2 * (C + 1) := by positivity
  obtain ⟨N, hN⟩ := hpReal (epsilon / (2 * (C + 1))) (div_pos hepsilon hden)
  refine ⟨N, fun n hn => ?_⟩
  let s : Set (Omega' n) := {omega | delta ≤ |X n omega|}
  have hs : MeasurableSet s := measurableSet_le measurable_const (hX n).abs
  have hind : Integrable (s.indicator (fun _ => (1 : Real))) (mu n) :=
    (integrable_const (1 : Real)).indicator hs
  have hmajorInt : Integrable
      (fun omega => delta + C * s.indicator (fun _ => (1 : Real)) omega) (mu n) :=
    (integrable_const delta).add (hind.const_mul C)
  have hmajor : ∀ omega, X n omega ≤
      delta + C * s.indicator (fun _ => (1 : Real)) omega := by
    intro omega
    by_cases hmem : omega ∈ s
    · rw [Set.indicator_of_mem hmem]
      linarith [hC n omega]
    · simp only [Set.indicator, if_neg hmem]
      have hnot : ¬ delta ≤ |X n omega| := by
        simpa only [s, Set.mem_setOf_eq] using hmem
      have hlt : |X n omega| < delta := lt_of_not_ge hnot
      linarith [le_abs_self (X n omega)]
  have hi_nonneg : 0 ≤ ∫ omega, X n omega ∂(mu n) :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall (h0 n))
  have hi_upper : (∫ omega, X n omega ∂(mu n)) ≤
      ∫ omega, delta + C * s.indicator (fun _ => (1 : Real)) omega ∂(mu n) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall (h0 n)) hmajorInt
      (Filter.Eventually.of_forall hmajor)
  have hmajorEq :
      (∫ omega, delta + C * s.indicator (fun _ => (1 : Real)) omega ∂(mu n)) =
        delta + C * (mu n).real s := by
    rw [integral_add (integrable_const delta) (hind.const_mul C)]
    rw [integral_const, probReal_univ, one_smul, integral_const_mul]
    have hiind_eq :
        (∫ a, s.indicator (fun _ => (1 : Real)) a ∂(mu n)) = (mu n).real s := by
      simpa only [Pi.one_apply] using (integral_indicator_one (μ := mu n) hs)
    rw [hiind_eq]
  have hpdist := hN n hn
  have hp_nonneg : 0 ≤ (mu n).real {omega | delta ≤ |X n omega|} :=
    MeasureTheory.measureReal_nonneg
  have hp_lt_explicit : (mu n).real {omega | delta ≤ |X n omega|} <
      epsilon / (2 * (C + 1)) := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hp_nonneg] using hpdist
  have hp_s_nonneg : 0 ≤ (mu n).real s := MeasureTheory.measureReal_nonneg
  have hp_lt : (mu n).real s < epsilon / (2 * (C + 1)) := by
    simpa only [s] using hp_lt_explicit
  have hfinal : (∫ omega, X n omega ∂(mu n)) < epsilon := by
    rw [hmajorEq] at hi_upper
    dsimp [delta] at hi_upper
    have hC1 : C < C + 1 := by linarith
    have hmul : C * (mu n).real s < epsilon / 2 := by
      calc
        C * (mu n).real s ≤ (C + 1) * (mu n).real s := by
          exact mul_le_mul_of_nonneg_right (le_of_lt hC1) hp_s_nonneg
        _ < (C + 1) * (epsilon / (2 * (C + 1))) := by
          exact mul_lt_mul_of_pos_left hp_lt (by linarith)
        _ = epsilon / 2 := by field_simp
    linarith
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hi_nonneg] using hfinal

/-- Convergence in probability on varying spaces gives genuine convergence of the
expectations of the clipped deviations `min 1 |X-c|`.  This is the bounded localization
principle used below for predictable quadratic variation and conditional Lindeberg sums. -/
theorem tendsto_integral_min_one_abs_sub_of_tendstoInProbabilityVarying
    {Omega' : Nat → Type u} [∀ n, MeasurableSpace (Omega' n)]
    (mu : (n : Nat) → Measure (Omega' n)) [∀ n, IsProbabilityMeasure (mu n)]
    (X : (n : Nat) → Omega' n → Real) (c : Real)
    (hX : ∀ n, Measurable (X n))
    (hprob : TendstoInProbabilityVarying Omega' mu X atTop c) :
    Tendsto (fun n => ∫ omega, min 1 |X n omega - c| ∂(mu n)) atTop (nhds 0) := by
  apply tendsto_integral_of_tendstoInProbabilityVarying_of_nonneg_bounded
    mu (fun n omega => min 1 |X n omega - c|) 1
  · intro n
    exact measurable_const.min ((hX n).sub measurable_const).abs
  · intro n omega
    exact le_min zero_le_one (abs_nonneg _)
  · norm_num
  · intro n omega
    exact min_le_left _ _
  · intro epsilon hepsilon
    have hupper := hprob epsilon hepsilon
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper
      (Filter.Eventually.of_forall (fun _ => bot_le))
      (Filter.Eventually.of_forall (fun n => measure_mono (by
        intro omega homega
        change epsilon ≤ |min 1 |X n omega - c| - 0| at homega
        have hmin_nonneg : 0 ≤ min 1 |X n omega - c| :=
          le_min zero_le_one (abs_nonneg _)
        rw [sub_zero, abs_of_nonneg hmin_nonneg] at homega
        exact le_trans homega (min_le_right _ _))))

/-- Distributional convergence expressed directly at the level of mapped laws, allowing
unrelated source spaces and measures. -/
def TendstoInDistributionVarying {ι : Type*} (Omega' : ι → Type*)
    [∀ i, MeasurableSpace (Omega' i)] {E : Type*} [MeasurableSpace E]
    [TopologicalSpace (Measure E)] (mu : (i : ι) → Measure (Omega' i))
    (X : (i : ι) → Omega' i → E) (l : Filter ι) (nu : Measure E) : Prop :=
  Tendsto (fun i => (mu i).map (X i)) l (nhds nu) ∧
    ∀ i, AEMeasurable (X i) (mu i)

/-! ## Generic partial-sum martingale adapter -/

section PartialSums

variable {Omega0 : Type*} [MeasurableSpace Omega0]
variable {P : Measure Omega0} [IsProbabilityMeasure P]
variable {F : Filtration Nat ‹MeasurableSpace Omega0›}

/-- Partial sums in the convention where `D k` is revealed between times `k` and `k+1`. -/
def natPartialSum (D : Nat → Omega0 → Real) (n : Nat) (omega : Omega0) : Real :=
  ∑ k ∈ Finset.range n, D k omega

lemma natPartialSum_succ_sub (D : Nat → Omega0 → Real) (n : Nat) :
    natPartialSum D (n + 1) - natPartialSum D n = D n := by
  funext omega
  change (∑ k ∈ Finset.range (n + 1), D k omega) -
    (∑ k ∈ Finset.range n, D k omega) = D n omega
  rw [show n + 1 = n.succ by omega, Finset.sum_range_succ]
  ring

lemma natPartialSum_zero (D : Nat → Omega0 → Real) : natPartialSum D 0 = 0 := by
  funext omega
  simp [natPartialSum]

lemma natPartialSum_succ (D : Nat → Omega0 → Real) (n : Nat) :
    natPartialSum D (n + 1) = natPartialSum D n + D n := by
  funext omega
  change (∑ k ∈ Finset.range (n + 1), D k omega) =
    (∑ k ∈ Finset.range n, D k omega) + D n omega
  rw [show n + 1 = n.succ by omega, Finset.sum_range_succ]

/-- Increment measurability implies strong adaptation of the partial sums. -/
lemma natPartialSum_stronglyAdapted (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k)) :
    StronglyAdapted F (natPartialSum D) := by
  intro n
  induction n with
  | zero =>
      rw [natPartialSum_zero]
      exact stronglyMeasurable_const
  | succ n ih =>
      have ih' : StronglyMeasurable[F (n + 1)] (natPartialSum D n) :=
        ih.mono (F.mono (Nat.le_succ n))
      rw [natPartialSum_succ]
      exact ih'.add (hmeas n)

/-- `L2` increments have integrable finite partial sums. -/
lemma natPartialSum_integrable (D : Nat → Omega0 → Real)
    (hL2 : ∀ k, MemLp (D k) 2 P) (n : Nat) :
    Integrable (natPartialSum D n) P := by
  induction n with
  | zero =>
      rw [natPartialSum_zero]
      exact (MemLp.zero : MemLp (0 : Omega0 → Real) 2 P).integrable one_le_two
  | succ n ih =>
      rw [natPartialSum_succ]
      exact ih.add ((hL2 n).integrable one_le_two)

/-- Partial sums of square-integrable conditionally centered increments form a martingale. -/
theorem natPartialSum_martingale (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) :
    Martingale (natPartialSum D) F P := by
  apply martingale_of_condExp_sub_eq_zero_nat (natPartialSum_stronglyAdapted D hmeas)
    (natPartialSum_integrable D hL2)
  intro n
  rw [natPartialSum_succ_sub]
  exact hcentered n

/-- Earlier and later martingale differences are orthogonal in `L2`. -/
theorem integral_mul_eq_zero_of_lt (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0)
    {i j : Nat} (hij : i < j) :
    ∫ omega, D i omega * D j omega ∂P = 0 := by
  change (∫ omega, (D i * D j) omega ∂P) = 0
  have hi_meas : AEStronglyMeasurable[F j] (D i) P :=
    ((hmeas i).mono (F.mono (Nat.succ_le_iff.mpr hij))).aestronglyMeasurable
  have hij_int : Integrable (D i * D j) P :=
    (hL2 i).integrable_mul (hL2 j)
  have hj_int : Integrable (D j) P := (hL2 j).integrable one_le_two
  calc
    (∫ omega, (D i * D j) omega ∂P) =
        ∫ omega, P[D i * D j | F j] omega ∂P := by
          rw [integral_condExp (F.le j)]
    _ = ∫ omega, D i omega * P[D j | F j] omega ∂P :=
      integral_congr_ae
        (condExp_mul_of_aestronglyMeasurable_left hi_meas hij_int hj_int)
    _ = 0 := by
      rw [show (∫ omega, D i omega * P[D j | F j] omega ∂P) =
          ∫ _omega, (0 : Real) ∂P by
        apply integral_congr_ae
        filter_upwards [hcentered j] with omega hj
        simp [hj]]
      simp

/-- Every martingale difference has mean zero. -/
theorem integral_eq_zero (D : Nat → Omega0 → Real)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) (k : Nat) :
    ∫ omega, D k omega ∂P = 0 := by
  calc
    ∫ omega, D k omega ∂P = ∫ omega, P[D k | F k] omega ∂P := by
      rw [integral_condExp (F.le k)]
    _ = 0 := by
      rw [show (∫ omega, P[D k | F k] omega ∂P) = ∫ _omega, (0 : Real) ∂P by
        exact integral_congr_ae (hcentered k)]
      simp

/-- Every finite partial sum has mean zero. -/
theorem integral_natPartialSum_eq_zero (D : Nat → Omega0 → Real)
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) (n : Nat) :
    ∫ omega, natPartialSum D n omega ∂P = 0 := by
  induction n with
  | zero => rw [natPartialSum_zero]; simp
  | succ n ih =>
      rw [natPartialSum_succ]
      change ∫ omega, natPartialSum D n omega + D n omega ∂P = 0
      rw [integral_add (natPartialSum_integrable D hL2 n)
        ((hL2 n).integrable one_le_two), ih, integral_eq_zero D hcentered n, zero_add]

/-- A finite partial sum is in `L2`. -/
theorem natPartialSum_memLp_two (D : Nat → Omega0 → Real)
    (hL2 : ∀ k, MemLp (D k) 2 P) (n : Nat) :
    MemLp (natPartialSum D n) 2 P := by
  induction n with
  | zero =>
      rw [natPartialSum_zero]
      exact MemLp.zero
  | succ n ih =>
      rw [natPartialSum_succ]
      exact ih.add (hL2 n)

/-- Orthogonality extends from individual increments to a past partial sum. -/
theorem integral_partialSum_mul_eq_zero (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) (n : Nat) :
    ∫ omega, natPartialSum D n omega * D n omega ∂P = 0 := by
  have hterm : ∀ k ∈ Finset.range n,
      Integrable (fun omega => D k omega * D n omega) P := by
    intro k hk
    exact (hL2 k).integrable_mul (hL2 n)
  calc
    ∫ omega, natPartialSum D n omega * D n omega ∂P =
        ∫ omega, ∑ k ∈ Finset.range n, D k omega * D n omega ∂P := by
          apply integral_congr_ae
          filter_upwards [] with omega
          change (∑ k ∈ Finset.range n, D k omega) * D n omega = _
          rw [Finset.sum_mul]
    _ = ∑ k ∈ Finset.range n, ∫ omega, D k omega * D n omega ∂P :=
      integral_finset_sum (Finset.range n) hterm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      exact integral_mul_eq_zero_of_lt D hmeas hL2 hcentered (Finset.mem_range.mp hk)

/-- Pythagoras for the second moment of a finite martingale-difference sum. -/
theorem integral_natPartialSum_sq (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) (n : Nat) :
    ∫ omega, (natPartialSum D n omega) ^ 2 ∂P =
      ∑ k ∈ Finset.range n, ∫ omega, (D k omega) ^ 2 ∂P := by
  induction n with
  | zero => rw [natPartialSum_zero]; simp
  | succ n ih =>
      have hSsq : Integrable (fun omega => (natPartialSum D n omega) ^ 2) P :=
        (natPartialSum_memLp_two D hL2 n).integrable_sq
      have hDsq : Integrable (fun omega => (D n omega) ^ 2) P :=
        (hL2 n).integrable_sq
      have hcross : Integrable (fun omega => natPartialSum D n omega * D n omega) P :=
        (natPartialSum_memLp_two D hL2 n).integrable_mul (hL2 n)
      rw [natPartialSum_succ]
      calc
        ∫ omega, (natPartialSum D n omega + D n omega) ^ 2 ∂P =
            (∫ omega, (natPartialSum D n omega) ^ 2 ∂P) +
              2 * (∫ omega, natPartialSum D n omega * D n omega ∂P) +
              ∫ omega, (D n omega) ^ 2 ∂P := by
                calc
                  ∫ omega, (natPartialSum D n omega + D n omega) ^ 2 ∂P =
                      ∫ omega, (natPartialSum D n omega) ^ 2 +
                        2 * (natPartialSum D n omega * D n omega) +
                        (D n omega) ^ 2 ∂P := by
                          apply integral_congr_ae
                          filter_upwards [] with omega
                          ring
                  _ =
                      (∫ omega, (natPartialSum D n omega) ^ 2 +
                        2 * (natPartialSum D n omega * D n omega) ∂P) +
                        ∫ omega, (D n omega) ^ 2 ∂P := by
                          simpa only [Pi.add_apply] using
                            integral_add (hSsq.add (hcross.const_mul 2)) hDsq
                  _ = ((∫ omega, (natPartialSum D n omega) ^ 2 ∂P) +
                        ∫ omega, 2 * (natPartialSum D n omega * D n omega) ∂P) +
                        ∫ omega, (D n omega) ^ 2 ∂P := by
                          rw [integral_add hSsq (hcross.const_mul 2)]
                  _ = (∫ omega, (natPartialSum D n omega) ^ 2 ∂P) +
                        2 * (∫ omega, natPartialSum D n omega * D n omega ∂P) +
                        ∫ omega, (D n omega) ^ 2 ∂P := by
                          rw [integral_const_mul]
        _ = (∫ omega, (natPartialSum D n omega) ^ 2 ∂P) +
              ∫ omega, (D n omega) ^ 2 ∂P := by
                rw [integral_partialSum_mul_eq_zero D hmeas hL2 hcentered n]
                ring
        _ = ∑ k ∈ Finset.range (n + 1), ∫ omega, (D k omega) ^ 2 ∂P := by
              rw [ih, show n + 1 = n.succ by omega, Finset.sum_range_succ]

/-- Variance additivity for finite martingale-difference sums, without independence. -/
theorem variance_natPartialSum (D : Nat → Omega0 → Real)
    (hmeas : ∀ k, StronglyMeasurable[F (k + 1)] (D k))
    (hL2 : ∀ k, MemLp (D k) 2 P)
    (hcentered : ∀ k, P[D k | F k] =ᵐ[P] 0) (n : Nat) :
    Var[natPartialSum D n; P] = ∑ k ∈ Finset.range n, Var[D k; P] := by
  rw [variance_of_integral_eq_zero (natPartialSum_memLp_two D hL2 n).aemeasurable
      (integral_natPartialSum_eq_zero D hL2 hcentered n),
    integral_natPartialSum_sq D hmeas hL2 hcentered n]
  apply Finset.sum_congr rfl
  intro k hk
  rw [variance_of_integral_eq_zero (hL2 k).aemeasurable
    (integral_eq_zero D hcentered k)]

end PartialSums

/-! ## Conditional characteristic-function algebra and truncation -/

section CharacteristicFunctions

/-- The Fourier phase `exp(i t x)`. -/
def complexPhase (t x : Real) : Complex :=
  Complex.exp (Complex.I * (t * x : Real))

/-- The remainder after the quadratic Taylor polynomial of `exp(i t x)`. -/
def thirdOrderRemainder (t x : Real) : Complex :=
  complexPhase t x - 1 - Complex.I * (t * x : Real) + ((t * x) ^ 2 / 2 : Real)

lemma complexPhase_add (t x y : Real) :
    complexPhase t (x + y) = complexPhase t x * complexPhase t y := by
  rw [complexPhase, complexPhase, complexPhase, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact finite characteristic-function telescoping, before integration. -/
theorem complexPhase_natPartialSum_telescope {Omega0 : Type*} [MeasurableSpace Omega0]
    (D : Nat → Omega0 → Real) (t : Real) (N : Nat) (omega : Omega0) :
    complexPhase t (natPartialSum D N omega) - 1 =
      ∑ k ∈ Finset.range N,
        complexPhase t (natPartialSum D k omega) * (complexPhase t (D k omega) - 1) := by
  induction N with
  | zero =>
      rw [natPartialSum_zero]
      change complexPhase t 0 - 1 = 0
      simp [complexPhase]
  | succ N ih =>
      rw [natPartialSum_succ]
      change complexPhase t (natPartialSum D N omega + D N omega) - 1 = _
      rw [complexPhase_add, show N + 1 = N.succ by omega, Finset.sum_range_succ]
      rw [← ih]
      ring

/-- The quantitative third-order complex Taylor estimate available in mathlib. -/
theorem norm_exp_sub_quadratic_le {z : Complex} (hz : ‖z‖ ≤ 1) :
    ‖Complex.exp z - 1 - z - z ^ 2 / 2‖ ≤ (2 / 9 : Real) * ‖z‖ ^ 3 := by
  have h := Complex.exp_bound (x := z) hz (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  convert h using 1 <;> ring

/-- Small-increment truncation bound for the Fourier remainder. -/
theorem norm_thirdOrderRemainder_le (t x : Real) (hsmall : |t * x| ≤ 1) :
    ‖thirdOrderRemainder t x‖ ≤ (2 / 9 : Real) * |t * x| ^ 3 := by
  let z : Complex := Complex.I * (t * x : Real)
  have hz : ‖z‖ ≤ 1 := by
    simpa [z, norm_mul, Real.norm_eq_abs] using hsmall
  have hTaylor := norm_exp_sub_quadratic_le hz
  have hrem : thirdOrderRemainder t x =
      Complex.exp z - 1 - z - z ^ 2 / 2 := by
    dsimp [thirdOrderRemainder, complexPhase, z]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    norm_num
  rw [hrem]
  simpa [z, norm_mul, Real.norm_eq_abs] using hTaylor

variable {Omega0 : Type*} [mOmega0 : MeasurableSpace Omega0]
variable {P : Measure Omega0} [IsProbabilityMeasure P]
variable {F0 : MeasurableSpace Omega0} (hF0 : F0 ≤ mOmega0)

include hF0

/-- Predictable pull-out under the integral, for a real random scalar and a complex
predictable multiplier. -/
theorem integral_predictable_smul_condExp {f : Omega0 → Real} {Z : Omega0 → Complex}
    (hf : Integrable f P) (hfZ : Integrable (f • Z) P)
    (hZ : AEStronglyMeasurable[F0] Z P) :
    ∫ omega, f omega • Z omega ∂P =
      ∫ omega, P[f | F0] omega • Z omega ∂P := by
  change (∫ omega, (f • Z) omega ∂P) = _
  calc
    (∫ omega, (f • Z) omega ∂P) =
        ∫ omega, P[f • Z | F0] omega ∂P := by
          rw [integral_condExp hF0]
    _ = ∫ omega, P[f | F0] omega • Z omega ∂P :=
      integral_congr_ae
        (condExp_smul_of_aestronglyMeasurable_right hf hfZ hZ)

/-- Conditional centering kills every integrable predictable complex multiplier.  This is
the conditional-expectation input used by characteristic-function telescoping. -/
theorem integral_predictable_smul_eq_zero {f : Omega0 → Real} {Z : Omega0 → Complex}
    (hf : Integrable f P) (hfZ : Integrable (f • Z) P)
    (hZ : AEStronglyMeasurable[F0] Z P)
    (hcentered : P[f | F0] =ᵐ[P] 0) :
    ∫ omega, f omega • Z omega ∂P = 0 := by
  change (∫ omega, (f • Z) omega ∂P) = 0
  calc
    (∫ omega, (f • Z) omega ∂P) =
        ∫ omega, P[f • Z | F0] omega ∂P := by
          rw [integral_condExp hF0]
    _ = ∫ omega, P[f | F0] omega • Z omega ∂P :=
      integral_congr_ae
        (condExp_smul_of_aestronglyMeasurable_right hf hfZ hZ)
    _ = 0 := by
      rw [show (∫ omega, P[f | F0] omega • Z omega ∂P) =
          ∫ _omega, (0 : Complex) ∂P by
        apply integral_congr_ae
        filter_upwards [hcentered] with omega homega
        simp [homega]]
      simp

omit hF0

/-- For an `L2` martingale-difference sequence, the Fourier-linear term against the past
phase vanishes; no separate cancellation assumption is needed. -/
theorem integral_pastPhase_fourierLinear_eq_zero
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0)
    (t : Real) (k : Nat) :
    ∫ omega, complexPhase t (natPartialSum D k omega) *
      (Complex.I * (t * D k omega : Real)) ∂P = 0 := by
  let G : Omega0 → Complex := fun omega =>
    t • (complexPhase t (natPartialSum D k omega) * Complex.I)
  have hS : StronglyMeasurable[F k] (natPartialSum D k) :=
    natPartialSum_stronglyAdapted D hmeas k
  have hphase : AEStronglyMeasurable[F k]
      (fun omega => complexPhase t (natPartialSum D k omega)) P := by
    have hc : Continuous (complexPhase t) := by
      unfold complexPhase
      exact Complex.continuous_exp.comp
        (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    exact hc.comp_aestronglyMeasurable hS.aestronglyMeasurable
  have hG : AEStronglyMeasurable[F k] G P :=
    (hphase.mul_const Complex.I).const_smul t
  have hf : Integrable (D k) P := (hL2 k).integrable one_le_two
  have hprod : Integrable ((D k) • G) P := by
    apply Integrable.mono' (hf.norm.const_mul |t|)
    · have hfC : AEStronglyMeasurable (fun omega => (D k omega : Complex)) P :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
      have hGambient : AEStronglyMeasurable G P := hG.mono (F.le k)
      simpa [Pi.smul_apply, Algebra.smul_def] using hfC.mul hGambient
    · filter_upwards [] with omega
      have hphaseNorm : ‖complexPhase t (natPartialSum D k omega)‖ = 1 := by
        exact Complex.norm_exp_I_mul_ofReal (t * natPartialSum D k omega)
      simp [G, Real.norm_eq_abs, hphaseNorm]
      simpa [mul_comm]
  have hzero := integral_predictable_smul_eq_zero (P := P) (F0 := F k)
    (f := D k) (Z := G) (F.le k) hf hprod hG (hcentered k)
  calc
    ∫ omega, complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real)) ∂P =
      ∫ omega, D k omega • G omega ∂P := by
        apply integral_congr_ae
        filter_upwards [] with omega
        dsimp [G]
        push_cast
        ring
    _ = 0 := hzero

/-- The past Fourier phase may be pulled through the conditional second moment.  This is
the predictable-quadratic-variation replacement needed after characteristic telescoping. -/
theorem integral_pastPhase_sq_eq_condExp
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P) (t : Real) (k : Nat) :
    ∫ omega, (D k omega) ^ 2 • complexPhase t (natPartialSum D k omega) ∂P =
      ∫ omega, P[fun x => (D k x) ^ 2 | F k] omega •
        complexPhase t (natPartialSum D k omega) ∂P := by
  let Z : Omega0 → Complex := fun omega => complexPhase t (natPartialSum D k omega)
  have hS : StronglyMeasurable[F k] (natPartialSum D k) :=
    natPartialSum_stronglyAdapted D hmeas k
  have hc : Continuous (complexPhase t) := by
    unfold complexPhase
    exact Complex.continuous_exp.comp
      (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hZ : AEStronglyMeasurable[F k] Z P :=
    hc.comp_aestronglyMeasurable hS.aestronglyMeasurable
  have hf : Integrable (fun omega => (D k omega) ^ 2) P := (hL2 k).integrable_sq
  have hprod : Integrable ((fun omega => (D k omega) ^ 2) • Z) P := by
    apply Integrable.mono' hf.norm
    · change AEStronglyMeasurable
        (fun omega => (↑((D k omega) ^ 2) : Complex) * Z omega) P
      have hfC : AEStronglyMeasurable
          (fun omega => (↑((D k omega) ^ 2) : Complex)) P :=
        Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable
      have hZambient : AEStronglyMeasurable Z P := hZ.mono (F.le k)
      exact hfC.mul hZambient
    · filter_upwards [] with omega
      have hphaseNorm : ‖Z omega‖ = 1 := by
        exact Complex.norm_exp_I_mul_ofReal (t * natPartialSum D k omega)
      simp [Z, hphaseNorm]
  exact integral_predictable_smul_condExp (P := P) (F0 := F k)
    (f := fun omega => (D k omega) ^ 2) (Z := Z) (F.le k) hf hprod hZ

/-- Multiplicative presentation of `integral_pastPhase_sq_eq_condExp`, matching the
quadratic term in the characteristic-function estimate. -/
theorem integral_pastPhase_mul_sq_eq_condExp
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P) (t : Real) (k : Nat) :
    ∫ omega, complexPhase t (natPartialSum D k omega) *
        ((D k omega) ^ 2 : Real) ∂P =
      ∫ omega, complexPhase t (natPartialSum D k omega) *
        (P[fun x => (D k x) ^ 2 | F k] omega : Real) ∂P := by
  calc
    _ = ∫ omega, (D k omega) ^ 2 •
        complexPhase t (natPartialSum D k omega) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with omega
          simp [Algebra.smul_def, mul_comm]
    _ = ∫ omega, P[fun x => (D k x) ^ 2 | F k] omega •
        complexPhase t (natPartialSum D k omega) ∂P :=
          integral_pastPhase_sq_eq_condExp (P := P) D hmeas hL2 t k
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with omega
      simp [Algebra.smul_def, mul_comm]

omit hF0

/-- One-step integrated quadratic Taylor estimate.  Its cancellation hypothesis is the
Fourier-linear instance of `integral_predictable_smul_eq_zero` after an elementary complex
algebra conversion. -/
theorem conditionalCharacteristicStepEstimate
    (f : Omega0 → Real) (Z : Omega0 → Complex) (t : Real)
    (hlinear : ∫ omega, Z omega * (Complex.I * (t * f omega : Real)) ∂P = 0)
    (hremProd : Integrable (fun omega => Z omega * thirdOrderRemainder t (f omega)) P)
    (hlinearProd : Integrable (fun omega =>
      Z omega * (Complex.I * (t * f omega : Real))) P)
    (hremNorm : Integrable (fun omega => ‖thirdOrderRemainder t (f omega)‖) P)
    (hZnorm : ∀ᵐ omega ∂P, ‖Z omega‖ ≤ 1) :
    ‖∫ omega, Z omega *
        (complexPhase t (f omega) - 1 + ((t * f omega) ^ 2 / 2 : Real)) ∂P‖ ≤
      ∫ omega, ‖thirdOrderRemainder t (f omega)‖ ∂P := by
  have heq : (∫ omega, Z omega *
        (complexPhase t (f omega) - 1 + ((t * f omega) ^ 2 / 2 : Real)) ∂P) =
      ∫ omega, Z omega * thirdOrderRemainder t (f omega) ∂P := by
    calc
      _ = ∫ omega, Z omega * thirdOrderRemainder t (f omega) +
          Z omega * (Complex.I * (t * f omega : Real)) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with omega
            simp only [thirdOrderRemainder]
            ring
      _ = (∫ omega, Z omega * thirdOrderRemainder t (f omega) ∂P) +
          ∫ omega, Z omega * (Complex.I * (t * f omega : Real)) ∂P := by
            rw [integral_add hremProd hlinearProd]
      _ = _ := by rw [hlinear, add_zero]
  rw [heq]
  apply norm_integral_le_of_norm_le hremNorm
  filter_upwards [hZnorm] with omega hnorm
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hnorm

/-- Finite conditional characteristic-function telescoping/truncation estimate.  The
multiplier at step `k` is the past phase `exp(i t S_k)`, so the hypotheses `hlinear` are
exactly the Fourier-linear cancellations delivered by conditional centering.  The theorem
combines all one-step quadratic Taylor errors, while the preceding pointwise telescope
identifies the uncorrected part with the terminal characteristic function. -/
theorem conditionalCharacteristicTelescopeEstimate
    (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hlinear : ∀ k ∈ Finset.range N,
      ∫ omega, complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real)) ∂P = 0)
    (hremProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        thirdOrderRemainder t (D k omega)) P)
    (hlinearProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real))) P)
    (hremNorm : ∀ k ∈ Finset.range N,
      Integrable (fun omega => ‖thirdOrderRemainder t (D k omega)‖) P) :
    ‖∑ k ∈ Finset.range N, ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          (complexPhase t (D k omega) - 1 + ((t * D k omega) ^ 2 / 2 : Real)) ∂P‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  calc
    ‖∑ k ∈ Finset.range N, ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          (complexPhase t (D k omega) - 1 + ((t * D k omega) ^ 2 / 2 : Real)) ∂P‖ ≤
      ∑ k ∈ Finset.range N, ‖∫ omega,
        complexPhase t (natPartialSum D k omega) *
          (complexPhase t (D k omega) - 1 + ((t * D k omega) ^ 2 / 2 : Real)) ∂P‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
      apply Finset.sum_le_sum
      intro k hk
      apply conditionalCharacteristicStepEstimate (P := P)
        (f := D k) (Z := fun omega => complexPhase t (natPartialSum D k omega)) (t := t)
        (hlinear k hk) (hremProd k hk) (hlinearProd k hk) (hremNorm k hk)
      filter_upwards [] with omega
      exact le_of_eq (Complex.norm_exp_I_mul_ofReal (t * natPartialSum D k omega))

/-- The finite truncation estimate specialized to an actual martingale-difference sequence;
the Fourier-linear cancellations are derived from adaptedness, `L2`, and conditional
centering rather than supplied as hypotheses. -/
theorem conditionalCharacteristicTelescopeEstimate_of_martingaleDifference
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0)
    (hremProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        thirdOrderRemainder t (D k omega)) P)
    (hlinearProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real))) P)
    (hremNorm : ∀ k ∈ Finset.range N,
      Integrable (fun omega => ‖thirdOrderRemainder t (D k omega)‖) P) :
    ‖∑ k ∈ Finset.range N, ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          (complexPhase t (D k omega) - 1 + ((t * D k omega) ^ 2 / 2 : Real)) ∂P‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  apply conditionalCharacteristicTelescopeEstimate (P := P) D t N
  · intro k _hk
    exact integral_pastPhase_fourierLinear_eq_zero (P := P) D hmeas hL2 hcentered t k
  · exact hremProd
  · exact hlinearProd
  · exact hremNorm

/-- Terminal integrated characteristic-function estimate for a martingale-difference
sequence.  Unlike the one-step-sum formulation, the first term here is explicitly the
terminal characteristic-function increment supplied by the exact telescope. -/
theorem terminalCharacteristicFunctionEstimate_of_martingaleDifference
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0)
    (hphaseDiff : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (complexPhase t (D k omega) - 1)) P)
    (hquad : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        ((t * D k omega) ^ 2 / 2 : Real)) P)
    (hremProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        thirdOrderRemainder t (D k omega)) P)
    (hlinearProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real))) P)
    (hremNorm : ∀ k ∈ Finset.range N,
      Integrable (fun omega => ‖thirdOrderRemainder t (D k omega)‖) P) :
    ‖(∫ omega, complexPhase t (natPartialSum D N omega) - 1 ∂P) +
        ∑ k ∈ Finset.range N, ∫ omega,
          complexPhase t (natPartialSum D k omega) *
            ((t * D k omega) ^ 2 / 2 : Real) ∂P‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  have htelescope :
      (∫ omega, complexPhase t (natPartialSum D N omega) - 1 ∂P) =
        ∑ k ∈ Finset.range N, ∫ omega,
          complexPhase t (natPartialSum D k omega) *
            (complexPhase t (D k omega) - 1) ∂P := by
    calc
      _ = ∫ omega, ∑ k ∈ Finset.range N,
          complexPhase t (natPartialSum D k omega) *
            (complexPhase t (D k omega) - 1) ∂P := by
          apply integral_congr_ae
          filter_upwards [] with omega
          exact complexPhase_natPartialSum_telescope D t N omega
      _ = _ := integral_finset_sum (Finset.range N) hphaseDiff
  have hcombine :
      (∫ omega, complexPhase t (natPartialSum D N omega) - 1 ∂P) +
          ∑ k ∈ Finset.range N, ∫ omega,
            complexPhase t (natPartialSum D k omega) *
              ((t * D k omega) ^ 2 / 2 : Real) ∂P =
        ∑ k ∈ Finset.range N, ∫ omega,
          complexPhase t (natPartialSum D k omega) *
            (complexPhase t (D k omega) - 1 +
              ((t * D k omega) ^ 2 / 2 : Real)) ∂P := by
    rw [htelescope, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← integral_add (hphaseDiff k hk) (hquad k hk)]
    apply integral_congr_ae
    filter_upwards [] with omega
    ring
  rw [hcombine]
  exact conditionalCharacteristicTelescopeEstimate_of_martingaleDifference
    (P := P) D t N hmeas hL2 hcentered hremProd hlinearProd hremNorm

/-- The terminal estimate in the standard factored characteristic-function form:
`E exp(i t S_N) - 1` plus `(t²/2)` times the Fourier-weighted square sum. -/
theorem terminalCharacteristicFunctionEstimate_factored
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0)
    (hterminalPhase : Integrable
      (fun omega => complexPhase t (natPartialSum D N omega)) P)
    (hphaseDiff : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (complexPhase t (D k omega) - 1)) P)
    (hsquarePhase : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        ((D k omega) ^ 2 : Real)) P)
    (hremProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        thirdOrderRemainder t (D k omega)) P)
    (hlinearProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real))) P)
    (hremNorm : ∀ k ∈ Finset.range N,
      Integrable (fun omega => ‖thirdOrderRemainder t (D k omega)‖) P) :
    ‖(∫ omega, complexPhase t (natPartialSum D N omega) ∂P) - 1 +
        (((t ^ 2 / 2 : Real) : Complex) *
          ∑ k ∈ Finset.range N, ∫ omega,
            complexPhase t (natPartialSum D k omega) *
              ((D k omega) ^ 2 : Real) ∂P)‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  have hquad : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        ((t * D k omega) ^ 2 / 2 : Real)) P := by
    intro k hk
    have h := (hsquarePhase k hk).const_mul (((t ^ 2 / 2 : Real) : Complex))
    apply h.congr
    filter_upwards [] with omega
    push_cast
    ring
  have hfirst :
      (∫ omega, complexPhase t (natPartialSum D N omega) ∂P) - 1 =
        ∫ omega, complexPhase t (natPartialSum D N omega) - 1 ∂P := by
    rw [integral_sub hterminalPhase (integrable_const (1 : Complex))]
    simp
  have hsecond :
      (((t ^ 2 / 2 : Real) : Complex) *
          ∑ k ∈ Finset.range N, ∫ omega,
            complexPhase t (natPartialSum D k omega) *
              ((D k omega) ^ 2 : Real) ∂P) =
        ∑ k ∈ Finset.range N, ∫ omega,
          complexPhase t (natPartialSum D k omega) *
            ((t * D k omega) ^ 2 / 2 : Real) ∂P := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    calc
      (((t ^ 2 / 2 : Real) : Complex) *
          ∫ omega, complexPhase t (natPartialSum D k omega) *
            ((D k omega) ^ 2 : Real) ∂P) =
          ∫ omega, ((t ^ 2 / 2 : Real) : Complex) *
            (complexPhase t (natPartialSum D k omega) *
              ((D k omega) ^ 2 : Real)) ∂P := by
            symm
            exact integral_const_mul _ _
      _ = ∫ omega, complexPhase t (natPartialSum D k omega) *
          ((t * D k omega) ^ 2 / 2 : Real) ∂P := by
            apply integral_congr_ae
            filter_upwards [] with omega
            push_cast
            ring
  rw [hfirst, hsecond]
  exact terminalCharacteristicFunctionEstimate_of_martingaleDifference
    (P := P) D t N hmeas hL2 hcentered hphaseDiff hquad hremProd hlinearProd hremNorm

/-- The Fourier phase is continuous as a function of its real argument. -/
lemma continuous_complexPhase (t : Real) : Continuous (complexPhase t) := by
  unfold complexPhase
  fun_prop

/-- A Fourier phase composed with an a.e. strongly measurable real random variable is
integrable on a probability space. -/
lemma integrable_complexPhase_comp {f : Omega0 → Real}
    (hf : AEStronglyMeasurable[mOmega0] f P) (t : Real) :
    Integrable (fun omega => complexPhase t (f omega)) P := by
  apply Integrable.mono' (integrable_const (1 : Real))
  · exact (continuous_complexPhase t).comp_aestronglyMeasurable hf
  · filter_upwards [] with omega
    exact le_of_eq (Complex.norm_exp_I_mul_ofReal (t * f omega))

omit [IsProbabilityMeasure P] in
/-- Multiplication by a Fourier phase preserves integrability. -/
lemma integrable_complexPhase_mul {f : Omega0 → Real} {g : Omega0 → Complex}
    (hf : AEStronglyMeasurable[mOmega0] f P) (hg : Integrable g P) (t : Real) :
    Integrable (fun omega => complexPhase t (f omega) * g omega) P := by
  apply Integrable.mono' hg.norm
  · exact ((continuous_complexPhase t).comp_aestronglyMeasurable hf).mul
      hg.aestronglyMeasurable
  · filter_upwards [] with omega
    rw [norm_mul, show ‖complexPhase t (f omega)‖ = 1 by
      exact Complex.norm_exp_I_mul_ofReal (t * f omega), one_mul]

/-- All integrability side conditions of the factored terminal estimate follow from `L2`.
This theorem is the finite-row truncation reduction with no extra analytic hypotheses. -/
theorem terminalCharacteristicFunctionEstimate_factored_auto
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0) :
    ‖(∫ omega, complexPhase t (natPartialSum D N omega) ∂P) - 1 +
        (((t ^ 2 / 2 : Real) : Complex) *
          ∑ k ∈ Finset.range N, ∫ omega,
            complexPhase t (natPartialSum D k omega) *
              ((D k omega) ^ 2 : Real) ∂P)‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  have hpartial : ∀ k, AEStronglyMeasurable (natPartialSum D k) P := fun k =>
    (natPartialSum_stronglyAdapted D hmeas k).aestronglyMeasurable.mono (F.le k)
  have hD : ∀ k, Integrable (D k) P := fun k =>
    (hL2 k).integrable one_le_two
  have hDsq : ∀ k, Integrable (fun omega => (D k omega) ^ 2) P := fun k =>
    (hL2 k).integrable_sq
  have hterminalPhase : Integrable
      (fun omega => complexPhase t (natPartialSum D N omega)) P :=
    integrable_complexPhase_comp (P := P) (hpartial N) t
  have hphaseDiff : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (complexPhase t (D k omega) - 1)) P := by
    intro k _hk
    apply integrable_complexPhase_mul (P := P) (hpartial k)
    exact (integrable_complexPhase_comp (P := P) (hD k).aestronglyMeasurable t).sub
      (integrable_const (1 : Complex))
  have hsquarePhase : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        ((D k omega) ^ 2 : Real)) P := by
    intro k _hk
    exact integrable_complexPhase_mul (P := P) (hpartial k) (hDsq k).ofReal t
  have hlinear : ∀ k, Integrable (fun omega =>
      Complex.I * (t * D k omega : Real)) P := by
    intro k
    have hreal : Integrable (fun omega => t * D k omega) P := (hD k).const_mul t
    exact hreal.ofReal.const_mul Complex.I
  have hquad : ∀ k, Integrable (fun omega =>
      (((t * D k omega) ^ 2 / 2 : Real) : Complex)) P := by
    intro k
    have hreal : Integrable (fun omega => (t ^ 2 / 2) * (D k omega) ^ 2) P :=
      (hDsq k).const_mul (t ^ 2 / 2)
    apply hreal.ofReal.congr
    filter_upwards [] with omega
    push_cast
    ring_nf
    rfl
  have hrem : ∀ k, Integrable (fun omega => thirdOrderRemainder t (D k omega)) P := by
    intro k
    have hphase := integrable_complexPhase_comp (P := P)
      (hD k).aestronglyMeasurable t
    simpa only [thirdOrderRemainder] using
      ((hphase.sub (integrable_const (1 : Complex))).sub (hlinear k)).add (hquad k)
  have hremProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        thirdOrderRemainder t (D k omega)) P := by
    intro k _hk
    exact integrable_complexPhase_mul (P := P) (hpartial k) (hrem k) t
  have hlinearProd : ∀ k ∈ Finset.range N,
      Integrable (fun omega => complexPhase t (natPartialSum D k omega) *
        (Complex.I * (t * D k omega : Real))) P := by
    intro k _hk
    exact integrable_complexPhase_mul (P := P) (hpartial k) (hlinear k) t
  have hremNorm : ∀ k ∈ Finset.range N,
      Integrable (fun omega => ‖thirdOrderRemainder t (D k omega)‖) P := by
    intro k _hk
    exact (hrem k).norm
  exact terminalCharacteristicFunctionEstimate_factored
    (P := P) D t N hmeas hL2 hcentered hterminalPhase hphaseDiff hsquarePhase
      hremProd hlinearProd hremNorm

/-- The automatic terminal estimate after replacing each square by its predictable
conditional second moment. -/
theorem terminalCharacteristicFunctionEstimate_predictable
    {F : Filtration Nat mOmega0} (D : Nat → Omega0 → Real) (t : Real) (N : Nat)
    (hmeas : ∀ j, StronglyMeasurable[F (j + 1)] (D j))
    (hL2 : ∀ j, MemLp (D j) 2 P)
    (hcentered : ∀ j, P[D j | F j] =ᵐ[P] 0) :
    ‖(∫ omega, complexPhase t (natPartialSum D N omega) ∂P) - 1 +
        (((t ^ 2 / 2 : Real) : Complex) *
          ∑ k ∈ Finset.range N, ∫ omega,
            complexPhase t (natPartialSum D k omega) *
              (P[fun x => (D k x) ^ 2 | F k] omega : Real) ∂P)‖ ≤
      ∑ k ∈ Finset.range N, ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂P := by
  have hsums :
      (∑ k ∈ Finset.range N, ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          ((D k omega) ^ 2 : Real) ∂P) =
      ∑ k ∈ Finset.range N, ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          (P[fun x => (D k x) ^ 2 | F k] omega : Real) ∂P := by
    apply Finset.sum_congr rfl
    intro k _hk
    exact integral_pastPhase_mul_sq_eq_condExp (P := P) D hmeas hL2 t k
  rw [← hsums]
  exact terminalCharacteristicFunctionEstimate_factored_auto
    (P := P) D t N hmeas hL2 hcentered

end CharacteristicFunctions

/-! ## The finite rows supply the generic adapter -/

namespace ArrayData

variable (A : ArrayData Omega) [∀ n, IsProbabilityMeasure (A.probability n)]

lemma paddedIncrement_stronglyMeasurable (hA : A.IsMartingaleDifferenceArray)
    (n k : Nat) :
    StronglyMeasurable[A.filtration n (k + 1)] (A.paddedIncrement n k) := by
  unfold ArrayData.paddedIncrement
  split_ifs with hk
  · exact hA.stronglyMeasurable n ⟨k, hk⟩
  · exact stronglyMeasurable_const

lemma paddedIncrement_memLp_two (hA : A.IsMartingaleDifferenceArray) (n k : Nat) :
    MemLp (A.paddedIncrement n k) 2 (A.probability n) := by
  unfold ArrayData.paddedIncrement
  split_ifs with hk
  · exact hA.memLp_two n ⟨k, hk⟩
  · exact (MemLp.zero : MemLp (0 : Omega n → Real) 2 (A.probability n))

lemma paddedIncrement_condExp_zero (hA : A.IsMartingaleDifferenceArray) (n k : Nat) :
    (A.probability n)[A.paddedIncrement n k | A.filtration n k] =ᵐ[A.probability n] 0 := by
  unfold ArrayData.paddedIncrement
  split_ifs with hk
  · exact hA.condExp_zero n ⟨k, hk⟩
  · change (A.probability n)[(0 : Omega n → Real) | A.filtration n k] =ᵐ[A.probability n] 0
    rw [condExp_zero]

/-- Every finite row, extended by zero, has a canonical natural-indexed partial-sum
martingale. -/
theorem rowPartialSum_martingale (hA : A.IsMartingaleDifferenceArray) (n : Nat) :
    Martingale (A.partialSum n) (A.filtration n) (A.probability n) := by
  exact natPartialSum_martingale (A.paddedIncrement n)
    (A.paddedIncrement_stronglyMeasurable hA n)
    (A.paddedIncrement_memLp_two hA n)
    (A.paddedIncrement_condExp_zero hA n)

/-- The automatic predictable terminal estimate specialized to a finite row.  In
particular, every measurability and integrability premise is derived from
`IsMartingaleDifferenceArray`. -/
theorem terminalCharacteristicFunctionEstimate_row
    (hA : A.IsMartingaleDifferenceArray) (n : Nat) (t : Real) :
    ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) - 1 +
        (((t ^ 2 / 2 : Real) : Complex) *
          ∑ k, ∫ omega,
            complexPhase t (A.partialSum n k.val omega) *
              (A.conditionalVariance n k omega : Real) ∂(A.probability n))‖ ≤
      ∑ k, ∫ omega,
        ‖thirdOrderRemainder t (A.increment n k omega)‖ ∂(A.probability n) := by
  have h := terminalCharacteristicFunctionEstimate_predictable
    (P := A.probability n) (F := A.filtration n) (D := A.paddedIncrement n)
    t (A.rowLength n)
    (A.paddedIncrement_stronglyMeasurable hA n)
    (A.paddedIncrement_memLp_two hA n)
    (A.paddedIncrement_condExp_zero hA n)
  simpa [A.rowSum_eq_partialSum_rowLength, ArrayData.partialSum, natPartialSum,
    ArrayData.paddedIncrement, ArrayData.conditionalVariance,
    ← Fin.sum_univ_eq_sum_range] using h

/-- Convergence in probability of predictable quadratic variation to one. -/
def PredictableQuadraticVariationCondition : Prop :=
  TendstoInProbabilityVarying Omega A.probability A.predictableQuadraticVariation atTop 1

/-- Conditional Lindeberg condition on the varying row spaces. -/
def ConditionalLindebergCondition : Prop :=
  ∀ epsilon : Real, 0 < epsilon →
    TendstoInProbabilityVarying Omega A.probability
      (A.conditionalLindebergSum epsilon) atTop 0

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- Conditional variances are measurable in the ambient row sigma-algebra. -/
lemma conditionalVariance_measurable (n : Nat) (k : Fin (A.rowLength n)) :
    Measurable (A.conditionalVariance n k) := by
  unfold conditionalVariance
  exact ((stronglyMeasurable_condExp
    (m := A.filtration n k.val) (μ := A.probability n)
    (f := fun x => (A.increment n k x) ^ 2)).mono
      ((A.filtration n).le k.val)).measurable

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- Predictable quadratic variation is measurable in the ambient row sigma-algebra. -/
lemma predictableQuadraticVariation_measurable (n : Nat) :
    Measurable (A.predictableQuadraticVariation n) := by
  unfold predictableQuadraticVariation
  apply Finset.measurable_sum
  intro k _
  exact A.conditionalVariance_measurable n k

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- The finite conditional Lindeberg sum is measurable in the ambient row sigma-algebra. -/
lemma conditionalLindebergSum_measurable (epsilon : Real) (n : Nat) :
    Measurable (A.conditionalLindebergSum epsilon n) := by
  unfold conditionalLindebergSum
  apply Finset.measurable_sum
  intro k _
  exact ((stronglyMeasurable_condExp
    (m := A.filtration n k.val) (μ := A.probability n)
    (f := fun x => if epsilon < |A.increment n k x| then
      (A.increment n k x) ^ 2 else 0)).mono
      ((A.filtration n).le k.val)).measurable

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- A pointwise nonnegative representative of the conditional variance. -/
def nonnegativeConditionalVariance (n : Nat) (k : Fin (A.rowLength n))
    (omega : Omega n) : Real :=
  max 0 (A.conditionalVariance n k omega)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- Predictable variance accumulated through increment `k` (including `k`). -/
def predictableVarianceThrough (n : Nat) (k : Fin (A.rowLength n))
    (omega : Omega n) : Real :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val),
    A.nonnegativeConditionalVariance n j omega

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- The prospective stopping event: retain increment `k` only when including its
predictable variance keeps the accumulated variance below `b`. -/
def predictableStopSet (b : Real) (n : Nat) (k : Fin (A.rowLength n)) : Set (Omega n) :=
  {omega | A.predictableVarianceThrough n k omega ≤ b}

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
/-- Increment stopped by the predictable prospective-variance event. -/
def stoppedIncrement (b : Real) (n : Nat) (k : Fin (A.rowLength n)) : Omega n → Real :=
  (A.predictableStopSet b n k).indicator (A.increment n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma nonnegativeConditionalVariance_stronglyMeasurable
    (n : Nat) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n k.val]
      (A.nonnegativeConditionalVariance n k) := by
  unfold nonnegativeConditionalVariance conditionalVariance
  exact (measurable_const.max (stronglyMeasurable_condExp
    (m := A.filtration n k.val) (μ := A.probability n)
    (f := fun x => (A.increment n k x) ^ 2)).measurable).stronglyMeasurable

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma predictableVarianceThrough_stronglyMeasurable
    (n : Nat) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n k.val]
      (A.predictableVarianceThrough n k) := by
  unfold predictableVarianceThrough
  exact Finset.stronglyMeasurable_fun_sum
    (f := fun j : Fin (A.rowLength n) => A.nonnegativeConditionalVariance n j)
    (Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val))
    (fun j hj =>
      (A.nonnegativeConditionalVariance_stronglyMeasurable n j).mono
        ((A.filtration n).mono ((Finset.mem_filter.mp hj).2)))

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma predictableStopSet_measurable
    (b : Real) (n : Nat) (k : Fin (A.rowLength n)) :
    MeasurableSet[A.filtration n k.val] (A.predictableStopSet b n k) := by
  exact (A.predictableVarianceThrough_stronglyMeasurable n k).measurable
    (measurableSet_Iic : MeasurableSet (Set.Iic b))

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma predictableStopSet_ambientMeasurable
    (b : Real) (n : Nat) (k : Fin (A.rowLength n)) :
    MeasurableSet (A.predictableStopSet b n k) :=
  (A.filtration n).le k.val _ (A.predictableStopSet_measurable b n k)

lemma stoppedIncrement_stronglyMeasurable
    (hA : A.IsMartingaleDifferenceArray) (b : Real)
    (n : Nat) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n (k.val + 1)] (A.stoppedIncrement b n k) := by
  unfold stoppedIncrement
  exact (hA.stronglyMeasurable n k).indicator
    ((A.filtration n).mono (Nat.le_succ k.val) _
      (A.predictableStopSet_measurable b n k))

lemma stoppedIncrement_memLp_two
    (hA : A.IsMartingaleDifferenceArray) (b : Real)
    (n : Nat) (k : Fin (A.rowLength n)) :
    MemLp (A.stoppedIncrement b n k) 2 (A.probability n) := by
  unfold stoppedIncrement
  exact (hA.memLp_two n k).indicator (A.predictableStopSet_ambientMeasurable b n k)

lemma stoppedIncrement_condExp_zero
    (hA : A.IsMartingaleDifferenceArray) (b : Real)
    (n : Nat) (k : Fin (A.rowLength n)) :
    (A.probability n)[A.stoppedIncrement b n k | A.filtration n k.val] =ᵐ[A.probability n] 0 := by
  unfold stoppedIncrement
  have hpull := condExp_indicator
    ((hA.memLp_two n k).integrable one_le_two)
    (A.predictableStopSet_measurable b n k)
  filter_upwards [hpull, hA.condExp_zero n k] with omega hpullω hzeroω
  rw [hpullω]
  by_cases hmem : omega ∈ A.predictableStopSet b n k
  · simpa [Set.indicator_of_mem hmem] using hzeroω
  · simp [Set.indicator_of_notMem hmem]

lemma stoppedIncrement_sq_condExp
    (hA : A.IsMartingaleDifferenceArray) (b : Real)
    (n : Nat) (k : Fin (A.rowLength n)) :
    (A.probability n)[fun omega => (A.stoppedIncrement b n k omega) ^ 2 |
      A.filtration n k.val] =ᵐ[A.probability n]
      (A.predictableStopSet b n k).indicator (A.conditionalVariance n k) := by
  have hsq : (fun omega => (A.stoppedIncrement b n k omega) ^ 2) =
      (A.predictableStopSet b n k).indicator
        (fun omega => (A.increment n k omega) ^ 2) := by
    funext omega
    by_cases hmem : omega ∈ A.predictableStopSet b n k <;>
      simp [stoppedIncrement, hmem]
  rw [hsq]
  exact condExp_indicator (hA.memLp_two n k).integrable_sq
    (A.predictableStopSet_measurable b n k)

/-- The predictable-QV assumption yields a genuine `L¹` conclusion after bounded
localization.  No convergence-in-probability hypothesis is treated as raw expectation
convergence. -/
theorem predictableQuadraticVariation_clipped_L1
    (hQV : A.PredictableQuadraticVariationCondition) :
    Tendsto (fun n => ∫ omega,
      min 1 |A.predictableQuadraticVariation n omega - 1| ∂(A.probability n))
      atTop (nhds 0) := by
  exact tendsto_integral_min_one_abs_sub_of_tendstoInProbabilityVarying
    A.probability A.predictableQuadraticVariation 1
    A.predictableQuadraticVariation_measurable hQV

/-- For every positive cutoff, conditional Lindeberg convergence yields a genuine `L¹`
conclusion after bounded localization. -/
theorem conditionalLindeberg_clipped_L1
    (hLindeberg : A.ConditionalLindebergCondition) (epsilon : Real) (hepsilon : 0 < epsilon) :
    Tendsto (fun n => ∫ omega,
      min 1 |A.conditionalLindebergSum epsilon n omega| ∂(A.probability n))
      atTop (nhds 0) := by
  simpa only [sub_zero] using
    (tendsto_integral_min_one_abs_sub_of_tendstoInProbabilityVarying
      A.probability (A.conditionalLindebergSum epsilon) 0
      (A.conditionalLindebergSum_measurable epsilon) (hLindeberg epsilon hepsilon))

/-- The sum of the two bounded localization errors tends to zero.  This is the actual
asymptotic content obtainable directly from the encoded probability limits without a
uniform-integrability assumption. -/
theorem clippedLocalizationErrors_tendsto_zero
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Tendsto (fun n =>
      (∫ omega, min 1 |A.predictableQuadraticVariation n omega - 1|
        ∂(A.probability n)) +
      ∫ omega, min 1 |A.conditionalLindebergSum epsilon n omega|
        ∂(A.probability n)) atTop (nhds 0) := by
  convert (A.predictableQuadraticVariation_clipped_L1 hQV).add
    (A.conditionalLindeberg_clipped_L1 hLindeberg epsilon hepsilon) using 1 <;> norm_num

/-- The exact specialized varying-space martingale-array CLT specification requested by Unit 6.

This remains a proposition-valued interface (`def`); it is inhabited below by
`varyingSpaceMartingaleArrayCLT`. -/
def VaryingSpaceMartingaleArrayCLT : Prop :=
  A.IsMartingaleDifferenceArray →
  A.PredictableQuadraticVariationCondition →
  A.ConditionalLindebergCondition →
  ∀ (OmegaLimit : Type*) (_ : MeasurableSpace OmegaLimit)
      (PLimit : Measure OmegaLimit) (_ : IsProbabilityMeasure PLimit)
      (Y : OmegaLimit → Real),
    HasLaw Y (gaussianReal 0 1) PLimit →
    TendstoInDistribution A.rowSum atTop Y A.probability PLimit

/-- The first distributional analytic residual, stated without assertion: convergence of all
row-sum characteristic functions to the standard Gaussian characteristic function.  Once
this implication is proved, Levy continuity supplies the final weak convergence step. -/
def CharacteristicFunctionConvergenceResidual : Prop :=
  A.IsMartingaleDifferenceArray →
  A.PredictableQuadraticVariationCondition →
  A.ConditionalLindebergCondition →
  ∀ t : Real, Tendsto
    (fun n => ∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n))
    atTop (nhds (Complex.exp (-((t : Complex) ^ 2) / 2)))

/-- Conditional completion from the raw terminal-estimate residual.  This lemma is retained
as the exact interface supplied by the finite-row estimate, but it is not called localization:
its first summand is an unlocalized integrated Taylor remainder, which does not follow from
convergence in probability without stopping or uniform integrability.

The single displayed premise combines that raw remainder with the Fourier-weighted
predictable-square error. -/
theorem characteristicFunctionConvergenceResidual_of_raw_row_residual
    (hlocalize : A.PredictableQuadraticVariationCondition →
      A.ConditionalLindebergCondition → ∀ t : Real,
      Tendsto (fun n =>
        (∑ k, ∫ omega,
          ‖thirdOrderRemainder t (A.increment n k omega)‖ ∂(A.probability n)) +
        ‖(1 : Complex) - Complex.exp (-((t : Complex) ^ 2) / 2) -
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n))‖)
        atTop (nhds 0)) :
    A.CharacteristicFunctionConvergenceResidual := by
  unfold CharacteristicFunctionConvergenceResidual
  intro hA hQV hLindeberg t
  have hresidual := hlocalize hQV hLindeberg t
  rw [Metric.tendsto_atTop] at hresidual ⊢
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := hresidual epsilon hepsilon
  refine ⟨N, fun n hn => ?_⟩
  have hestimate := A.terminalCharacteristicFunctionEstimate_row hA n t
  have hbound :
      dist (∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n))
          (Complex.exp (-((t : Complex) ^ 2) / 2)) ≤
        (∑ k, ∫ omega,
          ‖thirdOrderRemainder t (A.increment n k omega)‖ ∂(A.probability n)) +
        ‖(1 : Complex) - Complex.exp (-((t : Complex) ^ 2) / 2) -
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n))‖ := by
    rw [Complex.dist_eq]
    calc
      ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
          Complex.exp (-((t : Complex) ^ 2) / 2)‖ =
        ‖((∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) - 1 +
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n))) +
          ((1 : Complex) - Complex.exp (-((t : Complex) ^ 2) / 2) -
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n)))‖ := by
            ring_nf
      _ ≤ ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) - 1 +
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n))‖ +
          ‖(1 : Complex) - Complex.exp (-((t : Complex) ^ 2) / 2) -
          (((t ^ 2 / 2 : Real) : Complex) *
            ∑ k, ∫ omega,
              complexPhase t (A.partialSum n k.val omega) *
                (A.conditionalVariance n k omega : Real) ∂(A.probability n))‖ :=
            norm_add_le _ _
      _ ≤ _ := add_le_add hestimate (le_refl _)
  exact lt_of_le_of_lt (hbound.trans (le_abs_self _)) (by
    simpa only [Real.dist_eq, sub_zero] using hN n hn)

/-- Completion from one exact Fourier localization residual after the two bounded
probability-to-`L¹` localization errors have been discharged.  The remaining premise is
precisely the excess characteristic-function error beyond those proved localization errors;
a predictable stopped-row estimate is needed to prove it from `IsMartingaleDifferenceArray`.
Unlike the raw-row lemma above, this premise does not re-assume Taylor-tail expectation
convergence. -/
theorem characteristicFunctionConvergenceResidual_of_clipped_fourier_residual
    (hfourier : ∀ (t epsilon : Real), 0 < epsilon →
      Tendsto (fun n =>
        ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
          Complex.exp (-((t : Complex) ^ 2) / 2)‖ -
        ((∫ omega, min 1 |A.predictableQuadraticVariation n omega - 1|
            ∂(A.probability n)) +
          ∫ omega, min 1 |A.conditionalLindebergSum epsilon n omega|
            ∂(A.probability n))) atTop (nhds 0)) :
    A.CharacteristicFunctionConvergenceResidual := by
  unfold CharacteristicFunctionConvergenceResidual
  intro _hA hQV hLindeberg t
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have herr := A.clippedLocalizationErrors_tendsto_zero hQV hLindeberg 1 zero_lt_one
  have hres := hfourier t 1 zero_lt_one
  simpa only [sub_add_cancel, zero_add] using hres.add herr


end ArrayData

lemma fin_prospectiveStoppedSum_le
    {N : ℕ} (q : Fin N → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hq : ∀ k, 0 ≤ q k) :
    (∑ k, if (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤ b
      then q k else 0) ≤ b := by
  classical
  let s : Finset (Fin N) := Finset.univ.filter (fun k =>
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤ b)
  have hrewrite :
      (∑ k, if (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤ b
        then q k else 0) = ∑ k ∈ s, q k := by
    simpa only [s] using
      (Finset.sum_filter
        (s := (Finset.univ : Finset (Fin N)))
        (fun k : Fin N =>
          (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤ b)
        q).symm
  rw [hrewrite]
  by_cases hs : s.Nonempty
  · let k : Fin N := s.max' hs
    have hks : k ∈ s := Finset.max'_mem s hs
    have hkbound : (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤ b :=
      (Finset.mem_filter.mp hks).2
    have hsubset : s ⊆ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val) := by
      intro j hjs
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        exact_mod_cast Finset.le_max' s j hjs⟩
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (s := s) (t := Finset.univ.filter (fun j : Fin N => j.val ≤ k.val))
      (f := q) hsubset (fun j _ _ => hq j)).trans hkbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simpa using hb

namespace ArrayData
variable (A : ArrayData Omega)
variable [∀ n, IsProbabilityMeasure (A.probability n)]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def stoppedConditionalVariance (b : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) : Omega n → ℝ :=
  (A.predictableStopSet b n k).indicator (A.nonnegativeConditionalVariance n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def stoppedPredictableQuadraticVariation (b : ℝ) (n : ℕ) : Omega n → ℝ :=
  fun omega => ∑ k, A.stoppedConditionalVariance b n k omega

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def paddedStoppedIncrement (b : ℝ) (n k : ℕ) : Omega n → ℝ :=
  if hk : k < A.rowLength n then A.stoppedIncrement b n ⟨k, hk⟩ else 0

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def paddedStoppedConditionalVariance (b : ℝ) (n k : ℕ) : Omega n → ℝ :=
  if hk : k < A.rowLength n then A.stoppedConditionalVariance b n ⟨k, hk⟩ else 0

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def stoppedPartialSum (b : ℝ) (n j : ℕ) : Omega n → ℝ :=
  natPartialSum (A.paddedStoppedIncrement b n) j

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def stoppedVarianceClock (b : ℝ) (n j : ℕ) : Omega n → ℝ :=
  fun omega => ∑ k ∈ Finset.range j, A.paddedStoppedConditionalVariance b n k omega

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedConditionalVariance_nonneg (b : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) (omega : Omega n) :
    0 ≤ A.stoppedConditionalVariance b n k omega := by
  by_cases h : omega ∈ A.predictableStopSet b n k
  · simp [stoppedConditionalVariance, h, nonnegativeConditionalVariance]
  · simp [stoppedConditionalVariance, h]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedPredictableQuadraticVariation_nonneg (b : ℝ) (n : ℕ) (omega : Omega n) :
    0 ≤ A.stoppedPredictableQuadraticVariation b n omega := by
  exact Finset.sum_nonneg (fun k _ => A.stoppedConditionalVariance_nonneg b n k omega)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedPredictableQuadraticVariation_le (b : ℝ) (hb : 0 ≤ b)
    (n : ℕ) (omega : Omega n) :
    A.stoppedPredictableQuadraticVariation b n omega ≤ b := by
  unfold stoppedPredictableQuadraticVariation stoppedConditionalVariance
  simpa only [predictableStopSet, Set.indicator, Set.mem_setOf_eq]
    using fin_prospectiveStoppedSum_le
      (fun k : Fin (A.rowLength n) => A.nonnegativeConditionalVariance n k omega)
      b hb (fun k => by simp [nonnegativeConditionalVariance])

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedVarianceClock_rowLength (b : ℝ) (n : ℕ) :
    A.stoppedVarianceClock b n (A.rowLength n) =
      A.stoppedPredictableQuadraticVariation b n := by
  funext omega
  simp [stoppedVarianceClock, paddedStoppedConditionalVariance,
    stoppedPredictableQuadraticVariation, ← Fin.sum_univ_eq_sum_range]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedVarianceClock_nonneg (b : ℝ) (n j : ℕ) (omega : Omega n) :
    0 ≤ A.stoppedVarianceClock b n j omega := by
  unfold stoppedVarianceClock
  apply Finset.sum_nonneg
  intro k hk
  unfold paddedStoppedConditionalVariance
  split_ifs with h
  · exact A.stoppedConditionalVariance_nonneg b n ⟨k, h⟩ omega
  · exact le_rfl

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma stoppedVarianceClock_le (b : ℝ) (hb : 0 ≤ b) (n j : ℕ)
    (hj : j ≤ A.rowLength n) (omega : Omega n) :
    A.stoppedVarianceClock b n j omega ≤ b := by
  have hpart : A.stoppedVarianceClock b n j omega ≤
      A.stoppedVarianceClock b n (A.rowLength n) omega := by
    unfold stoppedVarianceClock
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (s := Finset.range j) (t := Finset.range (A.rowLength n))
      (f := fun k => A.paddedStoppedConditionalVariance b n k omega)
      (Finset.range_mono hj) (fun k hk _ => by
        have hk' : k < A.rowLength n := Finset.mem_range.mp hk
        simp [paddedStoppedConditionalVariance, hk',
          A.stoppedConditionalVariance_nonneg b n ⟨k, hk'⟩ omega])
  rw [A.stoppedVarianceClock_rowLength b n] at hpart
  exact hpart.trans (A.stoppedPredictableQuadraticVariation_le b hb n omega)

lemma conditionalVariance_ae_nonneg (hA : A.IsMartingaleDifferenceArray)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    0 ≤ᵐ[A.probability n] A.conditionalVariance n k := by
  exact condExp_nonneg (Filter.Eventually.of_forall (fun omega => sq_nonneg (A.increment n k omega)))

lemma conditionalVariance_eq_nonnegative_ae (hA : A.IsMartingaleDifferenceArray)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    A.conditionalVariance n k =ᵐ[A.probability n]
      A.nonnegativeConditionalVariance n k := by
  filter_upwards [A.conditionalVariance_ae_nonneg hA n k] with omega homega
  have ho : 0 ≤ A.conditionalVariance n k omega := by simpa using homega
  simp [nonnegativeConditionalVariance, max_eq_right ho]

lemma stoppedIncrement_sq_condExp_nonnegative
    (hA : A.IsMartingaleDifferenceArray) (b : ℝ)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    (A.probability n)[fun omega => (A.stoppedIncrement b n k omega) ^ 2 |
      A.filtration n k.val] =ᵐ[A.probability n]
      A.stoppedConditionalVariance b n k := by
  filter_upwards [A.stoppedIncrement_sq_condExp hA b n k,
    A.conditionalVariance_eq_nonnegative_ae hA n k] with omega hsq hnonneg
  rw [hsq]
  by_cases hmem : omega ∈ A.predictableStopSet b n k
  · simp [stoppedConditionalVariance, hmem, hnonneg]
  · simp [stoppedConditionalVariance, hmem]



variable (A : ArrayData Omega)
variable [∀ n, IsProbabilityMeasure (A.probability n)]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def nonnegativeConditionalLindebergTerm (delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) : Omega n → ℝ :=
  max 0 ((A.probability n)[fun x =>
    if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0 |
      A.filtration n k.val])

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma nonnegativeConditionalLindebergTerm_stronglyMeasurable
    (delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n k.val]
      (A.nonnegativeConditionalLindebergTerm delta n k) := by
  unfold nonnegativeConditionalLindebergTerm
  exact (measurable_const.max (stronglyMeasurable_condExp
    (m := A.filtration n k.val) (μ := A.probability n)
    (f := fun x => if delta < |A.increment n k x| then
      (A.increment n k x) ^ 2 else 0)).measurable).stronglyMeasurable

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def predictableLindebergThrough (delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) (omega : Omega n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val),
    A.nonnegativeConditionalLindebergTerm delta n j omega

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma predictableLindebergThrough_stronglyMeasurable
    (delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n k.val]
      (A.predictableLindebergThrough delta n k) := by
  unfold predictableLindebergThrough
  exact Finset.stronglyMeasurable_fun_sum
    (f := fun j : Fin (A.rowLength n) =>
      A.nonnegativeConditionalLindebergTerm delta n j)
    (Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val))
    (fun j hj =>
      (A.nonnegativeConditionalLindebergTerm_stronglyMeasurable delta n j).mono
        ((A.filtration n).mono ((Finset.mem_filter.mp hj).2)))

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def twoClockStopSet (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) : Set (Omega n) :=
  {omega | A.predictableVarianceThrough n k omega ≤ b ∧
    A.predictableLindebergThrough delta n k omega ≤ c}

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma twoClockStopSet_measurable
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    MeasurableSet[A.filtration n k.val] (A.twoClockStopSet b c delta n k) := by
  exact MeasurableSet.inter
    ((A.predictableVarianceThrough_stronglyMeasurable n k).measurable
      (measurableSet_Iic : MeasurableSet (Set.Iic b)))
    ((A.predictableLindebergThrough_stronglyMeasurable delta n k).measurable
      (measurableSet_Iic : MeasurableSet (Set.Iic c)))

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma twoClockStopSet_ambientMeasurable
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    MeasurableSet (A.twoClockStopSet b c delta n k) :=
  (A.filtration n).le k.val _ (A.twoClockStopSet_measurable b c delta n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma twoClockStopSet_subset_varianceStop
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    A.twoClockStopSet b c delta n k ⊆ A.predictableStopSet b n k := by
  intro omega h
  exact h.1


omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma fin_clock_prefix_le_total
    {N : ℕ} (q : Fin N → ℝ) (hq : ∀ k, 0 ≤ q k) (k : Fin N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val ≤ k.val), q j) ≤
      ∑ j, q j := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) (fun j _ hj => hq j)

lemma conditionalLindebergTerm_eq_nonnegative_ae
    (delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    (A.probability n)[fun x =>
      if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0 |
        A.filtration n k.val] =ᵐ[A.probability n]
      A.nonnegativeConditionalLindebergTerm delta n k := by
  have hnonneg : 0 ≤ᶠ[ae (A.probability n)] (fun x =>
      if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0) :=
    Filter.Eventually.of_forall (fun x => by
      by_cases h : delta < |A.increment n k x|
      · simp [h]
        positivity
      · simp [h])
  have hce := condExp_nonneg (μ := A.probability n)
    (m := A.filtration n k.val)
    (f := fun x =>
      if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0) hnonneg
  filter_upwards [hce] with omega hω
  simpa only [nonnegativeConditionalLindebergTerm] using (max_eq_right hω).symm

lemma predictableQuadraticVariation_eq_nonnegative_sum_ae
    (hA : A.IsMartingaleDifferenceArray) (n : ℕ) :
    A.predictableQuadraticVariation n =ᵐ[A.probability n]
      (fun omega => ∑ k, A.nonnegativeConditionalVariance n k omega) := by
  have hall : ∀ᵐ omega ∂(A.probability n), ∀ k : Fin (A.rowLength n),
      A.conditionalVariance n k omega = A.nonnegativeConditionalVariance n k omega :=
    (ae_all_iff).2 (fun k => A.conditionalVariance_eq_nonnegative_ae hA n k)
  filter_upwards [hall] with omega hω
  unfold predictableQuadraticVariation
  exact Finset.sum_congr rfl (fun k _ => hω k)

lemma conditionalLindebergSum_eq_nonnegative_sum_ae
    (delta : ℝ) (n : ℕ) :
    A.conditionalLindebergSum delta n =ᵐ[A.probability n]
      (fun omega => ∑ k, A.nonnegativeConditionalLindebergTerm delta n k omega) := by
  have hall : ∀ᵐ omega ∂(A.probability n), ∀ k : Fin (A.rowLength n),
      ((A.probability n)[fun x =>
        if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0 |
          A.filtration n k.val]) omega =
        A.nonnegativeConditionalLindebergTerm delta n k omega :=
    (ae_all_iff).2 (fun k => A.conditionalLindebergTerm_eq_nonnegative_ae delta n k)
  filter_upwards [hall] with omega hω
  unfold conditionalLindebergSum
  exact Finset.sum_congr rfl (fun k _ => hω k)

lemma twoClockStopSet_of_total_nonnegative_clocks_le
    (b c delta : ℝ) (n : ℕ) (omega : Omega n)
    (hV : (∑ k, A.nonnegativeConditionalVariance n k omega) ≤ b)
    (hL : (∑ k, A.nonnegativeConditionalLindebergTerm delta n k omega) ≤ c) :
    ∀ k : Fin (A.rowLength n), omega ∈ A.twoClockStopSet b c delta n k := by
  intro k
  change
    (∑ j ∈ Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val),
      A.nonnegativeConditionalVariance n j omega) ≤ b ∧
    (∑ j ∈ Finset.univ.filter (fun j : Fin (A.rowLength n) => j.val ≤ k.val),
      A.nonnegativeConditionalLindebergTerm delta n j omega) ≤ c
  exact ⟨(fin_clock_prefix_le_total
      (fun j => A.nonnegativeConditionalVariance n j omega)
      (fun j => by simp [nonnegativeConditionalVariance]) k).trans hV,
    (fin_clock_prefix_le_total
      (fun j => A.nonnegativeConditionalLindebergTerm delta n j omega)
      (fun j => by simp [nonnegativeConditionalLindebergTerm]) k).trans hL⟩

lemma twoClockStopSet_of_original_total_clocks_le_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ) :
    ∀ᵐ omega ∂(A.probability n),
      (A.predictableQuadraticVariation n omega ≤ b ∧
        A.conditionalLindebergSum delta n omega ≤ c) →
      ∀ k : Fin (A.rowLength n), omega ∈ A.twoClockStopSet b c delta n k := by
  have hV := A.predictableQuadraticVariation_eq_nonnegative_sum_ae hA n
  have hL := A.conditionalLindebergSum_eq_nonnegative_sum_ae delta n
  filter_upwards [hV, hL] with omega hVω hLω hgood
  rw [hVω, hLω] at hgood
  exact A.twoClockStopSet_of_total_nonnegative_clocks_le b c delta n omega
    hgood.1 hgood.2

def twoClockStopEvent (b c delta : ℝ) (n : ℕ) : Set (Omega n) :=
  {omega | ∃ k : Fin (A.rowLength n), omega ∉ A.twoClockStopSet b c delta n k}

lemma twoClockStopEvent_subset_original_bad_union_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ) :
    A.twoClockStopEvent b c delta n ≤ᶠ[ae (A.probability n)]
    Set.union ({omega : Omega n | b < A.predictableQuadraticVariation n omega} : Set (Omega n))
      {omega : Omega n | c < A.conditionalLindebergSum delta n omega} := by
  have hgood := A.twoClockStopSet_of_original_total_clocks_le_ae hA b c delta n
  filter_upwards [hgood] with omega hgood hstop
  rcases hstop with ⟨k, hk⟩
  by_contra hbad
  have hV : A.predictableQuadraticVariation n omega ≤ b := by
    exact le_of_not_gt (fun h => hbad (Or.inl h))
  have hL : A.conditionalLindebergSum delta n omega ≤ c := by
    exact le_of_not_gt (fun h => hbad (Or.inr h))
  exact hk (hgood ⟨hV, hL⟩ k)

lemma twoClockStopEvent_probability_le_original_bad_union
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ) :
    (A.probability n) (A.twoClockStopEvent b c delta n) ≤
      (A.probability n) {omega | b < A.predictableQuadraticVariation n omega} +
        (A.probability n) {omega | c < A.conditionalLindebergSum delta n omega} := by
  exact (measure_mono_ae
    (A.twoClockStopEvent_subset_original_bad_union_ae hA b c delta n)).trans
    (measure_union_le _ _)

/-- The prospective stop event is controlled, modulo the representative null set, by
exceeding either original total clock.  The limit statement necessarily uses `b > 1`,
`c > 0`, and `delta > 0`, because those are the thresholds available from the two encoded
convergence-in-probability assumptions. -/
theorem twoClockStopEvent_measure_tendsto_zero
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (b c delta : ℝ) (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta) :
    Tendsto (fun n => (A.probability n) (A.twoClockStopEvent b c delta n))
      atTop (nhds 0) := by
  have hsubset : ∀ n,
      (A.probability n) (A.twoClockStopEvent b c delta n) ≤
        (A.probability n) {omega | b < A.predictableQuadraticVariation n omega} +
        (A.probability n) {omega | c < A.conditionalLindebergSum delta n omega} := by
    intro n
    exact A.twoClockStopEvent_probability_le_original_bad_union hA b c delta n
  have hQVbad : Tendsto
      (fun n => (A.probability n) {omega | b < A.predictableQuadraticVariation n omega})
      atTop (nhds 0) := by
    have hprob := hQV (b - 1) (sub_pos.mpr hb)
    have hle : ∀ n,
        (A.probability n) {omega | b < A.predictableQuadraticVariation n omega} ≤
          (A.probability n) {omega |
            b - 1 ≤ |A.predictableQuadraticVariation n omega - 1|} := by
      intro n
      apply measure_mono
      intro omega hω
      dsimp at hω ⊢
      have hlow := le_abs_self
        (A.predictableQuadraticVariation n omega - 1)
      linarith [abs_nonneg (A.predictableQuadraticVariation n omega - 1), hlow]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hprob
      (Filter.Eventually.of_forall (fun _ => bot_le))
      (Filter.Eventually.of_forall hle)
  have hLbad : Tendsto
      (fun n => (A.probability n) {omega | c < A.conditionalLindebergSum delta n omega})
      atTop (nhds 0) := by
    have hprob := (hLindeberg delta hdelta) c hc
    have hle : ∀ n,
        (A.probability n) {omega | c < A.conditionalLindebergSum delta n omega} ≤
          (A.probability n) {omega | c ≤
            |A.conditionalLindebergSum delta n omega - 0|} := by
      intro n
      apply measure_mono
      intro omega hω
      dsimp at hω ⊢
      have hlow := le_abs_self
        (A.conditionalLindebergSum delta n omega - 0)
      linarith [abs_nonneg (A.conditionalLindebergSum delta n omega - 0), hlow]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hprob
      (Filter.Eventually.of_forall (fun _ => bot_le))
      (Filter.Eventually.of_forall hle)
  have hupper : Tendsto
      (fun n => (A.probability n) {omega | b < A.predictableQuadraticVariation n omega} +
        (A.probability n) {omega | c < A.conditionalLindebergSum delta n omega})
      atTop (nhds 0) := by
    simpa only [add_zero] using hQVbad.add hLbad
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Filter.Eventually.of_forall (fun _ => bot_le))
    (Filter.Eventually.of_forall hsubset)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def twoClockStoppedConditionalVariance (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) : Omega n → ℝ :=
  (A.twoClockStopSet b c delta n k).indicator (A.nonnegativeConditionalVariance n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
def twoClockStoppedLindebergTerm (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) : Omega n → ℝ :=
  (A.twoClockStopSet b c delta n k).indicator
    (A.nonnegativeConditionalLindebergTerm delta n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma twoClockStoppedConditionalVariance_nonneg
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) (omega : Omega n) :
    0 ≤ A.twoClockStoppedConditionalVariance b c delta n k omega := by
  by_cases h : omega ∈ A.twoClockStopSet b c delta n k
  · simp [twoClockStoppedConditionalVariance, h, nonnegativeConditionalVariance]
  · simp [twoClockStoppedConditionalVariance, h]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma twoClockStoppedLindebergTerm_nonneg
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) (omega : Omega n) :
    0 ≤ A.twoClockStoppedLindebergTerm b c delta n k omega := by
  by_cases h : omega ∈ A.twoClockStopSet b c delta n k
  · simp [twoClockStoppedLindebergTerm, h, nonnegativeConditionalLindebergTerm]
  · simp [twoClockStoppedLindebergTerm, h]

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma fin_twoClockStoppedVariance_le
    (b c delta : ℝ) (hb : 0 ≤ b) (n : ℕ) (omega : Omega n) :
    (∑ k, A.twoClockStoppedConditionalVariance b c delta n k omega) ≤ b := by
  classical
  have hterm : ∀ k : Fin (A.rowLength n),
      (if omega ∈ A.twoClockStopSet b c delta n k then
        A.nonnegativeConditionalVariance n k omega else 0) ≤
      (if omega ∈ A.predictableStopSet b n k then
        A.nonnegativeConditionalVariance n k omega else 0) := by
    intro k
    by_cases hs : omega ∈ A.twoClockStopSet b c delta n k
    · have hv : omega ∈ A.predictableStopSet b n k :=
        A.twoClockStopSet_subset_varianceStop b c delta n k hs
      simp [hs, hv]
    · by_cases hv : omega ∈ A.predictableStopSet b n k <;>
        simp [hs, hv, nonnegativeConditionalVariance]
  calc
    (∑ k, A.twoClockStoppedConditionalVariance b c delta n k omega) =
        ∑ k, if omega ∈ A.twoClockStopSet b c delta n k then
          A.nonnegativeConditionalVariance n k omega else 0 := by
            rfl
    _ ≤ ∑ k, if omega ∈ A.predictableStopSet b n k then
          A.nonnegativeConditionalVariance n k omega else 0 :=
      Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ b := by
      unfold predictableStopSet
      simpa [nonnegativeConditionalVariance] using
        fin_prospectiveStoppedSum_le
          (fun k : Fin (A.rowLength n) => A.nonnegativeConditionalVariance n k omega)
          b hb (fun k => by simp [nonnegativeConditionalVariance])


def twoClockStoppedIncrement (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) : Omega n → ℝ :=
  (A.twoClockStopSet b c delta n k).indicator (A.increment n k)

lemma twoClockStoppedIncrement_stronglyMeasurable
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n (k.val + 1)]
      (A.twoClockStoppedIncrement b c delta n k) := by
  unfold twoClockStoppedIncrement
  exact (hA.stronglyMeasurable n k).indicator
    ((A.filtration n).mono (Nat.le_succ k.val) _
      (A.twoClockStopSet_measurable b c delta n k))

lemma twoClockStoppedIncrement_memLp_two
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    MemLp (A.twoClockStoppedIncrement b c delta n k) 2 (A.probability n) := by
  unfold twoClockStoppedIncrement
  exact (hA.memLp_two n k).indicator
    (A.twoClockStopSet_ambientMeasurable b c delta n k)

lemma twoClockStoppedIncrement_condExp_zero
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    (A.probability n)[A.twoClockStoppedIncrement b c delta n k |
      A.filtration n k.val] =ᵐ[A.probability n] 0 := by
  unfold twoClockStoppedIncrement
  have hpull := condExp_indicator
    ((hA.memLp_two n k).integrable one_le_two)
    (A.twoClockStopSet_measurable b c delta n k)
  filter_upwards [hpull, hA.condExp_zero n k] with omega hpullω hzeroω
  rw [hpullω]
  by_cases hmem : omega ∈ A.twoClockStopSet b c delta n k
  · simpa [Set.indicator_of_mem hmem] using hzeroω
  · simp [Set.indicator_of_notMem hmem]

lemma twoClockStoppedIncrement_sq_condExp
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    (A.probability n)[fun omega =>
      (A.twoClockStoppedIncrement b c delta n k omega) ^ 2 |
      A.filtration n k.val] =ᵐ[A.probability n]
      (A.twoClockStopSet b c delta n k).indicator
        (A.conditionalVariance n k) := by
  have hsq : (fun omega =>
      (A.twoClockStoppedIncrement b c delta n k omega) ^ 2) =
      (A.twoClockStopSet b c delta n k).indicator
        (fun omega => (A.increment n k omega) ^ 2) := by
    funext omega
    by_cases hmem : omega ∈ A.twoClockStopSet b c delta n k <;>
      simp [twoClockStoppedIncrement, hmem]
  rw [hsq]
  exact condExp_indicator (hA.memLp_two n k).integrable_sq
    (A.twoClockStopSet_measurable b c delta n k)

omit [∀ n, IsProbabilityMeasure (A.probability n)] in
lemma fin_twoClockStoppedLindeberg_le
    (b c delta : ℝ) (hc : 0 ≤ c) (n : ℕ) (omega : Omega n) :
    (∑ k, A.twoClockStoppedLindebergTerm b c delta n k omega) ≤ c := by
  classical
  let r : Fin (A.rowLength n) → ℝ := fun k =>
    A.nonnegativeConditionalLindebergTerm delta n k omega
  have hr : ∀ k, 0 ≤ r k := by
    intro k
    simp [r, nonnegativeConditionalLindebergTerm]
  have hterm : ∀ k : Fin (A.rowLength n),
      (if omega ∈ A.twoClockStopSet b c delta n k then r k else 0) ≤
      (if (∑ j ∈ Finset.univ.filter
          (fun j : Fin (A.rowLength n) => j.val ≤ k.val), r j) ≤ c
        then r k else 0) := by
    intro k
    by_cases hs : omega ∈ A.twoClockStopSet b c delta n k
    · have ht : (∑ j ∈ Finset.univ.filter
          (fun j : Fin (A.rowLength n) => j.val ≤ k.val), r j) ≤ c := by
        simpa [r, predictableLindebergThrough] using hs.2
      rw [if_pos hs, if_pos ht]
    · rw [if_neg hs]
      by_cases ht : (∑ j ∈ Finset.univ.filter
          (fun j : Fin (A.rowLength n) => j.val ≤ k.val), r j) ≤ c
      · rw [if_pos ht]
        exact hr k
      · rw [if_neg ht]
  calc
    (∑ k, A.twoClockStoppedLindebergTerm b c delta n k omega) =
        ∑ k, if omega ∈ A.twoClockStopSet b c delta n k then r k else 0 := by
      rfl
    _ ≤ ∑ k, if (∑ j ∈ Finset.univ.filter
          (fun j : Fin (A.rowLength n) => j.val ≤ k.val), r j) ≤ c
        then r k else 0 := Finset.sum_le_sum (fun k _ => hterm k)
    _ ≤ c := fin_prospectiveStoppedSum_le r c hc hr

lemma conditionalVariance_le_delta_sq_add_nonnegativeConditionalLindebergTerm_ae
    (hA : A.IsMartingaleDifferenceArray) (delta : ℝ) (hdelta : 0 ≤ delta)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    A.conditionalVariance n k ≤ᵐ[A.probability n]
      (fun omega => delta ^ 2 +
        A.nonnegativeConditionalLindebergTerm delta n k omega) := by
  let tail : Omega n → ℝ := fun x =>
    if delta < |A.increment n k x| then (A.increment n k x) ^ 2 else 0
  have hinc_sm : StronglyMeasurable (A.increment n k) :=
    (hA.stronglyMeasurable n k).mono ((A.filtration n).le (k.val + 1))
  have hset : MeasurableSet {x : Omega n | delta < |A.increment n k x|} := by
    exact measurableSet_Ioi.preimage hinc_sm.measurable.abs
  have htail_sm : StronglyMeasurable tail := by
    simpa [tail, Set.indicator] using
      MeasureTheory.StronglyMeasurable.indicator (hinc_sm.pow 2) hset
  have htail_int : Integrable tail (A.probability n) := by
    apply (hA.memLp_two n k).integrable_sq.mono htail_sm.aestronglyMeasurable
    filter_upwards [] with omega
    dsimp [tail]
    by_cases h : delta < |A.increment n k omega|
    · simp [h]
    · simp [h]
      positivity
  have hconst_int : Integrable (fun _ : Omega n => delta ^ 2)
      (A.probability n) := integrable_const _
  have hsum_int : Integrable (fun x => delta ^ 2 + tail x)
      (A.probability n) := by
    simpa only [Pi.add_apply] using hconst_int.add htail_int
  have hpoint : (fun x => (A.increment n k x) ^ 2) ≤ᵐ[A.probability n]
      (fun x => delta ^ 2 + tail x) := by
    filter_upwards [] with omega
    dsimp [tail]
    by_cases h : delta < |A.increment n k omega|
    · simp [h]
      nlinarith [sq_nonneg delta]
    · have habs : |A.increment n k omega| ≤ delta := le_of_not_gt h
      have hsquare : (A.increment n k omega) ^ 2 ≤ delta ^ 2 := by
        calc
          (A.increment n k omega) ^ 2 =
              |A.increment n k omega| ^ 2 := (sq_abs _).symm
          _ ≤ delta ^ 2 := (sq_le_sq₀ (abs_nonneg _) hdelta).2 habs
      simpa [h] using hsquare
  have hmono := condExp_mono (m := A.filtration n k.val)
    (hA.memLp_two n k).integrable_sq hsum_int hpoint
  have hadd := condExp_add hconst_int htail_int (A.filtration n k.val)
  have hconst := condExp_const (μ := A.probability n)
    (m := A.filtration n k.val) (m₀ := mOmega n)
    ((A.filtration n).le k.val) (delta ^ 2)
  rw [hconst] at hadd
  have hceg : (A.probability n)[fun x => delta ^ 2 + tail x |
      A.filtration n k.val] =ᶠ[ae (A.probability n)]
      (fun x => delta ^ 2 +
        (A.probability n)[tail | A.filtration n k.val] x) := by
    simpa only [Pi.add_apply] using hadd
  have hbound : (fun omega =>
      (A.probability n)[fun x => (A.increment n k x) ^ 2 |
        A.filtration n k.val] omega) ≤ᵐ[A.probability n]
    (fun omega => delta ^ 2 + max 0
      ((A.probability n)[tail | A.filtration n k.val] omega)) := by
    filter_upwards [hmono, hceg] with omega hmonoω hcegω
    rw [hcegω] at hmonoω
    have htailmax : (A.probability n)[tail | A.filtration n k.val] omega ≤
        max 0 ((A.probability n)[tail | A.filtration n k.val] omega) :=
      le_max_right 0 _
    exact hmonoω.trans (by
      simpa [add_comm] using add_le_add_left htailmax (delta ^ 2))
  have hres : (fun omega => max 0
      ((A.probability n)[fun x => (A.increment n k x) ^ 2 |
        A.filtration n k.val] omega)) ≤ᵐ[A.probability n]
    (fun omega => delta ^ 2 + max 0
      ((A.probability n)[tail | A.filtration n k.val] omega)) := by
    filter_upwards [hbound] with omega h
    exact max_le (by positivity) h
  simpa [conditionalVariance, nonnegativeConditionalLindebergTerm, tail] using hbound

lemma twoClockStoppedConditionalVariance_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (hdelta : 0 ≤ delta)
    (n : ℕ) (k : Fin (A.rowLength n)) :
    A.twoClockStoppedConditionalVariance b c delta n k ≤ᵐ[A.probability n]
      (fun omega => delta ^ 2 +
        A.twoClockStoppedLindebergTerm b c delta n k omega) := by
  filter_upwards [A.conditionalVariance_le_delta_sq_add_nonnegativeConditionalLindebergTerm_ae
    hA delta hdelta n k, A.conditionalVariance_ae_nonneg hA n k] with omega hbound hnonneg
  by_cases hs : omega ∈ A.twoClockStopSet b c delta n k
  · simp only [twoClockStoppedConditionalVariance, twoClockStoppedLindebergTerm,
      Set.indicator_of_mem hs]
    change max 0 (A.conditionalVariance n k omega) ≤
      delta ^ 2 + A.nonnegativeConditionalLindebergTerm delta n k omega
    have hmax : max 0 (A.conditionalVariance n k omega) =
        A.conditionalVariance n k omega := max_eq_right hnonneg
    rw [hmax]
    exact hbound
  · simp [twoClockStoppedConditionalVariance, twoClockStoppedLindebergTerm, hs]
    positivity


lemma twoClockStoppedLindebergTerm_le_c
    (b c delta : ℝ) (hc : 0 ≤ c) (n : ℕ) (k : Fin (A.rowLength n))
    (omega : Omega n) :
    A.twoClockStoppedLindebergTerm b c delta n k omega ≤ c := by
  calc
    A.twoClockStoppedLindebergTerm b c delta n k omega ≤
        ∑ j, A.twoClockStoppedLindebergTerm b c delta n j omega := by
      exact Finset.single_le_sum
        (fun j _ => A.twoClockStoppedLindebergTerm_nonneg b c delta n j omega)
        (Finset.mem_univ k)
    _ ≤ c := A.fin_twoClockStoppedLindeberg_le b c delta hc n omega

lemma twoClockStoppedConditionalVariance_le_delta_sq_add_c_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (n : ℕ)
    (k : Fin (A.rowLength n)) :
    A.twoClockStoppedConditionalVariance b c delta n k ≤ᵐ[A.probability n]
      (fun _ => delta ^ 2 + c) := by
  filter_upwards [A.twoClockStoppedConditionalVariance_le hA b c delta hdelta n k]
    with omega hk
  linarith [A.twoClockStoppedLindebergTerm_le_c b c delta hc n k omega]

lemma twoClockStoppedConditionalVariance_max_bound_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (n : ℕ) :
    ∀ᵐ omega ∂(A.probability n), ∀ k : Fin (A.rowLength n),
      A.twoClockStoppedConditionalVariance b c delta n k omega ≤ delta ^ 2 + c := by
  rw [ae_all_iff]
  intro k
  exact A.twoClockStoppedConditionalVariance_le_delta_sq_add_c_ae
    hA b c delta hc hdelta n k

lemma twoClockStoppedConditionalVariance_sq_sum_le_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 ≤ delta) (n : ℕ) :
    (fun omega => ∑ k,
      (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2) ≤ᵐ[A.probability n]
      (fun _ => b * (delta ^ 2 + c)) := by
  have hall := A.twoClockStoppedConditionalVariance_max_bound_ae
    hA b c delta hc hdelta n
  filter_upwards [hall] with omega hω
  have hD : 0 ≤ delta ^ 2 + c := by positivity
  have hsum := A.fin_twoClockStoppedVariance_le b c delta hb n omega
  have hsq : ∀ k : Fin (A.rowLength n),
      (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 ≤
        (delta ^ 2 + c) *
          A.twoClockStoppedConditionalVariance b c delta n k omega := by
    intro k
    have hw := A.twoClockStoppedConditionalVariance_nonneg b c delta n k omega
    have hk := hω k
    simpa [pow_two, mul_comm] using
      (mul_le_mul_of_nonneg_left hk hw)
  calc
    (∑ k, (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2) ≤
        ∑ k, (delta ^ 2 + c) *
          A.twoClockStoppedConditionalVariance b c delta n k omega :=
      Finset.sum_le_sum (fun k _ => hsq k)
    _ = (delta ^ 2 + c) *
          ∑ k, A.twoClockStoppedConditionalVariance b c delta n k omega := by
      rw [Finset.mul_sum]
    _ ≤ (delta ^ 2 + c) * b :=
      mul_le_mul_of_nonneg_left hsum hD
    _ = b * (delta ^ 2 + c) := by ring


/-- Natural-indexed zero-padded version of the two-clock stopped row. -/
def twoClockPaddedStoppedIncrement (b c delta : ℝ) (n k : ℕ) : Omega n → ℝ :=
  if hk : k < A.rowLength n then
    A.twoClockStoppedIncrement b c delta n ⟨k, hk⟩ else 0

lemma twoClockPaddedStoppedIncrement_stronglyMeasurable
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n k : ℕ) :
    StronglyMeasurable[A.filtration n (k + 1)]
      (A.twoClockPaddedStoppedIncrement b c delta n k) := by
  unfold twoClockPaddedStoppedIncrement
  split_ifs with hk
  · exact A.twoClockStoppedIncrement_stronglyMeasurable hA b c delta n ⟨k, hk⟩
  · exact stronglyMeasurable_const

lemma twoClockPaddedStoppedIncrement_memLp_two
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n k : ℕ) :
    MemLp (A.twoClockPaddedStoppedIncrement b c delta n k) 2 (A.probability n) := by
  unfold twoClockPaddedStoppedIncrement
  split_ifs with hk
  · exact A.twoClockStoppedIncrement_memLp_two hA b c delta n ⟨k, hk⟩
  · exact (MemLp.zero : MemLp (0 : Omega n → ℝ) 2 (A.probability n))

lemma twoClockPaddedStoppedIncrement_condExp_zero
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n k : ℕ) :
    (A.probability n)[A.twoClockPaddedStoppedIncrement b c delta n k |
      A.filtration n k] =ᵐ[A.probability n] 0 := by
  unfold twoClockPaddedStoppedIncrement
  split_ifs with hk
  · simpa using A.twoClockStoppedIncrement_condExp_zero hA b c delta n ⟨k, hk⟩
  · change (A.probability n)[(0 : Omega n → ℝ) | A.filtration n k] =ᵐ[A.probability n] 0
    rw [condExp_zero]

/-- Padded stopped row partial sums and its predictable square clock. -/
def twoClockStoppedPartialSum (b c delta : ℝ) (n j : ℕ) : Omega n → ℝ :=
  natPartialSum (A.twoClockPaddedStoppedIncrement b c delta n) j

def twoClockPaddedStoppedConditionalVariance
    (b c delta : ℝ) (n k : ℕ) : Omega n → ℝ :=
  if hk : k < A.rowLength n then
    A.twoClockStoppedConditionalVariance b c delta n ⟨k, hk⟩ else 0

lemma twoClockPaddedStoppedConditionalVariance_sq_condExp
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n k : ℕ) :
    (A.probability n)[fun omega =>
      (A.twoClockPaddedStoppedIncrement b c delta n k omega) ^ 2 |
      A.filtration n k] =ᵐ[A.probability n]
      A.twoClockPaddedStoppedConditionalVariance b c delta n k := by
  unfold twoClockPaddedStoppedIncrement twoClockPaddedStoppedConditionalVariance
  split_ifs with hk
  · have hraw := A.twoClockStoppedIncrement_sq_condExp hA b c delta n ⟨k, hk⟩
    have hnonneg := A.conditionalVariance_eq_nonnegative_ae hA n ⟨k, hk⟩
    filter_upwards [hraw, hnonneg] with omega hsq hvar
    rw [hsq]
    by_cases hs : omega ∈ A.twoClockStopSet b c delta n ⟨k, hk⟩
    · simp [twoClockStoppedConditionalVariance, hs, hvar]
    · simp [twoClockStoppedConditionalVariance, hs]
  · have hz : (fun omega : Omega n =>
        (0 : Omega n → ℝ) omega ^ 2) = (0 : Omega n → ℝ) := by
      funext x
      simp
    rw [hz, condExp_zero]

/-- Finite stopped-row terminal estimate.  The square term is explicitly the
predictable stopped variance, obtained from the stopped-square conditional-expectation
identity; the generic estimate therefore uses conditional centering and predictable
measurability rather than an unconditional square replacement. -/
theorem terminalCharacteristicFunctionEstimate_twoClockStopped
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ) (t : ℝ) :
    ‖(∫ omega, complexPhase t
        (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
        ∂(A.probability n)) - 1 +
        (((t ^ 2 / 2 : ℝ) : ℂ) *
          ∑ k : Fin (A.rowLength n), ∫ omega,
            complexPhase t
              (A.twoClockStoppedPartialSum b c delta n k.val omega) *
              (A.twoClockStoppedConditionalVariance b c delta n k omega)
              ∂(A.probability n))‖ ≤
      ∑ k : Fin (A.rowLength n), ∫ omega, ‖thirdOrderRemainder t
        (A.twoClockStoppedIncrement b c delta n k omega)‖
        ∂(A.probability n) := by
  let D : ℕ → Omega n → ℝ := A.twoClockPaddedStoppedIncrement b c delta n
  have hmeas : ∀ j, StronglyMeasurable[A.filtration n (j + 1)] (D j) := by
    intro j
    exact A.twoClockPaddedStoppedIncrement_stronglyMeasurable hA b c delta n j
  have hL2 : ∀ j, MemLp (D j) 2 (A.probability n) := by
    intro j
    exact A.twoClockPaddedStoppedIncrement_memLp_two hA b c delta n j
  have hcentered : ∀ j,
      (A.probability n)[D j | A.filtration n j] =ᵐ[A.probability n] 0 := by
    intro j
    exact A.twoClockPaddedStoppedIncrement_condExp_zero hA b c delta n j
  have h := terminalCharacteristicFunctionEstimate_predictable
    (P := A.probability n) (F := A.filtration n) D t (A.rowLength n)
    hmeas hL2 hcentered
  have hsq : ∀ k : Fin (A.rowLength n),
      (A.probability n)[fun x => (D k.val x) ^ 2 | A.filtration n k.val] =ᵐ[A.probability n]
        A.twoClockPaddedStoppedConditionalVariance b c delta n k.val := by
    intro k
    exact A.twoClockPaddedStoppedConditionalVariance_sq_condExp hA b c delta n k.val
  have hsum : (∑ k ∈ Finset.range (A.rowLength n), ∫ omega,
        complexPhase t (natPartialSum D k omega) *
          ((A.probability n)[fun x => (D k x) ^ 2 | A.filtration n k] omega : ℝ)
          ∂(A.probability n)) =
      ∑ k : Fin (A.rowLength n), ∫ omega,
        complexPhase t (A.twoClockStoppedPartialSum b c delta n k.val omega) *
          A.twoClockStoppedConditionalVariance b c delta n k omega
          ∂(A.probability n) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < A.rowLength n := k.isLt
    have hsqk := hsq ⟨k, hklt⟩
    have heq : (fun omega => complexPhase t (natPartialSum D k omega) *
          ((A.probability n)[fun x => (D k x) ^ 2 | A.filtration n k] omega : ℝ)) =ᵐ[A.probability n]
        (fun omega => complexPhase t
          (A.twoClockStoppedPartialSum b c delta n k omega) *
          A.twoClockStoppedConditionalVariance b c delta n ⟨k, hklt⟩ omega) := by
      filter_upwards [hsqk] with omega hω
      simpa [D, twoClockStoppedPartialSum, natPartialSum,
        twoClockPaddedStoppedIncrement, twoClockPaddedStoppedConditionalVariance,
        hklt] using congrArg (fun z : ℝ =>
          complexPhase t (natPartialSum D k omega) * z) hω
    exact integral_congr_ae heq
  have hrem :
      (∑ k ∈ Finset.range (A.rowLength n), ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂(A.probability n)) =
      ∑ k : Fin (A.rowLength n), ∫ omega,
        ‖thirdOrderRemainder t
          (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    apply integral_congr_ae
    filter_upwards [] with omega
    simp [D, twoClockPaddedStoppedIncrement, k.isLt]
  rw [hsum] at h
  calc
    ‖(∫ omega, complexPhase t
        (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
        ∂(A.probability n)) - 1 +
        (((t ^ 2 / 2 : ℝ) : ℂ) *
          ∑ k : Fin (A.rowLength n), ∫ omega,
            complexPhase t
              (A.twoClockStoppedPartialSum b c delta n k.val omega) *
              (A.twoClockStoppedConditionalVariance b c delta n k omega)
              ∂(A.probability n))‖ ≤
      ∑ k ∈ Finset.range (A.rowLength n), ∫ omega,
        ‖thirdOrderRemainder t (D k omega)‖ ∂(A.probability n) := by
          simpa [D, twoClockStoppedPartialSum, natPartialSum] using h
    _ = ∑ k : Fin (A.rowLength n), ∫ omega,
        ‖thirdOrderRemainder t
          (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n) := hrem




/-- The stopped predictable-variance clock attached to the padded two-clock row. -/
def twoClockStoppedVarianceClock (b c delta : ℝ) (n j : ℕ) (omega : Omega n) : ℝ :=
  ∑ k ∈ Finset.range j,
    A.twoClockPaddedStoppedConditionalVariance b c delta n k omega

/-- The finite random-clock compensator used in the martingale-array Fourier argument. -/
def twoClockCompensator (b c delta t : ℝ) (n j : ℕ) (omega : Omega n) : ℂ :=
  (Real.exp ((t ^ 2 / 2) *
      (A.twoClockStoppedVarianceClock b c delta n j omega - 1)) : ℂ) *
    complexPhase t (A.twoClockStoppedPartialSum b c delta n j omega)


/-- One-step recurrence for the finite random-clock compensator. -/
lemma twoClockCompensator_succ_eq_mul
    (b c delta t : ℝ) (n j : ℕ) (omega : Omega n) :
    A.twoClockCompensator b c delta t n (j + 1) omega =
      (Real.exp ((t ^ 2 / 2) *
        A.twoClockPaddedStoppedConditionalVariance b c delta n j omega) : ℂ) *
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n j omega) *
        A.twoClockCompensator b c delta t n j omega := by
  simp [twoClockCompensator, twoClockStoppedVarianceClock,
    twoClockStoppedPartialSum, natPartialSum, Finset.sum_range_succ,
    complexPhase]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Deterministic finite telescoping identity for the random-clock compensator. -/
lemma twoClockCompensator_sub_initial_eq_sum
    (b c delta t : ℝ) (n N : ℕ) (omega : Omega n) :
    A.twoClockCompensator b c delta t n N omega -
        A.twoClockCompensator b c delta t n 0 omega =
      ∑ k ∈ Finset.range N,
        (A.twoClockCompensator b c delta t n (k + 1) omega -
          A.twoClockCompensator b c delta t n k omega) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        A.twoClockCompensator b c delta t n (N + 1) omega -
            A.twoClockCompensator b c delta t n 0 omega =
          (A.twoClockCompensator b c delta t n (N + 1) omega -
            A.twoClockCompensator b c delta t n N omega) +
            (A.twoClockCompensator b c delta t n N omega -
              A.twoClockCompensator b c delta t n 0 omega) := by ring
        _ = ∑ k ∈ Finset.range N,
              (A.twoClockCompensator b c delta t n (k + 1) omega -
                A.twoClockCompensator b c delta t n k omega) +
            (A.twoClockCompensator b c delta t n (N + 1) omega -
              A.twoClockCompensator b c delta t n N omega) := by
          rw [ih]
          ac_rfl


/-- Quadratic remainder estimate for the scalar exponential, in the normalization used by
`twoClockCompensator`. -/
lemma abs_real_exp_sub_linear_le (x : ℝ) (hx : |x| ≤ 1) :
    |Real.exp x - 1 - x| ≤ (3 / 4 : ℝ) * |x| ^ 2 := by
  have h := Real.exp_bound (x := x) hx (n := 2) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  convert h using 1 <;> ring


/-- A finite one-step Fourier-weighted scalar compensator estimate.  The phase has unit
norm, so the error of multiplying the linearized factor `1-a*w` by `exp(a*w)` is
quadratic in `a*w`. -/
lemma twoClockCompensator_oneStep_error
    (a w t d : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hsmall : a * w ≤ 1) :
    ‖(Real.exp (a * w) : ℂ) * complexPhase t d * (1 - (a * w : ℂ)) -
        complexPhase t d‖ ≤ (7 / 4 : ℝ) * (a * w) ^ 2 := by
  have hscalar :
      ‖(Real.exp (a * w) : ℂ) * (1 - (a * w : ℂ)) - 1‖ ≤
        (7 / 4 : ℝ) * (a * w) ^ 2 := by
    have hreal : |Real.exp (a * w) * (1 - a * w) - 1| ≤
        (7 / 4 : ℝ) * (a * w) ^ 2 := by
      have h := abs_real_exp_sub_linear_le (a * w) (by
        rw [abs_of_nonneg (mul_nonneg ha hw)]
        exact hsmall)
      have h1 : |1 - a * w| ≤ (1 : ℝ) := by
        rw [abs_le]
        constructor <;> nlinarith
      calc
        |Real.exp (a * w) * (1 - a * w) - 1| =
            |(Real.exp (a * w) - 1 - a * w) * (1 - a * w) -
              (a * w) ^ 2| := by
                congr 1 <;> ring
        _ ≤ |Real.exp (a * w) - 1 - a * w| * |1 - a * w| +
            |(a * w) ^ 2| := by
          simpa only [abs_mul] using
            (abs_sub ((Real.exp (a * w) - 1 - a * w) * (1 - a * w))
              ((a * w) ^ 2))
        _ ≤ ((3 / 4 : ℝ) * |a * w| ^ 2) * 1 + (a * w) ^ 2 := by
          apply add_le_add
          · exact mul_le_mul h h1 (abs_nonneg _) (by positivity)
          · rw [abs_of_nonneg (sq_nonneg (a * w))]
        _ = (7 / 4 : ℝ) * (a * w) ^ 2 := by
          rw [abs_of_nonneg (mul_nonneg ha hw)]
          ring
    calc
      ‖(Real.exp (a * w) : ℂ) * (1 - (a * w : ℂ)) - 1‖ =
          ‖((Real.exp (a * w) * (1 - a * w) - 1 : ℝ) : ℂ)‖ := by
            congr 1
            push_cast
            ring
      _ = |Real.exp (a * w) * (1 - a * w) - 1| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (7 / 4 : ℝ) * (a * w) ^ 2 := hreal
  calc
    ‖(Real.exp (a * w) : ℂ) * complexPhase t d * (1 - (a * w : ℂ)) -
        complexPhase t d‖ =
        ‖complexPhase t d *
          ((Real.exp (a * w) : ℂ) * (1 - (a * w : ℂ)) - 1)‖ := by
            congr 1
            ring
    _ = ‖complexPhase t d‖ *
          ‖(Real.exp (a * w) : ℂ) * (1 - (a * w : ℂ)) - 1‖ := norm_mul _ _
    _ = ‖(Real.exp (a * w) : ℂ) * (1 - (a * w : ℂ)) - 1‖ := by
      have hnorm : ‖complexPhase t d‖ = (1 : ℝ) := by
        unfold complexPhase
        rw [show Complex.I * (t * d : ℝ) = Complex.I * ((t * d : ℝ) : ℂ) by
          push_cast; ring]
        exact Complex.norm_exp_I_mul_ofReal _
      rw [hnorm, one_mul]
    _ ≤ (7 / 4 : ℝ) * (a * w) ^ 2 := hscalar

/-- Summed finite-row form of the preceding one-step random-clock inequality. -/
theorem twoClockCompensator_fourierStepError_sum_le_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hsmall : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    (fun omega => ∑ k : Fin (A.rowLength n),
      ‖(Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) -
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega)‖) ≤ᵐ[A.probability n]
      (fun _ => (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)) := by
  have hmax := A.twoClockStoppedConditionalVariance_max_bound_ae
    hA b c delta hc hdelta n
  have hsq := A.twoClockStoppedConditionalVariance_sq_sum_le_ae
    hA b c delta hb hc hdelta n
  filter_upwards [hmax, hsq] with omega hmaxω hsqω
  let a : ℝ := t ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hterm : ∀ k : Fin (A.rowLength n),
      ‖(Real.exp (a * A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega) *
        (1 - ((a * A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) -
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega)‖ ≤
      (7 / 4 : ℝ) * a ^ 2 *
        (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
    intro k
    let w := A.twoClockStoppedConditionalVariance b c delta n k omega
    have hw : 0 ≤ w := A.twoClockStoppedConditionalVariance_nonneg b c delta n k omega
    have hx : a * w ≤ 1 := by
      exact (mul_le_mul_of_nonneg_left (hmaxω k) ha).trans (by simpa [a] using hsmall)
    have hstep := twoClockCompensator_oneStep_error a w t
      (A.twoClockPaddedStoppedIncrement b c delta n k omega) hw ha hx
    calc
      _ ≤ (7 / 4 : ℝ) * (a * w) ^ 2 := by simpa [w] using hstep
      _ = (7 / 4 : ℝ) * a ^ 2 * w ^ 2 := by ring
  calc
    (∑ k : Fin (A.rowLength n),
      ‖(Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) -
        complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega)‖) ≤
      ∑ k : Fin (A.rowLength n), (7 / 4 : ℝ) * a ^ 2 *
        (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
          simpa [a] using Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((7 / 4 : ℝ) * a ^ 2) *
        ∑ k : Fin (A.rowLength n),
          (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ((7 / 4 : ℝ) * a ^ 2) * (b * (delta ^ 2 + c)) :=
      mul_le_mul_of_nonneg_left hsqω (by positivity)
    _ = (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) := by
      dsimp [a]
      ring



/-- Finite random-clock compensator inequality.  Its first summand is the stopped terminal
Fourier estimate, whose proof uses predictable stop-set measurability, conditional centering,
and the stopped-square conditional-expectation identity.  Its second summand is the explicit
one-step exponential compensation error proved above. -/
theorem twoClockCompensator_finite_randomClock_inequality
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hsmall : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    (fun omega =>
      ‖(∫ z, complexPhase t
          (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) z)
          ∂(A.probability n)) - 1 +
        (((t ^ 2 / 2 : ℝ) : ℂ) *
          ∑ k : Fin (A.rowLength n), ∫ z,
            complexPhase t
              (A.twoClockStoppedPartialSum b c delta n k.val z) *
              A.twoClockStoppedConditionalVariance b c delta n k z
              ∂(A.probability n))‖ +
      ∑ k : Fin (A.rowLength n),
        ‖(Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
          complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega) *
          (1 - (((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) -
          complexPhase t (A.twoClockPaddedStoppedIncrement b c delta n k omega)‖) ≤ᵐ[A.probability n]
      (fun omega =>
        (∑ k : Fin (A.rowLength n), ∫ z,
          ‖thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k z)‖
          ∂(A.probability n)) +
        (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)) := by
  have hterminal := A.terminalCharacteristicFunctionEstimate_twoClockStopped
    hA b c delta n t
  have hstep := A.twoClockCompensator_fourierStepError_sum_le_ae
    hA b c delta t hb hc hdelta hsmall n
  filter_upwards [hstep] with omega hω
  exact add_le_add hterminal hω



/-- The deterministic error in the finite random-clock estimate vanishes when the two
localization parameters `(delta,c)` tend jointly to zero, with `b,t` fixed. -/
theorem twoClockCompensator_error_bound_tendsto_zero (b t : ℝ) :
    Tendsto (fun p : ℝ × ℝ =>
      (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (p.1 ^ 2 + p.2))
      (𝓝 ((0 : ℝ), (0 : ℝ))) (𝓝 0) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ =>
      (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (p.1 ^ 2 + p.2)) (0, 0) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (p.1 ^ 2 + p.2))).continuousAt
  have hzero : (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b *
      (((0 : ℝ), (0 : ℝ)).1 ^ 2 + ((0 : ℝ), (0 : ℝ)).2) = 0 := by norm_num
  rw [ContinuousAt, hzero] at hc
  exact hc


/-- The exponential-clock part of the random compensator has a deterministic aggregate
quadratic error.  Its bound is `3/4 * (t²/2)² * b * (delta²+c)`, hence tends to zero as
`c, delta → 0` for fixed `b,t`. -/
theorem twoClockCompensator_exponentialError_sum_le_ae
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hsmall : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    (fun omega => ∑ k : Fin (A.rowLength n),
      |Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) - 1 -
        (t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega|) ≤ᵐ[A.probability n]
      (fun _ => (3 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)) := by
  have hmax := A.twoClockStoppedConditionalVariance_max_bound_ae
    hA b c delta hc hdelta n
  have hsq := A.twoClockStoppedConditionalVariance_sq_sum_le_ae
    hA b c delta hb hc hdelta n
  filter_upwards [hmax, hsq] with omega hmaxω hsqω
  let a : ℝ := t ^ 2 / 2
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hterm : ∀ k : Fin (A.rowLength n),
      |Real.exp (a * A.twoClockStoppedConditionalVariance b c delta n k omega) - 1 -
        a * A.twoClockStoppedConditionalVariance b c delta n k omega| ≤
      (3 / 4 : ℝ) * a ^ 2 *
        (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
    intro k
    let w := A.twoClockStoppedConditionalVariance b c delta n k omega
    have hw : 0 ≤ w := A.twoClockStoppedConditionalVariance_nonneg b c delta n k omega
    have hxnonneg : 0 ≤ a * w := mul_nonneg ha hw
    have hx : |a * w| ≤ 1 := by
      rw [abs_of_nonneg hxnonneg]
      exact (mul_le_mul_of_nonneg_left (hmaxω k) ha).trans (by simpa [a] using hsmall)
    calc
      |Real.exp (a * w) - 1 - a * w| ≤ (3 / 4 : ℝ) * |a * w| ^ 2 :=
        abs_real_exp_sub_linear_le (a * w) hx
      _ = (3 / 4 : ℝ) * a ^ 2 * w ^ 2 := by
        rw [abs_of_nonneg hxnonneg]
        ring
  calc
    (∑ k : Fin (A.rowLength n),
      |Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) - 1 -
        (t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega|) ≤
      ∑ k : Fin (A.rowLength n), (3 / 4 : ℝ) * a ^ 2 *
        (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
          simpa [a] using Finset.sum_le_sum (fun k _ => hterm k)
    _ = ((3 / 4 : ℝ) * a ^ 2) *
        ∑ k : Fin (A.rowLength n),
          (A.twoClockStoppedConditionalVariance b c delta n k omega) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ((3 / 4 : ℝ) * a ^ 2) * (b * (delta ^ 2 + c)) :=
      mul_le_mul_of_nonneg_left hsqω (by positivity)
    _ = (3 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) := by
      dsimp [a]
      ring


lemma twoClockStopEvent_measurable
    (b c delta : ℝ) (n : ℕ) :
    MeasurableSet (A.twoClockStopEvent b c delta n) := by
  classical
  rw [twoClockStopEvent]
  have heq :
      {omega | ∃ k : Fin (A.rowLength n),
        omega ∉ A.twoClockStopSet b c delta n k} =
        ⋃ k : Fin (A.rowLength n),
          (A.twoClockStopSet b c delta n k)ᶜ := by
    ext omega
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun k =>
    (A.twoClockStopSet_ambientMeasurable b c delta n k).compl)


lemma twoClockPaddedStoppedIncrement_eq_paddedIncrement_of_not_stopEvent
    (b c delta : ℝ) (n k : ℕ) (omega : Omega n)
    (hω : omega ∉ A.twoClockStopEvent b c delta n) :
    A.twoClockPaddedStoppedIncrement b c delta n k omega =
      A.paddedIncrement n k omega := by
  by_cases hklt : k < A.rowLength n
  · have hall : omega ∈ A.twoClockStopSet b c delta n ⟨k, hklt⟩ := by
      by_contra hk
      exact hω ⟨⟨k, hklt⟩, hk⟩
    simp [twoClockPaddedStoppedIncrement, twoClockStoppedIncrement,
      paddedIncrement, hklt, Set.indicator_of_mem hall]
  · simp [twoClockPaddedStoppedIncrement, paddedIncrement, hklt]


lemma twoClockStoppedPartialSum_eq_rowSum_of_not_stopEvent
    (b c delta : ℝ) (n : ℕ) (omega : Omega n)
    (hω : omega ∉ A.twoClockStopEvent b c delta n) :
    A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega =
      A.rowSum n omega := by
  have hall : ∀ k : Fin (A.rowLength n),
      omega ∈ A.twoClockStopSet b c delta n k := by
    intro k
    by_contra hk
    exact hω ⟨k, hk⟩
  rw [A.rowSum_eq_partialSum_rowLength n]
  simp only [twoClockStoppedPartialSum, partialSum, natPartialSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < A.rowLength n := (Finset.mem_range.mp hk)
  simp only [twoClockPaddedStoppedIncrement, dif_pos hklt,
    twoClockStoppedIncrement]
  rw [Set.indicator_of_mem (hall ⟨k, hklt⟩)]
  simp [paddedIncrement, hklt]



/-- A reusable original-versus-stopped characteristic-function comparison.  Once the
rows agree off `E`, the bounded Fourier phase gives the sharp `2 P(E)` estimate. -/
theorem complexPhase_integral_diff_le_twice_measure
    (n : ℕ) (t : ℝ) {f g : Omega n → ℝ} {E : Set (Omega n)}
    (hE : MeasurableSet E)
    (hf : Integrable (fun omega => complexPhase t (f omega)) (A.probability n))
    (hg : Integrable (fun omega => complexPhase t (g omega)) (A.probability n))
    (hEq : ∀ᵐ omega ∂(A.probability n), omega ∉ E → f omega = g omega) :
    ‖(∫ omega, complexPhase t (f omega) ∂(A.probability n)) -
        ∫ omega, complexPhase t (g omega) ∂(A.probability n)‖ ≤
      2 * (A.probability n).real E := by
  have hdiff : Integrable
      (fun omega => complexPhase t (f omega) - complexPhase t (g omega))
      (A.probability n) := hf.sub hg
  have hind : Integrable (E.indicator (fun _ : Omega n => (2 : ℝ)))
      (A.probability n) := (integrable_const (2 : ℝ)).indicator hE
  rw [← integral_sub hf hg]
  calc
    ‖∫ omega, (complexPhase t (f omega) - complexPhase t (g omega))
        ∂(A.probability n)‖ ≤
        ∫ omega, E.indicator (fun _ : Omega n => (2 : ℝ)) omega
          ∂(A.probability n) := by
      apply norm_integral_le_of_norm_le hind
      filter_upwards [hEq] with omega hω
      by_cases hmem : omega ∈ E
      · have h1 : ‖complexPhase t (f omega)‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        have h2 : ‖complexPhase t (g omega)‖ = 1 :=
          Complex.norm_exp_I_mul_ofReal _
        rw [Set.indicator_of_mem hmem]
        calc
          ‖complexPhase t (f omega) - complexPhase t (g omega)‖ ≤
              ‖complexPhase t (f omega)‖ + ‖complexPhase t (g omega)‖ :=
            norm_sub_le _ _
          _ = 2 := by rw [h1, h2]; norm_num
      · simp [hmem, hω]
    _ = 2 * (A.probability n).real E := by
      rw [integral_indicator hE]
      simp [smul_eq_mul]
      ring


/-- The stopped and original terminal Fourier integrals differ only on the prospective
stop event.  This is the requested clipped-to-event estimate before taking limits. -/
theorem twoClockStopped_original_phase_integral_diff_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ) (n : ℕ) :
    ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
        ∫ omega, complexPhase t
          (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
          ∂(A.probability n)‖ ≤
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n) := by
  have hE := A.twoClockStopEvent_measurable b c delta n
  have hrowmeas : AEStronglyMeasurable (A.rowSum n) (A.probability n) := by
    rw [A.rowSum_eq_partialSum_rowLength n]
    exact (natPartialSum_stronglyAdapted (A.paddedIncrement n)
      (A.paddedIncrement_stronglyMeasurable hA n) (A.rowLength n)).aestronglyMeasurable.mono
      ((A.filtration n).le (A.rowLength n))
  have hstopmeas : AEStronglyMeasurable
      (A.twoClockStoppedPartialSum b c delta n (A.rowLength n))
      (A.probability n) := by
    apply (natPartialSum_stronglyAdapted
      (A.twoClockPaddedStoppedIncrement b c delta n)
      (fun j => A.twoClockPaddedStoppedIncrement_stronglyMeasurable
        hA b c delta n j) (A.rowLength n)).aestronglyMeasurable.mono
    exact (A.filtration n).le (A.rowLength n)
  apply A.complexPhase_integral_diff_le_twice_measure n t hE
    (integrable_complexPhase_comp hrowmeas t)
    (integrable_complexPhase_comp hstopmeas t)
  filter_upwards [] with omega
  intro hnot
  exact A.twoClockStoppedPartialSum_eq_rowSum_of_not_stopEvent b c delta n omega hnot |>.symm


/-- For fixed positive clock thresholds, the stopped/original Fourier discrepancy vanishes
along the row limit.  This is the fixed-parameter consequence of the prospective stopping
inclusion, not an unconditional characteristic-function CLT. -/
theorem twoClockStopped_original_phase_integral_diff_tendsto_zero
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (b c delta t : ℝ) (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta) :
    Tendsto (fun n =>
      ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
        ∫ omega, complexPhase t
          (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
          ∂(A.probability n)‖) atTop (nhds 0) := by
  have hprob := A.twoClockStopEvent_measure_tendsto_zero
    hA hQV hLindeberg b c delta hb hc hdelta
  have hreal : Tendsto (fun n =>
      (A.probability n).real (A.twoClockStopEvent b c delta n))
      atTop (nhds 0) := by
    apply (ENNReal.tendsto_toReal_zero_iff (f := fun n =>
      (A.probability n) (A.twoClockStopEvent b c delta n))
      (fun n => measure_ne_top (A.probability n) _)).2
    exact hprob
  have hscaled : Tendsto (fun n =>
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hreal)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hscaled
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
    (Filter.Eventually.of_forall (fun n =>
      A.twoClockStopped_original_phase_integral_diff_le hA b c delta t n))


/-- Measurability of the terminal stopped predictable-variance clock. -/
lemma twoClockStoppedVarianceClock_measurable
    (b c delta : ℝ) (n : ℕ) :
    Measurable (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n)) := by
  unfold twoClockStoppedVarianceClock
  apply Finset.measurable_sum
  intro k hk
  unfold twoClockPaddedStoppedConditionalVariance
  split_ifs with hlt
  · exact ((A.nonnegativeConditionalVariance_stronglyMeasurable n ⟨k, hlt⟩).mono
      ((A.filtration n).le k)).measurable.indicator
      (A.twoClockStopSet_ambientMeasurable b c delta n ⟨k, hlt⟩)
  · exact measurable_const

/-- Off the prospective stopping event, the stopped terminal variance clock agrees a.e.
with the original predictable quadratic variation. -/
lemma twoClockStoppedVarianceClock_eq_original_of_not_stopEvent
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ) :
    ∀ᵐ omega ∂(A.probability n),
      omega ∉ A.twoClockStopEvent b c delta n →
      A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega =
        A.predictableQuadraticVariation n omega := by
  have hvar := A.predictableQuadraticVariation_eq_nonnegative_sum_ae hA n
  filter_upwards [hvar] with omega hvar hnot
  have hall : ∀ k : Fin (A.rowLength n),
      omega ∈ A.twoClockStopSet b c delta n k := by
    intro k
    by_contra hk
    exact hnot ⟨k, hk⟩
  rw [twoClockStoppedVarianceClock]
  rw [show (∑ k ∈ Finset.range (A.rowLength n),
      A.twoClockPaddedStoppedConditionalVariance b c delta n k omega) =
      ∑ k : Fin (A.rowLength n),
        A.twoClockStoppedConditionalVariance b c delta n k omega by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp [twoClockPaddedStoppedConditionalVariance, k.isLt]]
  rw [show (∑ k : Fin (A.rowLength n),
      A.twoClockStoppedConditionalVariance b c delta n k omega) =
      ∑ k : Fin (A.rowLength n),
        A.nonnegativeConditionalVariance n k omega by
    apply Finset.sum_congr rfl
    intro k hk
    simp [twoClockStoppedConditionalVariance, hall k]]
  simpa [predictableQuadraticVariation] using (congrArg id hvar).symm

/-- Every partial stopped variance clock is bounded by the prospective variance budget. -/
lemma twoClockStoppedVarianceClock_le
    (b c delta : ℝ) (hb : 0 ≤ b) (n j : ℕ)
    (hj : j ≤ A.rowLength n) (omega : Omega n) :
    A.twoClockStoppedVarianceClock b c delta n j omega ≤ b := by
  have hpart : A.twoClockStoppedVarianceClock b c delta n j omega ≤
      A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega := by
    unfold twoClockStoppedVarianceClock
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (s := Finset.range j) (t := Finset.range (A.rowLength n))
      (f := fun k => A.twoClockPaddedStoppedConditionalVariance b c delta n k omega)
      (Finset.range_mono hj) (fun k hk _ => by
        have hk' : k < A.rowLength n := Finset.mem_range.mp hk
        simp [twoClockPaddedStoppedConditionalVariance, hk',
          A.twoClockStoppedConditionalVariance_nonneg b c delta n ⟨k, hk'⟩ omega])
  rw [show A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega =
      ∑ k : Fin (A.rowLength n), A.twoClockStoppedConditionalVariance b c delta n k omega by
    unfold twoClockStoppedVarianceClock
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp [twoClockPaddedStoppedConditionalVariance, k.isLt]] at hpart
  exact hpart.trans (A.fin_twoClockStoppedVariance_le b c delta hb n omega)

/-- The stopped terminal variance clock converges in probability to one. -/
theorem twoClockStoppedVarianceClock_tendstoInProbability_one
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (b c delta : ℝ) (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta) :
    TendstoInProbabilityVarying Omega A.probability
      (fun n omega => A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega)
      atTop 1 := by
  have hstop := A.twoClockStopEvent_measure_tendsto_zero
    hA hQV hLindeberg b c delta hb hc hdelta
  intro epsilon hepsilon
  have hQVε := hQV epsilon hepsilon
  have hsubset : ∀ n,
      (A.probability n) {omega |
        epsilon ≤ |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1|} ≤
        (A.probability n) {omega |
          epsilon ≤ |A.predictableQuadraticVariation n omega - 1|} +
        (A.probability n) (A.twoClockStopEvent b c delta n) := by
    intro n
    apply (measure_mono_ae ?_).trans (measure_union_le _ _)
    have heq := A.twoClockStoppedVarianceClock_eq_original_of_not_stopEvent
      hA b c delta n
    filter_upwards [heq] with omega hEq
    change (epsilon ≤ |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1|) →
      epsilon ≤ |A.predictableQuadraticVariation n omega - 1| ∨
        omega ∈ A.twoClockStopEvent b c delta n
    intro hXω
    by_cases hstopω : omega ∈ A.twoClockStopEvent b c delta n
    · exact Or.inr hstopω
    · left
      rw [hEq hstopω] at hXω
      exact hXω
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa only [add_zero] using hQVε.add hstop)
    (Filter.Eventually.of_forall (fun _ => bot_le))
    (Filter.Eventually.of_forall hsubset)

/-- For fixed localization parameters, the exponential terminal clock factor converges to
one in `L¹`.  This is the bounded continuous-transform step needed after clock stopping. -/
theorem twoClockStoppedVarianceClock_exp_factor_L1_tendsto_zero
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (b c delta t : ℝ) (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta) :
    Tendsto (fun n => ∫ omega,
      |Real.exp ((t ^ 2 / 2) *
        (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
      ∂(A.probability n)) atTop (nhds 0) := by
  by_cases ht : t = 0
  · subst t
    simp [Real.exp_zero]
  let a : ℝ := t ^ 2 / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  let X : (n : ℕ) → Omega n → ℝ := fun n omega =>
    |Real.exp (a *
      (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
  have hX : ∀ n, Measurable (X n) := by
    intro n
    dsimp [X]
    exact (((Real.measurable_exp.comp
      ((measurable_const.mul
        ((A.twoClockStoppedVarianceClock_measurable b c delta n).sub measurable_const)))).sub
          measurable_const).abs)
  have hVprob := A.twoClockStoppedVarianceClock_tendstoInProbability_one
    hA hQV hLindeberg b c delta hb hc hdelta
  have hXprob : TendstoInProbabilityVarying Omega A.probability X atTop 0 := by
    intro epsilon hepsilon
    let eta : ℝ := min (1 / (2 * a)) (epsilon / (2 * a))
    have heta : 0 < eta := by
      dsimp [eta]
      exact lt_min (by positivity) (by positivity)
    have hVε := hVprob eta heta
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hVε
      (Filter.Eventually.of_forall (fun _ => bot_le)) ?_
    filter_upwards [] with n
    apply measure_mono_ae
    filter_upwards [] with omega
    change (epsilon ≤ |X n omega - 0|) →
      eta ≤ |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1|
    intro hbad
    have hbad' : epsilon ≤ X n omega := by simpa [X] using hbad
    by_contra hnot
    have hd : |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1| < eta :=
      lt_of_not_ge hnot
    have hxa : |a * (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)| ≤ 1 := by
      rw [abs_mul, abs_of_pos ha]
      have hle : a * |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1| <
          a * (1 / (2 * a)) := by
        exact mul_lt_mul_of_pos_left (lt_of_lt_of_le hd (min_le_left _ _)) ha
      have heq : a * (1 / (2 * a)) = (1 / 2 : ℝ) := by field_simp
      linarith
    have hexp := Real.abs_exp_sub_one_le hxa
    have hsmall : X n omega < epsilon := by
      dsimp [X]
      calc
        |Real.exp (a *
            (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1| ≤
            2 * |a * (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)| := hexp
        _ = 2 * a * |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1| := by
          rw [abs_mul, abs_of_pos ha]
          ring
        _ < 2 * a * (epsilon / (2 * a)) :=
          mul_lt_mul_of_pos_left (lt_of_lt_of_le hd (min_le_right _ _)) (by positivity)
        _ = epsilon := by field_simp
    exact (not_lt_of_ge hbad') hsmall
  let C : ℝ := Real.exp (a * b) + 1
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  have hX0 : ∀ n omega, 0 ≤ X n omega := by intro n omega; exact abs_nonneg _
  have hXle : ∀ n omega, X n omega ≤ C := by
    intro n omega
    dsimp [X, C]
    have hb0 : 0 ≤ b := le_trans (by norm_num) (le_of_lt hb)
    have hVle := A.twoClockStoppedVarianceClock_le b c delta hb0
      n (A.rowLength n) (le_rfl) omega
    have hexp : Real.exp (a *
        (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) ≤
        Real.exp (a * b) := by
      have harg : a *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1) ≤ a * b := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt ha)
        linarith [hVle]
      exact Real.exp_le_exp.mpr harg
    calc
      |Real.exp (a *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1| ≤
          |Real.exp (a *
            (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1))| + |(1 : ℝ)| :=
        (by simpa using (abs_sub_le
          (Real.exp (a *
            (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1))) 0 1))
      _ = Real.exp (a *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) + 1 := by
        rw [abs_of_pos (Real.exp_pos _), abs_one]
      _ ≤ Real.exp (a * b) + 1 := by linarith [hexp]
  exact tendsto_integral_of_tendstoInProbabilityVarying_of_nonneg_bounded
    A.probability X C hX hX0 hC0 hXle hXprob


/-- The stopped terminal variance clock converges to one in the bounded clipped `L¹`
sense.  The proof combines the exact off-stop equality with the already encoded PQV limit
and the prospective stop-event probability bound. -/
theorem twoClockStoppedVarianceClock_clipped_L1_tendsto_zero
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition)
    (b c delta : ℝ) (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta) :
    Tendsto (fun n => ∫ omega,
      min 1 |A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1|
      ∂(A.probability n)) atTop (nhds 0) := by
  let X : (n : ℕ) → Omega n → ℝ := fun n omega =>
    A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega
  have hX : ∀ n, Measurable (X n) := by
    intro n
    exact A.twoClockStoppedVarianceClock_measurable b c delta n
  have hstop := A.twoClockStopEvent_measure_tendsto_zero
    hA hQV hLindeberg b c delta hb hc hdelta
  have hXprob : TendstoInProbabilityVarying Omega A.probability X atTop 1 := by
    intro epsilon hepsilon
    have hQVε := hQV epsilon hepsilon
    have hsubset : ∀ n,
        (A.probability n) {omega | epsilon ≤ |X n omega - 1|} ≤
          (A.probability n) {omega |
            epsilon ≤ |A.predictableQuadraticVariation n omega - 1|} +
          (A.probability n) (A.twoClockStopEvent b c delta n) := by
      intro n
      apply (measure_mono_ae ?_).trans (measure_union_le _ _)
      have heq := A.twoClockStoppedVarianceClock_eq_original_of_not_stopEvent
        hA b c delta n
      filter_upwards [heq] with omega hEq
      change (epsilon ≤ |X n omega - 1|) →
        epsilon ≤ |A.predictableQuadraticVariation n omega - 1| ∨
          omega ∈ A.twoClockStopEvent b c delta n
      intro hXω
      by_cases hstopω : omega ∈ A.twoClockStopEvent b c delta n
      · exact Or.inr hstopω
      · left
        have hxeq : X n omega = A.predictableQuadraticVariation n omega := hEq hstopω
        rw [hxeq] at hXω
        exact hXω
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds (by simpa only [add_zero] using hQVε.add hstop)
      (Filter.Eventually.of_forall (fun _ => bot_le))
      (Filter.Eventually.of_forall hsubset)
  exact tendsto_integral_min_one_abs_sub_of_tendstoInProbabilityVarying
    A.probability X 1 hX hXprob


/-! ## Exact predictable-multiplier random-clock compensator -/

/-- The stopped predictable conditional variance is measurable at its pre-increment
sigma-field. -/
lemma twoClockStoppedConditionalVariance_stronglyMeasurable
    (b c delta : ℝ) (n : ℕ) (k : Fin (A.rowLength n)) :
    StronglyMeasurable[A.filtration n k.val]
      (A.twoClockStoppedConditionalVariance b c delta n k) := by
  unfold twoClockStoppedConditionalVariance
  exact (A.nonnegativeConditionalVariance_stronglyMeasurable n k).indicator
    (A.twoClockStopSet_measurable b c delta n k)

/-- The padded stopped conditional variance is measurable at its natural predictable
index. -/
lemma twoClockPaddedStoppedConditionalVariance_stronglyMeasurable
    (b c delta : ℝ) (n k : ℕ) :
    StronglyMeasurable[A.filtration n k]
      (A.twoClockPaddedStoppedConditionalVariance b c delta n k) := by
  unfold twoClockPaddedStoppedConditionalVariance
  split_ifs with hk
  · exact A.twoClockStoppedConditionalVariance_stronglyMeasurable
      b c delta n ⟨k, hk⟩
  · exact stronglyMeasurable_const

/-- Every partial stopped variance clock is predictable at its terminal index. -/
lemma twoClockStoppedVarianceClock_stronglyMeasurable
    (b c delta : ℝ) (n j : ℕ) :
    StronglyMeasurable[A.filtration n j]
      (A.twoClockStoppedVarianceClock b c delta n j) := by
  unfold twoClockStoppedVarianceClock
  apply Finset.stronglyMeasurable_fun_sum
  intro k hk
  exact (A.twoClockPaddedStoppedConditionalVariance_stronglyMeasurable
    b c delta n k).mono ((A.filtration n).mono (Finset.mem_range.mp hk).le)

/-- The stopped random-clock compensator at time `j` is measurable at time `j`. -/
lemma twoClockCompensator_stronglyMeasurable
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ) (n j : ℕ) :
    StronglyMeasurable[A.filtration n j]
      (A.twoClockCompensator b c delta t n j) := by
  unfold twoClockCompensator
  have hV := A.twoClockStoppedVarianceClock_stronglyMeasurable b c delta n j
  have hS : StronglyMeasurable[A.filtration n j]
      (A.twoClockStoppedPartialSum b c delta n j) :=
    natPartialSum_stronglyAdapted
      (A.twoClockPaddedStoppedIncrement b c delta n)
      (fun k => A.twoClockPaddedStoppedIncrement_stronglyMeasurable
        hA b c delta n k) j
  exact (Complex.continuous_ofReal.comp_stronglyMeasurable
    (Real.continuous_exp.comp_stronglyMeasurable
      ((hV.sub stronglyMeasurable_const).const_mul (t ^ 2 / 2)))).mul
      ((continuous_complexPhase t).comp_stronglyMeasurable hS)

/-- Pointwise norm of the compensator on a stopped variance clock bounded by `b`. -/
lemma twoClockCompensator_norm_le
    (b c delta t : ℝ) (hb : 0 ≤ b) (n j : ℕ)
    (hj : j ≤ A.rowLength n) (omega : Omega n) :
    ‖A.twoClockCompensator b c delta t n j omega‖ ≤
      Real.exp ((t ^ 2 / 2) * b) := by
  unfold twoClockCompensator
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  rw [show ‖complexPhase t
      (A.twoClockStoppedPartialSum b c delta n j omega)‖ = 1 by
    exact Complex.norm_exp_I_mul_ofReal _, mul_one]
  apply Real.exp_le_exp.mpr
  have ha : 0 ≤ t ^ 2 / 2 := by positivity
  have hV := A.twoClockStoppedVarianceClock_le b c delta hb n j hj omega
  exact mul_le_mul_of_nonneg_left (by linarith) ha

/-- A bounded stopped compensator is integrable. -/
lemma twoClockCompensator_integrable
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ) (hb : 0 ≤ b)
    (n j : ℕ) (hj : j ≤ A.rowLength n) :
    Integrable (A.twoClockCompensator b c delta t n j) (A.probability n) := by
  apply Integrable.mono' (integrable_const (Real.exp ((t ^ 2 / 2) * b)))
  · exact (A.twoClockCompensator_stronglyMeasurable hA b c delta t n j).aestronglyMeasurable.mono
      ((A.filtration n).le j)
  · filter_upwards [] with omega
    simpa using A.twoClockCompensator_norm_le b c delta t hb n j hj omega

/-- A stopped predictable conditional variance is integrable because it is the conditional
expectation of the stopped square. -/
lemma twoClockStoppedConditionalVariance_integrable
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) :
    Integrable (A.twoClockStoppedConditionalVariance b c delta n k)
      (A.probability n) := by
  have hsq := A.twoClockPaddedStoppedConditionalVariance_sq_condExp
    hA b c delta n k.val
  have hint : Integrable
      ((A.probability n)[fun omega =>
        (A.twoClockPaddedStoppedIncrement b c delta n k.val omega) ^ 2 |
        A.filtration n k.val]) (A.probability n) :=
    integrable_condExp
  exact hint.congr (by
    simpa [twoClockPaddedStoppedConditionalVariance, k.isLt] using hsq)

/-- The conditional expectation of the stopped tail square is the stopped Lindeberg
clock term. -/
lemma twoClockStoppedTailSq_condExp
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (n : ℕ)
    (k : Fin (A.rowLength n)) :
    (A.probability n)[fun omega =>
      if delta < |A.twoClockStoppedIncrement b c delta n k omega| then
        (A.twoClockStoppedIncrement b c delta n k omega) ^ 2 else 0 |
      A.filtration n k.val] =ᵐ[A.probability n]
      A.twoClockStoppedLindebergTerm b c delta n k := by
  let E := A.twoClockStopSet b c delta n k
  let f : Omega n → ℝ := fun omega =>
    if delta < |A.increment n k omega| then (A.increment n k omega) ^ 2 else 0
  have hfun : (fun omega =>
      if delta < |A.twoClockStoppedIncrement b c delta n k omega| then
        (A.twoClockStoppedIncrement b c delta n k omega) ^ 2 else 0) =
      E.indicator f := by
    funext omega
    by_cases hE : omega ∈ E
    · simp [E, f, twoClockStoppedIncrement, hE]
    · simp [E, f, twoClockStoppedIncrement, hE]
  rw [hfun]
  have hfint : Integrable f (A.probability n) := by
    have hinc := (hA.memLp_two n k).integrable_sq
    have hsm : StronglyMeasurable (A.increment n k) :=
      (hA.stronglyMeasurable n k).mono ((A.filtration n).le (k.val + 1))
    have hset : MeasurableSet {omega : Omega n | delta < |A.increment n k omega|} :=
      measurableSet_lt measurable_const hsm.measurable.abs
    apply hinc.mono
    · exact ((hsm.pow 2).ite hset stronglyMeasurable_const).aestronglyMeasurable
    · filter_upwards [] with omega
      dsimp [f]
      by_cases h : delta < |A.increment n k omega|
      · simp [h]
      · simp [h]
        positivity
  have hpull := condExp_indicator hfint
    (A.twoClockStopSet_measurable b c delta n k)
  have hnonneg := A.conditionalLindebergTerm_eq_nonnegative_ae delta n k
  filter_upwards [hpull, hnonneg] with omega hpullω hnonnegω
  rw [hpullω]
  by_cases hE : omega ∈ E
  · simp [E, twoClockStoppedLindebergTerm, hE, f, hnonnegω]
  · simp [E, twoClockStoppedLindebergTerm, hE]

/-- Integrated stopped conditional variances sum to at most the deterministic variance
budget. -/
lemma integral_twoClockStoppedConditionalVariance_sum_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta : ℝ) (hb : 0 ≤ b)
    (n : ℕ) :
    (∑ k : Fin (A.rowLength n), ∫ omega,
      A.twoClockStoppedConditionalVariance b c delta n k omega
      ∂(A.probability n)) ≤ b := by
  have hint : ∀ k : Fin (A.rowLength n),
      Integrable (A.twoClockStoppedConditionalVariance b c delta n k)
        (A.probability n) := fun k =>
    A.twoClockStoppedConditionalVariance_integrable hA b c delta n k
  rw [← integral_finset_sum (s := Finset.univ) (fun k _ => hint k)]
  calc
    ∫ omega, ∑ k : Fin (A.rowLength n),
        A.twoClockStoppedConditionalVariance b c delta n k omega
        ∂(A.probability n) ≤ ∫ _omega : Omega n, b ∂(A.probability n) :=
      integral_mono_ae (MeasureTheory.integrable_finset_sum _ (fun k _ => hint k))
        (integrable_const _) (Filter.Eventually.of_forall (fun omega =>
          A.fin_twoClockStoppedVariance_le b c delta hb n omega))
    _ = b := by simp

/-- Integrated stopped Lindeberg clock terms sum to at most their deterministic budget. -/
lemma integral_twoClockStoppedLindebergTerm_sum_le
    (b c delta : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    (∑ k : Fin (A.rowLength n), ∫ omega,
      A.twoClockStoppedLindebergTerm b c delta n k omega
      ∂(A.probability n)) ≤ c := by
  have hint : ∀ k : Fin (A.rowLength n),
      Integrable (A.twoClockStoppedLindebergTerm b c delta n k)
        (A.probability n) := by
    intro k
    unfold twoClockStoppedLindebergTerm
    have hcond : Integrable
        ((A.probability n)[fun x => if delta < |A.increment n k x|
          then (A.increment n k x) ^ 2 else 0 | A.filtration n k.val])
        (A.probability n) := integrable_condExp
    exact (hcond.congr
      (A.conditionalLindebergTerm_eq_nonnegative_ae delta n k)).indicator
        (A.twoClockStopSet_ambientMeasurable b c delta n k)
  rw [← integral_finset_sum (s := Finset.univ) (fun k _ => hint k)]
  calc
    ∫ omega, ∑ k : Fin (A.rowLength n),
        A.twoClockStoppedLindebergTerm b c delta n k omega
        ∂(A.probability n) ≤ ∫ _omega : Omega n, c ∂(A.probability n) :=
      integral_mono_ae (MeasureTheory.integrable_finset_sum _ (fun k _ => hint k))
        (integrable_const _) (Filter.Eventually.of_forall (fun omega =>
          A.fin_twoClockStoppedLindeberg_le b c delta hc n omega))
    _ = c := by simp

/-- The integrated Fourier Taylor remainders of the two-clock stopped row are controlled
by the variance and Lindeberg budgets, without any uniform-integrability assumption. -/
lemma twoClockStoppedRemainder_integral_sum_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 < delta)
    (hsmall : |t| * delta ≤ 1) (n : ℕ) :
    (∑ k : Fin (A.rowLength n), ∫ omega,
      ‖thirdOrderRemainder t
        (A.twoClockStoppedIncrement b c delta n k omega)‖
      ∂(A.probability n)) ≤
      (2 / 9 : ℝ) * |t| ^ 3 * delta * b +
        (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c := by
  let D : Fin (A.rowLength n) → Omega n → ℝ := fun k =>
    A.twoClockStoppedIncrement b c delta n k
  let R : Fin (A.rowLength n) → Omega n → ℝ := fun k omega =>
    ‖thirdOrderRemainder t (D k omega)‖
  let Q : Fin (A.rowLength n) → Omega n → ℝ := fun k omega =>
    (D k omega) ^ 2
  let Tail : Fin (A.rowLength n) → Omega n → ℝ := fun k omega =>
    if delta < |D k omega| then Q k omega else 0
  have hpoint : ∀ k omega,
      R k omega ≤ (2 / 9 : ℝ) * |t| ^ 3 * delta * Q k omega +
        (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * Tail k omega := by
    intro k omega
    by_cases hbig : delta < |D k omega|
    · have hd : 0 < |D k omega| := lt_of_lt_of_le hdelta (le_of_lt hbig)
      have hbound : R k omega ≤
          2 + |t| * |D k omega| + (t ^ 2 / 2) * Q k omega := by
        dsimp [R]
        unfold thirdOrderRemainder
        calc
          ‖complexPhase t (D k omega) - 1 -
              Complex.I * (t * D k omega : ℝ) +
              (((t * D k omega) ^ 2 / 2 : ℝ) : ℂ)‖ ≤
              ‖complexPhase t (D k omega)‖ + ‖(1 : ℂ)‖ +
                ‖Complex.I * (t * D k omega : ℝ)‖ +
                ‖(((t * D k omega) ^ 2 / 2 : ℝ) : ℂ)‖ := by
            calc
              _ ≤ ‖complexPhase t (D k omega) - 1 -
                  Complex.I * (t * D k omega : ℝ)‖ +
                  ‖(((t * D k omega) ^ 2 / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
              _ ≤ (‖complexPhase t (D k omega) - 1‖ +
                  ‖Complex.I * (t * D k omega : ℝ)‖) +
                  ‖(((t * D k omega) ^ 2 / 2 : ℝ) : ℂ)‖ :=
                add_le_add (norm_sub_le _ _) le_rfl
              _ ≤ ((‖complexPhase t (D k omega)‖ + ‖(1 : ℂ)‖) +
                  ‖Complex.I * (t * D k omega : ℝ)‖) +
                  ‖(((t * D k omega) ^ 2 / 2 : ℝ) : ℂ)‖ :=
                add_le_add (add_le_add (norm_sub_le _ _) le_rfl) le_rfl
              _ = _ := by ring
          _ = 2 + |t| * |D k omega| + (t ^ 2 / 2) * Q k omega := by
            rw [show ‖complexPhase t (D k omega)‖ = 1 by
              exact Complex.norm_exp_I_mul_ofReal _, norm_one]
            simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_mul, norm_one]
            rw [abs_div, abs_pow, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            dsimp [Q]
            rw [show (|t| * |D k omega|) ^ 2 = |t| ^ 2 * |D k omega| ^ 2 by ring,
              sq_abs t, sq_abs (D k omega)]
            ring
      have h2 : 2 ≤ (2 / delta ^ 2) * Q k omega := by
        dsimp [Q]
        rw [show (D k omega) ^ 2 = |D k omega| ^ 2 by simp [sq_abs]]
        have hs : delta ^ 2 < |D k omega| ^ 2 := by nlinarith [abs_nonneg (D k omega)]
        have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
        nlinarith [div_mul_cancel₀ 2 (ne_of_gt hd2)]
      have ht : |t| * |D k omega| ≤ (|t| / delta) * Q k omega := by
        dsimp [Q]
        rw [show (D k omega) ^ 2 = |D k omega| ^ 2 by simp [sq_abs]]
        have htd : 0 ≤ |t| / delta := div_nonneg (abs_nonneg _) (le_of_lt hdelta)
        have hx : delta * |D k omega| ≤ |D k omega| ^ 2 := by
          nlinarith [abs_nonneg (D k omega)]
        calc
          |t| * |D k omega| = (|t| / delta) * (delta * |D k omega|) := by
            field_simp
          _ ≤ (|t| / delta) * |D k omega| ^ 2 :=
            mul_le_mul_of_nonneg_left hx htd
      dsimp [Tail]
      rw [if_pos hbig]
      exact le_trans hbound (by
        have hmain_nonneg : 0 ≤ (2 / 9 : ℝ) * |t| ^ 3 * delta * Q k omega := by positivity
        nlinarith)
    · have hDle : |D k omega| ≤ delta := le_of_not_gt hbig
      have htx : |t * D k omega| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_left hDle (abs_nonneg t)).trans hsmall
      have hTaylor := norm_thirdOrderRemainder_le t (D k omega) htx
      have hcube : |t * D k omega| ^ 3 ≤
          |t| ^ 3 * delta * Q k omega := by
        rw [abs_mul]
        dsimp [Q]
        rw [show (D k omega) ^ 2 = |D k omega| ^ 2 by simp [sq_abs]]
        calc
          (|t| * |D k omega|) ^ 3 = |t| ^ 3 * |D k omega| ^ 3 := by ring
          _ ≤ |t| ^ 3 * (delta * |D k omega| ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              |D k omega| ^ 3 = |D k omega| * |D k omega| ^ 2 := by ring
              _ ≤ delta * |D k omega| ^ 2 :=
                mul_le_mul_of_nonneg_right hDle (by positivity)
          _ = |t| ^ 3 * delta * |D k omega| ^ 2 := by ring
      dsimp [Tail]
      rw [if_neg hbig]
      norm_num
      calc
        _ ≤ (2 / 9 : ℝ) * (|t| ^ 3 * delta * Q k omega) :=
          hTaylor.trans (mul_le_mul_of_nonneg_left hcube (by norm_num))
        _ = (2 / 9 : ℝ) * |t| ^ 3 * delta * Q k omega := by ring
  have hQint : ∀ k, Integrable (Q k) (A.probability n) := by
    intro k
    exact (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable_sq
  have hTailint : ∀ k, Integrable (Tail k) (A.probability n) := by
    intro k
    have hDsm : StronglyMeasurable (D k) :=
      (A.twoClockStoppedIncrement_stronglyMeasurable hA b c delta n k).mono
        ((A.filtration n).le (k.val + 1))
    have hset : MeasurableSet {omega : Omega n | delta < |D k omega|} :=
      measurableSet_lt measurable_const hDsm.measurable.abs
    apply (hQint k).mono
    · exact ((hDsm.pow 2).ite hset stronglyMeasurable_const).aestronglyMeasurable
    · filter_upwards [] with omega
      dsimp [Tail]
      by_cases h : delta < |D k omega| <;> simp [h]
  have hRint : ∀ k, Integrable (R k) (A.probability n) := by
    intro k
    apply Integrable.mono' ((hQint k).norm.const_mul
      ((2 / 9 : ℝ) * |t| ^ 3 * delta) |>.add
        ((hTailint k).norm.const_mul (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2)))
    · have hcont : Continuous (fun x : ℝ => ‖thirdOrderRemainder t x‖) := by
        unfold thirdOrderRemainder complexPhase
        fun_prop
      exact hcont.comp_aestronglyMeasurable
        (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).aestronglyMeasurable
    · filter_upwards [] with omega
      have hQ0 : 0 ≤ Q k omega := by dsimp [Q]; positivity
      have hTail0 : 0 ≤ Tail k omega := by
        dsimp [Tail]
        split_ifs
        · exact hQ0
        · positivity
      simpa [R, Real.norm_eq_abs, abs_of_nonneg hQ0, abs_of_nonneg hTail0,
        abs_of_nonneg (by positivity : 0 ≤ (2 / 9 : ℝ) * |t| ^ 3 * delta),
        abs_of_nonneg (by positivity : 0 ≤ 2 / delta ^ 2 + |t| / delta + t ^ 2 / 2)]
        using hpoint k omega
  calc
    (∑ k, ∫ omega, R k omega ∂(A.probability n)) ≤
        ∑ k, ∫ omega,
          ((2 / 9 : ℝ) * |t| ^ 3 * delta) * Q k omega +
          (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * Tail k omega
          ∂(A.probability n) := by
      apply Finset.sum_le_sum
      intro k hk
      exact integral_mono_ae (hRint k)
        (((hQint k).const_mul _).add ((hTailint k).const_mul _))
        (Filter.Eventually.of_forall (hpoint k))
    _ = ((2 / 9 : ℝ) * |t| ^ 3 * delta) *
          ∑ k, ∫ omega, Q k omega ∂(A.probability n) +
        (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) *
          ∑ k, ∫ omega, Tail k omega ∂(A.probability n) := by
      calc
        _ = ∑ k, (((2 / 9 : ℝ) * |t| ^ 3 * delta) *
              ∫ omega, Q k omega ∂(A.probability n) +
            (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) *
              ∫ omega, Tail k omega ∂(A.probability n)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [integral_add ((hQint k).const_mul _) ((hTailint k).const_mul _),
            integral_const_mul, integral_const_mul]
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ((2 / 9 : ℝ) * |t| ^ 3 * delta) * b +
        (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (∑ k, ∫ omega, Q k omega ∂(A.probability n)) =
              ∑ k, ∫ omega,
                A.twoClockStoppedConditionalVariance b c delta n k omega
                ∂(A.probability n) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← integral_condExp ((A.filtration n).le k.val)]
            exact integral_congr_ae (by
              filter_upwards [A.twoClockStoppedIncrement_sq_condExp hA b c delta n k,
                A.conditionalVariance_eq_nonnegative_ae hA n k] with omega hsq hnonneg
              rw [hsq]
              by_cases hs : omega ∈ A.twoClockStopSet b c delta n k
              · simp [twoClockStoppedConditionalVariance, Q, D, hs, hnonneg]
              · simp [twoClockStoppedConditionalVariance, Q, D, hs])
          _ ≤ b := A.integral_twoClockStoppedConditionalVariance_sum_le
            hA b c delta hb n
      · apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          (∑ k, ∫ omega, Tail k omega ∂(A.probability n)) =
              ∑ k, ∫ omega,
                A.twoClockStoppedLindebergTerm b c delta n k omega
                ∂(A.probability n) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← integral_condExp ((A.filtration n).le k.val)]
            exact integral_congr_ae
              (A.twoClockStoppedTailSq_condExp hA b c delta n k)
          _ ≤ c := A.integral_twoClockStoppedLindebergTerm_sum_le
            b c delta hc n
    _ = _ := by ring

/-- Exact one-step integrated compensator identity.  The random previous compensator and
new exponential clock factor are treated as one predictable complex multiplier, so both
the linear martingale term and the conditional-square replacement are justified under the
pre-increment sigma-field. -/
lemma integral_twoClockCompensator_succ_sub
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (n : ℕ) (k : Fin (A.rowLength n)) :
    (∫ omega, A.twoClockCompensator b c delta t n (k.val + 1) omega
      ∂(A.probability n)) -
      ∫ omega, A.twoClockCompensator b c delta t n k.val omega
      ∂(A.probability n) =
    ∫ omega, A.twoClockCompensator b c delta t n k.val omega *
      ((Real.exp ((t ^ 2 / 2) *
        A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1) +
      A.twoClockCompensator b c delta t n k.val omega *
        (Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        thirdOrderRemainder t
          (A.twoClockStoppedIncrement b c delta n k omega)
      ∂(A.probability n) := by
  let a : ℝ := t ^ 2 / 2
  let D : Omega n → ℝ := A.twoClockStoppedIncrement b c delta n k
  let w : Omega n → ℝ := A.twoClockStoppedConditionalVariance b c delta n k
  let C : Omega n → ℂ := A.twoClockCompensator b c delta t n k.val
  let Z : Omega n → ℂ := fun omega => C omega * (Real.exp (a * w omega) : ℂ)
  have hCint : Integrable C (A.probability n) :=
    A.twoClockCompensator_integrable hA b c delta t hb n k.val k.isLt.le
  have hwsm : StronglyMeasurable[A.filtration n k.val] w :=
    A.twoClockStoppedConditionalVariance_stronglyMeasurable b c delta n k
  have hZmeas : AEStronglyMeasurable[A.filtration n k.val] Z (A.probability n) := by
    have hC := A.twoClockCompensator_stronglyMeasurable hA b c delta t n k.val
    exact (hC.mul (Complex.continuous_ofReal.comp_stronglyMeasurable
      (Real.continuous_exp.comp_stronglyMeasurable (hwsm.const_mul a)))).aestronglyMeasurable
  have hwle : ∀ omega, w omega ≤ b := by
    intro omega
    have hV := A.twoClockStoppedVarianceClock_le b c delta hb n (k.val + 1)
      (Nat.succ_le_iff.mpr k.isLt) omega
    simp [twoClockStoppedVarianceClock, Finset.sum_range_succ,
      twoClockPaddedStoppedConditionalVariance, k.isLt, w] at hV
    have hsum0 : 0 ≤ ∑ x ∈ Finset.range k.val,
        (if hk : x < A.rowLength n then
          A.twoClockStoppedConditionalVariance b c delta n ⟨x, hk⟩ else 0) omega := by
      apply Finset.sum_nonneg
      intro x hx
      split_ifs with hxrow
      · exact A.twoClockStoppedConditionalVariance_nonneg b c delta n ⟨x, hxrow⟩ omega
      · exact le_rfl
    linarith
  have hZbound : ∀ omega, ‖Z omega‖ ≤ Real.exp (a * b) ^ 2 := by
    intro omega
    have hC := A.twoClockCompensator_norm_le b c delta t hb n k.val k.isLt.le omega
    have ha : 0 ≤ a := by dsimp [a]; positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (a * b) * Real.exp (a * b) :=
        mul_le_mul hC (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hwle omega) ha))
          (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (a * b) ^ 2 := by ring
  have hZint : Integrable Z (A.probability n) := by
    apply Integrable.mono' (integrable_const (Real.exp (a * b) ^ 2))
    · exact hZmeas.mono ((A.filtration n).le k.val)
    · filter_upwards [] with omega
      simpa using hZbound omega
  have hDint : Integrable D (A.probability n) :=
    (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable one_le_two
  have hDsqint : Integrable (fun omega => D omega ^ 2) (A.probability n) :=
    (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable_sq
  have hDZ : Integrable (fun omega => (D omega : ℂ) * Z omega)
      (A.probability n) :=
    hDint.ofReal.mul_bdd (hZmeas.mono ((A.filtration n).le k.val))
      (Filter.Eventually.of_forall hZbound)
  have hDsmulZ : Integrable (D • Z) (A.probability n) := by
    change Integrable (fun omega => (D omega : ℂ) * Z omega) (A.probability n)
    exact hDZ
  have hDsqZ : Integrable (fun omega => ((D omega ^ 2 : ℝ) : ℂ) * Z omega)
      (A.probability n) :=
    hDsqint.ofReal.mul_bdd (hZmeas.mono ((A.filtration n).le k.val))
      (Filter.Eventually.of_forall hZbound)
  have hDsqsmulZ : Integrable ((fun omega => D omega ^ 2) • Z)
      (A.probability n) := by
    change Integrable (fun omega => ((D omega ^ 2 : ℝ) : ℂ) * Z omega)
      (A.probability n)
    exact hDsqZ
  have hlinearInt : Integrable (fun omega =>
      Z omega * (Complex.I * (t * D omega : ℝ))) (A.probability n) := by
    have hp := hDZ.mul_const ((t : ℂ) * Complex.I)
    apply hp.congr
    filter_upwards [] with omega
    push_cast
    ring
  have hlin : ∫ omega, Z omega *
      (Complex.I * (t * D omega : ℝ)) ∂(A.probability n) = 0 := by
    have hpredprod : Integrable
        (D • fun omega => t • (Z omega * Complex.I)) (A.probability n) := by
      change Integrable (fun omega => (D omega : ℂ) *
        ((t : ℂ) * (Z omega * Complex.I))) (A.probability n)
      have hp := hDZ.mul_const ((t : ℂ) * Complex.I)
      apply hp.congr
      filter_upwards [] with omega
      ring
    have hz := integral_predictable_smul_eq_zero
      (P := A.probability n) (F0 := A.filtration n k.val)
      (f := D) (Z := fun omega => t • (Z omega * Complex.I))
      ((A.filtration n).le k.val) hDint hpredprod
      ((hZmeas.mul_const Complex.I).const_smul t)
      (A.twoClockStoppedIncrement_condExp_zero hA b c delta n k)
    calc
      _ = ∫ omega, D omega • (t • (Z omega * Complex.I)) ∂(A.probability n) := by
        apply integral_congr_ae
        filter_upwards [] with omega
        change Z omega * (Complex.I * ((t * D omega : ℝ) : ℂ)) =
          (D omega : ℂ) * ((t : ℂ) * (Z omega * Complex.I))
        push_cast
        ring
      _ = 0 := hz
  have hsq : ∫ omega, Z omega * ((D omega) ^ 2 : ℝ) ∂(A.probability n) =
      ∫ omega, Z omega * (w omega : ℝ) ∂(A.probability n) := by
    have hz := integral_predictable_smul_condExp
      (P := A.probability n) (F0 := A.filtration n k.val)
      (f := fun omega => D omega ^ 2) (Z := Z)
      ((A.filtration n).le k.val) hDsqint hDsqsmulZ hZmeas
    have hcond :
        (A.probability n)[fun x => D x ^ 2 | A.filtration n k.val] =ᵐ[A.probability n]
          w := by
      simpa [D, w, twoClockPaddedStoppedIncrement,
        twoClockPaddedStoppedConditionalVariance, k.isLt] using
        (A.twoClockPaddedStoppedConditionalVariance_sq_condExp
          hA b c delta n k.val)
    calc
      _ = ∫ omega, (D omega ^ 2) • Z omega ∂(A.probability n) := by
        apply integral_congr_ae
        filter_upwards [] with omega
        simp [Algebra.smul_def, mul_comm]
      _ = ∫ omega,
          (A.probability n)[fun x => D x ^ 2 | A.filtration n k.val] omega • Z omega
          ∂(A.probability n) := hz
      _ = ∫ omega, Z omega * (w omega : ℝ) ∂(A.probability n) := by
        apply integral_congr_ae
        filter_upwards [hcond] with omega hω
        rw [hω]
        simp [Algebra.smul_def, mul_comm]
  have hCsuccint : Integrable
      (A.twoClockCompensator b c delta t n (k.val + 1)) (A.probability n) :=
    A.twoClockCompensator_integrable hA b c delta t hb n (k.val + 1)
      (Nat.succ_le_iff.mpr k.isLt)
  have hphase : Integrable (fun omega => complexPhase t (D omega))
      (A.probability n) := integrable_complexPhase_comp
        (P := A.probability n) hDint.aestronglyMeasurable t
  have hrem : Integrable (fun omega => thirdOrderRemainder t (D omega))
      (A.probability n) := by
    have hlinear : Integrable (fun omega => Complex.I * (t * D omega : ℝ))
        (A.probability n) := (hDint.const_mul t).ofReal.const_mul Complex.I
    have hquad : Integrable (fun omega => (((t * D omega) ^ 2 / 2 : ℝ) : ℂ))
        (A.probability n) := by
      apply ((hDsqint.const_mul (t ^ 2 / 2)).ofReal).congr
      filter_upwards [] with omega
      norm_num
      push_cast
      ring
    simpa only [thirdOrderRemainder] using
      ((hphase.sub (integrable_const (1 : ℂ))).sub hlinear).add hquad
  have hremZ : Integrable (fun omega => Z omega * thirdOrderRemainder t (D omega))
      (A.probability n) := by
    apply Integrable.mono' (hrem.norm.const_mul (Real.exp (a * b) ^ 2))
    · exact (hZmeas.mono ((A.filtration n).le k.val)).mul hrem.aestronglyMeasurable
    · filter_upwards [] with omega
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hZbound omega) (norm_nonneg _)
  have hwint := A.twoClockStoppedConditionalVariance_integrable hA b c delta n k
  have hexp : Integrable (fun omega => (Real.exp (a * w omega) : ℂ))
      (A.probability n) := by
    apply Integrable.mono' (integrable_const (Real.exp (a * b)))
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable
        (Real.continuous_exp.comp_aestronglyMeasurable
          ((hwsm.aestronglyMeasurable.mono ((A.filtration n).le k.val)).const_mul a))
    · filter_upwards [] with omega
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hwle omega) (by dsimp [a]; positivity))
  have haw : Integrable (fun omega => ((a * w omega : ℝ) : ℂ))
      (A.probability n) := (hwint.const_mul a).ofReal
  have hfactor := (integrable_const (1 : ℂ)).sub haw
  have hexpBound : ∀ᵐ omega ∂(A.probability n),
      ‖(Real.exp (a * w omega) : ℂ)‖ ≤ Real.exp (a * b) := by
    filter_upwards [] with omega
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (hwle omega) (by dsimp [a]; positivity))
  have hprod0 := hfactor.mul_bdd hexp.aestronglyMeasurable hexpBound
  have hprod : Integrable (fun omega => (Real.exp (a * w omega) : ℂ) *
      (1 - (a * w omega : ℂ))) (A.probability n) := by
    apply hprod0.congr
    filter_upwards [] with omega
    simp only [Pi.sub_apply]
    push_cast
    ring
  have hinside := hprod.sub (integrable_const (1 : ℂ))
  have hdefect : Integrable (fun omega => C omega *
      ((Real.exp (a * w omega) : ℂ) * (1 - (a * w omega : ℂ)) - 1))
      (A.probability n) := by
    apply Integrable.mono' (hinside.norm.const_mul (Real.exp (a * b)))
    · exact hCint.aestronglyMeasurable.mul hinside.aestronglyMeasurable
    · filter_upwards [] with omega
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (A.twoClockCompensator_norm_le b c delta t hb n k.val k.isLt.le omega)
        (norm_nonneg _)
  have hZD : Integrable (fun omega => Z omega * ((D omega) ^ 2 : ℝ))
      (A.probability n) := by
    apply hDsqsmulZ.congr
    filter_upwards [] with omega
    simp [Algebra.smul_def, mul_comm]
  have hwCmeas : AEStronglyMeasurable (fun omega => (w omega : ℂ))
      (A.probability n) := Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hwsm.aestronglyMeasurable.mono ((A.filtration n).le k.val))
  have hwBound : ∀ᵐ omega ∂(A.probability n), ‖(w omega : ℂ)‖ ≤ b := by
    filter_upwards [] with omega
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (A.twoClockStoppedConditionalVariance_nonneg b c delta n k omega)]
    exact hwle omega
  have hZw : Integrable (fun omega => Z omega * (w omega : ℝ))
      (A.probability n) := hZint.mul_bdd hwCmeas hwBound
  have hquadInt : Integrable (fun omega => (a : ℂ) *
      (Z omega * (w omega : ℝ) - Z omega * ((D omega) ^ 2 : ℝ)))
      (A.probability n) := (hZw.sub hZD).const_mul a
  have hquadZero : ∫ omega, (a : ℂ) *
      (Z omega * (w omega : ℝ) - Z omega * ((D omega) ^ 2 : ℝ))
      ∂(A.probability n) = 0 := by
    calc
      _ = (a : ℂ) * (∫ omega,
          Z omega * (w omega : ℝ) - Z omega * ((D omega) ^ 2 : ℝ)
          ∂(A.probability n)) := integral_const_mul _ _
      _ = (a : ℂ) * ((∫ omega, Z omega * (w omega : ℝ) ∂(A.probability n)) -
          ∫ omega, Z omega * ((D omega) ^ 2 : ℝ) ∂(A.probability n)) := by
        rw [integral_sub hZw hZD]
      _ = 0 := by rw [hsq]; ring
  rw [← integral_sub hCsuccint hCint]
  have hpoint : ∀ omega,
      A.twoClockCompensator b c delta t n (k.val + 1) omega - C omega =
        (C omega * ((Real.exp (a * w omega) : ℂ) *
          (1 - (a * w omega : ℂ)) - 1) +
        Z omega * thirdOrderRemainder t (D omega)) +
        Z omega * (Complex.I * (t * D omega : ℝ)) +
        ((a : ℂ) * (Z omega * (w omega : ℝ) -
          Z omega * ((D omega) ^ 2 : ℝ))) := by
    intro omega
    rw [A.twoClockCompensator_succ_eq_mul]
    have hpw : A.twoClockPaddedStoppedConditionalVariance b c delta n k.val = w := by
      simp [twoClockPaddedStoppedConditionalVariance, k.isLt, w]
    have hpD : A.twoClockPaddedStoppedIncrement b c delta n k.val = D := by
      simp [twoClockPaddedStoppedIncrement, k.isLt, D]
    rw [hpw, hpD]
    simp only [a, D, w, C, Z, Complex.ofReal_exp]
    unfold thirdOrderRemainder
    push_cast
    ring_nf
  calc
    ∫ omega, A.twoClockCompensator b c delta t n (k.val + 1) omega - C omega
        ∂(A.probability n) =
      ∫ omega, (C omega * ((Real.exp (a * w omega) : ℂ) *
          (1 - (a * w omega : ℂ)) - 1) +
        Z omega * thirdOrderRemainder t (D omega)) +
        Z omega * (Complex.I * (t * D omega : ℝ)) +
        ((a : ℂ) * (Z omega * (w omega : ℝ) -
          Z omega * ((D omega) ^ 2 : ℝ))) ∂(A.probability n) :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ omega, (C omega * ((Real.exp (a * w omega) : ℂ) *
          (1 - (a * w omega : ℂ)) - 1) +
        Z omega * thirdOrderRemainder t (D omega)) +
        Z omega * (Complex.I * (t * D omega : ℝ)) ∂(A.probability n)) +
        ∫ omega, (a : ℂ) * (Z omega * (w omega : ℝ) -
          Z omega * ((D omega) ^ 2 : ℝ)) ∂(A.probability n) :=
      integral_add ((hdefect.add hremZ).add hlinearInt) hquadInt
    _ = ((∫ omega, C omega * ((Real.exp (a * w omega) : ℂ) *
          (1 - (a * w omega : ℂ)) - 1) +
        Z omega * thirdOrderRemainder t (D omega) ∂(A.probability n)) +
        (∫ omega, Z omega * (Complex.I * (t * D omega : ℝ))
          ∂(A.probability n))) +
        ∫ omega, (a : ℂ) * (Z omega * (w omega : ℝ) -
          Z omega * ((D omega) ^ 2 : ℝ)) ∂(A.probability n) := by
      congr 1
      exact integral_add (hdefect.add hremZ) hlinearInt
    _ = ∫ omega, C omega * ((Real.exp (a * w omega) : ℂ) *
          (1 - (a * w omega : ℂ)) - 1) +
        Z omega * thirdOrderRemainder t (D omega) ∂(A.probability n) := by
      rw [hlin, hquadZero]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with omega
      simp only [a, C, D, w, Z]
      push_cast
      ring




/-- Integrated scalar defect of the exact random-clock compensator. -/
lemma twoClockCompensator_scalarDefect_integral_sum_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hsmall : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    (∑ k : Fin (A.rowLength n), ∫ omega,
      ‖(Real.exp ((t ^ 2 / 2) *
        A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
      ∂(A.probability n)) ≤
      (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) := by
  have hstep := A.twoClockCompensator_fourierStepError_sum_le_ae
    hA b c delta t hb hc hdelta hsmall n
  have hpoint : (fun omega => ∑ k : Fin (A.rowLength n),
      ‖(Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖) ≤ᵐ[A.probability n]
      (fun _ => (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)) := by
    filter_upwards [hstep] with omega hω
    refine le_trans ?_ hω
    apply Finset.sum_le_sum
    intro k hk
    let E : ℂ := Real.exp ((t ^ 2 / 2) *
      A.twoClockStoppedConditionalVariance b c delta n k omega)
    let F : ℂ := 1 - (((t ^ 2 / 2) *
      A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)
    let z : ℂ := complexPhase t
      (A.twoClockPaddedStoppedIncrement b c delta n k.val omega)
    have hz : ‖z‖ = (1 : ℝ) := Complex.norm_exp_I_mul_ofReal _
    have halg : E * z * F - z = z * (E * F - 1) := by ring
    rw [halg, norm_mul, hz, one_mul]
  have hint : ∀ k : Fin (A.rowLength n), Integrable (fun omega =>
      ‖(Real.exp ((t ^ 2 / 2) *
        A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
        (1 - (((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖)
      (A.probability n) := by
    intro k
    have hwint := A.twoClockStoppedConditionalVariance_integrable hA b c delta n k
    have hwmeas := A.twoClockStoppedConditionalVariance_stronglyMeasurable b c delta n k
    have hexp : Integrable (fun omega => (Real.exp ((t ^ 2 / 2) *
        A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ))
        (A.probability n) := by
      apply Integrable.mono' (integrable_const (Real.exp ((t ^ 2 / 2) * b)))
      · exact Complex.continuous_ofReal.comp_aestronglyMeasurable
          (Real.continuous_exp.comp_aestronglyMeasurable
            ((hwmeas.mono ((A.filtration n).le k.val)).aestronglyMeasurable.const_mul
              (t ^ 2 / 2)))
      · filter_upwards [] with omega
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
          le_trans (Finset.single_le_sum
            (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
            (Finset.mem_univ k))
            (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
        exact mul_le_mul_of_nonneg_left hwle (by positivity)
    have hfactor := (integrable_const (1 : ℂ)).sub
      ((hwint.const_mul (t ^ 2 / 2)).ofReal)
    have hprod := hfactor.mul_bdd hexp.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun omega => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
          le_trans (Finset.single_le_sum
            (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
            (Finset.mem_univ k))
            (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
        exact mul_le_mul_of_nonneg_left hwle (by positivity)))
    have hraw := (hprod.sub (integrable_const (1 : ℂ))).norm
    apply hraw.congr
    filter_upwards [] with omega
    simp only [Pi.sub_apply]
    push_cast
    ring_nf
    rfl
  rw [← integral_finset_sum (s := Finset.univ) (fun k _ => hint k)]
  calc
    ∫ omega, ∑ k : Fin (A.rowLength n),
        ‖(Real.exp ((t ^ 2 / 2) *
          A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
          (1 - (((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
        ∂(A.probability n) ≤
      ∫ _omega : Omega n,
        (7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)
        ∂(A.probability n) :=
      integral_mono_ae (MeasureTheory.integrable_finset_sum _ (fun k _ => hint k))
        (integrable_const _) hpoint
    _ = _ := by simp

/-- The exact predictable-multiplier compensator telescope has a deterministic error bound.
This is the missing random-PQV Fourier interface: unlike the predecessor's unweighted
finite estimate, every one-step Taylor identity carries the previous random compensator. -/
theorem twoClockCompensator_integral_sub_initial_norm_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hdelta : 0 < delta)
    (hsmallTaylor : |t| * delta ≤ 1)
    (hsmallClock : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    ‖(∫ omega, A.twoClockCompensator b c delta t n (A.rowLength n) omega
        ∂(A.probability n)) -
      ∫ omega, A.twoClockCompensator b c delta t n 0 omega
        ∂(A.probability n)‖ ≤
      Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) +
          (2 / 9 : ℝ) * |t| ^ 3 * delta * b +
          (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c) := by
  let N := A.rowLength n
  have htelescope :
      (∫ omega, A.twoClockCompensator b c delta t n N omega
        ∂(A.probability n)) -
        ∫ omega, A.twoClockCompensator b c delta t n 0 omega
          ∂(A.probability n) =
      ∑ k : Fin N,
        ((∫ omega, A.twoClockCompensator b c delta t n (k.val + 1) omega
          ∂(A.probability n)) -
          ∫ omega, A.twoClockCompensator b c delta t n k.val omega
            ∂(A.probability n)) := by
    rw [← integral_sub
      (A.twoClockCompensator_integrable hA b c delta t hb n N (by exact le_rfl))
      (A.twoClockCompensator_integrable hA b c delta t hb n 0 (Nat.zero_le _))]
    calc
      _ = ∫ omega, ∑ k ∈ Finset.range N,
          (A.twoClockCompensator b c delta t n (k + 1) omega -
            A.twoClockCompensator b c delta t n k omega)
          ∂(A.probability n) := by
        apply integral_congr_ae
        filter_upwards [] with omega
        exact A.twoClockCompensator_sub_initial_eq_sum b c delta t n N omega
      _ = ∑ k ∈ Finset.range N, ∫ omega,
          (A.twoClockCompensator b c delta t n (k + 1) omega -
            A.twoClockCompensator b c delta t n k omega)
          ∂(A.probability n) := by
        apply integral_finset_sum
        intro k hk
        exact (A.twoClockCompensator_integrable hA b c delta t hb n (k + 1)
          (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))).sub
          (A.twoClockCompensator_integrable hA b c delta t hb n k
            (Finset.mem_range.mp hk).le)
      _ = _ := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        rw [integral_sub
          (A.twoClockCompensator_integrable hA b c delta t hb n (k.val + 1)
            (Nat.succ_le_iff.mpr k.isLt))
          (A.twoClockCompensator_integrable hA b c delta t hb n k.val k.isLt.le)]
  rw [htelescope]
  have hboundStep : ∀ k : Fin N,
      ‖∫ omega,
        A.twoClockCompensator b c delta t n k.val omega *
          ((Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            (1 - (((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1) +
        A.twoClockCompensator b c delta t n k.val omega *
          (Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
          thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k omega)
        ∂(A.probability n)‖ ≤
      Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        ((∫ omega,
          ‖(Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            (1 - (((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
          ∂(A.probability n)) +
        ∫ omega,
          ‖thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n)) := by
    intro k
    calc
      _ ≤ ∫ omega,
          ‖A.twoClockCompensator b c delta t n k.val omega *
            ((Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
              (1 - (((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1) +
          A.twoClockCompensator b c delta t n k.val omega *
            (Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            thirdOrderRemainder t
              (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n) := norm_integral_le_integral_norm _
      _ ≤ ∫ omega,
          Real.exp ((t ^ 2 / 2) * b) ^ 2 *
            (‖(Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
              (1 - (((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖ +
            ‖thirdOrderRemainder t
              (A.twoClockStoppedIncrement b c delta n k omega)‖)
          ∂(A.probability n) := by
        apply integral_mono_ae
        · have hCmeas : AEStronglyMeasurable
              (A.twoClockCompensator b c delta t n k.val) (A.probability n) :=
            ((A.twoClockCompensator_stronglyMeasurable
              hA b c delta t n k.val).mono ((A.filtration n).le k.val)).aestronglyMeasurable
          have hwmeas : AEStronglyMeasurable
              (A.twoClockStoppedConditionalVariance b c delta n k) (A.probability n) :=
            ((A.twoClockStoppedConditionalVariance_stronglyMeasurable
              b c delta n k).mono ((A.filtration n).le k.val)).aestronglyMeasurable
          have hexpmeas : AEStronglyMeasurable (fun omega =>
              (Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ))
              (A.probability n) :=
            Complex.continuous_ofReal.comp_aestronglyMeasurable
              (Real.continuous_exp.comp_aestronglyMeasurable
                (hwmeas.const_mul (t ^ 2 / 2)))
          have hfactorMeas : AEStronglyMeasurable (fun omega =>
              (1 : ℂ) - (((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ))
              (A.probability n) :=
            aestronglyMeasurable_const.sub
              (Complex.continuous_ofReal.comp_aestronglyMeasurable
                (hwmeas.const_mul (t ^ 2 / 2)))
          have hdefectMeas : AEStronglyMeasurable (fun omega =>
              (Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                (1 - (((t ^ 2 / 2) *
                  A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1)
              (A.probability n) :=
            (hexpmeas.mul hfactorMeas).sub aestronglyMeasurable_const
          have hd := (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable one_le_two
          have hphase := integrable_complexPhase_comp (P := A.probability n)
            hd.aestronglyMeasurable t
          have hlin := (hd.const_mul t).ofReal.const_mul Complex.I
          have hquad : Integrable (fun omega =>
              ((((t * A.twoClockStoppedIncrement b c delta n k omega) ^ 2 / 2 : ℝ) : ℂ)))
              (A.probability n) := by
            apply (((A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable_sq.const_mul
              (t ^ 2 / 2)).ofReal).congr
            filter_upwards [] with omega
            push_cast
            ring
            rfl
          have hrem : Integrable (fun omega => thirdOrderRemainder t
              (A.twoClockStoppedIncrement b c delta n k omega))
              (A.probability n) :=
            (((hphase.sub (integrable_const (1 : ℂ))).sub hlin).add hquad)
          have hwint := A.twoClockStoppedConditionalVariance_integrable
            hA b c delta n k
          have hexpBound : ∀ᵐ omega ∂(A.probability n),
              ‖(Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ)‖ ≤
                Real.exp ((t ^ 2 / 2) * b) := by
            filter_upwards [] with omega
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            apply Real.exp_le_exp.mpr
            have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
              le_trans (Finset.single_le_sum
                (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
                (Finset.mem_univ k))
                (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
            exact mul_le_mul_of_nonneg_left hwle (by positivity)
          have hexpint : Integrable (fun omega =>
              (Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ))
              (A.probability n) := by
            apply Integrable.mono' (integrable_const (Real.exp ((t ^ 2 / 2) * b)))
            · exact hexpmeas
            · exact hexpBound
          have hfactorInt := (integrable_const (1 : ℂ)).sub
            ((hwint.const_mul (t ^ 2 / 2)).ofReal)
          have hprodInt := hfactorInt.mul_bdd hexpmeas hexpBound
          have hdefectInt : Integrable (fun omega =>
              (Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                (1 - (((t ^ 2 / 2) *
                  A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1)
              (A.probability n) := by
            have hraw := hprodInt.sub (integrable_const (1 : ℂ))
            apply hraw.congr
            filter_upwards [] with omega
            simp only [Pi.sub_apply]
            push_cast
            ring_nf
            rfl
          have hCbound : ∀ᵐ omega ∂(A.probability n),
              ‖A.twoClockCompensator b c delta t n k.val omega‖ ≤
                Real.exp ((t ^ 2 / 2) * b) :=
            Filter.Eventually.of_forall
              (A.twoClockCompensator_norm_le b c delta t hb n k.val k.isLt.le)
          have hterm1raw := hdefectInt.mul_bdd hCmeas hCbound
          have hterm1 : Integrable (fun omega =>
              A.twoClockCompensator b c delta t n k.val omega *
                ((Real.exp ((t ^ 2 / 2) *
                  A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                  (1 - (((t ^ 2 / 2) *
                    A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1))
              (A.probability n) := by
            apply hterm1raw.congr
            filter_upwards [] with omega
            ring
          have hremExpRaw := hrem.mul_bdd hexpmeas hexpBound
          have hremExpCraw := hremExpRaw.mul_bdd hCmeas hCbound
          have hterm2 : Integrable (fun omega =>
              A.twoClockCompensator b c delta t n k.val omega *
                (Real.exp ((t ^ 2 / 2) *
                  A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                thirdOrderRemainder t
                  (A.twoClockStoppedIncrement b c delta n k omega))
              (A.probability n) := by
            apply hremExpCraw.congr
            filter_upwards [] with omega
            ring
          exact (hterm1.add hterm2).norm
        · have hwint := A.twoClockStoppedConditionalVariance_integrable
            hA b c delta n k
          have hwmeas := A.twoClockStoppedConditionalVariance_stronglyMeasurable
            b c delta n k
          have he : Integrable (fun omega => (Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ))
              (A.probability n) := by
            apply Integrable.mono' (integrable_const
              (Real.exp ((t ^ 2 / 2) * b)))
            · exact Complex.continuous_ofReal.comp_aestronglyMeasurable
                (Real.continuous_exp.comp_aestronglyMeasurable
                  ((hwmeas.mono ((A.filtration n).le k.val)).aestronglyMeasurable.const_mul
                    (t ^ 2 / 2)))
            · filter_upwards [] with omega
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              apply Real.exp_le_exp.mpr
              have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
                le_trans (Finset.single_le_sum
                  (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
                  (Finset.mem_univ k))
                  (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
              exact mul_le_mul_of_nonneg_left hwle (by positivity)
          have hfactor := (integrable_const (1 : ℂ)).sub
            ((hwint.const_mul (t ^ 2 / 2)).ofReal)
          have hprod := hfactor.mul_bdd he.aestronglyMeasurable
            (Filter.Eventually.of_forall (fun omega => by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              apply Real.exp_le_exp.mpr
              have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
                le_trans (Finset.single_le_sum
                  (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
                  (Finset.mem_univ k))
                  (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
              exact mul_le_mul_of_nonneg_left hwle (by positivity)))
          have hdefect : Integrable (fun omega =>
              ‖(Real.exp ((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                (1 - (((t ^ 2 / 2) *
                  A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖)
              (A.probability n) := by
            have hraw := (hprod.sub (integrable_const (1 : ℂ))).norm
            apply hraw.congr
            filter_upwards [] with omega
            simp only [Pi.sub_apply]
            push_cast
            congr 1
            ring
            rfl
          have hd := (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable one_le_two
          have hphase := integrable_complexPhase_comp (P := A.probability n)
            hd.aestronglyMeasurable t
          have hlin := (hd.const_mul t).ofReal.const_mul Complex.I
          have hquad : Integrable (fun omega =>
              ((((t * A.twoClockStoppedIncrement b c delta n k omega) ^ 2 / 2 : ℝ) : ℂ)))
              (A.probability n) := by
            apply (((A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable_sq.const_mul
              (t ^ 2 / 2)).ofReal).congr
            filter_upwards [] with omega
            push_cast
            ring
            rfl
          have hrem : Integrable (fun omega =>
              ‖thirdOrderRemainder t
                (A.twoClockStoppedIncrement b c delta n k omega)‖)
              (A.probability n) :=
            (((hphase.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).norm
          exact (hdefect.add hrem).const_mul _
        · filter_upwards [] with omega
          have hC := A.twoClockCompensator_norm_le b c delta t hb n k.val k.isLt.le omega
          have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
            le_trans (Finset.single_le_sum
              (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
              (Finset.mem_univ k))
              (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
          have he : ‖(Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ)‖ ≤
              Real.exp ((t ^ 2 / 2) * b) := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hwle (by positivity))
          let X := ‖(Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
              (1 - (((t ^ 2 / 2) *
                A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
          let Y := ‖thirdOrderRemainder t
              (A.twoClockStoppedIncrement b c delta n k omega)‖
          have hE1 : 1 ≤ Real.exp ((t ^ 2 / 2) * b) :=
            Real.one_le_exp_iff.mpr (mul_nonneg (by positivity) hb)
          calc
            ‖A.twoClockCompensator b c delta t n k.val omega * _ +
                A.twoClockCompensator b c delta t n k.val omega * _ * _‖ ≤
                ‖A.twoClockCompensator b c delta t n k.val omega *
                  ((Real.exp ((t ^ 2 / 2) *
                    A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                    (1 - (((t ^ 2 / 2) *
                      A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1)‖ +
                ‖A.twoClockCompensator b c delta t n k.val omega *
                  (Real.exp ((t ^ 2 / 2) *
                    A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
                  thirdOrderRemainder t
                    (A.twoClockStoppedIncrement b c delta n k omega)‖ := norm_add_le _ _
            _ = ‖A.twoClockCompensator b c delta t n k.val omega‖ * X +
                ‖A.twoClockCompensator b c delta t n k.val omega‖ *
                  ‖(Real.exp ((t ^ 2 / 2) *
                    A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ)‖ * Y := by
              simp [X, Y, norm_mul, mul_assoc]
            _ ≤ Real.exp ((t ^ 2 / 2) * b) ^ 2 * (X + Y) := by
              have hX : 0 ≤ X := norm_nonneg _
              have hY : 0 ≤ Y := norm_nonneg _
              calc
                _ ≤ Real.exp ((t ^ 2 / 2) * b) * X +
                    Real.exp ((t ^ 2 / 2) * b) *
                      Real.exp ((t ^ 2 / 2) * b) * Y := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_right hC hX
                  · exact mul_le_mul_of_nonneg_right
                      (mul_le_mul hC he (norm_nonneg _) (Real.exp_pos _).le) hY
                _ ≤ Real.exp ((t ^ 2 / 2) * b) ^ 2 * X +
                    Real.exp ((t ^ 2 / 2) * b) ^ 2 * Y := by
                  apply add_le_add
                  · apply mul_le_mul_of_nonneg_right _ hX
                    calc
                      Real.exp ((t ^ 2 / 2) * b) =
                          Real.exp ((t ^ 2 / 2) * b) * 1 := by ring
                      _ ≤ Real.exp ((t ^ 2 / 2) * b) *
                          Real.exp ((t ^ 2 / 2) * b) :=
                        mul_le_mul_of_nonneg_left hE1 (Real.exp_pos _).le
                      _ = Real.exp ((t ^ 2 / 2) * b) ^ 2 := by ring
                  · exact le_of_eq (by ring)
                _ = _ := by ring
      _ = _ := by
        rw [integral_const_mul, integral_add]
        ring
        · have hw := A.twoClockStoppedConditionalVariance_integrable hA b c delta n k
          have hwmeas := A.twoClockStoppedConditionalVariance_stronglyMeasurable b c delta n k
          have he : Integrable (fun omega => (Real.exp ((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ))
              (A.probability n) := by
            apply Integrable.mono' (integrable_const (Real.exp ((t ^ 2 / 2) * b)))
            · exact Complex.continuous_ofReal.comp_aestronglyMeasurable
                (Real.continuous_exp.comp_aestronglyMeasurable
                  ((hwmeas.mono ((A.filtration n).le k.val)).aestronglyMeasurable.const_mul
                    (t ^ 2 / 2)))
            · filter_upwards [] with omega
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              apply Real.exp_le_exp.mpr
              have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
                le_trans (Finset.single_le_sum
                  (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
                  (Finset.mem_univ k))
                  (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
              exact mul_le_mul_of_nonneg_left hwle (by positivity)
          have hfactor := (integrable_const (1 : ℂ)).sub
            ((hw.const_mul (t ^ 2 / 2)).ofReal)
          have hprod := hfactor.mul_bdd he.aestronglyMeasurable
            (Filter.Eventually.of_forall (fun omega => by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
              apply Real.exp_le_exp.mpr
              have hwle : A.twoClockStoppedConditionalVariance b c delta n k omega ≤ b :=
                le_trans (Finset.single_le_sum
                  (fun j _ => A.twoClockStoppedConditionalVariance_nonneg b c delta n j omega)
                  (Finset.mem_univ k))
                  (A.fin_twoClockStoppedVariance_le b c delta hb n omega)
              exact mul_le_mul_of_nonneg_left hwle (by positivity)))
          have hraw := (hprod.sub (integrable_const (1 : ℂ))).norm
          apply hraw.congr
          filter_upwards [] with omega
          simp only [Pi.sub_apply]
          push_cast
          ring_nf
          rfl
        · have hd := (A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable one_le_two
          have hphase := integrable_complexPhase_comp (P := A.probability n)
            hd.aestronglyMeasurable t
          have hlin := (hd.const_mul t).ofReal.const_mul Complex.I
          have hquad : Integrable (fun omega =>
              ((((t * A.twoClockStoppedIncrement b c delta n k omega) ^ 2 / 2 : ℝ) : ℂ)))
              (A.probability n) := by
            apply (((A.twoClockStoppedIncrement_memLp_two hA b c delta n k).integrable_sq.const_mul
              (t ^ 2 / 2)).ofReal).congr
            filter_upwards [] with omega
            push_cast
            ring
            rfl
          exact (((hphase.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).norm
  calc
    ‖∑ k : Fin N,
        ((∫ omega, A.twoClockCompensator b c delta t n (k.val + 1) omega
          ∂(A.probability n)) -
          ∫ omega, A.twoClockCompensator b c delta t n k.val omega
            ∂(A.probability n))‖ ≤
      ∑ k : Fin N, ‖∫ omega,
        A.twoClockCompensator b c delta t n k.val omega *
          ((Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            (1 - (((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1) +
        A.twoClockCompensator b c delta t n k.val omega *
          (Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
          thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k omega)
        ∂(A.probability n)‖ := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro k hk
      rw [A.integral_twoClockCompensator_succ_sub hA b c delta t hb n k]
    _ ≤ ∑ k : Fin N, Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        ((∫ omega,
          ‖(Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            (1 - (((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
          ∂(A.probability n)) +
        ∫ omega,
          ‖thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n)) := Finset.sum_le_sum (fun k _ => hboundStep k)
    _ = Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        ((∑ k : Fin N, ∫ omega,
          ‖(Real.exp ((t ^ 2 / 2) *
            A.twoClockStoppedConditionalVariance b c delta n k omega) : ℂ) *
            (1 - (((t ^ 2 / 2) *
              A.twoClockStoppedConditionalVariance b c delta n k omega : ℝ) : ℂ)) - 1‖
          ∂(A.probability n)) +
        (∑ k : Fin N, ∫ omega,
          ‖thirdOrderRemainder t
            (A.twoClockStoppedIncrement b c delta n k omega)‖
          ∂(A.probability n))) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        (((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c)) +
          ((2 / 9 : ℝ) * |t| ^ 3 * delta * b +
            (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact add_le_add
        (A.twoClockCompensator_scalarDefect_integral_sum_le
          hA b c delta t hb hc (le_of_lt hdelta) hsmallClock n)
        (A.twoClockStoppedRemainder_integral_sum_le
          hA b c delta t hb hc hdelta hsmallTaylor n)
    _ = _ := by ring


/-- The random-clock compensator starts at the target Gaussian characteristic function. -/
lemma integral_twoClockCompensator_zero
    (b c delta t : ℝ) (n : ℕ) :
    ∫ omega, A.twoClockCompensator b c delta t n 0 omega
      ∂(A.probability n) = (Real.exp (-(t ^ 2 / 2)) : ℂ) := by
  simp [twoClockCompensator, twoClockStoppedVarianceClock,
    twoClockStoppedPartialSum, natPartialSum, complexPhase]

/-- At the terminal time the random compensator differs from the stopped Fourier phase
only by its exponential stopped-variance-clock factor. -/
lemma twoClockCompensator_terminal_phase_integral_diff_norm_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ) (hb : 0 ≤ b)
    (n : ℕ) :
    ‖(∫ omega, A.twoClockCompensator b c delta t n (A.rowLength n) omega
        ∂(A.probability n)) -
      ∫ omega, complexPhase t
        (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
        ∂(A.probability n)‖ ≤
      ∫ omega,
        |Real.exp ((t ^ 2 / 2) *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
        ∂(A.probability n) := by
  have hCint := A.twoClockCompensator_integrable hA b c delta t hb n
    (A.rowLength n) le_rfl
  have hphaseMeas : AEStronglyMeasurable
      (A.twoClockStoppedPartialSum b c delta n (A.rowLength n))
      (A.probability n) := by
    apply (natPartialSum_stronglyAdapted
      (A.twoClockPaddedStoppedIncrement b c delta n)
      (fun j => A.twoClockPaddedStoppedIncrement_stronglyMeasurable
        hA b c delta n j) (A.rowLength n)).aestronglyMeasurable.mono
    exact (A.filtration n).le (A.rowLength n)
  have hphaseint := integrable_complexPhase_comp (P := A.probability n) hphaseMeas t
  rw [← integral_sub hCint hphaseint]
  calc
    ‖∫ omega,
        A.twoClockCompensator b c delta t n (A.rowLength n) omega -
          complexPhase t
            (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
        ∂(A.probability n)‖ ≤
      ∫ omega,
        ‖A.twoClockCompensator b c delta t n (A.rowLength n) omega -
          complexPhase t
            (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)‖
        ∂(A.probability n) := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with omega
      unfold twoClockCompensator
      let x := (t ^ 2 / 2) *
        (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)
      let z := complexPhase t
        (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
      have hz : ‖z‖ = 1 := Complex.norm_exp_I_mul_ofReal _
      calc
        ‖(Real.exp x : ℂ) * z - z‖ = ‖((Real.exp x : ℂ) - 1) * z‖ := by
          congr 1
          ring
        _ = ‖((Real.exp x : ℂ) - 1)‖ := by rw [norm_mul, hz, mul_one]
        _ = |Real.exp x - 1| := by
          rw [show ((Real.exp x : ℂ) - 1) = ((Real.exp x - 1 : ℝ) : ℂ) by
            push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
        _ = _ := rfl

/-- Finite-row comparison of the original characteristic function with the Gaussian target.
The three terms are respectively the stop-event error, terminal clock-factor error, and
exact predictable-multiplier compensator error. -/
theorem characteristicFunction_gaussian_error_le
    (hA : A.IsMartingaleDifferenceArray) (b c delta t : ℝ)
    (hb : 1 < b) (hc : 0 < c) (hdelta : 0 < delta)
    (hsmallTaylor : |t| * delta ≤ 1)
    (hsmallClock : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1) (n : ℕ) :
    ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
        (Real.exp (-(t ^ 2 / 2)) : ℂ)‖ ≤
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n) +
      (∫ omega,
        |Real.exp ((t ^ 2 / 2) *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
        ∂(A.probability n)) +
      Real.exp ((t ^ 2 / 2) * b) ^ 2 *
        ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) +
          (2 / 9 : ℝ) * |t| ^ 3 * delta * b +
          (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c) := by
  let phi := ∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)
  let psi := ∫ omega, complexPhase t
    (A.twoClockStoppedPartialSum b c delta n (A.rowLength n) omega)
    ∂(A.probability n)
  let C := ∫ omega, A.twoClockCompensator b c delta t n (A.rowLength n) omega
    ∂(A.probability n)
  let g : ℂ := Real.exp (-(t ^ 2 / 2))
  have hstop := A.twoClockStopped_original_phase_integral_diff_le
    hA b c delta t n
  have hclock := A.twoClockCompensator_terminal_phase_integral_diff_norm_le
    hA b c delta t (le_trans (by norm_num) (le_of_lt hb)) n
  have hcomp := A.twoClockCompensator_integral_sub_initial_norm_le
    hA b c delta t (le_trans (by norm_num) (le_of_lt hb)) (le_of_lt hc)
      hdelta hsmallTaylor hsmallClock n
  rw [A.integral_twoClockCompensator_zero b c delta t n] at hcomp
  change ‖phi - g‖ ≤ _
  have htri1 : ‖phi - g‖ ≤ ‖phi - psi‖ + ‖psi - g‖ := by
    rw [show phi - g = (phi - psi) + (psi - g) by ring]
    exact norm_add_le _ _
  have htri2 : ‖psi - g‖ ≤ ‖psi - C‖ + ‖C - g‖ := by
    rw [show psi - g = (psi - C) + (C - g) by ring]
    exact norm_add_le _ _
  have hclock' : ‖psi - C‖ ≤ ∫ omega,
      |Real.exp ((t ^ 2 / 2) *
        (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
      ∂(A.probability n) := by
    rw [norm_sub_rev]
    exact hclock
  calc
    ‖phi - g‖ ≤ ‖phi - psi‖ + ‖psi - g‖ := htri1
    _ ≤ ‖phi - psi‖ + (‖psi - C‖ + ‖C - g‖) :=
      add_le_add_right htri2 _
    _ ≤ 2 * (A.probability n).real (A.twoClockStopEvent b c delta n) +
        ((∫ omega,
          |Real.exp ((t ^ 2 / 2) *
            (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
          ∂(A.probability n)) +
        Real.exp ((t ^ 2 / 2) * b) ^ 2 *
          ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) +
            (2 / 9 : ℝ) * |t| ^ 3 * delta * b +
            (2 / delta ^ 2 + |t| / delta + t ^ 2 / 2) * c)) :=
      add_le_add hstop (add_le_add hclock' hcomp)
    _ = _ := by ring


/-- Characteristic-function convergence from the martingale-array assumptions alone.
The proof localizes the row by the predictable variance and Lindeberg clocks, applies the
exact predictable-multiplier compensator telescope, lets the row index tend to infinity
at fixed localization parameters, and then sends those parameters to zero. -/
theorem characteristicFunctionConvergence
    (hA : A.IsMartingaleDifferenceArray)
    (hQV : A.PredictableQuadraticVariationCondition)
    (hLindeberg : A.ConditionalLindebergCondition) (t : ℝ) :
    Tendsto (fun n => ∫ omega, complexPhase t (A.rowSum n omega)
      ∂(A.probability n)) atTop (nhds (Real.exp (-(t ^ 2 / 2)) : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let err : ℕ → ℝ := fun n =>
    ‖(∫ omega, complexPhase t (A.rowSum n omega) ∂(A.probability n)) -
      (Real.exp (-(t ^ 2 / 2)) : ℂ)‖
  have herr0 : ∀ n, 0 ≤ err n := fun n => norm_nonneg _
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  by_cases ht : t = 0
  · subst t
    refine ⟨0, fun n hn => ?_⟩
    simpa [err, complexPhase, Real.dist_eq] using hepsilon
  have ht_abs : 0 < |t| := abs_pos.mpr ht
  let b : ℝ := 2
  have hb : 1 < b := by norm_num [b]
  have hb0 : 0 ≤ b := le_trans (by norm_num) (le_of_lt hb)
  have hEpos : 0 < Real.exp ((t ^ 2 / 2) * b) ^ 2 := sq_pos_of_pos (Real.exp_pos _)
  let C : ℝ := Real.exp ((t ^ 2 / 2) * b) ^ 2
  let A0 : ℝ := (7 / 4) * (t ^ 2 / 2) ^ 2 * b
  let B0 : ℝ := (2 / 9) * |t| ^ 3 * b
  let delta : ℝ := min 1
    (min (1 / |t|) (epsilon / (4 * C * (A0 + B0 + 1))))
  have hden : 0 < 4 * C * (A0 + B0 + 1) := by
    dsimp [C, A0, B0, b]
    positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num)
      (lt_min (by positivity) (div_pos hepsilon hden))
  have hsmallTaylor : |t| * delta ≤ 1 := by
    calc
      |t| * delta ≤ |t| * (1 / |t|) :=
        mul_le_mul_of_nonneg_left
          (le_trans (min_le_right _ _) (min_le_left _ _)) (abs_nonneg _)
      _ = 1 := by field_simp
  let K : ℝ := 2 / delta ^ 2 + |t| / delta + t ^ 2 / 2
  have hKpos : 0 < K := by
    dsimp [K]
    have hd2 : 0 < delta ^ 2 := sq_pos_of_pos hdelta
    positivity
  let c : ℝ := min 1 (min (1 / (2 * (t ^ 2 / 2 + 1)))
    (epsilon / (4 * C * (K + (7 / 4) * (t ^ 2 / 2) ^ 2 * b))))
  have hcden : 0 < 4 * C * (K + (7 / 4) * (t ^ 2 / 2) ^ 2 * b) := by
    dsimp [C, b]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by norm_num) (lt_min (by positivity) (div_pos hepsilon hcden))
  have hdeltaClock : (t ^ 2 / 2) * delta ^ 2 ≤ 1 / 2 := by
    have hdle : delta ≤ 1 / |t| :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hdsq : delta ^ 2 ≤ (1 / |t|) ^ 2 := by
      nlinarith [le_of_lt hdelta, abs_nonneg t]
    have habs2 : |t| ^ 2 = t ^ 2 := sq_abs t
    calc
      (t ^ 2 / 2) * delta ^ 2 ≤ (t ^ 2 / 2) * (1 / |t|) ^ 2 :=
        mul_le_mul_of_nonneg_left hdsq (by positivity)
      _ = 1 / 2 := by
        rw [show (1 / |t|) ^ 2 = 1 / t ^ 2 by
          rw [div_pow, sq_abs]
          norm_num]
        field_simp
  have hcClock : (t ^ 2 / 2) * c ≤ 1 / 2 := by
    have hcle : c ≤ 1 / (2 * (t ^ 2 / 2 + 1)) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have ha0 : 0 ≤ t ^ 2 / 2 := by positivity
    have ha1 : 0 < t ^ 2 / 2 + 1 := by positivity
    calc
      (t ^ 2 / 2) * c ≤ (t ^ 2 / 2) * (1 / (2 * (t ^ 2 / 2 + 1))) :=
        mul_le_mul_of_nonneg_left hcle ha0
      _ ≤ 1 / 2 := by
        have hfrac : (t ^ 2 / 2) / (t ^ 2 / 2 + 1) ≤ 1 := by
          exact (div_le_one ha1).mpr (by linarith)
        have heq : (t ^ 2 / 2) * (1 / (2 * (t ^ 2 / 2 + 1))) =
            (1 / 2) * ((t ^ 2 / 2) / (t ^ 2 / 2 + 1)) := by field_simp
        rw [heq]
        nlinarith
  have hsmallClock : (t ^ 2 / 2) * (delta ^ 2 + c) ≤ 1 := by
    ring_nf at hdeltaClock hcClock ⊢
    linarith
  have hdet : C *
      ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) +
        (2 / 9 : ℝ) * |t| ^ 3 * delta * b + K * c) < epsilon / 2 := by
    have hdchoice : delta ≤ epsilon / (4 * C * (A0 + B0 + 1)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hcchoice : c ≤ epsilon / (4 * C * (K + A0)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hdelta1 : delta ≤ 1 := min_le_left _ _
    have hdeltaSq : delta ^ 2 ≤ delta := by
      nlinarith [le_of_lt hdelta]
    have hCpos : 0 < C := by dsimp [C]; positivity
    have hA0 : 0 ≤ A0 := by dsimp [A0, b]; positivity
    have hB0 : 0 ≤ B0 := by dsimp [B0, b]; positivity
    have hABpos : 0 < A0 + B0 + 1 := by positivity
    have hdeltaPart : C * (A0 * delta ^ 2 + B0 * delta) < epsilon / 4 := by
      calc
        C * (A0 * delta ^ 2 + B0 * delta) ≤
            C * (A0 * delta + B0 * delta) := by
          apply mul_le_mul_of_nonneg_left _ hCpos.le
          exact add_le_add (mul_le_mul_of_nonneg_left hdeltaSq hA0) le_rfl
        _ = (C * (A0 + B0)) * delta := by ring
        _ ≤ (C * (A0 + B0)) *
            (epsilon / (4 * C * (A0 + B0 + 1))) :=
          mul_le_mul_of_nonneg_left hdchoice
            (mul_nonneg hCpos.le (add_nonneg hA0 hB0))
        _ < epsilon / 4 := by
          have hratio : (A0 + B0) / (A0 + B0 + 1) < 1 :=
            (div_lt_one hABpos).mpr (by linarith)
          have hCne : C ≠ 0 := ne_of_gt hCpos
          calc
            (C * (A0 + B0)) *
                (epsilon / (4 * C * (A0 + B0 + 1))) =
              (epsilon / 4) * ((A0 + B0) / (A0 + B0 + 1)) := by
                field_simp
            _ < (epsilon / 4) * 1 :=
              mul_lt_mul_of_pos_left hratio (by positivity)
            _ = epsilon / 4 := by ring
    have hKApos : 0 < K + A0 := by
      exact add_pos_of_pos_of_nonneg hKpos hA0
    have hcPart : C * ((A0 + K) * c) ≤ epsilon / 4 := by
      calc
        C * ((A0 + K) * c) = (C * (K + A0)) * c := by ring
        _ ≤ (C * (K + A0)) *
            (epsilon / (4 * C * (K + A0))) :=
          mul_le_mul_of_nonneg_left hcchoice
            (mul_nonneg hCpos.le hKApos.le)
        _ = epsilon / 4 := by field_simp
    dsimp [A0, B0] at hdeltaPart hcPart
    calc
      C * ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * (delta ^ 2 + c) +
          (2 / 9 : ℝ) * |t| ^ 3 * delta * b + K * c) =
        C * (((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * delta ^ 2 +
          (2 / 9 : ℝ) * |t| ^ 3 * b * delta) +
          (((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b + K) * c)) := by ring
      _ = C * ((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b * delta ^ 2 +
          (2 / 9 : ℝ) * |t| ^ 3 * b * delta) +
        C * (((7 / 4 : ℝ) * (t ^ 2 / 2) ^ 2 * b + K) * c) := by ring
      _ < epsilon / 4 + epsilon / 4 := add_lt_add_of_lt_of_le hdeltaPart hcPart
      _ = epsilon / 2 := by ring
  have hstop := A.twoClockStopEvent_measure_tendsto_zero
    hA hQV hLindeberg b c delta hb hc hdelta
  have hstopReal : Tendsto (fun n =>
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n))
      atTop (nhds 0) := by
    have hr : Tendsto (fun n =>
        (A.probability n).real (A.twoClockStopEvent b c delta n))
        atTop (nhds 0) := by
      apply (ENNReal.tendsto_toReal_zero_iff
        (fun n => measure_ne_top (A.probability n) _)).2
      exact hstop
    simpa using tendsto_const_nhds.mul hr
  have hclock := A.twoClockStoppedVarianceClock_exp_factor_L1_tendsto_zero
    hA hQV hLindeberg b c delta t hb hc hdelta
  have hvar : Tendsto (fun n =>
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n) +
      ∫ omega,
        |Real.exp ((t ^ 2 / 2) *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
        ∂(A.probability n)) atTop (nhds 0) := by
    simpa using hstopReal.add hclock
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hvar)
    (epsilon / 2) (half_pos hepsilon)
  refine ⟨N, fun n hn => ?_⟩
  have hvarn := hN n hn
  have hfinite := A.characteristicFunction_gaussian_error_le
    hA b c delta t hb hc hdelta hsmallTaylor hsmallClock n
  have hvar_nonneg : 0 ≤
      2 * (A.probability n).real (A.twoClockStopEvent b c delta n) +
      ∫ omega,
        |Real.exp ((t ^ 2 / 2) *
          (A.twoClockStoppedVarianceClock b c delta n (A.rowLength n) omega - 1)) - 1|
        ∂(A.probability n) := add_nonneg
      (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (integral_nonneg (fun _ => abs_nonneg _))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hvar_nonneg] at hvarn
  change dist (err n) 0 < epsilon
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (herr0 n)]
  exact lt_of_le_of_lt hfinite (by
    dsimp [C, K] at hdet
    linarith)

/-- The exact residual promised by the generic martingale-array CLT. -/
theorem characteristicFunctionConvergenceResidual :
    A.CharacteristicFunctionConvergenceResidual := by
  unfold CharacteristicFunctionConvergenceResidual
  intro hA hQV hLindeberg t
  have h := A.characteristicFunctionConvergence hA hQV hLindeberg t
  convert h using 1
  simp [Complex.exp_ofReal_re]
  push_cast
  ring


/-- The public finite varying-space martingale-array central limit theorem.

The row laws converge weakly to the standard Gaussian law.  The proof uses
`characteristicFunctionConvergence` and Lévy's continuity theorem; no relation between
the sample spaces or filtrations of distinct rows is required. -/
theorem varyingSpaceMartingaleArrayCLT :
    A.VaryingSpaceMartingaleArrayCLT := by
  unfold VaryingSpaceMartingaleArrayCLT
  intro hA hQV hLindeberg OmegaLimit mLimit PLimit hPLimit Y hY
  have hrowmeas : ∀ n, AEMeasurable (A.rowSum n) (A.probability n) := by
    intro n
    rw [A.rowSum_eq_partialSum_rowLength n]
    exact (natPartialSum_stronglyAdapted (A.paddedIncrement n)
      (A.paddedIncrement_stronglyMeasurable hA n) (A.rowLength n)).aestronglyMeasurable.mono
      ((A.filtration n).le (A.rowLength n)) |>.aemeasurable
  let mu : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(A.probability n).map (A.rowSum n),
      Measure.isProbabilityMeasure_map (hrowmeas n)⟩
  let mu0 : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hchar : ∀ t : ℝ, Tendsto (fun n => charFun (mu n) t)
      atTop (nhds (charFun mu0 t)) := by
    intro t
    have hcf := A.characteristicFunctionConvergenceResidual hA hQV hLindeberg t
    convert hcf using 1
    · funext n
      dsimp [mu]
      rw [charFun_apply_real, integral_map]
      · apply integral_congr_ae
        filter_upwards [] with omega
        rw [complexPhase]
        congr 1
        push_cast
        ring
      · exact hrowmeas n
      · exact (by fun_prop)
    · dsimp [mu0]
      rw [charFun_gaussianReal]
      congr 1
      norm_num
      push_cast
      ring
  have hmu : Tendsto mu atTop (nhds mu0) :=
    ProbabilityMeasure.tendsto_of_tendsto_charFun hchar
  refine TendstoInDistribution.mk hrowmeas hY.aemeasurable ?_
  convert hmu using 2
  exact Subtype.ext hY.map_eq


end ArrayData

end
end MartingaleArrayCLT
end Forest
end Erdos993
