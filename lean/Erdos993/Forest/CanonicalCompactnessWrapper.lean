import Erdos993.Forest.CanonicalLaw
import Erdos993.Forest.FourierTuranCurvature
import Erdos993.MeasureFourierInversion
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter MeasureTheory Complex Real Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos993.Forest.CanonicalCompactnessWrapper

noncomputable section

open FourierTuranCurvature
open Erdos993.MeasureFourierInversion

/-- An actual canonical first-recovery sequence.  The vertex type is `Fin (order n)`,
so both the finite type and graph are allowed to vary with `n`.  The variance is
not independent data: it is always the variance of the stored canonical law. -/
structure CanonicalSequence where
  order : ℕ → ℕ
  graph : ∀ n, SimpleGraph (Fin (order n))
  state : ∀ n, CanonicalFirstRecoveryState (graph n)
  activity_lt : ∀ n, (state n).activity < 27
  variance_pos : ∀ n, 0 < (state n).variance
  variance_tendsto : Tendsto (fun n => (state n).variance) atTop atTop

namespace CanonicalSequence

variable (S : CanonicalSequence)

/-- Canonical variance `V_n`. -/
def V (n : ℕ) : ℝ := (S.state n).variance

/-- Centered rank mass `p_n(j)=P(X_n=s_n+j)`, with zero outside natural ranks. -/
def centeredMass (n : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ (S.state n).index + j then
    (S.state n).law.rankMass (Int.toNat ((S.state n).index + j))
  else 0

/-- The standardized lattice point corresponding to rank `k`. -/
def standardizedRank (n : ℕ) (k : Fin (S.order n + 1)) : ℝ :=
  (((k : ℕ) : ℝ) - ((S.state n).index : ℝ)) / Real.sqrt (S.V n)

/-- The actual rank PMF of the canonical hard-core law. -/
def rankPMF (n : ℕ) : PMF (Fin (S.order n + 1)) := by
  refine PMF.ofFintype
    (fun k => ENNReal.ofReal ((S.state n).law.rankMass (k : ℕ))) ?_
  calc
    (∑ k : Fin (S.order n + 1),
        ENNReal.ofReal ((S.state n).law.rankMass (k : ℕ))) =
      ∑ k ∈ Finset.range (S.order n + 1),
        ENNReal.ofReal ((S.state n).law.rankMass k) :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ENNReal.ofReal ((S.state n).law.rankMass k))
        (S.order n + 1)
    _ = ENNReal.ofReal (∑ k ∈ Finset.range (S.order n + 1),
          (S.state n).law.rankMass k) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro k hk
      exact (S.state n).law.rankMass_nonneg k
    _ = 1 := by
      have hsum : ∑ k ∈ Finset.range (S.order n + 1),
          (S.state n).law.rankMass k = 1 := by
        simpa [CanonicalFirstRecoveryState.order] using
          (S.state n).sum_law_rankMass_eq_one
      rw [hsum]
      norm_num

@[simp] theorem rankPMF_apply (n : ℕ) (k : Fin (S.order n + 1)) :
    (S.rankPMF n k).toReal = (S.state n).law.rankMass (k : ℕ) := by
  simp [rankPMF, ENNReal.toReal_ofReal,
    (S.state n).law.rankMass_nonneg (k : ℕ)]

/-- The actual finite rank probability measure. -/
def rankLaw (n : ℕ) : ProbabilityMeasure (Fin (S.order n + 1)) :=
  ⟨(S.rankPMF n).toMeasure, PMF.toMeasure.isProbabilityMeasure (S.rankPMF n)⟩

/-- The law of `(X_n-s_n)/sqrt(V_n)`, obtained by pushing forward the actual
canonical rank law. -/
def standardizedLaw (n : ℕ) : ProbabilityMeasure ℝ :=
  (S.rankLaw n).map (measurable_of_finite (S.standardizedRank n)).aemeasurable

/-- The standardized characteristic function of the actual law. -/
def characteristic (n : ℕ) (u : ℝ) : ℂ :=
  charFun (S.standardizedLaw n) u

/-- The scaled lattice Fourier fundamental domain. -/
def domain (n : ℕ) : Set ℝ :=
  Set.Icc (-Real.pi * Real.sqrt (S.V n)) (Real.pi * Real.sqrt (S.V n))

/-- The zero extension from the scaled fundamental domain. -/
def zeroExtendedCharacteristic (n : ℕ) : ℝ → ℂ :=
  (S.domain n).indicator (S.characteristic n)

/-- Canonical mean regrouped over the actual finite rank PMF. -/
theorem rank_mean_eq_index (n : ℕ) :
    ∑ k : Fin (S.order n + 1),
      (S.state n).law.rankMass (k : ℕ) * ((k : ℕ) : ℝ) =
        ((S.state n).index : ℝ) := by
  calc
    _ = ∑ k ∈ Finset.range (S.order n + 1),
        (S.state n).law.rankMass k * (k : ℝ) :=
      Fin.sum_univ_eq_sum_range
        (fun k : ℕ => (S.state n).law.rankMass k * (k : ℝ))
        (S.order n + 1)
    _ = (S.state n).law.mean := by
      have hstat : ∀ s, (S.state n).law.stat s ≤ (S.state n).order := by
        intro s
        exact hardCoreLaw_stat_le_order (S.graph n) (S.state n).activity
          (S.state n).activity_pos s
      have hmean := FiniteLatticeLaw.mean_eq_sum_rankMass (S.state n).law
        (S.state n).order hstat
      simpa [CanonicalFirstRecoveryState.order] using hmean.symm
    _ = _ := (S.state n).law_mean

/-- Total actual rank mass is exactly one. -/
theorem rank_mass_sum_eq_one (n : ℕ) :
    ∑ k : Fin (S.order n + 1), (S.state n).law.rankMass (k : ℕ) = 1 := by
  calc
    _ = ∑ k ∈ Finset.range (S.order n + 1),
        (S.state n).law.rankMass k :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => (S.state n).law.rankMass k)
        (S.order n + 1)
    _ = 1 := by
      simpa [CanonicalFirstRecoveryState.order] using
        (S.state n).sum_law_rankMass_eq_one

/-- The unscaled centered first moment is zero. -/
theorem centered_rank_sum_eq_zero (n : ℕ) :
    ∑ k : Fin (S.order n + 1),
      (S.state n).law.rankMass (k : ℕ) *
        (((k : ℕ) : ℝ) - ((S.state n).index : ℝ)) = 0 := by
  calc
    _ = (∑ k : Fin (S.order n + 1),
        (S.state n).law.rankMass (k : ℕ) * ((k : ℕ) : ℝ)) -
      ((S.state n).index : ℝ) *
        (∑ k : Fin (S.order n + 1),
          (S.state n).law.rankMass (k : ℕ)) := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
    _ = 0 := by rw [S.rank_mean_eq_index n, S.rank_mass_sum_eq_one n]; ring

/-- Exact standardized first moment (finite-law form). -/
theorem standardized_mean_sum_eq_zero (n : ℕ) :
    ∑ k : Fin (S.order n + 1),
      (S.state n).law.rankMass (k : ℕ) * S.standardizedRank n k = 0 := by
  unfold standardizedRank
  calc
    _ = (∑ k : Fin (S.order n + 1),
        (S.state n).law.rankMass (k : ℕ) *
          (((k : ℕ) : ℝ) - ((S.state n).index : ℝ))) /
        Real.sqrt (S.V n) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by rw [S.centered_rank_sum_eq_zero n, zero_div]

/-- Exact standardized second moment/variance one (finite-law form). -/
theorem standardized_secondMoment_sum_eq_one (n : ℕ) :
    ∑ k : Fin (S.order n + 1),
      (S.state n).law.rankMass (k : ℕ) * (S.standardizedRank n k) ^ 2 = 1 := by
  have hV : 0 < S.V n := S.variance_pos n
  have hsqrt_sq : (Real.sqrt (S.V n)) ^ 2 = S.V n := sq_sqrt hV.le
  unfold standardizedRank
  calc
    _ = (1 / S.V n) *
        (∑ k : Fin (S.order n + 1),
          (S.state n).law.rankMass (k : ℕ) *
            (((k : ℕ) : ℝ) - ((S.state n).index : ℝ)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [div_pow, hsqrt_sq]
      field_simp
    _ = (1 / S.V n) * S.V n := by
      congr 1
      calc
        _ = ∑ k ∈ Finset.range (S.order n + 1),
            (S.state n).law.rankMass k *
              ((k : ℝ) - ((S.state n).index : ℝ)) ^ 2 :=
          Fin.sum_univ_eq_sum_range
            (fun k : ℕ => (S.state n).law.rankMass k *
              ((k : ℝ) - ((S.state n).index : ℝ)) ^ 2)
            (S.order n + 1)
        _ = S.V n := by
          simpa [V, CanonicalFirstRecoveryState.order] using
            (S.state n).variance_eq_sum_rankMass.symm
    _ = 1 := by field_simp

/-- A concrete finite Chebyshev certificate. -/
theorem chebyshev_tail_sum (n : ℕ) {R : ℝ} (hR : 0 < R) :
    (∑ k : Fin (S.order n + 1),
      (if R ≤ |S.standardizedRank n k| then
        (S.state n).law.rankMass (k : ℕ) else 0)) ≤ 1 / R ^ 2 := by
  have hmul : R ^ 2 *
      (∑ k : Fin (S.order n + 1),
        (if R ≤ |S.standardizedRank n k| then
          (S.state n).law.rankMass (k : ℕ) else 0)) ≤ 1 := by
    calc
      _ = ∑ k : Fin (S.order n + 1), R ^ 2 *
          (if R ≤ |S.standardizedRank n k| then
            (S.state n).law.rankMass (k : ℕ) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ ∑ k : Fin (S.order n + 1),
          (S.state n).law.rankMass (k : ℕ) * (S.standardizedRank n k) ^ 2 := by
          apply Finset.sum_le_sum
          intro k hk
          split_ifs with h
          · have hp := (S.state n).law.rankMass_nonneg (k : ℕ)
            have habs_sq : |S.standardizedRank n k| ^ 2 =
                (S.standardizedRank n k) ^ 2 := sq_abs _
            have hsquare : R ^ 2 ≤ (S.standardizedRank n k) ^ 2 := by
              nlinarith [sq_nonneg (|S.standardizedRank n k| - R)]
            nlinarith
          · simpa using mul_nonneg
              ((S.state n).law.rankMass_nonneg (k : ℕ))
              (sq_nonneg (S.standardizedRank n k))
      _ = 1 := S.standardized_secondMoment_sum_eq_one n
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  apply (le_div_iff₀ hR2).2
  simpa [mul_comm] using hmul

/-- Integration against the pushed-forward finite law is the expected finite sum. -/
theorem integral_standardizedLaw_of_continuous
    (n : ℕ) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x : ℝ, f x ∂(S.standardizedLaw n : Measure ℝ) =
      ∑ k : Fin (S.order n + 1),
        (S.state n).law.rankMass (k : ℕ) * f (S.standardizedRank n k) := by
  change ∫ x : ℝ, f x ∂Measure.map
      (S.standardizedRank n) (S.rankLaw n : Measure (Fin (S.order n + 1))) = _
  rw [MeasureTheory.integral_map
    (measurable_of_finite (S.standardizedRank n)).aemeasurable
    hf.aestronglyMeasurable]
  change ∫ k : Fin (S.order n + 1),
      f (S.standardizedRank n k) ∂(S.rankPMF n).toMeasure = _
  rw [PMF.integral_eq_sum]
  simp only [rankPMF_apply, smul_eq_mul]

/-- Complex-valued finite-law integration after the push-forward. -/
theorem integral_standardizedLaw_of_continuous_complex
    (n : ℕ) {f : ℝ → ℂ} (hf : Continuous f) :
    ∫ x : ℝ, f x ∂(S.standardizedLaw n : Measure ℝ) =
      ∑ k : Fin (S.order n + 1),
        ((S.state n).law.rankMass (k : ℕ) : ℂ) * f (S.standardizedRank n k) := by
  change ∫ x : ℝ, f x ∂Measure.map
      (S.standardizedRank n) (S.rankLaw n : Measure (Fin (S.order n + 1))) = _
  rw [MeasureTheory.integral_map
    (measurable_of_finite (S.standardizedRank n)).aemeasurable
    hf.aestronglyMeasurable]
  change ∫ k : Fin (S.order n + 1),
      f (S.standardizedRank n k) ∂(S.rankPMF n).toMeasure = _
  rw [PMF.integral_eq_sum]
  simp only [rankPMF_apply, smul_eq_mul]
  norm_cast

/-- The actual characteristic function is the finite exponential sum of the
standardized rank masses. -/
theorem characteristic_eq_finite_sum (n : ℕ) (u : ℝ) :
    S.characteristic n u =
      ∑ k : Fin (S.order n + 1),
        ((S.state n).law.rankMass (k : ℕ) : ℂ) *
          Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I) := by
  rw [characteristic, charFun_apply_real]
  rw [S.integral_standardizedLaw_of_continuous_complex n]
  · simp only [Complex.ofReal_mul]
  · fun_prop

/-- Multiplying the Fourier phase by one finite-law exponential produces the
single lattice frequency given by the centered rank difference. -/
theorem phase_mul_exp_eq_frequency (n : ℕ) (j : ℤ)
    (k : Fin (S.order n + 1)) (u : ℝ) :
    phase (S.V n) j u *
        Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I) =
      Complex.exp (((((((k : ℕ) : ℤ) - (S.state n).index - j : ℤ) /
        Real.sqrt (S.V n) : ℝ) : ℂ) * Complex.I) * (u : ℂ)) := by
  rw [phase, ← Complex.exp_add]
  congr 1
  dsimp [standardizedRank]
  push_cast
  have hs : Real.sqrt (S.V n) ≠ 0 :=
    (Real.sqrt_pos.2 (S.variance_pos n)).ne'
  field_simp [hs]
  ring

/-- Exact orthogonality on one scaled Fourier period. -/
theorem intervalIntegral_exp_lattice (r : ℝ) (hr : 0 < r) (m : ℤ) :
    (∫ u : ℝ in (-Real.pi * r)..(Real.pi * r),
      Complex.exp (((((m : ℝ) / r : ℝ) : ℂ) * Complex.I) * (u : ℂ))) =
      if m = 0 then ((2 * Real.pi * r : ℝ) : ℂ) else 0 := by
  split_ifs with hm
  · subst m
    simp only [Int.cast_zero, zero_div, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    change (((Real.pi * r - -Real.pi * r : ℝ) : ℂ) * 1) =
      ((2 * Real.pi * r : ℝ) : ℂ)
    rw [mul_one]
    push_cast
    ring
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    let c : ℂ := ((((m : ℝ) / r : ℝ) : ℂ) * Complex.I)
    have hc : c ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast div_ne_zero hmR (ne_of_gt hr)
      · exact Complex.I_ne_zero
    have hend : Complex.exp (c * (Real.pi * r : ℝ)) =
        Complex.exp (c * (-Real.pi * r : ℝ)) := by
      have harg : c * (Real.pi * r : ℝ) =
          c * (-Real.pi * r : ℝ) +
            (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        dsimp [c]
        push_cast
        field_simp [ne_of_gt hr]
        ring
      rw [harg, Complex.exp_add,
        Complex.exp_int_mul_two_pi_mul_I, mul_one]
    change (∫ u : ℝ in (-Real.pi * r)..(Real.pi * r),
      Complex.exp (c * (u : ℂ))) = 0
    rw [integral_exp_mul_complex hc, hend, sub_self, zero_div]


/-- On an interior centered rank, the finite characteristic-function sum
integrates to the corresponding centered mass. -/
theorem intervalIntegral_phase_characteristic_of_mem
    (n : ℕ) (j : ℤ)
    (hlo : 0 ≤ (S.state n).index + j)
    (hhi : (S.state n).index + j ≤ (S.order n : ℤ)) :
    (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
      phase (S.V n) j u * S.characteristic n u) =
      ((2 * Real.pi * Real.sqrt (S.V n) : ℝ) : ℂ) *
        (S.state n).law.rankMass (Int.toNat ((S.state n).index + j)) := by
  let q : ℤ := (S.state n).index + j
  let k0 : Fin (S.order n + 1) :=
    ⟨Int.toNat q, by
      have hq : q ≤ (S.order n : ℤ) := hhi
      have hnat : q.toNat ≤ S.order n := by omega
      exact Nat.lt_succ_of_le hnat⟩
  have hq : (k0 : ℤ) = q := by
    dsimp [k0, q]
    exact Int.toNat_of_nonneg hlo
  have hzero : ((k0 : ℤ) - (S.state n).index - j) = 0 := by
    rw [hq]
    dsimp [q]
    ring
  calc
    _ = ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        phase (S.V n) j u *
          ∑ k : Fin (S.order n + 1),
            ((S.state n).law.rankMass (k : ℕ) : ℂ) *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change phase (S.V n) j u * S.characteristic n u = _
      rw [S.characteristic_eq_finite_sum n u]
    _ = ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        ∑ k : Fin (S.order n + 1),
          ((S.state n).law.rankMass (k : ℕ) : ℂ) *
            (phase (S.V n) j u *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k : Fin (S.order n + 1),
        ((S.state n).law.rankMass (k : ℕ) : ℂ) *
          (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
            phase (S.V n) j u *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) := by
      rw [intervalIntegral.integral_finset_sum (by
        intro k hk
        apply Continuous.intervalIntegrable
        simp only [phase]
        fun_prop)]
      apply Finset.sum_congr rfl
      intro k hk
      simpa only using
        (intervalIntegral.integral_const_mul
          ((S.state n).law.rankMass (k : ℕ) : ℂ)
          (fun x : ℝ => phase (S.V n) j x *
            Complex.exp ((x * S.standardizedRank n k : ℝ) * Complex.I)))
    _ = ∑ k : Fin (S.order n + 1),
        ((S.state n).law.rankMass (k : ℕ) : ℂ) *
          (if ((k : ℤ) - (S.state n).index - j) = 0 then
            ((2 * Real.pi * Real.sqrt (S.V n) : ℝ) : ℂ) else 0) := by
      apply Finset.sum_congr rfl
      intro k hk
      congr 1
      have hintegral :
          (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
            phase (S.V n) j u *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) =
            ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
              Complex.exp (((((((k : ℕ) : ℤ) - (S.state n).index - j : ℤ) /
                Real.sqrt (S.V n) : ℝ) : ℂ) * Complex.I) * (u : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro u hu
        exact S.phase_mul_exp_eq_frequency n j k u
      rw [hintegral, intervalIntegral_exp_lattice]
      exact Real.sqrt_pos.2 (S.variance_pos n)
    _ = ((2 * Real.pi * Real.sqrt (S.V n) : ℝ) : ℂ) *
        (S.state n).law.rankMass (Int.toNat q) := by
      rw [Finset.sum_eq_single k0]
      · rw [hzero]
        change ((S.state n).law.rankMass (Int.toNat q) : ℂ) *
            ((2 * Real.pi * Real.sqrt (S.V n) : ℝ) : ℂ) =
          ((2 * Real.pi * Real.sqrt (S.V n) : ℝ) : ℂ) *
            ((S.state n).law.rankMass (Int.toNat q) : ℂ)
        ring
      · intro b hb hne
        have hne' : (b : ℤ) - (S.state n).index - j ≠ 0 := by
          intro hz
          apply hne
          apply Fin.ext
          omega
        simp [hne']
      · simp

/-- After expanding the finite characteristic function, the interval integral
is the finite sum of one-frequency integrals. -/
theorem intervalIntegral_phase_characteristic_eq_sum
    (n : ℕ) (j : ℤ) :
    (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
      phase (S.V n) j u * S.characteristic n u) =
      ∑ k : Fin (S.order n + 1),
        ((S.state n).law.rankMass (k : ℕ) : ℂ) *
          (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
            phase (S.V n) j u *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) := by
  calc
    _ = ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        phase (S.V n) j u *
          ∑ k : Fin (S.order n + 1),
            ((S.state n).law.rankMass (k : ℕ) : ℂ) *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I) := by
      apply intervalIntegral.integral_congr
      intro u hu
      change phase (S.V n) j u * S.characteristic n u = _
      rw [S.characteristic_eq_finite_sum n u]
    _ = ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        ∑ k : Fin (S.order n + 1),
          ((S.state n).law.rankMass (k : ℕ) : ℂ) *
            (phase (S.V n) j u *
              Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finset_sum (by
        intro k hk
        apply Continuous.intervalIntegrable
        simp only [phase]
        fun_prop)]
      apply Finset.sum_congr rfl
      intro k hk
      simpa only using
        (intervalIntegral.integral_const_mul
          ((S.state n).law.rankMass (k : ℕ) : ℂ)
          (fun x : ℝ => phase (S.V n) j x *
            Complex.exp ((x * S.standardizedRank n k : ℝ) * Complex.I)))

/-- The interval integral vanishes when the centered target is outside the
finite rank support. -/
theorem intervalIntegral_phase_characteristic_of_not_mem
    (n : ℕ) (j : ℤ)
    (hout : ¬ (0 ≤ (S.state n).index + j ∧
      (S.state n).index + j ≤ (S.order n : ℤ))) :
    (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
      phase (S.V n) j u * S.characteristic n u) = 0 := by
  rw [S.intervalIntegral_phase_characteristic_eq_sum n j]
  apply Finset.sum_eq_zero
  intro k hk
  have hintegral :
      (∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        phase (S.V n) j u *
          Complex.exp ((u * S.standardizedRank n k : ℝ) * Complex.I)) =
        ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
          Complex.exp (((((((k : ℕ) : ℤ) - (S.state n).index - j : ℤ) /
            Real.sqrt (S.V n) : ℝ) : ℂ) * Complex.I) * (u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact S.phase_mul_exp_eq_frequency n j k u
  rw [hintegral, intervalIntegral_exp_lattice]
  · simp only [mul_ite, mul_zero]
    split_ifs with hz
    · have hqlo : 0 ≤ (S.state n).index + j := by omega
      have hqhi : (S.state n).index + j ≤ (S.order n : ℤ) := by
        have hklt := k.isLt
        omega
      exact False.elim (hout ⟨hqlo, hqhi⟩)
    · rfl
  · exact Real.sqrt_pos.2 (S.variance_pos n)

/-- The zero extension has the same integral as the scaled fundamental interval;
the endpoint convention is immaterial for Lebesgue integration. -/
theorem zeroExtended_phase_integral_eq_interval (n : ℕ) (j : ℤ) :
    (∫ u : ℝ,
      phase (S.V n) j u * S.zeroExtendedCharacteristic n u) =
      ∫ u : ℝ in (-Real.pi * Real.sqrt (S.V n))..(Real.pi * Real.sqrt (S.V n)),
        phase (S.V n) j u * S.characteristic n u := by
  let a : ℝ := -Real.pi * Real.sqrt (S.V n)
  let b : ℝ := Real.pi * Real.sqrt (S.V n)
  have hab : a ≤ b := by
    dsimp [a, b]
    have hnon : 0 ≤ Real.pi * Real.sqrt (S.V n) :=
      mul_nonneg Real.pi_pos.le (Real.sqrt_nonneg (S.V n))
    linarith
  calc
    _ = ∫ u : ℝ, (S.domain n).indicator
        (fun x : ℝ => phase (S.V n) j x * S.characteristic n x) u := by
      apply integral_congr_ae
      filter_upwards with u
      by_cases hu : u ∈ S.domain n
      · simp [zeroExtendedCharacteristic, Set.indicator_of_mem hu]
      · simp [zeroExtendedCharacteristic, Set.indicator_of_notMem hu]
    _ = ∫ u : ℝ in S.domain n,
        phase (S.V n) j u * S.characteristic n u := by
      change (∫ u : ℝ, (Set.Icc (-Real.pi * Real.sqrt (S.V n))
        (Real.pi * Real.sqrt (S.V n))).indicator
          (fun x : ℝ => phase (S.V n) j x * S.characteristic n x) u) = _
      exact MeasureTheory.integral_indicator measurableSet_Icc
    _ = ∫ u : ℝ in Set.Ioc a b,
        phase (S.V n) j u * S.characteristic n u := by
      rw [show S.domain n = Set.Icc a b by rfl]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [MeasureTheory.Measure.ae_ne (μ := volume) a] with u hua
      by_cases hub : u ∈ Set.Ioc a b
      · have hucc : u ∈ Set.Icc a b := ⟨le_of_lt hub.1, hub.2⟩
        simp [Set.indicator_of_mem hub, Set.indicator_of_mem hucc]
      · have hnot : u ∉ Set.Icc a b := by
          intro hucc
          exact hub ⟨lt_of_le_of_ne hucc.1 (Ne.symm hua), hucc.2⟩
        simp [Set.indicator_of_notMem hub, Set.indicator_of_notMem hnot]
    _ = ∫ u : ℝ in a..b,
        phase (S.V n) j u * S.characteristic n u := by
      rw [intervalIntegral.integral_of_le hab]
    _ = _ := by rfl

/-- Actual finite-law lattice inversion, derived from finite Fourier
orthogonality and the zero extension rather than assumed. -/
theorem actual_lattice_fourier_inversion (n : ℕ) :
    LatticeFourierInversion (S.V n) (S.centeredMass n)
      (S.zeroExtendedCharacteristic n) := by
  intro j
  by_cases hlo : 0 ≤ (S.state n).index + j
  · by_cases hhi : (S.state n).index + j ≤ (S.order n : ℤ)
    · rw [S.zeroExtended_phase_integral_eq_interval n j,
        S.intervalIntegral_phase_characteristic_of_mem n j hlo hhi]
      have hs : Real.sqrt (S.V n) ≠ 0 :=
        (Real.sqrt_pos.2 (S.variance_pos n)).ne'
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      field_simp [hs, hpi]
      simp [centeredMass, hlo]
    · rw [S.zeroExtended_phase_integral_eq_interval n j,
        S.intervalIntegral_phase_characteristic_of_not_mem n j (by
          intro h
          exact hhi h.2)]
      have hk : S.order n < Int.toNat ((S.state n).index + j) := by
        omega
      unfold centeredMass
      rw [if_pos hlo]
      have hk' : (S.state n).order < Int.toNat ((S.state n).index + j) := by
        simpa [CanonicalFirstRecoveryState.order] using hk
      rw [(S.state n).law_rankMass_eq_zero_of_order_lt
        (Int.toNat ((S.state n).index + j)) hk']
      simp
  · rw [S.zeroExtended_phase_integral_eq_interval n j]
    have hout : ¬ (0 ≤ (S.state n).index + j ∧
        (S.state n).index + j ≤ (S.order n : ℤ)) := by
      intro h
      exact hlo h.1
    rw [S.intervalIntegral_phase_characteristic_of_not_mem n j hout]
    simp [centeredMass, hlo]

/-- Exact standardized mean and second moment as actual probability integrals. -/
theorem standardized_mean_integral_eq_zero (n : ℕ) :
    ∫ x : ℝ, x ∂(S.standardizedLaw n : Measure ℝ) = 0 := by
  simpa using (S.integral_standardizedLaw_of_continuous n
    (f := fun x : ℝ => x) continuous_id |>.trans
    (S.standardized_mean_sum_eq_zero n))

theorem standardized_secondMoment_integral_eq_one (n : ℕ) :
    ∫ x : ℝ, x ^ 2 ∂(S.standardizedLaw n : Measure ℝ) = 1 := by
  simpa using (S.integral_standardizedLaw_of_continuous n
    (f := fun x : ℝ => x ^ 2) (continuous_id.pow 2) |>.trans
    (S.standardized_secondMoment_sum_eq_one n))

/-- The second moment is integrable, a fact used by the compactness argument. -/
theorem standardized_secondMoment_integrable (n : ℕ) :
    Integrable (fun x : ℝ => x ^ 2) (S.standardizedLaw n : Measure ℝ) := by
  by_contra h
  have hzero := integral_undef h
  have hone := S.standardized_secondMoment_integral_eq_one n
  rw [hzero] at hone
  norm_num at hone


/-- Prokhorov extraction from the derived second-moment certificate. -/
theorem exists_subseq_tendsto
    (S : CanonicalSequence) :
    ∃ ν : ProbabilityMeasure ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (S.standardizedLaw ∘ φ) atTop (𝓝 ν) := by
  let laws : Set (ProbabilityMeasure ℝ) := Set.range S.standardizedLaw
  have htight : MeasureTheory.IsTightMeasureSet
      {x : Measure ℝ | ∃ μ ∈ laws, (μ : Measure ℝ) = x} := by
    rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases htop : ε = ∞
    · refine ⟨∅, isCompact_empty, ?_⟩
      intro μ hμ
      simp [htop]
    · let e : ℝ := ε.toReal
      let R : ℝ := e⁻¹ + 1
      have he : 0 < e := ENNReal.toReal_pos hε.ne' htop
      have hR : 0 < R := by
        dsimp [R]
        positivity
      have hR1 : 1 ≤ R := by
        dsimp [R]
        linarith [inv_nonneg.mpr he.le]
      have hreal : 1 / R ^ 2 ≤ e := by
        rw [div_le_iff₀ (sq_pos_of_pos hR)]
        have hi : e * e⁻¹ = 1 := by field_simp [he.ne']
        have hie : e⁻¹ ≤ R := by dsimp [R]; linarith
        have hRR : R ≤ R ^ 2 := by nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hR1)]
        calc
          1 = e * e⁻¹ := hi.symm
          _ ≤ e * R := mul_le_mul_of_nonneg_left hie he.le
          _ ≤ e * R ^ 2 := mul_le_mul_of_nonneg_left hRR he.le
      have henn : ENNReal.ofReal (1 / R ^ 2) ≤ ε := by
        rw [← ENNReal.ofReal_toReal htop]
        exact ENNReal.ofReal_le_ofReal hreal
      refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
      rintro μ ⟨ν, ⟨n, rfl⟩, rfl⟩
      have hsqint : Integrable (fun x : ℝ => x ^ 2)
          (S.standardizedLaw n : Measure ℝ) :=
        S.standardized_secondMoment_integrable n
      let q : ℝ → ℝ≥0 := fun x => ⟨x ^ 2, sq_nonneg x⟩
      have hqint : Integrable (fun x : ℝ => (q x : ℝ))
          (S.standardizedLaw n : Measure ℝ) := by
        simpa [q] using hsqint
      have hlin : (∫⁻ x : ℝ, (q x : ENNReal)
          ∂(S.standardizedLaw n : Measure ℝ)) = 1 := by
        rw [MeasureTheory.lintegral_coe_eq_integral q hqint]
        simpa [q] using S.standardized_secondMoment_integral_eq_one n
      have hsubset : (Set.Icc (-R) R)ᶜ ⊆
          {x : ℝ | ENNReal.ofReal (R ^ 2) ≤ (q x : ENNReal)} := by
        intro x hx
        have hx' : x < -R ∨ R < x := by
          have hxnot : ¬ (-R ≤ x ∧ x ≤ R) := by
            simpa [Set.mem_compl_iff, Set.mem_Icc] using hx
          by_cases hleft : x < -R
          · exact Or.inl hleft
          · right
            have hleft' : -R ≤ x := le_of_not_gt hleft
            exact lt_of_not_ge (fun hright => hxnot ⟨hleft', hright⟩)
        change ENNReal.ofReal (R ^ 2) ≤ (q x : ENNReal)
        rw [show (q x : ENNReal) = ENNReal.ofReal (x ^ 2) by
          rw [ENNReal.coe_nnreal_eq]
          congr 1
]
        rw [ENNReal.ofReal_le_ofReal_iff (sq_nonneg x)]
        rcases hx' with hx' | hx'
        · nlinarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : x - R ≤ 0)
            (by linarith : x + R ≤ 0)]
        · nlinarith [mul_nonneg (by linarith : 0 ≤ x - R)
            (by linarith : 0 ≤ x + R)]
      calc
        (S.standardizedLaw n : Measure ℝ) (Set.Icc (-R) R)ᶜ ≤
            (S.standardizedLaw n : Measure ℝ)
              {x : ℝ | ENNReal.ofReal (R ^ 2) ≤ (q x : ENNReal)} :=
          measure_mono hsubset
        _ ≤ (∫⁻ x : ℝ, (q x : ENNReal)
            ∂(S.standardizedLaw n : Measure ℝ)) /
              ENNReal.ofReal (R ^ 2) := by
          apply MeasureTheory.meas_ge_le_lintegral_div
          · fun_prop
          · exact ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hR)
          · exact ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (1 / R ^ 2) := by
          rw [hlin]
          rw [← ENNReal.ofReal_one]
          rw [← ENNReal.ofReal_div_of_pos (sq_pos_of_pos hR)]
        _ ≤ ε := henn
  have hcompact : IsCompact (closure laws) :=
    isCompact_closure_of_isTightMeasureSet htight
  obtain ⟨ν, hν, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨ν, φ, hφ, hlim⟩

/-- Each finite canonical law already satisfies the strict reverse Turán
inequality at its first-recovery center. -/
theorem centered_mass_strict_reverse_turan (n : ℕ) :
    (S.centeredMass n 0) ^ 2 <
      S.centeredMass n (-1) * S.centeredMass n 1 := by
  have hi : 0 < (S.state n).index := (S.state n).firstRecovery.index_pos
  have h := (S.state n).central_rankMass_strict_reverse_turan
  have hm : Int.toNat (((S.state n).index : ℤ) - 1) =
      (S.state n).index - 1 := by
    omega
  have hp : Int.toNat (((S.state n).index : ℤ) + 1) =
      (S.state n).index + 1 := by
    omega
  have h0 : S.centeredMass n 0 = (S.state n).law.rankMass (S.state n).index := by
    unfold centeredMass
    rw [if_pos]
    · simp
    · omega
  have hm' : S.centeredMass n (-1) =
      (S.state n).law.rankMass ((S.state n).index - 1) := by
    unfold centeredMass
    rw [if_pos]
    · rw [show (S.state n).index + (-1 : ℤ) =
          (S.state n).index - 1 by ring, hm]
    · omega
  have hp' : S.centeredMass n 1 =
      (S.state n).law.rankMass ((S.state n).index + 1) := by
    unfold centeredMass
    rw [if_pos]
    · rw [show (S.state n).index + (1 : ℤ) =
          (S.state n).index + 1 by norm_num, hp]
    · omega
  rw [h0, hm', hp']
  nlinarith [h]

/-- Weakly convergent subsequence and its pointwise characteristic-function limit. -/
theorem exists_subseq_charFun_tendsto
    (S : CanonicalSequence) :
    ∃ ν : ProbabilityMeasure ℝ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      Tendsto (S.standardizedLaw ∘ φ) atTop (𝓝 ν) ∧
      ∀ u : ℝ, Tendsto (fun m => S.characteristic (φ m) u) atTop
        (𝓝 (charFun ν u)) := by
  obtain ⟨ν, φ, hφ, hlim⟩ := S.exists_subseq_tendsto
  refine ⟨ν, φ, hφ, hlim, ?_⟩
  intro u
  have hchars :=
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hlim u
  simpa [CanonicalSequence.characteristic, Function.comp_def] using hchars

/-- The Fourier domains exhaust the line along the variance-divergent sequence. -/
theorem eventually_mem_domain
    (S : CanonicalSequence) (x : ℝ) :
    ∀ᶠ n in atTop, x ∈ S.domain n := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hev : ∀ᶠ n in atTop,
      (|x| / Real.pi) ^ 2 ≤ S.V n := by
    exact (tendsto_atTop.1 S.variance_tendsto ((|x| / Real.pi) ^ 2))
  filter_upwards [hev] with n hn
  have hsqrt : |x| / Real.pi ≤ Real.sqrt (S.V n) := by
    have hnon : 0 ≤ |x| / Real.pi := div_nonneg (abs_nonneg x) hpi.le
    have hsq : (|x| / Real.pi) ^ 2 ≤ (Real.sqrt (S.V n)) ^ 2 := by
      simpa [Real.sq_sqrt (S.variance_pos n).le, V] using hn
    exact (sq_le_sq₀ hnon (Real.sqrt_nonneg _)).1 hsq
  have habs : |x| ≤ Real.pi * Real.sqrt (S.V n) := by
    have habs' : |x| ≤ Real.sqrt (S.V n) * Real.pi :=
      (div_le_iff₀ hpi).1 hsqrt
    simpa [mul_comm] using habs'
  constructor
  · calc
      -Real.pi * Real.sqrt (S.V n) = -(Real.pi * Real.sqrt (S.V n)) := by ring
      _ ≤ -|x| := neg_le_neg habs
      _ ≤ x := neg_abs_le x
  · exact le_trans (le_abs_self x) habs

/-- A full-domain A.1-type envelope.  The envelope is a pointwise majorant
for the actual zero-extended characteristic functions and their limit; no
weighted `L¹` convergence is packaged in this interface. -/
structure FullDomainEnvelope
    (ψ : ℕ → ℝ → ℂ) (φ : ℝ → ℂ) (A : ℝ → ℝ) : Prop where
  A_nonneg : ∀ u, 0 ≤ A u
  A_weight_integrable : Integrable (fun u => weight u * A u)
  psi_measurable : ∀ n, AEStronglyMeasurable (weightedNorm (ψ n))
  phi_measurable : AEStronglyMeasurable (weightedNorm φ)
  difference_measurable : ∀ n,
    AEStronglyMeasurable (weightedDifference (ψ n) φ)
  psi_bound : ∀ n u, weightedNorm (ψ n) u ≤ weight u * A u
  phi_bound : ∀ u, weightedNorm φ u ≤ weight u * A u

/-- Dominated convergence derives all weighted data required by the promoted
W1.3 endpoint from the full-domain envelope. -/
theorem weightedL1_of_fullDomainEnvelope
    {ψ : ℕ → ℝ → ℂ} {φ : ℝ → ℂ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ φ A)
    (hpoint : ∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 (φ u))) :
    WeightedL1Convergence ψ φ := by
  have hAint : Integrable (fun u : ℝ => 2 * (weight u * A u)) := by
    simpa only [integral_const_mul] using hA.A_weight_integrable.const_mul 2
  have hpsi_int : ∀ n, Integrable (weightedNorm (ψ n)) := by
    intro n
    apply hA.A_weight_integrable.mono' (hA.psi_measurable n)
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.psi_bound n u
    · dsimp [weightedNorm]
      exact mul_nonneg (weight_nonneg u) (norm_nonneg _)
  have hphi_int : Integrable (weightedNorm φ) := by
    apply hA.A_weight_integrable.mono' hA.phi_measurable
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.phi_bound u
    · dsimp [weightedNorm]
      exact mul_nonneg (weight_nonneg u) (norm_nonneg _)
  have hdiff_bound : ∀ n u,
      ‖weightedDifference (ψ n) φ u‖ ≤ 2 * (weight u * A u) := by
    intro n u
    have hw : 0 ≤ weight u := weight_nonneg u
    have hnorm : ‖ψ n u - φ u‖ ≤ ‖ψ n u‖ + ‖φ u‖ := norm_sub_le _ _
    have hsum : weight u * ‖ψ n u‖ + weight u * ‖φ u‖ ≤
        2 * (weight u * A u) := by
      have h1 := hA.psi_bound n u
      have h2 := hA.phi_bound u
      dsimp [weightedNorm] at h1 h2
      nlinarith
    have hnon : 0 ≤ weightedDifference (ψ n) φ u := by
      dsimp [weightedDifference]
      exact mul_nonneg hw (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    dsimp [weightedDifference]
    calc
      weight u * ‖ψ n u - φ u‖ ≤
          weight u * (‖ψ n u‖ + ‖φ u‖) :=
        mul_le_mul_of_nonneg_left hnorm hw
      _ = weight u * ‖ψ n u‖ + weight u * ‖φ u‖ := by ring
      _ ≤ 2 * (weight u * A u) := hsum
  have hdiff_int : ∀ n, Integrable (weightedDifference (ψ n) φ) := by
    intro n
    apply hAint.mono' (hA.difference_measurable n)
    filter_upwards with u
    exact hdiff_bound n u
  have hzero : ∀ᵐ u : ℝ ∂volume,
      Tendsto (fun n => weightedDifference (ψ n) φ u) atTop (𝓝 0) := by
    filter_upwards with u
    have hu := hpoint u
    have hconst : Tendsto (fun _ : ℕ => φ u) atTop (𝓝 (φ u)) := tendsto_const_nhds
    have hn : Tendsto (fun n => ‖ψ n u - φ u‖) atTop (𝓝 0) := by
      have hsub := hu.sub hconst
      have hnorm := continuous_norm.continuousAt.tendsto.comp hsub
      simpa using hnorm
    have hw : Tendsto (fun _ : ℕ => weight u) atTop (𝓝 (weight u)) := tendsto_const_nhds
    have hmul := hw.mul hn
    simpa [weightedDifference] using hmul
  have hdist : Tendsto
      (fun n => weightedL1Distance (ψ n) φ) atTop (nhds 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun u : ℝ => 2 * (weight u * A u))
      (hA.difference_measurable) hAint (by
        intro n
        filter_upwards with u
        exact hdiff_bound n u) hzero
    simpa only [weightedL1Distance, integral_zero] using h
  refine ⟨hphi_int, hpsi_int, hdiff_int, hdist⟩

/-- The moment-factorization hypotheses required by the promoted endpoint are
consequences of one weighted second-moment integrability statement. -/
theorem moment_factorization_integrability_from_weighted
    (φ : ℝ → ℂ) (hφ : Integrable (weightedNorm φ))
    (hleft_meas : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2) (volume.prod volume))
    (hright_meas : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)) (volume.prod volume))
    (hcross_meas : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2))
      (volume.prod volume)) :
    Integrable (fun z : ℝ × ℝ =>
      ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2) (volume.prod volume) ∧
    Integrable (fun z : ℝ × ℝ =>
      φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)) (volume.prod volume) ∧
    Integrable (fun z : ℝ × ℝ =>
      (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2))
      (volume.prod volume) := by
  have hp := hφ.mul_prod hφ
  have hleft : Integrable (fun z : ℝ × ℝ =>
      ((((z.1 ^ 2) / 2 : ℝ) : ℂ) * φ z.1) * φ z.2) (volume.prod volume) := by
    apply hp.mono' hleft_meas
    filter_upwards with z
    have hu : 0 ≤ weight z.1 := weight_nonneg z.1
    have hv : 0 ≤ weight z.2 := weight_nonneg z.2
    have hq : (z.1 ^ 2) / 2 ≤ weight z.1 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.1]
    dsimp [weightedNorm]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (z.1 ^ 2) / 2)]
    have hn1 : 0 ≤ ‖φ z.1‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖φ z.2‖ := norm_nonneg _
    have hw1 : 1 ≤ weight z.1 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.1]
    have hw2 : 1 ≤ weight z.2 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.2]
    calc
      (z.1 ^ 2 / 2) * ‖φ z.1‖ * ‖φ z.2‖ ≤
          weight z.1 * ‖φ z.1‖ * ‖φ z.2‖ := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right hq hn1
            · exact hn2
      _ ≤ (weight z.1 * ‖φ z.1‖) * (weight z.2 * ‖φ z.2‖) := by
            apply mul_le_mul_of_nonneg_left
            · simpa using (mul_le_mul_of_nonneg_right hw2 hn2)
            · exact mul_nonneg (weight_nonneg _) hn1
  have hright : Integrable (fun z : ℝ × ℝ =>
      φ z.1 * ((((z.2 ^ 2) / 2 : ℝ) : ℂ) * φ z.2)) (volume.prod volume) := by
    apply hp.mono' hright_meas
    filter_upwards with z
    have hq : (z.2 ^ 2) / 2 ≤ weight z.2 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.2]
    dsimp [weightedNorm]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ (z.2 ^ 2) / 2)]
    have hn1 : 0 ≤ ‖φ z.1‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖φ z.2‖ := norm_nonneg _
    have hw1 : 1 ≤ weight z.1 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.1]
    have hw2 : 1 ≤ weight z.2 := by
      dsimp [weight]
      nlinarith [sq_nonneg z.2]
    apply le_trans
    · exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hq hn2) hn1
    · exact mul_le_mul_of_nonneg_right
        (by simpa using (mul_le_mul_of_nonneg_right hw1 hn1)) (mul_nonneg (weight_nonneg _) hn2)
  have hcross : Integrable (fun z : ℝ × ℝ =>
      (((z.1 : ℝ) : ℂ) * φ z.1) * (((z.2 : ℝ) : ℂ) * φ z.2))
      (volume.prod volume) := by
    apply hp.mono' hcross_meas
    filter_upwards with z
    dsimp [weightedNorm]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hu : |z.1| ≤ weight z.1 := by
      dsimp [weight]
      nlinarith [sq_nonneg (|z.1| - (1 / 2 : ℝ)), sq_abs z.1]
    have hv : |z.2| ≤ weight z.2 := by
      dsimp [weight]
      nlinarith [sq_nonneg (|z.2| - (1 / 2 : ℝ)), sq_abs z.2]
    have hn1 : 0 ≤ ‖φ z.1‖ := norm_nonneg _
    have hn2 : 0 ≤ ‖φ z.2‖ := norm_nonneg _
    exact le_trans
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hv hn2) (mul_nonneg (abs_nonneg _) hn1))
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hu hn1)
        (mul_nonneg (weight_nonneg _) hn2))
  exact ⟨hleft, hright, hcross⟩

lemma integrableCharFunUpToTwo_of_fullDomainEnvelope
    {ψ : ℕ → ℝ → ℂ} {ν : ProbabilityMeasure ℝ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ (charFun ν) A) :
    IntegrableCharFunUpToTwo (ν : Measure ℝ) := by
  have hweighted : Integrable (weightedNorm (charFun ν)) := by
    apply hA.A_weight_integrable.mono' hA.phi_measurable
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.phi_bound u
    · exact mul_nonneg (weight_nonneg u) (norm_nonneg _)
  intro k hk
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ k * charFun ν t) := by fun_prop
  apply hweighted.mono' hmeas
  filter_upwards with t
  rw [norm_mul, norm_pow, Complex.norm_real]
  dsimp [weightedNorm]
  have h0 : 1 ≤ weight t := by
    dsimp [weight]
    nlinarith [sq_nonneg t]
  have h1 : |t| ≤ weight t := by
    dsimp [weight]
    nlinarith [sq_nonneg (|t| - (1 / 2 : ℝ)), sq_abs t]
  have h2 : |t| ^ 2 ≤ weight t := by
    dsimp [weight]
    rw [sq_abs]
    linarith
  have habs : |t| ^ k ≤ weight t := by
    interval_cases k
    · simpa only [pow_zero] using h0
    · simpa only [pow_one] using h1
    · exact h2
  exact mul_le_mul_of_nonneg_right habs (norm_nonneg _)

/-- B.14 for the actual weak-limit law: the full-domain envelope alone supplies
the weighted characteristic-function hypotheses required by the generic
measure-level inversion theorem. -/
theorem probabilityFourierInversionUpToTwo_of_fullDomainEnvelope
    {ψ : ℕ → ℝ → ℂ} {ν : ProbabilityMeasure ℝ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ (charFun ν) A) :
    ProbabilityFourierInversionUpToTwo (ν : Measure ℝ) :=
  probabilityFourierInversionUpToTwo (ν : Measure ℝ)
    (integrableCharFunUpToTwo_of_fullDomainEnvelope hA)

lemma fourierDerivativeIdentities_inverseCharFun
    (ν : ProbabilityMeasure ℝ) (hφ : IntegrableCharFunUpToTwo (ν : Measure ℝ)) :
    FourierDerivativeIdentities
      (inverseCharFunDensity (ν : Measure ℝ))
      (fun x => (inverseCharFunDerivOne (ν : Measure ℝ) x).re)
      (fun x => (inverseCharFunDerivTwo (ν : Measure ℝ) x).re)
      (charFun ν) := by
  have hpack := probabilityFourierInversionUpToTwo (ν : Measure ℝ) hφ
  constructor
  · rw [hpack.density_eq_inverse]
    simp [inverseCharFun, inversePhase, moment0]
  constructor
  · rw [hpack.derivOne_formula]
    simp only [inversePhase, moment1]
    have hint :
        (∫ t : ℝ, (-Complex.I * (t : ℂ)) *
            Complex.exp (-Complex.I * (((t * 0 : ℝ) : ℂ))) * charFun ν t) =
          -Complex.I * ∫ t : ℝ, (t : ℂ) * charFun ν t := by
      calc
        _ = ∫ t : ℝ, -Complex.I * ((t : ℂ) * charFun ν t) := by
          apply integral_congr_ae
          filter_upwards with t
          simp
          ring
        _ = _ := MeasureTheory.integral_const_mul _ _
    rw [hint]
    change ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (-I * ∫ u : ℝ, (u : ℂ) * charFun ν u) =
      (1 / ((2 * Real.pi : ℝ) : ℂ)) *
        (-I * ∫ u : ℝ, (u : ℂ) * charFun ν u)
    rw [one_div]
  · rw [hpack.derivTwo_formula]
    simp only [inversePhase, moment2]
    have hint :
        (∫ t : ℝ, (-((t ^ 2 : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * (((t * 0 : ℝ) : ℂ))) * charFun ν t) =
          -(∫ t : ℝ, ((t ^ 2 : ℝ) : ℂ) * charFun ν t) := by
      calc
        _ = ∫ t : ℝ, -(((t ^ 2 : ℝ) : ℂ) * charFun ν t) := by
          apply integral_congr_ae
          filter_upwards with t
          simp
        _ = _ := MeasureTheory.integral_neg _
    rw [hint]
    change ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (-(∫ u : ℝ, ((u ^ 2 : ℝ) : ℂ) * charFun ν u)) =
      (1 / ((2 * Real.pi : ℝ) : ℂ)) *
        (-(∫ u : ℝ, ((u ^ 2 : ℝ) : ℂ) * charFun ν u))
    rw [one_div]

/-- The actual B.14 package: the inverse characteristic-function density has
the displayed first two Fourier derivatives, and these functions really are
its first and second derivatives. -/
theorem twiceDifferentiableFourierDensity_inverseCharFun
    (ν : ProbabilityMeasure ℝ) (hφ : IntegrableCharFunUpToTwo (ν : Measure ℝ)) :
    TwiceDifferentiableFourierDensity
      (inverseCharFunDensity (ν : Measure ℝ))
      (fun x => (inverseCharFunDerivOne (ν : Measure ℝ) x).re)
      (fun x => (inverseCharFunDerivTwo (ν : Measure ℝ) x).re)
      (charFun ν) := by
  have hpack := probabilityFourierInversionUpToTwo (ν : Measure ℝ) hφ
  exact ⟨⟨hpack.hasDeriv_density, hpack.hasDeriv_derivOne⟩,
    fourierDerivativeIdentities_inverseCharFun ν hφ⟩

/-- Full B.14 for a canonical weak-limit law, derived solely from the
full-domain envelope. -/
theorem twiceDifferentiableFourierDensity_of_fullDomainEnvelope
    {ψ : ℕ → ℝ → ℂ} {ν : ProbabilityMeasure ℝ} {A : ℝ → ℝ}
    (hA : FullDomainEnvelope ψ (charFun ν) A) :
    TwiceDifferentiableFourierDensity
      (inverseCharFunDensity (ν : Measure ℝ))
      (fun x => (inverseCharFunDerivOne (ν : Measure ℝ) x).re)
      (fun x => (inverseCharFunDerivTwo (ν : Measure ℝ) x).re)
      (charFun ν) :=
  twiceDifferentiableFourierDensity_inverseCharFun ν
    (integrableCharFunUpToTwo_of_fullDomainEnvelope hA)


lemma integrable_of_weighted {g : ℝ → ℂ}
    (hg : Integrable (weightedNorm g))
    (hgm : StronglyMeasurable g) : Integrable g := by
  apply hg.mono' hgm.aestronglyMeasurable
  filter_upwards with u
  dsimp [weightedNorm]
  have hw : 1 ≤ weight u := by
    dsimp [weight]
    nlinarith [sq_nonneg u]
  exact le_mul_of_one_le_left (norm_nonneg _) hw

lemma b16_integrability_of_weighted (V : ℝ) (g : ℝ → ℂ)
    (hg : Integrable (weightedNorm g))
    (hgm : StronglyMeasurable g) :
    Integrable (fun z : ℝ × ℝ => (V : ℂ) * (g z.1 * g z.2))
        (volume.prod volume) ∧
    Integrable (fun z : ℝ × ℝ =>
      (V : ℂ) *
        ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * g z.1) *
         (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * g z.2)))
        (volume.prod volume) ∧
    Integrable (imaginarySineIntegrand V g) (volume.prod volume) := by
  have hg0 : Integrable g := integrable_of_weighted hg hgm
  have hp : Integrable (fun z : ℝ × ℝ => g z.1 * g z.2)
      (volume.prod volume) := hg0.mul_prod hg0
  have hmajor : Integrable (fun z : ℝ × ℝ =>
      ‖(V : ℂ)‖ * (‖g z.1‖ * ‖g z.2‖)) (volume.prod volume) := by
    have hnorm : Integrable (fun x : ℝ => ‖g x‖) := hg0.norm
    exact (hnorm.mul_prod hnorm).const_mul ‖(V : ℂ)‖
  have hphase_meas : StronglyMeasurable (fun z : ℝ × ℝ =>
      (V : ℂ) *
        ((Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ)) * g z.1) *
         (Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ)) * g z.2))) := by
    apply StronglyMeasurable.const_mul
    apply StronglyMeasurable.mul
    · apply StronglyMeasurable.mul
      · fun_prop
      · exact hgm.comp_measurable measurable_fst
    · apply StronglyMeasurable.mul
      · fun_prop
      · exact hgm.comp_measurable measurable_snd
  have hsine_meas : StronglyMeasurable (imaginarySineIntegrand V g) := by
    apply StronglyMeasurable.const_mul
    apply StronglyMeasurable.mul
    · fun_prop
    · exact (hgm.comp_measurable measurable_fst).mul
        (hgm.comp_measurable measurable_snd)
  constructor
  · exact hp.const_mul (V : ℂ)
  constructor
  · apply hmajor.mono' hphase_meas.aestronglyMeasurable
    filter_upwards with z
    have hnorm1 :
        ‖Complex.exp (Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ))‖ = 1 := by
      rw [show Complex.I * ((z.1 / Real.sqrt V : ℝ) : ℂ) =
          ((z.1 / Real.sqrt V : ℝ) : ℂ) * Complex.I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hnorm2 :
        ‖Complex.exp (-Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ))‖ = 1 := by
      rw [show -Complex.I * ((z.2 / Real.sqrt V : ℝ) : ℂ) =
          ((-(z.2 / Real.sqrt V) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp only [norm_mul, hnorm1, hnorm2, one_mul]
    exact le_rfl
  · apply hmajor.mono' hsine_meas.aestronglyMeasurable
    filter_upwards with z
    dsimp [imaginarySineIntegrand]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have hs : |Real.sin ((z.1 - z.2) / Real.sqrt V)| ≤ 1 := abs_sin_le_one _
    have hq : 0 ≤ ‖g z.1‖ * ‖g z.2‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    rw [norm_mul]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hq)
      (abs_nonneg V)

lemma zeroExtendedCharacteristic_tendsto
    (S : CanonicalSequence) {ν : ProbabilityMeasure ℝ} {subseq : ℕ → ℕ}
    (hsubseq : StrictMono subseq)
    (hchar : ∀ u : ℝ, Tendsto (fun n => S.characteristic (subseq n) u) atTop
      (𝓝 (charFun ν u))) :
    ∀ u : ℝ, Tendsto (fun n => S.zeroExtendedCharacteristic (subseq n) u) atTop
      (𝓝 (charFun ν u)) := by
  intro u
  apply (hchar u).congr'
  have hevent := (hsubseq.tendsto_atTop.eventually (S.eventually_mem_domain u))
  filter_upwards [hevent] with n hn
  simp [zeroExtendedCharacteristic, hn]

/-- Actual canonical-limit adapter: the envelope supplies all weighted and
measure-inversion hypotheses, while finite inversion and variance growth come
from `CanonicalSequence`. -/
theorem fourier_turan_curvature_limit_of_fullDomainEnvelope
    (S : CanonicalSequence) (ν : ProbabilityMeasure ℝ) (subseq : ℕ → ℕ) (A : ℝ → ℝ)
    (hsubseq : StrictMono subseq)
    (hweak : Tendsto (S.standardizedLaw ∘ subseq) atTop (𝓝 ν))
    (hA : FullDomainEnvelope
      (fun n => S.zeroExtendedCharacteristic (subseq n)) (charFun ν) A) :
    Tendsto
      (fun n => (S.V (subseq n)) ^ 2 *
        ((S.centeredMass (subseq n) 0) ^ 2 -
          S.centeredMass (subseq n) (-1) * S.centeredMass (subseq n) 1))
      atTop
      (𝓝 (((fun x => (inverseCharFunDerivOne (ν : Measure ℝ) x).re) 0) ^ 2 -
        inverseCharFunDensity (ν : Measure ℝ) 0 *
          (fun x => (inverseCharFunDerivTwo (ν : Measure ℝ) x).re) 0)) := by
  let ψ : ℕ → ℝ → ℂ := fun n => S.zeroExtendedCharacteristic (subseq n)
  let φ : ℝ → ℂ := charFun ν
  let f : ℝ → ℝ := inverseCharFunDensity (ν : Measure ℝ)
  let f' : ℝ → ℝ := fun x => (inverseCharFunDerivOne (ν : Measure ℝ) x).re
  let f'' : ℝ → ℝ := fun x => (inverseCharFunDerivTwo (ν : Measure ℝ) x).re
  have hchar : ∀ u : ℝ, Tendsto (fun n => S.characteristic (subseq n) u) atTop
      (𝓝 (charFun ν u)) := by
    intro u
    have hchars := (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hweak u
    simpa [CanonicalSequence.characteristic, Function.comp_def] using hchars
  have hpoint : ∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 (φ u)) := by
    exact zeroExtendedCharacteristic_tendsto S hsubseq hchar
  have hweighted : WeightedL1Convergence ψ φ :=
    weightedL1_of_fullDomainEnvelope hA hpoint
  have hB14 : TwiceDifferentiableFourierDensity f f' f'' φ := by
    exact twiceDifferentiableFourierDensity_of_fullDomainEnvelope hA
  have hdensity : FourierDerivativeIdentities f f' f'' φ := hB14.2
  have hV : Tendsto (fun n => S.V (subseq n)) atTop atTop := by
    exact S.variance_tendsto.comp hsubseq.tendsto_atTop
  have hVpos : ∀ n, 0 < S.V (subseq n) := fun n => S.variance_pos (subseq n)
  have hInv : ∀ n, LatticeFourierInversion (S.V (subseq n))
      (S.centeredMass (subseq n)) (ψ n) := by
    intro n
    exact S.actual_lattice_fourier_inversion (subseq n)
  have hψstrong : ∀ n, StronglyMeasurable (ψ n) := by
    intro n
    dsimp [ψ, zeroExtendedCharacteristic]
    exact (continuous_charFun (μ := (S.standardizedLaw (subseq n) : Measure ℝ))).stronglyMeasurable.indicator
      measurableSet_Icc
  have hψmeas : ∀ n, AEStronglyMeasurable (ψ n) := by
    intro n
    exact (hψstrong n).aestronglyMeasurable
  have hφstrong : StronglyMeasurable φ := by
    dsimp [φ]
    exact continuous_charFun.stronglyMeasurable
  have hφmeas : AEStronglyMeasurable φ := hφstrong.aestronglyMeasurable
  have hmeasψ : ∀ n, AEStronglyMeasurable
      (curvatureIntegrand (S.V (subseq n)) (ψ n)) (volume.prod volume) := by
    intro n
    change AEStronglyMeasurable (fun z : ℝ × ℝ =>
      (kernel (S.V (subseq n)) z.1 z.2 : ℂ) * (ψ n z.1 * ψ n z.2))
      (volume.prod volume)
    apply StronglyMeasurable.aestronglyMeasurable
    have hk : StronglyMeasurable (fun z : ℝ × ℝ =>
        (kernel (S.V (subseq n)) z.1 z.2 : ℂ)) := by
      apply Continuous.stronglyMeasurable
      unfold kernel
      fun_prop
    exact hk.mul ((hψstrong n).comp_measurable measurable_fst |>.mul
        ((hψstrong n).comp_measurable measurable_snd))
  have hmeasφ : ∀ n, AEStronglyMeasurable
      (curvatureIntegrand (S.V (subseq n)) φ) (volume.prod volume) := by
    intro n
    change AEStronglyMeasurable (fun z : ℝ × ℝ =>
      (kernel (S.V (subseq n)) z.1 z.2 : ℂ) * (φ z.1 * φ z.2))
      (volume.prod volume)
    apply StronglyMeasurable.aestronglyMeasurable
    have hk : StronglyMeasurable (fun z : ℝ × ℝ =>
        (kernel (S.V (subseq n)) z.1 z.2 : ℂ)) := by
      apply Continuous.stronglyMeasurable
      unfold kernel
      fun_prop
    exact hk.mul (hφstrong.comp_measurable measurable_fst |>.mul
        (hφstrong.comp_measurable measurable_snd))
  have hfinite : ∀ n,
      Integrable (fun z : ℝ × ℝ => ((S.V (subseq n) : ℝ) : ℂ) *
          (ψ n z.1 * ψ n z.2)) (volume.prod volume) ∧
      Integrable (fun z : ℝ × ℝ =>
        ((S.V (subseq n) : ℝ) : ℂ) *
          ((Complex.exp (Complex.I *
              ((z.1 / Real.sqrt (S.V (subseq n)) : ℝ) : ℂ)) * ψ n z.1) *
           (Complex.exp (-Complex.I *
              ((z.2 / Real.sqrt (S.V (subseq n)) : ℝ) : ℂ)) * ψ n z.2)))
          (volume.prod volume) ∧
      Integrable (imaginarySineIntegrand (S.V (subseq n)) (ψ n))
        (volume.prod volume) := by
    intro n
    exact b16_integrability_of_weighted _ _
      (hweighted.psi_integrable n) (hψstrong n)
  have hmoments := moment_factorization_integrability_from_weighted φ
    hweighted.phi_integrable (by fun_prop) (by fun_prop) (by fun_prop)
  exact fourier_turan_curvature_limit
    (fun n => S.V (subseq n))
    (fun n => S.centeredMass (subseq n)) ψ φ f f' f'' hV hVpos hInv
    hweighted hmeasψ hmeasφ (fun n => (hfinite n).1)
    (fun n => (hfinite n).2.1) (fun n => (hfinite n).2.2)
    hmoments.1 hmoments.2.1 hmoments.2.2 hdensity


theorem integral_tendsto_of_weightedL1
    {ψ : ℕ → ℝ → ℂ} {φ : ℝ → ℂ}
    (hweighted : WeightedL1Convergence ψ φ)
    (hψstrong : ∀ n, StronglyMeasurable (ψ n))
    (hφstrong : StronglyMeasurable φ) :
    Tendsto (fun n => ∫ u : ℝ, ψ n u) atTop (𝓝 (∫ u : ℝ, φ u)) := by
  have hψint : ∀ n, Integrable (ψ n) := by
    intro n
    exact integrable_of_weighted (hweighted.psi_integrable n) (hψstrong n)
  have hφint : Integrable φ :=
    integrable_of_weighted hweighted.phi_integrable hφstrong
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hweighted.tendsto_distance
  · exact Eventually.of_forall fun n => norm_nonneg _
  · exact Eventually.of_forall fun n => by
      rw [← integral_sub (hψint n) hφint]
      calc
        ‖∫ u : ℝ, ψ n u - φ u‖ ≤ ∫ u : ℝ, ‖ψ n u - φ u‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ u : ℝ, weightedDifference (ψ n) φ u := by
          apply integral_mono_of_nonneg
          · exact Eventually.of_forall fun u => norm_nonneg (ψ n u - φ u)
          · exact hweighted.difference_integrable n
          · filter_upwards with u
            dsimp [weightedDifference, weight]
            have hn := norm_nonneg (ψ n u - φ u)
            nlinarith [sq_nonneg u]
        _ = weightedL1Distance (ψ n) φ := rfl

 theorem centeredMass_zero_scaled_tendsto_D40
    (S : CanonicalSequence) (ν : ProbabilityMeasure ℝ)
    (subseq : ℕ → ℕ) (A : ℝ → ℝ)
    (hsubseq : StrictMono subseq)
    (hweak : Tendsto (S.standardizedLaw ∘ subseq) atTop (𝓝 ν))
    (hA : FullDomainEnvelope
      (fun n => S.zeroExtendedCharacteristic (subseq n)) (charFun ν) A) :
    Tendsto (fun n => Real.sqrt (S.V (subseq n)) *
      S.centeredMass (subseq n) 0) atTop
      (𝓝 (inverseCharFunDensity (ν : Measure ℝ) 0)) := by
  let ψ : ℕ → ℝ → ℂ := fun n => S.zeroExtendedCharacteristic (subseq n)
  let φ : ℝ → ℂ := charFun ν
  have hchar : ∀ u : ℝ, Tendsto (fun n => S.characteristic (subseq n) u) atTop
      (𝓝 (charFun ν u)) := by
    intro u
    have hchars := (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hweak u
    simpa [CanonicalSequence.characteristic, Function.comp_def] using hchars
  have hpoint : ∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 (φ u)) :=
    zeroExtendedCharacteristic_tendsto S hsubseq hchar
  have hweighted : WeightedL1Convergence ψ φ :=
    weightedL1_of_fullDomainEnvelope hA hpoint
  have hψstrong : ∀ n, StronglyMeasurable (ψ n) := by
    intro n
    dsimp [ψ, zeroExtendedCharacteristic]
    exact (continuous_charFun (μ := (S.standardizedLaw (subseq n) : Measure ℝ))).stronglyMeasurable.indicator
      measurableSet_Icc
  have hφstrong : StronglyMeasurable φ := by
    dsimp [φ]
    exact continuous_charFun.stronglyMeasurable
  have hint : Tendsto (fun n => ∫ u : ℝ, ψ n u) atTop (𝓝 (∫ u : ℝ, φ u)) :=
    integral_tendsto_of_weightedL1 hweighted hψstrong hφstrong
  have hscaled : ∀ n,
      ((Real.sqrt (S.V (subseq n)) * S.centeredMass (subseq n) 0 : ℝ) : ℂ) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, ψ n u) := by
    intro n
    have hinv := probability_eq_fourier_integral
      (S.actual_lattice_fourier_inversion (subseq n)) 0
    simp only [phase, Int.cast_zero, mul_zero, zero_div, ofReal_zero,
      Complex.exp_zero, one_mul] at hinv
    have hs : Real.sqrt (S.V (subseq n)) ≠ 0 :=
      (Real.sqrt_pos.2 (S.variance_pos (subseq n))).ne'
    calc
      ((Real.sqrt (S.V (subseq n)) * S.centeredMass (subseq n) 0 : ℝ) : ℂ) =
          (Real.sqrt (S.V (subseq n)) : ℂ) *
            (S.centeredMass (subseq n) 0 : ℂ) := by push_cast; ring
      _ = (Real.sqrt (S.V (subseq n)) : ℂ) *
          ((1 / ((2 * Real.pi * Real.sqrt (S.V (subseq n)) : ℝ) : ℂ)) *
            ∫ u : ℝ, ψ n u) := by rw [hinv]
      _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, ψ n u) := by
        field_simp [hs, Real.pi_ne_zero] <;> push_cast <;> ring
  have hcomplex : Tendsto (fun n =>
      (((Real.sqrt (S.V (subseq n)) * S.centeredMass (subseq n) 0 : ℝ) : ℂ)))
      atTop (𝓝 ((inverseCharFunDensity (ν : Measure ℝ) 0 : ℝ) : ℂ)) := by
    have hmul : Tendsto
        (fun n => (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, ψ n u)) atTop
        (𝓝 (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, φ u)) :=
      tendsto_const_nhds.mul hint
    have hphi : (((2 * Real.pi : ℝ) : ℂ)⁻¹ * ∫ u : ℝ, φ u) =
        ((inverseCharFunDensity (ν : Measure ℝ) 0 : ℝ) : ℂ) := by
      rw [coe_inverseCharFunDensity ν
        (integrable_charFun_of_upToTwo
          (integrableCharFunUpToTwo_of_fullDomainEnvelope hA)) 0]
      simp [inverseCharFun, inversePhase, φ]
    have hc := hmul.congr'
      (Eventually.of_forall fun n => (hscaled n).symm)
    rw [hphi] at hc
    exact hc
  have hre := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
  simpa [Function.comp_def] using hre


end CanonicalSequence
end

end Erdos993.Forest.CanonicalCompactnessWrapper
