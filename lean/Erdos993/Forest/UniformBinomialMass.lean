import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Uniform lower bound for a binomial atom

This file formalizes manuscript Lemma C.6.  The shifted-binomial atom is kept as
an explicit formula, so the statement does not depend on the still-incomplete
measure-level binomial singleton API.
-/

namespace Erdos993
namespace Forest
namespace UniformBinomialMass

noncomputable section

/-- The real probability mass of `Bin(a, θ)` at the natural rank `k`. -/
def binomialMass (a k : ℕ) (θ : ℝ) : ℝ :=
  (a.choose k : ℝ) * θ ^ k * (1 - θ) ^ (a - k)

/-- The atom at `s` of the shifted law `K + Bin(a, θ)`.  Outside the natural
support `K ≤ s ≤ K+a` it is zero. -/
def shiftedBinomialMass (a : ℕ) (K s : ℤ) (θ : ℝ) : ℝ :=
  if 0 ≤ s - K ∧ s - K ≤ (a : ℤ) then
    binomialMass a (s - K).toNat θ
  else 0

/-- Bernoulli relative entropy `D(r || θ)`. -/
def bernoulliRelativeEntropy (r θ : ℝ) : ℝ :=
  r * Real.log (r / θ) + (1 - r) * Real.log ((1 - r) / (1 - θ))

/-- The lower half of the finite Stirling estimate used in (C.52). -/
theorem finiteStirling_lower (n : ℕ) :
    Real.sqrt (2 * Real.pi * (n : ℝ)) *
        ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  simpa [mul_assoc] using Stirling.le_factorial_stirling n

/-- The upper half of the finite Stirling estimate used in (C.52).
It follows from monotonicity of the effective Stirling sequence. -/
theorem finiteStirling_upper (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤
      Real.exp 1 * Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  suffices (((m + 1).factorial : ℕ) : ℝ) ≤
      Real.exp 1 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
        (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) by
    simpa [Nat.add_comm] using this
  have hmono : Stirling.stirlingSeq (m + 1) ≤ Stirling.stirlingSeq 1 := by
    simpa [Function.comp_def] using Stirling.stirlingSeq'_antitone (Nat.zero_le m)
  rw [Stirling.stirlingSeq_one, Stirling.stirlingSeq] at hmono
  have h : (((m + 1).factorial : ℕ) : ℝ) ≤
      (Real.exp 1 / Real.sqrt 2) *
        (Real.sqrt (2 * (((m + 1 : ℕ) : ℝ))) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) :=
    (div_le_iff₀ (by positivity)).mp hmono
  calc
    (((m + 1).factorial : ℕ) : ℝ) ≤
        (Real.exp 1 / Real.sqrt 2) *
          (Real.sqrt (2 * (m + 1 : ℝ)) *
            (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1)) := by
      simpa using h
    _ = Real.exp 1 * Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
      have hs : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      field_simp
      norm_cast

/-- The manuscript's hypotheses force a positive trial count and put the real
rank `(s-K)/a` in the fixed compact interval from Lemma C.6. -/
theorem interior_rank_bounds
    (a : ℕ) (K s : ℤ) (θ H M W : ℝ)
    (hθlo : (3 : ℝ) / 5 ≤ θ) (hθhi : θ ≤ (27 : ℝ) / 28)
    (hH : 1 ≤ H) (hM : M = (K : ℝ) + (a : ℝ) * θ)
    (hW : W = (a : ℝ) * θ * (1 - θ))
    (hWH : 4 * H ≤ W) (hclose : (M - (s : ℝ)) ^ 2 ≤ H * W) :
    1 ≤ a ∧
      (12 : ℝ) / 25 ≤ ((s - K : ℤ) : ℝ) / (a : ℝ) ∧
      ((s - K : ℤ) : ℝ) / (a : ℝ) ≤ (1539 : ℝ) / 1568 := by
  have hθpos : 0 < θ := by linarith
  have hθlt : θ < 1 := by norm_num at hθhi ⊢; linarith
  have hWpos : 0 < W := by nlinarith
  have ha : 1 ≤ a := by
    by_contra h
    have ha0 : a = 0 := by omega
    subst a
    simp at hW
    linarith
  have hacast : 0 < (a : ℝ) := by exact_mod_cast ha
  let x : ℝ := ((s - K : ℤ) : ℝ)
  have hd : x - (a : ℝ) * θ = (s : ℝ) - M := by
    dsimp [x]
    rw [hM]
    push_cast
    ring
  have hd_sq : (x - (a : ℝ) * θ) ^ 2 ≤ H * W := by
    rw [hd]
    nlinarith [hclose]
  have hHW : H * W ≤ W ^ 2 / 4 := by nlinarith
  have hd_sq' : (x - (a : ℝ) * θ) ^ 2 ≤ (W / 2) ^ 2 := by
    nlinarith
  have hdlo : -(W / 2) ≤ x - (a : ℝ) * θ := by nlinarith [sq_nonneg (x - (a : ℝ) * θ + W / 2)]
  have hdhi : x - (a : ℝ) * θ ≤ W / 2 := by nlinarith [sq_nonneg (x - (a : ℝ) * θ - W / 2)]
  have hlowpoly : (12 : ℝ) / 25 ≤ θ - θ * (1 - θ) / 2 := by
    have hp : 0 ≤ (θ - (3 : ℝ) / 5) * (θ + (8 : ℝ) / 5) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hhighpoly : θ + θ * (1 - θ) / 2 ≤ (1539 : ℝ) / 1568 := by
    have hp : 0 ≤ ((27 : ℝ) / 28 - θ) * ((29 : ℝ) / 28 - θ) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hxlo : (a : ℝ) * ((12 : ℝ) / 25) ≤ x := by
    rw [hW] at hdlo
    have := mul_le_mul_of_nonneg_left hlowpoly (le_of_lt hacast)
    nlinarith
  have hxhi : x ≤ (a : ℝ) * ((1539 : ℝ) / 1568) := by
    rw [hW] at hdhi
    have := mul_le_mul_of_nonneg_left hhighpoly (le_of_lt hacast)
    nlinarith
  dsimp [x] at hxlo hxhi
  refine ⟨ha, ?_, ?_⟩
  · exact (le_div_iff₀ hacast).2 (by simpa [mul_comm] using hxlo)
  · exact (div_le_iff₀ hacast).2 (by simpa [mul_comm] using hxhi)

/-- The elementary `log u ≤ u-1` inequality gives a global quadratic upper
bound for Bernoulli relative entropy. -/
theorem relativeEntropy_le_chiSquare
    {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    bernoulliRelativeEntropy r θ ≤ (r - θ) ^ 2 / (θ * (1 - θ)) := by
  have hfirst := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hr0 hθ0)) (le_of_lt hr0)
  have hsecond := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos (sub_pos.mpr hr1) (sub_pos.mpr hθ1)))
    (sub_nonneg.mpr (le_of_lt hr1))
  dsimp [bernoulliRelativeEntropy]
  calc
    r * Real.log (r / θ) + (1 - r) * Real.log ((1 - r) / (1 - θ)) ≤
        r * (r / θ - 1) + (1 - r) * ((1 - r) / (1 - θ) - 1) :=
      add_le_add hfirst hsecond
    _ = (r - θ) ^ 2 / (θ * (1 - θ)) := by
      field_simp [ne_of_gt hθ0, ne_of_gt (sub_pos.mpr hθ1)]
      ring

/-- On the fixed intervals in C.6, the rank variance and binomial variance are
uniformly comparable.  The explicit factors `8` and `30` are deliberately
coarse universal constants. -/
theorem variance_comparison
    (a : ℕ) {r θ W : ℝ}
    (hθlo : (3 : ℝ) / 5 ≤ θ) (hθhi : θ ≤ (27 : ℝ) / 28)
    (hrlo : (12 : ℝ) / 25 ≤ r) (hrhi : r ≤ (1539 : ℝ) / 1568)
    (hW : W = (a : ℝ) * θ * (1 - θ)) :
    (a : ℝ) * r * (1 - r) ≤ 8 * W ∧
      W ≤ 30 * ((a : ℝ) * r * (1 - r)) := by
  have hθpos : 0 < θ := by linarith
  have hθlt : θ < 1 := by norm_num at hθhi ⊢; linarith
  have hrpos : 0 < r := by linarith
  have hrlt : r < 1 := by norm_num at hrhi ⊢; linarith
  have hθmin : (1 : ℝ) / 32 ≤ θ * (1 - θ) := by
    have hp : 0 ≤ ((27 : ℝ) / 28 - θ) * (θ - (1 : ℝ) / 28) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hθmax : θ * (1 - θ) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (θ - (1 : ℝ) / 2)]
  have hrmax : r * (1 - r) ≤ (1 : ℝ) / 4 := by
    nlinarith [sq_nonneg (r - (1 : ℝ) / 2)]
  have hrmin : (1 : ℝ) / 120 ≤ r * (1 - r) := by
    have h1mr : (29 : ℝ) / 1568 ≤ 1 - r := by linarith
    have hp := mul_le_mul hrlo h1mr (by positivity) (le_of_lt hrpos)
    norm_num at hp ⊢
    nlinarith
  have ha0 : 0 ≤ (a : ℝ) := by positivity
  constructor
  · rw [hW]
    have := mul_le_mul_of_nonneg_left (show r * (1 - r) ≤ 8 * (θ * (1 - θ)) by nlinarith)
      ha0
    nlinarith
  · rw [hW]
    have := mul_le_mul_of_nonneg_left (show θ * (1 - θ) ≤ 30 * (r * (1 - r)) by nlinarith)
      ha0
    nlinarith

/-- Casted factorial quotient for the binomial coefficient. -/
theorem choose_eq_factorial_ratio {a k : ℕ} (hk : k ≤ a) :
    (a.choose k : ℝ) =
      (a.factorial : ℝ) / ((k.factorial : ℝ) * ((a - k).factorial : ℝ)) := by
  have hmul :
      (a.choose k : ℝ) * (k.factorial : ℝ) * ((a - k).factorial : ℝ) =
        (a.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  apply (eq_div_iff (by positivity : (k.factorial : ℝ) * ((a-k).factorial : ℝ) ≠ 0)).2
  simpa [mul_assoc] using hmul

/-- The elementary likelihood-ratio factor is the exponential of minus the
Bernoulli relative entropy. -/
theorem likelihoodRatio_eq_exp_neg_entropy
    (a k : ℕ) (hkpos : 1 ≤ k) (hklt : k < a) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let r := (k : ℝ) / (a : ℝ)
    (θ / r) ^ k * ((1 - θ) / (1 - r)) ^ (a - k) =
      Real.exp (-(a : ℝ) * bernoulliRelativeEntropy r θ) := by
  let A : ℝ := a
  let K : ℝ := k
  let J : ℝ := ((a - k : ℕ) : ℝ)
  let r : ℝ := K / A
  have hka : k ≤ a := Nat.le_of_lt hklt
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) (Nat.le_of_lt hklt))
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hkpos
  have hJ : 0 < J := by
    change 0 < (((a - k : ℕ) : ℝ))
    exact_mod_cast Nat.sub_pos_of_lt hklt
  have hr : 0 < r := div_pos hK hA
  have hr1 : r < 1 := (div_lt_one₀ hA).2 (by
    change (k : ℝ) < (a : ℝ)
    exact_mod_cast hklt)
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  have hKr : A * r = K := by
    dsimp [r]
    field_simp
  have hKJ : K + J = A := by
    dsimp [K, J, A]
    rw [Nat.cast_sub hka]
    ring
  have hJr : A * (1 - r) = J := by nlinarith
  have hp1 : (θ / r) ^ k = Real.exp (K * Real.log (θ / r)) := by
    dsimp [K]
    rw [Real.exp_nat_mul, Real.exp_log (div_pos hθ0 hr)]
  have hp2 : ((1 - θ) / (1 - r)) ^ (a - k) =
      Real.exp (J * Real.log ((1 - θ) / (1 - r))) := by
    dsimp [J]
    rw [Real.exp_nat_mul, Real.exp_log (div_pos h1θ h1r)]
  dsimp only
  change (θ / r) ^ k * ((1 - θ) / (1 - r)) ^ (a - k) = _
  rw [hp1, hp2, ← Real.exp_add]
  congr 1
  dsimp [bernoulliRelativeEntropy]
  rw [Real.log_div hθ0.ne' hr.ne', Real.log_div h1θ.ne' h1r.ne',
    Real.log_div hr.ne' hθ0.ne', Real.log_div h1r.ne' h1θ.ne']
  rw [← hKr, ← hJr]
  ring

/-- Algebraic normalization of the powers occurring after Stirling's bounds. -/
theorem stirlingPowerRatio_eq_likelihoodRatio
    (a k : ℕ) (hkpos : 1 ≤ k) (hklt : k < a) (θ : ℝ) :
    let r := (k : ℝ) / (a : ℝ)
    ((a : ℝ) / Real.exp 1) ^ a /
          (((k : ℝ) / Real.exp 1) ^ k *
            (((a - k : ℕ) : ℝ) / Real.exp 1) ^ (a - k)) *
        θ ^ k * (1 - θ) ^ (a - k) =
      (θ / r) ^ k * ((1 - θ) / (1 - r)) ^ (a - k) := by
  let A : ℝ := a
  let K : ℝ := k
  let J : ℝ := ((a - k : ℕ) : ℝ)
  let r : ℝ := K / A
  have hka : k ≤ a := Nat.le_of_lt hklt
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) (Nat.le_of_lt hklt))
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hkpos
  have hJ : 0 < J := by
    change 0 < (((a - k : ℕ) : ℝ))
    exact_mod_cast Nat.sub_pos_of_lt hklt
  have he : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
  have hsum : k + (a - k) = a := Nat.add_sub_of_le hka
  have hKJ : K + J = A := by
    dsimp [K, J, A]
    rw [Nat.cast_sub hka]
    ring
  have hr : r = K / A := rfl
  have h1r : 1 - r = J / A := by
    rw [hr]
    field_simp
    linarith
  have hbase1 : (A / Real.exp 1) / (K / Real.exp 1) * θ = θ / (K / A) := by
    field_simp [he, hA.ne', hK.ne']
  have hbase2 : (A / Real.exp 1) / (J / Real.exp 1) * (1 - θ) =
      (1 - θ) / (J / A) := by
    field_simp [he, hA.ne', hJ.ne']
  dsimp only
  change (A / Real.exp 1) ^ a /
          ((K / Real.exp 1) ^ k * (J / Real.exp 1) ^ (a - k)) *
        θ ^ k * (1 - θ) ^ (a - k) =
      (θ / r) ^ k * ((1 - θ) / (1 - r)) ^ (a - k)
  calc
    _ = (((A / Real.exp 1) / (K / Real.exp 1)) * θ) ^ k *
        (((A / Real.exp 1) / (J / Real.exp 1)) * (1 - θ)) ^ (a - k) := by
      rw [← hsum, pow_add]
      simp only [Nat.add_sub_cancel_left, mul_pow, div_pow]
      ring
    _ = _ := by rw [hbase1, hbase2, ← hr, ← h1r]

/-- The square-root prefactor in Stirling's formula is exactly the reciprocal
square root of `a r (1-r)`. -/
theorem sqrtRatio_eq_inv_sqrt_rankVariance
    (a k : ℕ) (hkpos : 1 ≤ k) (hklt : k < a) :
    let r := (k : ℝ) / (a : ℝ)
    Real.sqrt (a : ℝ) /
        (Real.sqrt (k : ℝ) * Real.sqrt ((a - k : ℕ) : ℝ)) =
      1 / Real.sqrt ((a : ℝ) * r * (1 - r)) := by
  let A : ℝ := a
  let K : ℝ := k
  let J : ℝ := ((a - k : ℕ) : ℝ)
  let r : ℝ := K / A
  have hka : k ≤ a := Nat.le_of_lt hklt
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) (Nat.le_of_lt hklt))
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hkpos
  have hJ : 0 < J := by
    change 0 < (((a - k : ℕ) : ℝ))
    exact_mod_cast Nat.sub_pos_of_lt hklt
  have hKJ : K + J = A := by
    dsimp [K, J, A]
    rw [Nat.cast_sub hka]
    ring
  have hKr : A * r = K := by
    dsimp [r]
    field_simp
  have hJr : A * (1 - r) = J := by nlinarith
  have hvar : A * r * (1 - r) = K * J / A := by
    rw [hKr]
    rw [show 1 - r = J / A by apply (eq_div_iff hA.ne').2; simpa [mul_comm] using hJr]
    ring
  dsimp only
  change Real.sqrt A / (Real.sqrt K * Real.sqrt J) =
    1 / Real.sqrt (A * r * (1 - r))
  rw [hvar, Real.sqrt_div (mul_nonneg hK.le hJ.le), Real.sqrt_mul hK.le]
  field_simp [Real.sqrt_ne_zero'.2 hA, Real.sqrt_ne_zero'.2 hK,
    Real.sqrt_ne_zero'.2 hJ]

/-- A slightly weakened form of the lower Stirling estimate with the universal
factor `sqrt (2π)` discarded. -/
theorem finiteStirling_lower_simple (n : ℕ) :
    Real.sqrt (n : ℝ) * ((n : ℝ) / Real.exp 1) ^ n ≤ (n.factorial : ℝ) := by
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.two_le_pi]
  have harg : (n : ℝ) ≤ 2 * Real.pi * (n : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hsqrt : Real.sqrt (n : ℝ) ≤ Real.sqrt (2 * Real.pi * (n : ℝ)) :=
    Real.sqrt_le_sqrt harg
  have hpow : 0 ≤ ((n : ℝ) / Real.exp 1) ^ n := by positivity
  exact (mul_le_mul_of_nonneg_right hsqrt hpow).trans (finiteStirling_lower n)

/-- Finite Stirling plus the likelihood-ratio identity.  This is the quantitative
point-mass estimate (C.52), with the explicit universal prefactor `exp(1)⁻²`. -/
theorem binomialMass_lower_entropy
    (a k : ℕ) (hkpos : 1 ≤ k) (hklt : k < a) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    let r := (k : ℝ) / (a : ℝ)
    (1 / (Real.exp 1) ^ 2) /
          Real.sqrt ((a : ℝ) * r * (1 - r)) *
        Real.exp (-(a : ℝ) * bernoulliRelativeEntropy r θ) ≤
      binomialMass a k θ := by
  let A : ℝ := a
  let K : ℝ := k
  let J : ℝ := ((a - k : ℕ) : ℝ)
  let r : ℝ := K / A
  have hka : k ≤ a := Nat.le_of_lt hklt
  have hjpos : 1 ≤ a - k := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_iff_lt.mpr hklt)
  have hA : 0 < A := by
    dsimp [A]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < k) hka)
  have hK : 0 < K := by dsimp [K]; exact_mod_cast hkpos
  have hJ : 0 < J := by
    change 0 < (((a - k : ℕ) : ℝ))
    exact_mod_cast hjpos
  let LA : ℝ := Real.sqrt A * (A / Real.exp 1) ^ a
  let UK : ℝ := Real.exp 1 * Real.sqrt K * (K / Real.exp 1) ^ k
  let UJ : ℝ := Real.exp 1 * Real.sqrt J * (J / Real.exp 1) ^ (a - k)
  have hLA : LA ≤ (a.factorial : ℝ) := by
    simpa [LA, A] using finiteStirling_lower_simple a
  have hUK : (k.factorial : ℝ) ≤ UK := by
    simpa [UK, K] using finiteStirling_upper k hkpos
  have hUJ : ((a - k).factorial : ℝ) ≤ UJ := by
    simpa [UJ, J] using finiteStirling_upper (a - k) hjpos
  have hden : (k.factorial : ℝ) * ((a - k).factorial : ℝ) ≤ UK * UJ := by
    exact mul_le_mul hUK hUJ (by positivity) (by positivity)
  have hratio : LA / (UK * UJ) ≤
      (a.factorial : ℝ) / ((k.factorial : ℝ) * ((a - k).factorial : ℝ)) := by
    exact div_le_div₀ (by positivity) hLA (by positivity) hden
  have hweight : 0 ≤ θ ^ k * (1 - θ) ^ (a - k) := by
    exact mul_nonneg (pow_nonneg hθ0.le _) (pow_nonneg (sub_nonneg.mpr hθ1.le) _)
  have hweighted := mul_le_mul_of_nonneg_right hratio hweight
  have hpow0 := stirlingPowerRatio_eq_likelihoodRatio a k hkpos hklt θ
  have hlike0 := likelihoodRatio_eq_exp_neg_entropy a k hkpos hklt θ hθ0 hθ1
  have hsqrt0 := sqrtRatio_eq_inv_sqrt_rankVariance a k hkpos hklt
  have hpow :
      (A / Real.exp 1) ^ a / ((K / Real.exp 1) ^ k * (J / Real.exp 1) ^ (a-k)) *
          θ ^ k * (1-θ) ^ (a-k) =
        (θ / r) ^ k * ((1-θ) / (1-r)) ^ (a-k) := by
    simpa [A, K, J, r] using hpow0
  have hlike :
      (θ / r) ^ k * ((1-θ) / (1-r)) ^ (a-k) =
        Real.exp (-A * bernoulliRelativeEntropy r θ) := by
    simpa [A, K, J, r] using hlike0
  have hsqrt : Real.sqrt A / (Real.sqrt K * Real.sqrt J) =
      1 / Real.sqrt (A * r * (1-r)) := by
    simpa [A, K, J, r] using hsqrt0
  change (1 / (Real.exp 1) ^ 2) / Real.sqrt (A * r * (1 - r)) *
      Real.exp (-A * bernoulliRelativeEntropy r θ) ≤ binomialMass a k θ
  calc
    _ = LA / (UK * UJ) * (θ ^ k * (1 - θ) ^ (a - k)) := by
      rw [← hlike, ← hpow]
      calc
        (1 / Real.exp 1 ^ 2) / Real.sqrt (A * r * (1-r)) *
            ((A / Real.exp 1) ^ a /
              ((K / Real.exp 1) ^ k * (J / Real.exp 1) ^ (a-k)) *
              θ ^ k * (1-θ) ^ (a-k)) =
            (1 / Real.exp 1 ^ 2) * (1 / Real.sqrt (A * r * (1-r))) *
              ((A / Real.exp 1) ^ a /
                ((K / Real.exp 1) ^ k * (J / Real.exp 1) ^ (a-k)) *
                θ ^ k * (1-θ) ^ (a-k)) := by ring
        _ = (1 / Real.exp 1 ^ 2) *
              (Real.sqrt A / (Real.sqrt K * Real.sqrt J)) *
              ((A / Real.exp 1) ^ a /
                ((K / Real.exp 1) ^ k * (J / Real.exp 1) ^ (a-k)) *
                θ ^ k * (1-θ) ^ (a-k)) := by rw [hsqrt]
        _ = LA / (UK * UJ) * (θ ^ k * (1 - θ) ^ (a - k)) := by
          dsimp [LA, UK, UJ]
          ring
    _ ≤ (a.factorial : ℝ) /
          ((k.factorial : ℝ) * ((a - k).factorial : ℝ)) *
          (θ ^ k * (1 - θ) ^ (a - k)) := hweighted
    _ = binomialMass a k θ := by
      rw [← choose_eq_factorial_ratio hka]
      simp [binomialMass, mul_assoc]

/-- Explicit uniform local lower bound, before inserting the integer shift.
The universal constants are `c_b = 1 / (3 * exp(1)^2)` and `C_b = 1`. -/
theorem binomialMass_uniform_lower
    (a k : ℕ) (θ H W : ℝ)
    (hθlo : (3 : ℝ) / 5 ≤ θ) (hθhi : θ ≤ (27 : ℝ) / 28)
    (hH : 1 ≤ H) (hW : W = (a : ℝ) * θ * (1 - θ))
    (hWH : 4 * H ≤ W)
    (hclose : ((a : ℝ) * θ - (k : ℝ)) ^ 2 ≤ H * W) :
    (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W * Real.exp (-H) ≤
      binomialMass a k θ := by
  let A : ℝ := a
  let K : ℝ := k
  let r : ℝ := K / A
  have hinter := interior_rank_bounds a (0 : ℤ) (k : ℤ) θ H (A * θ) W
    hθlo hθhi hH (by simp [A]) hW hWH (by simpa [A, K] using hclose)
  have ha : 1 ≤ a := hinter.1
  have hA : 0 < A := by dsimp [A]; exact_mod_cast ha
  have hrlo : (12 : ℝ) / 25 ≤ r := by simpa [r, K, A] using hinter.2.1
  have hrhi : r ≤ (1539 : ℝ) / 1568 := by simpa [r, K, A] using hinter.2.2
  have hr0 : 0 < r := by norm_num at hrlo ⊢; linarith
  have hr1 : r < 1 := by norm_num at hrhi ⊢; linarith
  have hkreal : 0 < K := by
    have hm := (le_div_iff₀ hA).mp hrlo
    have hp : 0 < ((12 : ℝ) / 25) * A := mul_pos (by norm_num) hA
    linarith
  have hkpos : 1 ≤ k := by
    have hkcast : (0 : ℝ) < (k : ℝ) := by simpa [K] using hkreal
    have : 0 < k := by exact_mod_cast hkcast
    omega
  have hklt : k < a := by
    have hKA : K < A := (div_lt_one₀ hA).mp hr1
    have hcast : (k : ℝ) < (a : ℝ) := by simpa [K, A] using hKA
    exact_mod_cast hcast
  have hθ0 : 0 < θ := by linarith
  have hθ1 : θ < 1 := by norm_num at hθhi ⊢; linarith
  have hWpos : 0 < W := by nlinarith
  have hRpos : 0 < A * r * (1-r) :=
    mul_pos (mul_pos hA hr0) (sub_pos.mpr hr1)
  have hRle : A * r * (1-r) ≤ 8 * W := by
    exact (variance_comparison a hθlo hθhi hrlo hrhi hW).1
  have hsqrt_le : Real.sqrt (A * r * (1-r)) ≤ 3 * Real.sqrt W := by
    have hsR := Real.sq_sqrt hRpos.le
    have hsW := Real.sq_sqrt hWpos.le
    have hnR := Real.sqrt_nonneg (A * r * (1-r))
    have hnW := Real.sqrt_nonneg W
    nlinarith
  have hrecip : 1 / (3 * Real.sqrt W) ≤ 1 / Real.sqrt (A * r * (1-r)) := by
    exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hRpos) hsqrt_le
  have hpref : (1 / (3 * (Real.exp 1)^2)) / Real.sqrt W ≤
      (1 / (Real.exp 1)^2) / Real.sqrt (A * r * (1-r)) := by
    have hc : 0 ≤ 1 / (Real.exp 1)^2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hrecip hc
    calc
      (1 / (3 * (Real.exp 1)^2)) / Real.sqrt W =
          (1 / (Real.exp 1)^2) * (1 / (3 * Real.sqrt W)) := by ring
      _ ≤ (1 / (Real.exp 1)^2) * (1 / Real.sqrt (A * r * (1-r))) := hm
      _ = (1 / (Real.exp 1)^2) / Real.sqrt (A * r * (1-r)) := by ring
  have hD0 := relativeEntropy_le_chiSquare hr0 hr1 hθ0 hθ1
  have hDmul : A * bernoulliRelativeEntropy r θ ≤
      A * ((r - θ)^2 / (θ * (1-θ))) :=
    mul_le_mul_of_nonneg_left hD0 hA.le
  have hnormalize : A * ((r - θ)^2 / (θ * (1-θ))) =
      (A * θ - K)^2 / W := by
    rw [hW]
    dsimp [r]
    field_simp [hA.ne', hθ0.ne', (sub_pos.mpr hθ1).ne']
    ring
  have hclose_div : (A * θ - K)^2 / W ≤ H := by
    apply (div_le_iff₀ hWpos).2
    simpa [A, K] using hclose
  have hAD : A * bernoulliRelativeEntropy r θ ≤ H := by
    calc
      _ ≤ A * ((r - θ)^2 / (θ * (1-θ))) := hDmul
      _ = (A * θ - K)^2 / W := hnormalize
      _ ≤ H := hclose_div
  have hexp : Real.exp (-H) ≤
      Real.exp (-A * bernoulliRelativeEntropy r θ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcombine :
      (1 / (3 * (Real.exp 1)^2)) / Real.sqrt W * Real.exp (-H) ≤
        (1 / (Real.exp 1)^2) / Real.sqrt (A * r * (1-r)) *
          Real.exp (-A * bernoulliRelativeEntropy r θ) := by
    exact mul_le_mul hpref hexp (Real.exp_pos _).le (by positivity)
  calc
    _ ≤ (1 / (Real.exp 1)^2) / Real.sqrt (A * r * (1-r)) *
          Real.exp (-A * bernoulliRelativeEntropy r θ) := hcombine
    _ ≤ binomialMass a k θ := by
      simpa [A, K, r] using binomialMass_lower_entropy a k hkpos hklt θ hθ0 hθ1

/-- Manuscript Lemma C.6 / equation (C.51), with explicit constants
`c_b = 1 / (3 * exp(1)^2)` and `C_b = 1`.  The integer support of `s-K` is a
consequence, not an extra hypothesis. -/
theorem uniformBinomialMassLowerBound_explicit
    (a : ℕ) (K s : ℤ) (θ H M W : ℝ)
    (hθlo : (3 : ℝ) / 5 ≤ θ) (hθhi : θ ≤ (27 : ℝ) / 28)
    (hH : 1 ≤ H) (hM : M = (K : ℝ) + (a : ℝ) * θ)
    (hW : W = (a : ℝ) * θ * (1 - θ))
    (hWH : 4 * H ≤ W) (hclose : (M - (s : ℝ)) ^ 2 ≤ H * W) :
    (1 / (3 * (Real.exp 1) ^ 2)) / Real.sqrt W * Real.exp (-H) ≤
      shiftedBinomialMass a K s θ := by
  have hinter := interior_rank_bounds a K s θ H M W hθlo hθhi hH hM hW hWH hclose
  have ha : 1 ≤ a := hinter.1
  have hA : 0 < (a : ℝ) := by exact_mod_cast ha
  let z : ℤ := s - K
  have hzlo : (12 : ℝ) / 25 ≤ (z : ℝ) / (a : ℝ) := by
    simpa [z] using hinter.2.1
  have hzhi : (z : ℝ) / (a : ℝ) ≤ (1539 : ℝ) / 1568 := by
    simpa [z] using hinter.2.2
  have hzrealpos : (0 : ℝ) < (z : ℝ) := by
    have hm := (le_div_iff₀ hA).mp hzlo
    have hp : 0 < ((12 : ℝ) / 25) * (a : ℝ) := mul_pos (by norm_num) hA
    linarith
  have hzpos : (0 : ℤ) < z := by exact_mod_cast hzrealpos
  have hzreal_lt : (z : ℝ) < (a : ℝ) := by
    apply (div_lt_one₀ hA).mp
    norm_num at hzhi ⊢
    linarith
  have hzlt : z < (a : ℤ) := by exact_mod_cast hzreal_lt
  have hsupport : 0 ≤ s - K ∧ s - K ≤ (a : ℤ) := by
    dsimp [z] at hzpos hzlt
    exact ⟨hzpos.le, hzlt.le⟩
  let k : ℕ := z.toNat
  have hkz : (k : ℤ) = z := by
    dsimp [k]
    exact Int.toNat_of_nonneg hzpos.le
  have hkcast : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
  have hclosek : ((a : ℝ) * θ - (k : ℝ)) ^ 2 ≤ H * W := by
    calc
      ((a : ℝ) * θ - (k : ℝ)) ^ 2 = (M - (s : ℝ)) ^ 2 := by
        rw [hkcast, hM]
        dsimp [z]
        push_cast
        ring
      _ ≤ H * W := hclose
  have hnat := binomialMass_uniform_lower a k θ H W hθlo hθhi hH hW hWH hclosek
  rw [shiftedBinomialMass, if_pos hsupport]
  simpa [k, z] using hnat

/-- Equation (C.51) in the manuscript's literal `W ^ (-1/2)` notation. -/
theorem uniformBinomialMassLowerBound_rpow
    (a : ℕ) (K s : ℤ) (θ H M W : ℝ)
    (hθlo : (3 : ℝ) / 5 ≤ θ) (hθhi : θ ≤ (27 : ℝ) / 28)
    (hH : 1 ≤ H) (hM : M = (K : ℝ) + (a : ℝ) * θ)
    (hW : W = (a : ℝ) * θ * (1 - θ))
    (hWH : 4 * H ≤ W) (hclose : (M - (s : ℝ)) ^ 2 ≤ H * W) :
    (1 / (3 * (Real.exp 1) ^ 2)) * W ^ (-(1 : ℝ) / 2) * Real.exp (-H) ≤
      shiftedBinomialMass a K s θ := by
  have hWnonneg : 0 ≤ W := by nlinarith
  have h := uniformBinomialMassLowerBound_explicit a K s θ H M W
    hθlo hθhi hH hM hW hWH hclose
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg hWnonneg, ← Real.sqrt_eq_rpow] 
  simpa [div_eq_mul_inv] using h

/-- The existential universal-constant formulation of manuscript (C.51).
The witnesses are independent of all binomial parameters. -/
theorem uniformBinomialMassLowerBound :
    ∃ c_b C_b : ℝ, 0 < c_b ∧ 0 < C_b ∧
      ∀ (a : ℕ) (K s : ℤ) (θ H M W : ℝ),
        (3 : ℝ) / 5 ≤ θ → θ ≤ (27 : ℝ) / 28 →
        1 ≤ H → M = (K : ℝ) + (a : ℝ) * θ →
        W = (a : ℝ) * θ * (1 - θ) →
        4 * H ≤ W → (M - (s : ℝ)) ^ 2 ≤ H * W →
        c_b * W ^ (-(1 : ℝ) / 2) * Real.exp (-C_b * H) ≤
          shiftedBinomialMass a K s θ := by
  refine ⟨1 / (3 * (Real.exp 1)^2), 1, by positivity, by norm_num, ?_⟩
  intro a K s θ H M W hθlo hθhi hH hM hW hWH hclose
  simpa using uniformBinomialMassLowerBound_rpow a K s θ H M W
    hθlo hθhi hH hM hW hWH hclose

end
end UniformBinomialMass
end Forest
end Erdos993
