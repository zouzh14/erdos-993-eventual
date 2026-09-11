import Erdos993.Forest.IndexVarianceLocalization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Uniform characteristic-function gap for finite forests

This file owns the finite hard-core Fourier vocabulary and the exact finite
predecessors used in Lemma A.4 / (A.19) of the manuscript.  All probabilities
are the actual weights of `hardCoreLaw`; there is no asymptotic or rooted-family
parameter.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators ENNReal

universe u

namespace FiniteLatticeLaw

variable {α : Type u} [Fintype α]

/-- Finite expectation for the real-valued law stored in `FiniteLatticeLaw`. -/
def expect (L : FiniteLatticeLaw α) (f : α → ℝ) : ℝ :=
  ∑ a, L.probability a * f a

/-- Probability of a finite event. -/
def eventMass (L : FiniteLatticeLaw α) (P : α → Prop) [DecidablePred P] : ℝ :=
  ∑ a ∈ Finset.univ.filter P, L.probability a

/-- The unit complex phase `exp(i θ x)`. -/
def phase (θ x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((θ * x : ℝ) : ℂ))

/-- The uncentered characteristic function of the finite lattice law. -/
def characteristic (L : FiniteLatticeLaw α) (θ : ℝ) : ℂ :=
  ∑ a, (L.probability a : ℂ) * phase θ (L.stat a : ℝ)

/-- The centered characteristic function used in Appendix A. -/
def centeredCharacteristic (L : FiniteLatticeLaw α) (θ : ℝ) : ℂ :=
  ∑ a, (L.probability a : ℂ) *
    phase θ ((L.stat a : ℝ) - L.mean)

/-- Modulus of the centered characteristic function. -/
def characteristicModulus (L : FiniteLatticeLaw α) (θ : ℝ) : ℝ :=
  ‖L.centeredCharacteristic θ‖

/-- Manuscript logarithmic loss, represented in `EReal` so that `-log 0 = +∞`.
Using `Real.log` directly would give the wrong value at zero. -/
def logarithmicLoss (L : FiniteLatticeLaw α) (θ : ℝ) : EReal :=
  - ENNReal.log (ENNReal.ofReal (L.characteristicModulus θ))

@[simp] theorem expect_one (L : FiniteLatticeLaw α) :
    L.expect (fun _ => 1) = 1 := by
  simp [expect, ← Finset.sum_mul, L.probability_sum]

@[simp] theorem eventMass_true (L : FiniteLatticeLaw α) :
    L.eventMass (fun _ => True) = 1 := by
  simp [eventMass, L.probability_sum]

 theorem eventMass_nonneg (L : FiniteLatticeLaw α)
    (P : α → Prop) [DecidablePred P] : 0 ≤ L.eventMass P := by
  unfold eventMass
  exact Finset.sum_nonneg fun a _ => L.probability_nonneg a

 theorem eventMass_le_one (L : FiniteLatticeLaw α)
    (P : α → Prop) [DecidablePred P] : L.eventMass P ≤ 1 := by
  calc
    L.eventMass P ≤ ∑ a, L.probability a := by
      unfold eventMass
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => L.probability_nonneg a)
    _ = 1 := L.probability_sum

 theorem eventMass_eq_sum_ite (L : FiniteLatticeLaw α)
    (P : α → Prop) [DecidablePred P] :
    L.eventMass P = ∑ a, if P a then L.probability a else 0 := by
  rw [eventMass, Finset.sum_filter]

 theorem eventMass_mono (L : FiniteLatticeLaw α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, P a → Q a) : L.eventMass P ≤ L.eventMass Q := by
  rw [L.eventMass_eq_sum_ite P, L.eventMass_eq_sum_ite Q]
  apply Finset.sum_le_sum
  intro a _
  by_cases hP : P a
  · simp [hP, hPQ a hP]
  · by_cases hQ : Q a <;> simp [hP, hQ, L.probability_nonneg a]

 theorem eventMass_compl (L : FiniteLatticeLaw α)
    (P : α → Prop) [DecidablePred P] [DecidablePred fun a => ¬ P a] :
    L.eventMass P + L.eventMass (fun a => ¬ P a) = 1 := by
  simpa only [eventMass, L.probability_sum] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset α) P L.probability)

 theorem eventMass_or_le (L : FiniteLatticeLaw α)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    [DecidablePred fun a => P a ∨ Q a] :
    L.eventMass (fun a => P a ∨ Q a) ≤ L.eventMass P + L.eventMass Q := by
  rw [L.eventMass_eq_sum_ite (fun a => P a ∨ Q a),
    L.eventMass_eq_sum_ite P, L.eventMass_eq_sum_ite Q,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  by_cases hP : P a <;> by_cases hQ : Q a <;>
    simp [hP, hQ, L.probability_nonneg a]

 theorem expect_le_three_quarters_add_quarter
    (L : FiniteLatticeLaw α) (f : α → ℝ) (P : α → Prop)
    [DecidablePred P] [DecidablePred fun a => ¬ P a] (c : ℝ)
    (hf_one : ∀ a, f a ≤ 1) (hf_event : ∀ a, P a → f a ≤ c)
    (hc : c ≤ 1) (hP : (1 / 4 : ℝ) ≤ L.eventMass P) :
    L.expect f ≤ (3 / 4 : ℝ) + c / 4 := by
  have hpoint : ∀ a, L.probability a * f a ≤
      L.probability a * (if P a then c else 1) := by
    intro a
    apply mul_le_mul_of_nonneg_left _ (L.probability_nonneg a)
    by_cases ha : P a
    · simpa [ha] using hf_event a ha
    · simpa [ha] using hf_one a
  calc
    L.expect f ≤ ∑ a, L.probability a * (if P a then c else 1) := by
      exact Finset.sum_le_sum (fun a _ => hpoint a)
    _ = c * L.eventMass P + L.eventMass (fun a => ¬ P a) := by
      rw [L.eventMass_eq_sum_ite P,
        L.eventMass_eq_sum_ite (fun a => ¬ P a), Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : P a <;> simp [ha, mul_comm]
    _ = c * L.eventMass P + (1 - L.eventMass P) := by
      have hcpl := L.eventMass_compl P
      rw [show L.eventMass (fun a => ¬ P a) = 1 - L.eventMass P by linarith]
    _ ≤ (3 / 4 : ℝ) + c / 4 := by
      have hmul := mul_le_mul_of_nonneg_right hP (sub_nonneg.mpr hc)
      nlinarith

@[simp] theorem norm_phase (θ x : ℝ) : ‖phase θ x‖ = 1 := by
  rw [phase, Complex.norm_exp]
  simp

@[simp] theorem phase_zero (θ : ℝ) : phase θ 0 = 1 := by
  simp [phase]

 theorem phase_add (θ x y : ℝ) :
    phase θ (x + y) = phase θ x * phase θ y := by
  rw [phase, phase, phase, ← Complex.exp_add]
  congr 2
  push_cast
  ring

 theorem phase_natCast (θ : ℝ) (n : ℕ) :
    phase θ (n : ℝ) = phase θ 1 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, phase_add, ih, pow_succ]

 theorem centeredCharacteristic_eq_phase_mul (L : FiniteLatticeLaw α) (θ : ℝ) :
    L.centeredCharacteristic θ = phase θ (-L.mean) * L.characteristic θ := by
  rw [centeredCharacteristic, characteristic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hphase :
      phase θ ((L.stat a : ℝ) - L.mean) =
        phase θ (-L.mean) * phase θ (L.stat a : ℝ) := by
    rw [phase, phase, phase, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hphase]
  ring

 theorem norm_centeredCharacteristic_eq (L : FiniteLatticeLaw α) (θ : ℝ) :
    ‖L.centeredCharacteristic θ‖ = ‖L.characteristic θ‖ := by
  rw [L.centeredCharacteristic_eq_phase_mul, norm_mul, norm_phase, one_mul]

 theorem characteristicModulus_nonneg (L : FiniteLatticeLaw α) (θ : ℝ) :
    0 ≤ L.characteristicModulus θ := norm_nonneg _

 theorem characteristicModulus_le_one (L : FiniteLatticeLaw α) (θ : ℝ) :
    L.characteristicModulus θ ≤ 1 := by
  rw [characteristicModulus, L.norm_centeredCharacteristic_eq]
  calc
    ‖∑ a, (L.probability a : ℂ) * phase θ (L.stat a : ℝ)‖ ≤
        ∑ a, ‖(L.probability a : ℂ) * phase θ (L.stat a : ℝ)‖ :=
      norm_sum_le _ _
    _ = ∑ a, L.probability a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [norm_mul, norm_phase, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (L.probability_nonneg a)]
    _ = 1 := L.probability_sum

/-- The extended-real logarithmic loss dominates the elementary modulus loss,
including the zero-modulus case where the left side is finite and the
logarithmic loss is `⊤`. -/
theorem one_sub_characteristicModulus_le_logarithmicLoss
    (L : FiniteLatticeLaw α) (θ : ℝ) :
    ((1 - L.characteristicModulus θ : ℝ) : EReal) ≤ L.logarithmicLoss θ := by
  have hx0 := L.characteristicModulus_nonneg θ
  by_cases hx : L.characteristicModulus θ = 0
  · simp [logarithmicLoss, hx]
  · have hxpos : 0 < L.characteristicModulus θ := lt_of_le_of_ne hx0 (Ne.symm hx)
    rw [logarithmicLoss, ENNReal.log_ofReal_of_pos hxpos]
    norm_cast
    have hlog := Real.log_le_sub_one_of_pos hxpos
    linarith

end FiniteLatticeLaw

/-- The manuscript constant in Lemma A.4. -/
def uniformGapConstant (Z : ℝ) : ℝ :=
  min ((1 - Real.exp (-(7 / 16 : ℝ))) / 8) (1 / (8 * (1 + Z)))

 theorem uniformGapConstant_nonneg {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ uniformGapConstant Z := by
  unfold uniformGapConstant
  apply le_min
  · have he : Real.exp (-(7 / 16 : ℝ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by norm_num)
    exact div_nonneg (sub_nonneg.mpr he) (by norm_num)
  · exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) (by linarith))

 theorem uniformGapConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < uniformGapConstant Z := by
  unfold uniformGapConstant
  apply lt_min
  · have he : Real.exp (-(7 / 16 : ℝ)) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    exact div_pos (sub_pos.mpr he) (by norm_num)
  · exact div_pos (by norm_num) (mul_pos (by norm_num) (by linarith))

/-- The exact `t = n p` comparison (A.24), isolated from the probabilistic
second-moment estimate. -/
theorem min_t_one_ge_half_min_variance_one
    {t variance : ℝ} (ht : 0 ≤ t)
    (hsecond : variance ≤ t + t ^ 2) :
    min t 1 ≥ min variance 1 / 2 := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1]
    have hv2 : variance ≤ 2 * t := by nlinarith
    have hminv : min variance 1 ≤ variance := min_le_left _ _
    nlinarith
  · have h1t : 1 ≤ t := le_of_not_ge ht1
    rw [min_eq_right h1t]
    have hminv : min variance 1 ≤ 1 := min_le_right _ _
    nlinarith

variable {V : Type u} [Fintype V]

/-- Number of vertices of an independent configuration that are available
inside an independent side `S`, expressed through the existing exact fiber
API. -/
def availableCount [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (I : IndepFinset G) : ℕ :=
  (freeInside G S (outsidePart G S I)).card

/-- Complex binomial expansion over all subsets. -/
theorem weightedPowersetComplex [DecidableEq V] (A : Finset V) (w : ℂ) :
    (∑ t ∈ A.powerset, w ^ t.card) = (1 + w) ^ A.card := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hsecond : (∑ t ∈ A.powerset, w ^ (insert a t).card) =
          w * ∑ t ∈ A.powerset, w ^ t.card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [Finset.card_insert_of_notMem hat, pow_succ]
        ring
      rw [hsecond, ih, Finset.card_insert_of_notMem ha, pow_succ]
      ring

/-- The exact complex counterpart of `fiber_weight_sum`: each fiber is a
product-binomial partition function over its available vertices. -/
theorem fiber_weight_sum_complex [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (b : OutsideConfig G S) (w : ℂ) :
    (∑ I ∈ fiberFinset G S b, w ^ I.val.card) =
      w ^ b.val.card * (1 + w) ^ (freeInside G S b).card := by
  classical
  let F := freeInside G S b
  calc
    _ = ∑ t ∈ F.powerset, w ^ b.val.card * w ^ t.card := by
      apply Finset.sum_bij (fun I _ => I.val ∩ S)
      · intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        let Ifib : Fiber G S b := ⟨I, hIb⟩
        exact Finset.mem_powerset.mpr
          ((fiberEquivPowerset G S hS b Ifib).property)
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
        · exact congrArg Subtype.val
            ((fiberEquivPowerset G S hS b).right_inv T)
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
    _ = w ^ b.val.card * (1 + w) ^ F.card := by
      rw [← Finset.mul_sum, weightedPowersetComplex]
    _ = _ := rfl

noncomputable local instance outsideConfigFintypeComplex [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : Fintype (OutsideConfig G S) :=
  Fintype.ofInjective (fun b : OutsideConfig G S => b.val) (by
    intro a b h
    exact Subtype.ext h)

/-- Fiber decomposition for complex-valued sums. -/
theorem sum_fiberFinset_complex [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (f : IndepFinset G → ℂ) :
    (∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b, f I) =
      ∑ I : IndepFinset G, f I := by
  classical
  simp only [fiberFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem sum_fiberFinset_real [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (f : IndepFinset G → ℝ) :
    (∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b, f I) =
      ∑ I : IndepFinset G, f I := by
  classical
  simp only [fiberFinset, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Modulus of the one-site Bernoulli characteristic factor at activity `z`. -/
def bernoulliRadius (z θ : ℝ) : ℝ :=
  ‖(1 : ℂ) + (z : ℂ) * FiniteLatticeLaw.phase θ 1‖ / (1 + z)

/-- Exact squared-radius identity for the Bernoulli characteristic factor. -/
theorem bernoulliRadius_sq (z θ : ℝ) (hz : 0 < z) :
    bernoulliRadius z θ ^ 2 =
      1 - 4 * (z / (1 + z) ^ 2) * Real.sin (θ / 2) ^ 2 := by
  rw [bernoulliRadius, div_pow, Complex.sq_norm, Complex.normSq_apply]
  simp [FiniteLatticeLaw.phase, Complex.exp_re, Complex.exp_im]
  have htrig := Real.sin_sq_add_cos_sq θ
  have hcos := Real.cos_two_mul_eq_one_sub (θ / 2)
  have harg : 2 * (θ / 2) = θ := by ring
  rw [harg] at hcos
  have hden : 1 + z ≠ 0 := ne_of_gt (by linarith)
  field_simp
  nlinarith

/-- Exponential decay of the Bernoulli radius, in the exact normalization used
in A.19. -/
theorem bernoulliRadius_le_exp (z θ : ℝ) (hz : 0 < z) :
    bernoulliRadius z θ ≤
      Real.exp (-2 * (z / (1 + z) ^ 2) * Real.sin (θ / 2) ^ 2) := by
  let q : ℝ := z / (1 + z) ^ 2
  let h : ℝ := Real.sin (θ / 2) ^ 2
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hh : 0 ≤ h := sq_nonneg _
  have hr : 0 ≤ bernoulliRadius z θ := by
    apply div_nonneg (norm_nonneg _)
    linarith
  have hsq : bernoulliRadius z θ ^ 2 = 1 - 4 * q * h := by
    simpa [q, h] using bernoulliRadius_sq z θ hz
  have hexp : 1 - 4 * q * h ≤ Real.exp (-4 * q * h) := by
    linarith [Real.add_one_le_exp (-4 * q * h)]
  have hexpsq :
      Real.exp (-2 * q * h) ^ 2 = Real.exp (-4 * q * h) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsquares : bernoulliRadius z θ ^ 2 ≤ Real.exp (-2 * q * h) ^ 2 := by
    rw [hsq, hexpsq]
    exact hexp
  have he : 0 ≤ Real.exp (-2 * q * h) := (Real.exp_pos _).le
  dsimp [q, h] at *
  nlinarith

/-- Linear one-step decay, obtained exactly from the squared-radius identity. -/
theorem bernoulliRadius_le_one_sub (z θ : ℝ) (hz : 0 < z) :
    bernoulliRadius z θ ≤
      1 - 2 * (z / (1 + z) ^ 2) * Real.sin (θ / 2) ^ 2 := by
  let q : ℝ := z / (1 + z) ^ 2
  let h : ℝ := Real.sin (θ / 2) ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hh : 0 ≤ h := sq_nonneg _
  have hr : 0 ≤ bernoulliRadius z θ := by
    apply div_nonneg (norm_nonneg _)
    linarith
  have hsq : bernoulliRadius z θ ^ 2 = 1 - 4 * q * h := by
    simpa [q, h] using bernoulliRadius_sq z θ hz
  have hbase : 0 ≤ 1 - 4 * q * h := by
    rw [← hsq]
    positivity
  have hrhs : 0 ≤ 1 - 2 * q * h := by linarith
  have hdiff : bernoulliRadius z θ ^ 2 ≤ (1 - 2 * q * h) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (2 * q * h)]
  dsimp [q, h] at *
  nlinarith

 theorem hardCore_weight_phase_eq_pow (z θ : ℝ) (n : ℕ) :
    (z : ℂ) ^ n * FiniteLatticeLaw.phase θ (n : ℝ) =
      ((z : ℂ) * FiniteLatticeLaw.phase θ 1) ^ n := by
  rw [FiniteLatticeLaw.phase_natCast, mul_pow]

/-- Exact complex characteristic numerator on one outside fiber. -/
theorem fiber_characteristic_sum [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (b : OutsideConfig G S) (z θ : ℝ) :
    (∑ I ∈ fiberFinset G S b,
      (z : ℂ) ^ I.val.card *
        FiniteLatticeLaw.phase θ (I.val.card : ℝ)) =
      ((z : ℂ) * FiniteLatticeLaw.phase θ 1) ^ b.val.card *
        (1 + (z : ℂ) * FiniteLatticeLaw.phase θ 1) ^
          (freeInside G S b).card := by
  calc
    _ = ∑ I ∈ fiberFinset G S b,
        ((z : ℂ) * FiniteLatticeLaw.phase θ 1) ^ I.val.card := by
      apply Finset.sum_congr rfl
      intro I _
      exact hardCore_weight_phase_eq_pow z θ I.val.card
    _ = _ := fiber_weight_sum_complex G S hS b
      ((z : ℂ) * FiniteLatticeLaw.phase θ 1)

/-- Unnormalized form of the conditional-fiber estimate (A.20). -/
theorem hardCore_unnormalized_characteristic_le_availability
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (z θ : ℝ) (hz : 0 < z) :
    ‖∑ I : IndepFinset G, (z : ℂ) ^ I.val.card *
        FiniteLatticeLaw.phase θ (I.val.card : ℝ)‖ ≤
      ∑ I : IndepFinset G, z ^ I.val.card *
        bernoulliRadius z θ ^ availableCount G S I := by
  classical
  let w : ℂ := (z : ℂ) * FiniteLatticeLaw.phase θ 1
  let r : ℝ := bernoulliRadius z θ
  rw [← sum_fiberFinset_complex G S]
  calc
    ‖∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b,
        (z : ℂ) ^ I.val.card *
          FiniteLatticeLaw.phase θ (I.val.card : ℝ)‖ ≤
      ∑ b : OutsideConfig G S, ‖∑ I ∈ fiberFinset G S b,
        (z : ℂ) ^ I.val.card *
          FiniteLatticeLaw.phase θ (I.val.card : ℝ)‖ := norm_sum_le _ _
    _ = ∑ b : OutsideConfig G S,
        z ^ b.val.card * ‖1 + w‖ ^ (freeInside G S b).card := by
      apply Finset.sum_congr rfl
      intro b _
      rw [fiber_characteristic_sum G S hS b z θ, norm_mul, norm_pow,
        norm_pow]
      have hw : ‖w‖ = z := by
        simp [w, norm_mul, hz.le]
      rw [hw]
    _ = ∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b,
        z ^ I.val.card * r ^ availableCount G S I := by
      apply Finset.sum_congr rfl
      intro b _
      have havail : ∀ I ∈ fiberFinset G S b,
          availableCount G S I = (freeInside G S b).card := by
        intro I hI
        have hIb : outsidePart G S I = b := by simpa [fiberFinset] using hI
        simp [availableCount, hIb]
      calc
        z ^ b.val.card * ‖1 + w‖ ^ (freeInside G S b).card =
            z ^ b.val.card * (1 + z) ^ (freeInside G S b).card *
              r ^ (freeInside G S b).card := by
          have hden : 1 + z ≠ 0 := ne_of_gt (by linarith)
          simp only [r, bernoulliRadius, w]
          rw [div_pow]
          field_simp
        _ = (∑ I ∈ fiberFinset G S b, z ^ I.val.card) *
              r ^ (freeInside G S b).card := by
          rw [fiber_weight_sum G S hS b z]
        _ = ∑ I ∈ fiberFinset G S b,
              z ^ I.val.card * r ^ availableCount G S I := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro I hI
          rw [havail I hI]
    _ = ∑ I : IndepFinset G, z ^ I.val.card *
        bernoulliRadius z θ ^ availableCount G S I := by
      change (∑ b : OutsideConfig G S, ∑ I ∈ fiberFinset G S b,
        z ^ I.val.card * bernoulliRadius z θ ^ availableCount G S I) = _
      exact sum_fiberFinset_real G S _

/-- Exact manuscript estimate (A.20) for the actual finite hard-core law:
conditioning on any independent side leaves independent Bernoulli variables
on precisely the available vertices. -/
theorem hardCoreLaw_characteristic_le_expected_radius_available
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (z θ : ℝ) (hz : 0 < z) :
    ‖(hardCoreLaw G z hz).characteristic θ‖ ≤
      ∑ I : IndepFinset G, (hardCoreLaw G z hz).probability I *
        bernoulliRadius z θ ^ availableCount G S I := by
  classical
  let E : ℝ := independenceEval G z
  have hE : 0 < E := independenceEval_pos G hz
  have hchar : (hardCoreLaw G z hz).characteristic θ =
      (1 / (E : ℂ)) * ∑ I : IndepFinset G,
        (z : ℂ) ^ I.val.card *
          FiniteLatticeLaw.phase θ (I.val.card : ℝ) := by
    rw [FiniteLatticeLaw.characteristic, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I _
    simp only [hardCoreLaw]
    push_cast
    dsimp [E]
    field_simp
  rw [hchar, norm_mul, norm_div, norm_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hE]
  have hnum := hardCore_unnormalized_characteristic_le_availability
    G S hS z θ hz
  calc
    1 / E * ‖∑ I : IndepFinset G, (z : ℂ) ^ I.val.card *
        FiniteLatticeLaw.phase θ (I.val.card : ℝ)‖ ≤
      1 / E * ∑ I : IndepFinset G, z ^ I.val.card *
        bernoulliRadius z θ ^ availableCount G S I := by
          exact mul_le_mul_of_nonneg_left hnum (by positivity)
    _ = ∑ I : IndepFinset G, (hardCoreLaw G z hz).probability I *
        bernoulliRadius z θ ^ availableCount G S I := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      simp only [hardCoreLaw, E]
      field_simp

def unavailableVertices [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (I : IndepFinset G) : Finset V :=
  Finset.univ.filter fun v => ¬ Disjoint I.val (G.neighborFinset v)

/-- The zero color class of mathlib's canonical two-coloring of a forest. -/
def leftSide (G : SimpleGraph V) (hG : G.IsAcyclic) : Finset V :=
  Finset.univ.filter fun v => hG.coloringTwo v = 0

/-- The nonzero color class of mathlib's canonical two-coloring of a forest. -/
def rightSide (G : SimpleGraph V) (hG : G.IsAcyclic) : Finset V :=
  Finset.univ.filter fun v => hG.coloringTwo v ≠ 0

 theorem leftSide_union_rightSide [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    leftSide G hG ∪ rightSide G hG = Finset.univ := by
  classical
  ext v
  simp only [Finset.mem_union, leftSide, rightSide, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro _
    trivial
  · intro _
    exact Classical.em _

 theorem leftSide_disjoint_rightSide [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    Disjoint (leftSide G hG) (rightSide G hG) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  exact (Finset.mem_filter.mp hvR).2 (Finset.mem_filter.mp hvL).2

 theorem leftSide_independent (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.IsIndepSet (leftSide G hG : Set V) := by
  let c : G.Coloring (Fin 2) := hG.coloringTwo
  apply (c.isIndepSet_colorClass 0).mono
  intro v hv
  exact (Finset.mem_filter.mp hv).2

 theorem rightSide_independent (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.IsIndepSet (rightSide G hG : Set V) := by
  let c : G.Coloring (Fin 2) := hG.coloringTwo
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

/-- Availability in the fiber API is exactly membership in the chosen side
and absence of an occupied neighbor. -/
theorem availableCount_eq_filter [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (hS : G.IsIndepSet (S : Set V)) (I : IndepFinset G) :
    availableCount G S I =
      (S.filter fun v => Disjoint I.val (G.neighborFinset v)).card := by
  classical
  unfold availableCount
  apply congrArg Finset.card
  ext v
  rw [Finset.mem_filter]
  constructor
  · intro hv
    have hvS : v ∈ S := (Finset.mem_filter.mp hv).1
    refine ⟨hvS, ?_⟩
    exact (fiber_free_iff_avoid G S hS v hvS
      (outsidePart G S I) I rfl).mp hv
  · intro hv
    exact (fiber_free_iff_avoid G S hS v hv.1
      (outsidePart G S I) I rfl).mpr hv.2

/-- Exact partition of every vertex into available-on-left,
available-on-right, or unavailable. -/
theorem available_left_add_right_add_unavailable [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (I : IndepFinset G) :
    availableCount G (leftSide G hG) I +
        availableCount G (rightSide G hG) I +
      (unavailableVertices G I).card = Fintype.card V := by
  classical
  let P : V → Prop := fun v => Disjoint I.val (G.neighborFinset v)
  let L := leftSide G hG
  let R := rightSide G hG
  have hL := availableCount_eq_filter G L (leftSide_independent G hG) I
  have hR := availableCount_eq_filter G R (rightSide_independent G hG) I
  have hLR : (L.filter P) ∪ (R.filter P) = Finset.univ.filter P := by
    ext v
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨hv, hP⟩ | ⟨hv, hP⟩) <;> exact hP
    · intro hP
      have hsides : v ∈ L ∪ R := by
        rw [show L ∪ R = Finset.univ by
          exact leftSide_union_rightSide G hG]
        simp
      rcases Finset.mem_union.mp hsides with hvL | hvR
      · exact Or.inl ⟨hvL, hP⟩
      · exact Or.inr ⟨hvR, hP⟩
  have hdisj : Disjoint (L.filter P) (R.filter P) :=
    (leftSide_disjoint_rightSide G hG).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hcardP : (L.filter P).card + (R.filter P).card =
      (Finset.univ.filter P).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hLR]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V)) (p := P)
  rw [hL, hR]
  change (L.filter P).card + (R.filter P).card +
      (Finset.univ.filter fun v => ¬P v).card = Fintype.card V
  rw [hcardP]
  simpa using hsplit

/-- Two distinct vertices are simultaneously occupied with probability at most
`p²`, where `p = z/(1+z)`.  This is the exact two-vertex deletion estimate used
in (A.22); adjacency is not needed for the estimate. -/
theorem hardCoreLaw_pair_marginal_le [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) (v w : V) (hvw : v ≠ w) :
    (∑ I ∈ Finset.univ.filter
        (fun I : IndepFinset G => v ∈ I.val ∧ w ∈ I.val),
      (hardCoreLaw G z hz).probability I) ≤ (z / (1 + z)) ^ 2 := by
  classical
  let μ := hardCoreLaw G z hz
  let C : Finset (IndepFinset G) :=
    Finset.univ.filter (fun I => v ∈ I.val ∧ w ∈ I.val)
  let A : Finset (IndepFinset G) :=
    Finset.univ.filter (fun I => v ∉ I.val ∧ w ∈ I.val)
  let eraseV : IndepFinset G → IndepFinset G := fun I =>
    ⟨I.val.erase v, I.property.mono (Finset.erase_subset v I.val)⟩
  change (∑ I ∈ C, μ.probability I) ≤ (z / (1 + z)) ^ 2
  have himage : C.image eraseV ⊆ A := by
    intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    have hIv : v ∈ I.val := (Finset.mem_filter.mp hI).2.1
    have hIw : w ∈ I.val := (Finset.mem_filter.mp hI).2.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp [eraseV]
    · simpa [eraseV, hvw.symm] using hIw
  have hinj : Set.InjOn eraseV (C : Set (IndepFinset G)) := by
    intro I hI J hJ hIJ
    have hIv : v ∈ I.val := (Finset.mem_filter.mp hI).2.1
    have hJv : v ∈ J.val := (Finset.mem_filter.mp hJ).2.1
    have herase := congrArg (fun K : IndepFinset G => K.val) hIJ
    change I.val.erase v = J.val.erase v at herase
    apply Subtype.ext
    calc
      I.val = insert v (I.val.erase v) := (Finset.insert_erase hIv).symm
      _ = insert v (J.val.erase v) := congrArg (insert v) herase
      _ = J.val := Finset.insert_erase hJv
  have hweight : ∀ I ∈ C,
      μ.probability I = z * μ.probability (eraseV I) := by
    intro I hI
    have hIv : v ∈ I.val := (Finset.mem_filter.mp hI).2.1
    change z ^ I.val.card / independenceEval G z =
      z * (z ^ (I.val.erase v).card / independenceEval G z)
    rw [← Finset.card_erase_add_one hIv, pow_succ]
    ring
  have hraw :
      (∑ I ∈ C, μ.probability I) ≤ z * ∑ J ∈ A, μ.probability J := by
    calc
      (∑ I ∈ C, μ.probability I) =
          ∑ I ∈ C, z * μ.probability (eraseV I) :=
        Finset.sum_congr rfl hweight
      _ = ∑ J ∈ C.image eraseV, z * μ.probability J := by
        symm
        apply Finset.sum_image
        intro I hI J hJ h
        exact hinj hI hJ h
      _ ≤ ∑ J ∈ A, z * μ.probability J := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro J hJA hJimage
        exact mul_nonneg hz.le (μ.probability_nonneg J)
      _ = z * ∑ J ∈ A, μ.probability J := by rw [Finset.mul_sum]
  have hpart :
      (∑ J ∈ A, μ.probability J) + (∑ I ∈ C, μ.probability I) =
        ∑ I ∈ Finset.univ.filter
          (fun I : IndepFinset G => w ∈ I.val), μ.probability I := by
    let T : Finset (IndepFinset G) :=
      Finset.univ.filter (fun I => w ∈ I.val)
    have h := Finset.sum_filter_not_add_sum_filter T
      (fun I : IndepFinset G => v ∈ I.val) μ.probability
    simpa only [A, C, T, Finset.filter_filter, and_comm, and_left_comm,
      and_assoc] using h
  have hmarg := hardCoreLaw_vertex_marginal_le G z hz w
  have hden : 0 < 1 + z := by linarith
  have hscale :
      (∑ I ∈ C, μ.probability I) ≤
        (z / (1 + z)) *
          ((∑ J ∈ A, μ.probability J) + (∑ I ∈ C, μ.probability I)) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hden).2
    calc
      (∑ I ∈ C, μ.probability I) * (1 + z) =
          (∑ I ∈ C, μ.probability I) +
            z * (∑ I ∈ C, μ.probability I) := by ring
      _ ≤ z * (∑ J ∈ A, μ.probability J) +
            z * (∑ I ∈ C, μ.probability I) := by
          gcongr
      _ = z * ((∑ J ∈ A, μ.probability J) +
            (∑ I ∈ C, μ.probability I)) := by ring
  have hp : 0 ≤ z / (1 + z) := by positivity
  calc
    (∑ I ∈ C, μ.probability I) ≤
        (z / (1 + z)) *
          ((∑ J ∈ A, μ.probability J) + (∑ I ∈ C, μ.probability I)) := hscale
    _ = (z / (1 + z)) *
          (∑ I ∈ Finset.univ.filter
            (fun I : IndepFinset G => w ∈ I.val), μ.probability I) := by rw [hpart]
    _ ≤ (z / (1 + z)) * (z / (1 + z)) :=
      mul_le_mul_of_nonneg_left hmarg hp
    _ = (z / (1 + z)) ^ 2 := by ring

/-- Cardinality squared as the number of ordered occupied vertex pairs. -/
theorem card_sq_eq_sum_pair_indicators [DecidableEq V] (I : Finset V) :
    (I.card : ℝ) ^ 2 =
      ∑ v : V, ∑ w : V, if v ∈ I ∧ w ∈ I then (1 : ℝ) else 0 := by
  classical
  have hcount : (∑ v : V, if v ∈ I then (1 : ℝ) else 0) = I.card := by
    rw [← Finset.sum_filter]
    simp
  symm
  calc
    (∑ v : V, ∑ w : V, if v ∈ I ∧ w ∈ I then (1 : ℝ) else 0) =
        ∑ v : V, (if v ∈ I then (1 : ℝ) else 0) *
          ∑ w : V, if w ∈ I then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v ∈ I <;> simp [hv]
    _ = (∑ v : V, if v ∈ I then (1 : ℝ) else 0) *
          (∑ w : V, if w ∈ I then (1 : ℝ) else 0) := by
      rw [Finset.sum_mul]
    _ = (I.card : ℝ) ^ 2 := by rw [hcount]; ring

/-- Actual hard-core second moment is at most `t+t²`, where `t=np`. -/
theorem hardCoreLaw_secondMoment_le_t_add_sq [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    let p := z / (1 + z)
    let t := (Fintype.card V : ℝ) * p
    (hardCoreLaw G z hz).secondMoment ≤ t + t ^ 2 := by
  classical
  let μ := hardCoreLaw G z hz
  let p : ℝ := z / (1 + z)
  let n : ℝ := Fintype.card V
  let t : ℝ := n * p
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hpair : ∀ v w : V,
      (∑ I : IndepFinset G, μ.probability I *
          (if v ∈ I.val ∧ w ∈ I.val then (1 : ℝ) else 0)) ≤
        p ^ 2 + if v = w then p else 0 := by
    intro v w
    by_cases hvw : v = w
    · subst w
      calc
        (∑ I : IndepFinset G, μ.probability I *
            (if v ∈ I.val ∧ v ∈ I.val then (1 : ℝ) else 0)) =
            ∑ I ∈ Finset.univ.filter
              (fun I : IndepFinset G => v ∈ I.val), μ.probability I := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro I _
              by_cases hI : v ∈ I.val <;> simp [hI]
        _ ≤ p := hardCoreLaw_vertex_marginal_le G z hz v
        _ ≤ p ^ 2 + (if v = v then p else 0) := by
          simp
          positivity
    · calc
        (∑ I : IndepFinset G, μ.probability I *
            (if v ∈ I.val ∧ w ∈ I.val then (1 : ℝ) else 0)) =
            ∑ I ∈ Finset.univ.filter
              (fun I : IndepFinset G => v ∈ I.val ∧ w ∈ I.val),
                μ.probability I := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro I _
              by_cases hI : v ∈ I.val ∧ w ∈ I.val <;> simp [hI]
        _ ≤ p ^ 2 := hardCoreLaw_pair_marginal_le G z hz v w hvw
        _ = p ^ 2 + (if v = w then p else 0) := by simp [hvw]
  have hdiag : (∑ v : V, ∑ w : V, if v = w then p else 0) = n * p := by
    calc
      (∑ v : V, ∑ w : V, if v = w then p else 0) = ∑ v : V, p := by
        apply Finset.sum_congr rfl
        intro v _
        rw [Finset.sum_eq_single v]
        · simp
        · intro b _ hb
          simp [show v ≠ b from fun h => hb h.symm]
        · intro hv
          exact (hv (Finset.mem_univ v)).elim
      _ = n * p := by simp [n]
  change (∑ I : IndepFinset G, μ.probability I * (I.val.card : ℝ) ^ 2) ≤
    t + t ^ 2
  calc
    (∑ I : IndepFinset G, μ.probability I * (I.val.card : ℝ) ^ 2) =
      ∑ I : IndepFinset G, μ.probability I *
        ∑ v : V, ∑ w : V,
          if v ∈ I.val ∧ w ∈ I.val then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro I _
      rw [card_sq_eq_sum_pair_indicators I.val]
    _ = ∑ v : V, ∑ w : V, ∑ I : IndepFinset G,
        μ.probability I *
          (if v ∈ I.val ∧ w ∈ I.val then (1 : ℝ) else 0) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
    _ ≤ ∑ v : V, ∑ w : V, (p ^ 2 + if v = w then p else 0) := by
      exact Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun w _ => hpair v w))
    _ = t + t ^ 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [hdiag]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [t, n]
      push_cast
      ring

/-- Actual hard-core variance is controlled by the same `t+t²` bound. -/
theorem hardCoreLaw_variance_le_t_add_sq [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    let p := z / (1 + z)
    let t := (Fintype.card V : ℝ) * p
    (hardCoreLaw G z hz).variance ≤ t + t ^ 2 := by
  let μ := hardCoreLaw G z hz
  let p := z / (1 + z)
  let t := (Fintype.card V : ℝ) * p
  have hsecond := hardCoreLaw_secondMoment_le_t_add_sq G z hz
  change μ.variance ≤ t + t ^ 2
  change μ.secondMoment ≤ t + t ^ 2 at hsecond
  calc
    μ.variance = μ.secondMoment - μ.mean ^ 2 :=
      FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean μ
    _ ≤ μ.secondMoment := by nlinarith [sq_nonneg μ.mean]
    _ ≤ t + t ^ 2 := hsecond

/-- The manuscript comparison with the actual hard-core variance and the
explicit parameter `t = |V|p`; no variance premise remains. -/
theorem hardCoreLaw_min_t_one_ge_half_min_variance_one [DecidableEq V]
    (G : SimpleGraph V) (z : ℝ) (hz : 0 < z) :
    let p := z / (1 + z)
    let t := (Fintype.card V : ℝ) * p
    min t 1 ≥ min (hardCoreLaw G z hz).variance 1 / 2 := by
  let p := z / (1 + z)
  let t := (Fintype.card V : ℝ) * p
  have ht : 0 ≤ t := by dsimp [t, p]; positivity
  have hvar := hardCoreLaw_variance_le_t_add_sq G z hz
  change (hardCoreLaw G z hz).variance ≤ t + t ^ 2 at hvar
  exact min_t_one_ge_half_min_variance_one ht hvar

/-- Every occupied vertex has no occupied neighbor. -/
theorem occupied_disjoint_neighbor [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : IndepFinset G)
    {v : V} (hv : v ∈ I.val) :
    Disjoint I.val (G.neighborFinset v) := by
  rw [Finset.disjoint_left]
  intro w hwI hwN
  have hadj : G.Adj v w := (SimpleGraph.mem_neighborFinset G v w).mp hwN
  have hvw : v ≠ w := fun h => by subst w; exact G.loopless.irrefl v hadj
  exact I.property hv hwI hvw hadj

/-- On a nonempty forest, at least one vertex is available on one of the two
color classes, for every independent configuration.  This is the pointwise
input to the high-activity two-side averaging argument. -/
theorem one_le_available_left_add_right [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    [Nonempty V] (I : IndepFinset G) :
    1 ≤ availableCount G (leftSide G hG) I +
      availableCount G (rightSide G hG) I := by
  classical
  have hproper : unavailableVertices G I ⊂ (Finset.univ : Finset V) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    by_cases hI : I.val.Nonempty
    · obtain ⟨v, hv⟩ := hI
      have hvU : v ∈ unavailableVertices G I := by
        rw [heq]
        simp
      exact (Finset.mem_filter.mp hvU).2 (occupied_disjoint_neighbor G I hv)
    · let v : V := Classical.choice (inferInstance : Nonempty V)
      have hvU : v ∈ unavailableVertices G I := by
        rw [heq]
        simp
      apply (Finset.mem_filter.mp hvU).2
      rw [Finset.disjoint_left]
      intro w hw _
      exact hI ⟨w, hw⟩
  have hU : (unavailableVertices G I).card < Fintype.card V := by
    simpa using Finset.card_lt_card hproper
  have hpart := available_left_add_right_add_unavailable G hG I
  omega

/-- Elementary numerical form of the two-side averaging step. -/
theorem pow_add_le_one_add_of_one_le_add
    {r : ℝ} {a b : ℕ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hab : 1 ≤ a + b) : r ^ a + r ^ b ≤ 1 + r := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst a
    simp only [pow_zero]
    have hbpos : 0 < b := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hbpos)
    rw [pow_succ]
    have hbpow : r ^ k * r ≤ r := by
      calc
        r ^ k * r ≤ 1 * r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1) hr0
        _ = r := one_mul r
    linarith
  · have ha' : r ^ a ≤ r := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
      rw [pow_succ]
      calc
        r ^ k * r ≤ 1 * r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr0 hr1) hr0
        _ = r := one_mul r
    have hb' : r ^ b ≤ 1 := pow_le_one₀ hr0 hr1
    linarith

/-- Averaging the pointwise two-side availability inequality against any
finite probability law.  Applied to `hardCoreLaw`, this is precisely the
high-`p` availability step before the Bernoulli radius estimate. -/
theorem two_side_average_pow_available
    {Ω : Type*} [Fintype Ω] (L : FiniteLatticeLaw Ω)
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) [Nonempty V] (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (X : Ω → IndepFinset G) :
    (∑ ω, L.probability ω * r ^ availableCount G (leftSide G hG) (X ω)) +
      (∑ ω, L.probability ω * r ^ availableCount G (rightSide G hG) (X ω)) ≤
        1 + r := by
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ ω : Ω, L.probability ω * (1 + r) := by
      apply Finset.sum_le_sum
      intro ω _
      simpa [mul_add] using mul_le_mul_of_nonneg_left
        (pow_add_le_one_add_of_one_le_add hr0 hr1
          (one_le_available_left_add_right G hG (X ω)))
        (L.probability_nonneg ω)
    _ = 1 + r := by
      rw [← Finset.sum_mul, L.probability_sum, one_mul]

/-- The complete high-activity branch of A.19 at the characteristic-modulus
level.  This combines the two exact A.20 bounds with pointwise two-side
availability; no probabilistic surrogate is assumed. -/
theorem SimpleGraph.IsAcyclic.high_p_characteristic_gap [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    [Nonempty V] (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hp : (1 / 8 : ℝ) ≤ z / (1 + z)) :
    1 - ‖(hardCoreLaw G z hz).characteristic θ‖ ≥
      (1 / (8 * (1 + Z))) * Real.sin (θ / 2) ^ 2 := by
  let μ := hardCoreLaw G z hz
  let r := bernoulliRadius z θ
  let q := z / (1 + z) ^ 2
  let h := Real.sin (θ / 2) ^ 2
  have hh : 0 ≤ h := sq_nonneg _
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r, bernoulliRadius]
    apply div_nonneg (norm_nonneg _)
    linarith
  have hrlinear : r ≤ 1 - 2 * q * h := by
    simpa [r, q, h] using bernoulliRadius_le_one_sub z θ hz
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hq hh]
  have hleft := hardCoreLaw_characteristic_le_expected_radius_available
    G (leftSide G hG) (leftSide_independent G hG) z θ hz
  have hright := hardCoreLaw_characteristic_le_expected_radius_available
    G (rightSide G hG) (rightSide_independent G hG) z θ hz
  have havg := two_side_average_pow_available μ G hG r hr0 hr1
    (fun I : IndepFinset G => I)
  change ‖μ.characteristic θ‖ ≤
      ∑ I : IndepFinset G, μ.probability I *
        r ^ availableCount G (leftSide G hG) I at hleft
  change ‖μ.characteristic θ‖ ≤
      ∑ I : IndepFinset G, μ.probability I *
        r ^ availableCount G (rightSide G hG) I at hright
  have htwo : 2 * ‖μ.characteristic θ‖ ≤ 1 + r := by linarith
  have hgapq : q * h ≤ 1 - ‖μ.characteristic θ‖ := by linarith
  have hqbound : 1 / (8 * (1 + Z)) ≤ q := by
    dsimp [q]
    calc
      1 / (8 * (1 + Z)) = (1 / 8) / (1 + Z) := by rw [div_div]
      _ ≤ (1 / 8) / (1 + z) := by gcongr
      _ ≤ (z / (1 + z)) / (1 + z) := by gcongr
      _ = z / (1 + z) ^ 2 := by
        field_simp
  change 1 - ‖μ.characteristic θ‖ ≥ _
  calc
    (1 / (8 * (1 + Z))) * Real.sin (θ / 2) ^ 2 ≤ q * h := by
      exact mul_le_mul_of_nonneg_right hqbound hh
    _ ≤ 1 - ‖μ.characteristic θ‖ := hgapq

/-- Every unavailable vertex is charged to an occupied neighboring vertex. -/
theorem unavailableVertices_card_le_sum_degrees [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (I : IndepFinset G) :
    (unavailableVertices G I).card ≤ ∑ v ∈ I.val, G.degree v := by
  classical
  have hsub : unavailableVertices G I ⊆
      I.val.biUnion (fun v => G.neighborFinset v) := by
    intro v hv
    have hv' : ¬ Disjoint I.val (G.neighborFinset v) :=
      (Finset.mem_filter.mp hv).2
    obtain ⟨w, hwI, hwv⟩ := Finset.not_disjoint_iff.mp hv'
    apply Finset.mem_biUnion.mpr
    refine ⟨w, hwI, ?_⟩
    rw [G.mem_neighborFinset] at hwv ⊢
    exact G.symm hwv
  calc
    (unavailableVertices G I).card ≤
        (I.val.biUnion (fun v => G.neighborFinset v)).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ I.val, (G.neighborFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ I.val, G.degree v := by simp

/-- The exact forest estimate `E U ≤ 2 p n` from (A.22), where `U` is the
number of vertices having an occupied neighbor and `p = z/(1+z)`.  The proof
uses the one-site marginal bound and the forest edge bound. -/
theorem SimpleGraph.IsAcyclic.expected_unavailable_le [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    (z : ℝ) (hz : 0 < z) :
    (∑ I : IndepFinset G, (hardCoreLaw G z hz).probability I *
      ((unavailableVertices G I).card : ℝ)) ≤
        2 * (z / (1 + z)) * (Fintype.card V : ℝ) := by
  classical
  let μ := hardCoreLaw G z hz
  let p := z / (1 + z)
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hpoint : ∀ I : IndepFinset G,
      μ.probability I * ((unavailableVertices G I).card : ℝ) ≤
        μ.probability I * ∑ v ∈ I.val, (G.degree v : ℝ) := by
    intro I
    apply mul_le_mul_of_nonneg_left _ (μ.probability_nonneg I)
    exact_mod_cast unavailableVertices_card_le_sum_degrees G I
  have hindicator : ∀ I : IndepFinset G,
      (∑ v ∈ I.val, μ.probability I * (G.degree v : ℝ)) =
        ∑ v : V, if v ∈ I.val then
          μ.probability I * (G.degree v : ℝ) else 0 := by
    intro I
    rw [← Finset.sum_filter]
    simp
  calc
    (∑ I : IndepFinset G, μ.probability I *
      ((unavailableVertices G I).card : ℝ)) ≤
        ∑ I : IndepFinset G, μ.probability I *
          ∑ v ∈ I.val, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑ I : IndepFinset G, ∑ v : V,
          if v ∈ I.val then μ.probability I * (G.degree v : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [Finset.mul_sum]
      exact hindicator I
    _ = ∑ v : V, ∑ I : IndepFinset G,
          if v ∈ I.val then μ.probability I * (G.degree v : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ v : V, (G.degree v : ℝ) *
          ∑ I ∈ Finset.univ.filter
            (fun I : IndepFinset G => v ∈ I.val), μ.probability I := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro I hI
      by_cases h : v ∈ I.val <;> simp [h, mul_comm]
    _ ≤ ∑ v : V, (G.degree v : ℝ) * p := by
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left
        (hardCoreLaw_vertex_marginal_le G z hz v) (Nat.cast_nonneg _)
    _ = p * (2 * (G.edgeFinset.card : ℝ)) := by
      rw [← Finset.sum_mul, ← Nat.cast_sum,
        SimpleGraph.sum_degrees_eq_twice_card_edges]
      push_cast
      ring
    _ ≤ p * (2 * (Fintype.card V : ℝ)) := by
      gcongr
      exact_mod_cast
        (SimpleGraph.IsAcyclic.card_edgeFinset_le_card (G := G) hG)
    _ = 2 * (z / (1 + z)) * (Fintype.card V : ℝ) := by
      dsimp [p]
      ring

/-- The low-activity Markov step in (A.22), still for the actual hard-core
law.  With probability at least one half, at least half of all vertices are
available across the two forest color classes. -/
theorem SimpleGraph.IsAcyclic.low_p_total_availability [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    [Nonempty V] (z : ℝ) (hz : 0 < z)
    (hp : z / (1 + z) ≤ (1 / 8 : ℝ)) :
    let μ := hardCoreLaw G z hz
    μ.eventMass (fun I : IndepFinset G =>
      Fintype.card V ≤ 2 * (availableCount G (leftSide G hG) I +
        availableCount G (rightSide G hG) I)) ≥ (1 / 2 : ℝ) := by
  classical
  let μ := hardCoreLaw G z hz
  let n : ℕ := Fintype.card V
  let U : IndepFinset G → ℕ := fun I => (unavailableVertices G I).card
  let A : IndepFinset G → ℕ := fun I =>
    availableCount G (leftSide G hG) I +
      availableCount G (rightSide G hG) I
  have hn : 0 < n := Fintype.card_pos
  have hEU : (∑ I : IndepFinset G, μ.probability I * (U I : ℝ)) ≤
      (n : ℝ) / 4 := by
    calc
      _ ≤ 2 * (z / (1 + z)) * (n : ℝ) :=
        SimpleGraph.IsAcyclic.expected_unavailable_le (G := G) hG z hz
      _ ≤ (n : ℝ) / 4 := by
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
  let Bad : IndepFinset G → Prop := fun I => n < 2 * U I
  have hscaled : (n : ℝ) * μ.eventMass Bad ≤
      2 * ∑ I : IndepFinset G, μ.probability I * (U I : ℝ) := by
    rw [μ.eventMass_eq_sum_ite Bad, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I _
    by_cases hbad : Bad I
    · simp only [hbad, if_true]
      have hcast : (n : ℝ) ≤ 2 * (U I : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hbad)
      have hprob := μ.probability_nonneg I
      nlinarith
    · simp only [hbad, if_false, mul_zero]
      exact mul_nonneg (by norm_num)
        (mul_nonneg (μ.probability_nonneg I) (Nat.cast_nonneg (U I)))
  have hbad : μ.eventMass Bad ≤ (1 / 2 : ℝ) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmass0 := μ.eventMass_nonneg Bad
    nlinarith
  let Good : IndepFinset G → Prop := fun I => ¬ Bad I
  have hgood : (1 / 2 : ℝ) ≤ μ.eventMass Good := by
    have hsplit := μ.eventMass_compl Bad
    change μ.eventMass Bad + μ.eventMass Good = 1 at hsplit
    linarith
  have hmono : μ.eventMass Good ≤ μ.eventMass (fun I : IndepFinset G => n ≤ 2 * A I) := by
    apply μ.eventMass_mono
    intro I hI
    have hpart := available_left_add_right_add_unavailable G hG I
    change A I + U I = n at hpart
    change ¬ n < 2 * U I at hI
    omega
  exact hgood.trans hmono

/-- Pigeonholing the preceding Markov event gives one fixed bipartition side
with probability at least `1/4` of having at least `n/4` available vertices.
This is the exact low-`p` availability statement used before (A.23). -/
theorem SimpleGraph.IsAcyclic.low_p_one_side_availability [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    [Nonempty V] (z : ℝ) (hz : 0 < z)
    (hp : z / (1 + z) ≤ (1 / 8 : ℝ)) :
    let μ := hardCoreLaw G z hz
    ∃ S : Finset V,
      (S = leftSide G hG ∨ S = rightSide G hG) ∧
      μ.eventMass (fun I : IndepFinset G =>
        Fintype.card V ≤ 4 * availableCount G S I) ≥ (1 / 4 : ℝ) := by
  classical
  let μ := hardCoreLaw G z hz
  let n : ℕ := Fintype.card V
  let PL : IndepFinset G → Prop := fun I =>
    n ≤ 4 * availableCount G (leftSide G hG) I
  let PR : IndepFinset G → Prop := fun I =>
    n ≤ 4 * availableCount G (rightSide G hG) I
  let P : IndepFinset G → Prop := fun I =>
    n ≤ 2 * (availableCount G (leftSide G hG) I +
      availableCount G (rightSide G hG) I)
  have hP : (1 / 2 : ℝ) ≤ μ.eventMass P :=
    SimpleGraph.IsAcyclic.low_p_total_availability (G := G) hG z hz hp
  have hPor : μ.eventMass P ≤ μ.eventMass (fun I => PL I ∨ PR I) := by
    apply μ.eventMass_mono
    intro I hI
    change n ≤ 2 * (_ + _) at hI
    change n ≤ 4 * _ ∨ n ≤ 4 * _
    omega
  have hunion : μ.eventMass (fun I => PL I ∨ PR I) ≤
      μ.eventMass PL + μ.eventMass PR := μ.eventMass_or_le PL PR
  by_cases hleft : (1 / 4 : ℝ) ≤ μ.eventMass PL
  · exact ⟨leftSide G hG, Or.inl rfl, hleft⟩
  · have hright : (1 / 4 : ℝ) ≤ μ.eventMass PR := by
      have := hP.trans (hPor.trans hunion)
      linarith
    exact ⟨rightSide G hG, Or.inr rfl, hright⟩

/-- The complete low-activity branch at the characteristic-modulus level.
It exposes `t = n p` and gives exactly the pre-concavity estimate in (A.23). -/
theorem SimpleGraph.IsAcyclic.low_p_characteristic_gap_t [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsAcyclic)
    [Nonempty V] (z θ : ℝ) (hz : 0 < z)
    (hp : z / (1 + z) ≤ (1 / 8 : ℝ)) :
    let p := z / (1 + z)
    let t := (Fintype.card V : ℝ) * p
    let h := Real.sin (θ / 2) ^ 2
    1 - ‖(hardCoreLaw G z hz).characteristic θ‖ ≥
      (1 / 4 : ℝ) * (1 - Real.exp (-(7 / 16 : ℝ) * t * h)) := by
  classical
  let μ := hardCoreLaw G z hz
  let n : ℕ := Fintype.card V
  let p : ℝ := z / (1 + z)
  let q : ℝ := z / (1 + z) ^ 2
  let t : ℝ := (n : ℝ) * p
  let h : ℝ := Real.sin (θ / 2) ^ 2
  let r : ℝ := bernoulliRadius z θ
  let c : ℝ := Real.exp (-(7 / 16 : ℝ) * t * h)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hh : 0 ≤ h := sq_nonneg _
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r, bernoulliRadius]
    apply div_nonneg (norm_nonneg _)
    linarith
  have hrlinear : r ≤ 1 - 2 * q * h := by
    simpa [r, q, h] using bernoulliRadius_le_one_sub z θ hz
  have hr1 : r ≤ 1 := by nlinarith [mul_nonneg hq0 hh]
  have hqeq : q = p * (1 - p) := by
    dsimp [q, p]
    have hden : 1 + z ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring
  have hqbound : (7 / 8 : ℝ) * p ≤ q := by
    rw [hqeq]
    have hone : (7 / 8 : ℝ) ≤ 1 - p := by linarith
    calc
      (7 / 8 : ℝ) * p = p * (7 / 8 : ℝ) := by ring
      _ ≤ p * (1 - p) := mul_le_mul_of_nonneg_left hone hp0
  obtain ⟨S, hSside, hmass⟩ :=
    SimpleGraph.IsAcyclic.low_p_one_side_availability (G := G) hG z hz hp
  have hSindep : G.IsIndepSet (S : Set V) := by
    rcases hSside with hS | hS
    · simpa [hS] using leftSide_independent G hG
    · simpa [hS] using rightSide_independent G hG
  have hcf := hardCoreLaw_characteristic_le_expected_radius_available
    G S hSindep z θ hz
  change ‖μ.characteristic θ‖ ≤
    μ.expect (fun I : IndepFinset G => r ^ availableCount G S I) at hcf
  let P : IndepFinset G → Prop := fun I =>
    n ≤ 4 * availableCount G S I
  have hmassP : (1 / 4 : ℝ) ≤ μ.eventMass P := by
    simpa [P, n, μ] using hmass
  have hf_one : ∀ I : IndepFinset G,
      r ^ availableCount G S I ≤ 1 := by
    intro I
    exact pow_le_one₀ hr0 hr1
  have hrexp : r ≤ Real.exp (-2 * q * h) := by
    simpa [r, q, h] using bernoulliRadius_le_exp z θ hz
  have hf_event : ∀ I : IndepFinset G, P I →
      r ^ availableCount G S I ≤ c := by
    intro I hPI
    let A : ℕ := availableCount G S I
    have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hnA : (n : ℝ) / 4 ≤ (A : ℝ) := by
      have hcast : (n : ℝ) ≤ 4 * (A : ℝ) := by
        exact_mod_cast hPI
      linarith
    have hcoef : 0 ≤ (7 / 8 : ℝ) * p := mul_nonneg (by norm_num) hp0
    have hqa : (7 / 32 : ℝ) * (n : ℝ) * p ≤ q * (A : ℝ) := by
      calc
        (7 / 32 : ℝ) * (n : ℝ) * p =
            ((7 / 8 : ℝ) * p) * ((n : ℝ) / 4) := by ring
        _ ≤ ((7 / 8 : ℝ) * p) * (A : ℝ) :=
          mul_le_mul_of_nonneg_left hnA hcoef
        _ ≤ q * (A : ℝ) := by
          exact mul_le_mul_of_nonneg_right hqbound hA0
    calc
      r ^ availableCount G S I ≤ Real.exp (-2 * q * h) ^ A := by
        exact pow_le_pow_left₀ hr0 hrexp A
      _ = Real.exp ((A : ℝ) * (-2 * q * h)) := by
        exact (Real.exp_nat_mul _ A).symm
      _ ≤ c := by
        apply Real.exp_le_exp.mpr
        dsimp [c, t]
        have hscaled := mul_le_mul_of_nonneg_right hqa hh
        nlinarith
  have hc : c ≤ 1 := by
    have hexp : Real.exp (-(7 / 16 : ℝ) * t * h) ≤ Real.exp 0 := by
      apply Real.exp_le_exp.mpr
      have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg n) hp0
      nlinarith [mul_nonneg ht0 hh]
    simpa [c] using hexp
  have hexpect := μ.expect_le_three_quarters_add_quarter
    (fun I : IndepFinset G => r ^ availableCount G S I) P c
    hf_one hf_event hc hmassP
  change 1 - ‖μ.characteristic θ‖ ≥ _
  change 1 - ‖μ.characteristic θ‖ ≥ (1 / 4 : ℝ) * (1 - c)
  linarith

/-- Chord inequality for `1-exp(-7x/16)` on the unit interval. -/
theorem one_sub_exp_neg_seven_sixteenths_ge
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - Real.exp (-(7 / 16 : ℝ) * x)) ≥
      (1 - Real.exp (-(7 / 16 : ℝ))) * x := by
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-(7 / 16 : ℝ)))
    (sub_nonneg.mpr hx1) hx0 (by ring : (1 - x) + x = 1)
  norm_num only [smul_eq_mul, Real.exp_zero, mul_zero, add_zero] at hconv
  have harg : x * (-(7 / 16 : ℝ)) = -(7 / 16 : ℝ) * x := by ring
  rw [harg] at hconv
  simp only [zero_add] at hconv
  nlinarith

/-- The exact manuscript scalar concavity estimate, including the `min(t,1)`
factor and the coefficient `1-exp(-7/16)`. -/
theorem one_sub_exp_neg_seven_sixteenths_mul_ge
    (t h : ℝ) (ht : 0 ≤ t) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    1 - Real.exp (-(7 / 16 : ℝ) * t * h) ≥
      (1 - Real.exp (-(7 / 16 : ℝ))) * min t 1 * h := by
  by_cases ht1 : t ≤ 1
  · rw [min_eq_left ht1]
    have hx0 : 0 ≤ t * h := mul_nonneg ht hh0
    have hx1 : t * h ≤ 1 := by
      have := mul_le_mul ht1 hh1 hh0 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    have hc := one_sub_exp_neg_seven_sixteenths_ge (t * h) hx0 hx1
    convert hc using 1 <;> ring
  · have h1t : 1 ≤ t := le_of_not_ge ht1
    have hmono : Real.exp (-(7 / 16 : ℝ) * t * h) ≤
        Real.exp (-(7 / 16 : ℝ) * h) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right h1t hh0]
    have hc := one_sub_exp_neg_seven_sixteenths_ge h hh0 hh1
    rw [min_eq_right h1t]
    nlinarith

/-- Exact uniform modulus gap on a nonempty finite forest, after combining the
high- and low-activity branches with the actual-law variance comparison. -/
theorem SimpleGraph.IsAcyclic.uniform_characteristic_modulus_gap_nonempty
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) [Nonempty V]
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    1 - (hardCoreLaw G z hz).characteristicModulus θ ≥
      uniformGapConstant Z * min (hardCoreLaw G z hz).variance 1 *
        Real.sin (θ / 2) ^ 2 := by
  let μ := hardCoreLaw G z hz
  let p : ℝ := z / (1 + z)
  let t : ℝ := (Fintype.card V : ℝ) * p
  let h : ℝ := Real.sin (θ / 2) ^ 2
  have hh0 : 0 ≤ h := sq_nonneg _
  have hh1 : h ≤ 1 := by
    dsimp [h]
    nlinarith [Real.neg_one_le_sin (θ / 2), Real.sin_le_one (θ / 2)]
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have ht0 : 0 ≤ t := mul_nonneg (Nat.cast_nonneg _) hp0
  have hv0 : 0 ≤ min μ.variance 1 :=
    le_min (FiniteLatticeLaw.variance_nonneg μ) (by norm_num)
  have hv1 : min μ.variance 1 ≤ 1 := min_le_right _ _
  have hk0 : 0 ≤ uniformGapConstant Z := uniformGapConstant_nonneg hZ.le
  have hmod : μ.characteristicModulus θ = ‖μ.characteristic θ‖ := by
    rw [FiniteLatticeLaw.characteristicModulus,
      FiniteLatticeLaw.norm_centeredCharacteristic_eq]
  by_cases hp : p ≤ (1 / 8 : ℝ)
  · have hlow := SimpleGraph.IsAcyclic.low_p_characteristic_gap_t
      G hG z θ hz hp
    change 1 - ‖μ.characteristic θ‖ ≥
      (1 / 4 : ℝ) *
        (1 - Real.exp (-(7 / 16 : ℝ) * t * h)) at hlow
    have hconc := one_sub_exp_neg_seven_sixteenths_mul_ge t h ht0 hh0 hh1
    have hmin := hardCoreLaw_min_t_one_ge_half_min_variance_one G z hz
    change min t 1 ≥ min μ.variance 1 / 2 at hmin
    have hc0 : 0 ≤ 1 - Real.exp (-(7 / 16 : ℝ)) := by
      exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
    have hk : uniformGapConstant Z ≤
        (1 - Real.exp (-(7 / 16 : ℝ))) / 8 := by
      exact min_le_left _ _
    rw [hmod]
    calc
      uniformGapConstant Z * min μ.variance 1 * h ≤
          ((1 - Real.exp (-(7 / 16 : ℝ))) / 8) *
            min μ.variance 1 * h := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hk hv0) hh0
      _ ≤ (1 / 4 : ℝ) *
          ((1 - Real.exp (-(7 / 16 : ℝ))) * min t 1 * h) := by
        have hm := mul_le_mul_of_nonneg_left hmin hc0
        nlinarith [mul_le_mul_of_nonneg_right hm hh0]
      _ ≤ (1 / 4 : ℝ) *
          (1 - Real.exp (-(7 / 16 : ℝ) * t * h)) := by
        exact mul_le_mul_of_nonneg_left hconc (by norm_num)
      _ ≤ 1 - ‖μ.characteristic θ‖ := hlow
  · have hp' : (1 / 8 : ℝ) ≤ p := le_of_not_ge hp
    have hhigh := SimpleGraph.IsAcyclic.high_p_characteristic_gap
      G hG Z z θ hZ hz hzZ hp'
    change 1 - ‖μ.characteristic θ‖ ≥
      (1 / (8 * (1 + Z))) * h at hhigh
    have hk : uniformGapConstant Z ≤ 1 / (8 * (1 + Z)) :=
      min_le_right _ _
    have hc0 : 0 ≤ 1 / (8 * (1 + Z)) := by positivity
    rw [hmod]
    calc
      uniformGapConstant Z * min μ.variance 1 * h ≤
          (1 / (8 * (1 + Z))) * min μ.variance 1 * h := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hk hv0) hh0
      _ ≤ (1 / (8 * (1 + Z))) * h := by
        nlinarith [mul_le_mul_of_nonneg_left hv1 hc0,
          mul_nonneg hc0 hh0]
      _ ≤ 1 - ‖μ.characteristic θ‖ := hhigh

/-- Exact A.19 for a nonempty finite forest, in the manuscript's extended-real
logarithmic-loss formulation. -/
theorem SimpleGraph.IsAcyclic.uniformCharacteristicFunctionGap_nonempty
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) [Nonempty V]
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    ((uniformGapConstant Z * min (hardCoreLaw G z hz).variance 1 *
      Real.sin (θ / 2) ^ 2 : ℝ) : EReal) ≤
        (hardCoreLaw G z hz).logarithmicLoss θ := by
  let μ := hardCoreLaw G z hz
  have hgap := SimpleGraph.IsAcyclic.uniform_characteristic_modulus_gap_nonempty
    G hG Z z θ hZ hz hzZ hθ
  change 1 - μ.characteristicModulus θ ≥
    uniformGapConstant Z * min μ.variance 1 * Real.sin (θ / 2) ^ 2 at hgap
  calc
    ((uniformGapConstant Z * min μ.variance 1 *
        Real.sin (θ / 2) ^ 2 : ℝ) : EReal) ≤
        ((1 - μ.characteristicModulus θ : ℝ) : EReal) := by
      exact_mod_cast hgap
    _ ≤ μ.logarithmicLoss θ :=
      FiniteLatticeLaw.one_sub_characteristicModulus_le_logarithmicLoss μ θ

/-- **Lemma A.4 / equation (A.19), exact finite form.**  For the actual
hard-core law on every finite forest (including the empty forest), uniformly
for `0 < z ≤ Z` and `|θ| ≤ π`, the centered logarithmic characteristic loss
has the manuscript lower bound with
`κ_Z = min ((1-exp(-7/16))/8) (1/(8(1+Z)))`.

The proof explicitly splits the empty vertex type.  In the empty branch the
actual hard-core variance is zero; in the nonempty branch it invokes the two
proved activity regimes and the exact actual-law variance comparison. -/
theorem SimpleGraph.IsAcyclic.uniformCharacteristicFunctionGap
    (G : SimpleGraph V) (hG : G.IsAcyclic)
    (Z z θ : ℝ) (hZ : 0 < Z) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) :
    ((uniformGapConstant Z * min (hardCoreLaw G z hz).variance 1 *
      Real.sin (θ / 2) ^ 2 : ℝ) : EReal) ≤
        (hardCoreLaw G z hz).logarithmicLoss θ := by
  classical
  let μ := hardCoreLaw G z hz
  cases isEmpty_or_nonempty V with
  | inr hne =>
      letI : Nonempty V := hne
      exact SimpleGraph.IsAcyclic.uniformCharacteristicFunctionGap_nonempty
        G hG Z z θ hZ hz hzZ hθ
  | inl hempty =>
      letI : IsEmpty V := hempty
      have hn : Fintype.card V = 0 := Fintype.card_eq_zero
      have hvarle := hardCoreLaw_variance_le_t_add_sq G z hz
      change μ.variance ≤
        (Fintype.card V : ℝ) * (z / (1 + z)) +
          ((Fintype.card V : ℝ) * (z / (1 + z))) ^ 2 at hvarle
      simp [hn] at hvarle
      have hvar0 : μ.variance = 0 :=
        le_antisymm hvarle (FiniteLatticeLaw.variance_nonneg μ)
      have hloss :=
        FiniteLatticeLaw.one_sub_characteristicModulus_le_logarithmicLoss μ θ
      have hmodle := FiniteLatticeLaw.characteristicModulus_le_one μ θ
      change ((uniformGapConstant Z * min μ.variance 1 *
        Real.sin (θ / 2) ^ 2 : ℝ) : EReal) ≤ μ.logarithmicLoss θ
      rw [hvar0]
      norm_num only [min_eq_left (by norm_num : (0 : ℝ) ≤ 1), mul_zero,
        zero_mul, EReal.coe_zero]
      exact (show ((0 : ℝ) : EReal) ≤
          ((1 - μ.characteristicModulus θ : ℝ) : EReal) by
            exact_mod_cast sub_nonneg.mpr hmodle).trans hloss

end
end Forest
end Erdos993
