import Erdos993.Forest.PathVarianceBound
import Erdos993.Forest.IndependentComponentFourier

/-!
# Two-state transfer algebra for Appendix A.8

Graph-free scalar and complex lemmas used by the genuine decorated-path
transfer contraction.  The encoding follows (A.44): a row `(x,y)` is updated
by

`(a * (q*x+y), b*phase*c*x)`.

In particular the first coordinate is the free/vacant mixture and the second
coordinate records the occupied contribution.  All zero cases are built into
the norm formulation; no argument of a zero complex number is chosen.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators

/-- A row vector in the two-state transfer calculation. -/
structure ComplexRow where
  fst : ℂ
  snd : ℂ

namespace ComplexRow

/-- The manuscript's `ℓ¹` row norm `N = |x| + |y|`. -/
def normOne (r : ComplexRow) : ℝ := ‖r.fst‖ + ‖r.snd‖

@[simp] theorem normOne_zero : (ComplexRow.mk 0 0).normOne = 0 := by
  simp [normOne]

/-- Pairing of a transfer row with a bottom vector. -/
def pair (r f : ComplexRow) : ℂ := r.fst * f.fst + r.snd * f.snd

/-- Coordinatewise bounded bottom vectors pair against a row by at most its
`ℓ¹` norm.  This includes every zero-coordinate case. -/
theorem norm_pair_le_normOne
    (r f : ComplexRow) (hf : ‖f.fst‖ ≤ 1) (hs : ‖f.snd‖ ≤ 1) :
    ‖r.pair f‖ ≤ r.normOne := by
  calc
    ‖r.pair f‖ ≤ ‖r.fst * f.fst‖ + ‖r.snd * f.snd‖ := norm_add_le _ _
    _ = ‖r.fst‖ * ‖f.fst‖ + ‖r.snd‖ * ‖f.snd‖ := by rw [norm_mul, norm_mul]
    _ ≤ ‖r.fst‖ * 1 + ‖r.snd‖ * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
    _ = r.normOne := by simp [normOne]

end ComplexRow

/-- One actual-form two-state transfer coefficient, matching equation (A.44).
`q,b` are the root vacancy/occupation probabilities, `a` the normalized side
forest characteristic, `c` the product of normalized root-deleted side
characteristics, and `phase = exp(iθ)`. -/
structure TransferCoefficient where
  q : ℝ
  b : ℝ
  a : ℂ
  c : ℂ
  phase : ℂ

namespace TransferCoefficient

/-- The hypotheses enjoyed by every genuine hard-core transfer coefficient. -/
structure Admissible (K : TransferCoefficient) : Prop where
  q_nonneg : 0 ≤ K.q
  b_nonneg : 0 ≤ K.b
  q_add_b : K.q + K.b = 1
  norm_phase : ‖K.phase‖ = 1
  norm_a_le_one : ‖K.a‖ ≤ 1
  norm_c_le_one : ‖K.c‖ ≤ 1

/-- Right multiplication of a row by the matrix in (A.44). -/
def applyRow (K : TransferCoefficient) (r : ComplexRow) : ComplexRow :=
  ⟨K.a * ((K.q : ℂ) * r.fst + r.snd),
    (K.b : ℂ) * K.phase * K.c * r.fst⟩

/-- The exact transfer matrix in a lightweight function encoding. -/
def matrix (K : TransferCoefficient) : Fin 2 → Fin 2 → ℂ
  | 0, 0 => (K.q : ℂ) * K.a
  | 0, 1 => (K.b : ℂ) * K.phase * K.c
  | 1, 0 => K.a
  | 1, 1 => 0

@[simp] theorem applyRow_fst (K : TransferCoefficient) (r : ComplexRow) :
    (K.applyRow r).fst = K.a * ((K.q : ℂ) * r.fst + r.snd) := rfl

@[simp] theorem applyRow_snd (K : TransferCoefficient) (r : ComplexRow) :
    (K.applyRow r).snd = (K.b : ℂ) * K.phase * K.c * r.fst := rfl

/-- Exact norm expression for one row update. -/
theorem normOne_applyRow
    (K : TransferCoefficient) (r : ComplexRow) (hb : 0 ≤ K.b)
    (hphase : ‖K.phase‖ = 1) :
    (K.applyRow r).normOne =
      ‖K.a‖ * ‖(K.q : ℂ) * r.fst + r.snd‖ +
        K.b * ‖K.c‖ * ‖r.fst‖ := by
  simp only [ComplexRow.normOne, applyRow, norm_mul, hphase, mul_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]

/-- Exact A.49 decrement identity. -/
theorem decrement_identity
    (K : TransferCoefficient) (r : ComplexRow)
    (hq : 0 ≤ K.q) (hb : 0 ≤ K.b) (hqb : K.q + K.b = 1)
    (hphase : ‖K.phase‖ = 1) :
    r.normOne - (K.applyRow r).normOne =
      (K.q * ‖r.fst‖ + ‖r.snd‖ -
        ‖(K.q : ℂ) * r.fst + r.snd‖) +
      (1 - ‖K.a‖) * ‖(K.q : ℂ) * r.fst + r.snd‖ +
      K.b * (1 - ‖K.c‖) * ‖r.fst‖ := by
  rw [normOne_applyRow K r hb hphase]
  dsimp [ComplexRow.normOne]
  rw [show K.q = 1 - K.b by linarith]
  ring

/-- Every actual-form transfer is `ℓ¹`-nonexpansive.  This is the monotonicity
of `N_k`; it also implies propagation of a zero row. -/
theorem normOne_applyRow_le
    (K : TransferCoefficient) (r : ComplexRow)
    (hq : 0 ≤ K.q) (hb : 0 ≤ K.b) (hqb : K.q + K.b = 1)
    (ha : ‖K.a‖ ≤ 1) (hc : ‖K.c‖ ≤ 1)
    (hphase : ‖K.phase‖ = 1) :
    (K.applyRow r).normOne ≤ r.normOne := by
  rw [normOne_applyRow K r hb hphase]
  have htri : ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
      K.q * ‖r.fst‖ + ‖r.snd‖ := by
    calc
      ‖(K.q : ℂ) * r.fst + r.snd‖ ≤
          ‖(K.q : ℂ) * r.fst‖ + ‖r.snd‖ := norm_add_le _ _
      _ = K.q * ‖r.fst‖ + ‖r.snd‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
  have ha0 : 0 ≤ ‖K.a‖ := norm_nonneg _
  have hc0 : 0 ≤ ‖K.c‖ := norm_nonneg _
  have hfirst := mul_le_mul_of_nonneg_left htri ha0
  have hsecond : K.b * ‖K.c‖ * ‖r.fst‖ ≤ K.b * ‖r.fst‖ := by
    calc
      K.b * ‖K.c‖ * ‖r.fst‖ ≤ (K.b * 1) * ‖r.fst‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc hb) (norm_nonneg _)
      _ = K.b * ‖r.fst‖ := by ring
  have hrad :
      ‖K.a‖ * (K.q * ‖r.fst‖ + ‖r.snd‖) ≤
        K.q * ‖r.fst‖ + ‖r.snd‖ := by
    apply mul_le_of_le_one_left _ ha
    exact add_nonneg (mul_nonneg hq (norm_nonneg _)) (norm_nonneg _)
  calc
    ‖K.a‖ * ‖(K.q : ℂ) * r.fst + r.snd‖ +
        K.b * ‖K.c‖ * ‖r.fst‖ ≤
      ‖K.a‖ * (K.q * ‖r.fst‖ + ‖r.snd‖) +
        K.b * ‖r.fst‖ := add_le_add hfirst hsecond
    _ ≤ (K.q * ‖r.fst‖ + ‖r.snd‖) +
        K.b * ‖r.fst‖ := by
      exact add_le_add hrad (le_refl _)
    _ = ‖r.fst‖ + ‖r.snd‖ := by
      rw [show K.b = 1 - K.q by linarith]
      ring

/-- A zero row stays zero, handling the zero-norm branch before logarithms or
relative decrements are introduced. -/
@[simp] theorem applyRow_zero (K : TransferCoefficient) :
    K.applyRow ⟨0, 0⟩ = ⟨0, 0⟩ := by
  cases K
  simp [applyRow]

end TransferCoefficient

/-- Iterated left-to-right multiplication of a row by transfer coefficients. -/
def applyTransferList : ComplexRow → List TransferCoefficient → ComplexRow
  | r, [] => r
  | r, K :: Ks => applyTransferList (K.applyRow r) Ks

@[simp] theorem applyTransferList_nil (r : ComplexRow) :
    applyTransferList r [] = r := rfl

@[simp] theorem applyTransferList_cons
    (r : ComplexRow) (K : TransferCoefficient) (Ks : List TransferCoefficient) :
    applyTransferList r (K :: Ks) = applyTransferList (K.applyRow r) Ks := rfl

@[simp] theorem applyTransferList_zero (Ks : List TransferCoefficient) :
    applyTransferList ⟨0, 0⟩ Ks = ⟨0, 0⟩ := by
  induction Ks with
  | nil => rfl
  | cons K Ks ih => simp only [applyTransferList_cons, TransferCoefficient.applyRow_zero, ih]

/-- Iterated nonexpansion for a list of admissible transfer coefficients. -/
theorem applyTransferList_normOne_le
    (r : ComplexRow) (Ks : List TransferCoefficient)
    (hK : ∀ K ∈ Ks, K.Admissible) :
    (applyTransferList r Ks).normOne ≤ r.normOne := by
  induction Ks generalizing r with
  | nil => exact le_rfl
  | cons K Ks ih =>
      have hhead := hK K (by simp)
      have htail : ∀ J ∈ Ks, J.Admissible := by
        intro J hJ
        exact hK J (by simp [hJ])
      exact (ih (K.applyRow r) htail).trans
        (K.normOne_applyRow_le r hhead.q_nonneg hhead.b_nonneg
          hhead.q_add_b hhead.norm_a_le_one hhead.norm_c_le_one hhead.norm_phase)

/-! ## Argument-free radial and relative-phase coercivity

The manuscript phrases the phase payment through a circular argument.  For
formal use we retain exactly the same information in the zero-safe chordal
quantity `‖a - phase*c‖²`.  On nonzero factors this is quantitatively
equivalent to the squared circular relative phase, while if either factor is
zero it is paid by the corresponding radial defect automatically. -/

/-- Exact squared-norm polarization for two complex numbers. -/
theorem norm_add_sq
    (x y : ℂ) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + 2 * (x * starRingEnd ℂ y).re := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_add,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

/-- Exact squared-norm polarization for a difference. -/
theorem norm_sub_sq
    (x y : ℂ) :
    ‖x - y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * (x * starRingEnd ℂ y).re := by
  rw [sub_eq_add_neg, norm_add_sq, norm_neg]
  simp only [map_neg, mul_neg, Complex.neg_re]
  ring

/-- The weighted squared norm loses exactly the product weight times the
squared chordal relative phase.  This is the argument-free form of the
triangle rationalization behind (A.48) and (A.51). -/
theorem weighted_norm_sq_identity
    (q b : ℝ) (x y : ℂ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (hqb : q + b = 1) :
    ‖(q : ℂ) * x + (b : ℂ) * y‖ ^ 2 =
      q * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - q * b * ‖x - y‖ ^ 2 := by
  have hqx : ‖(q : ℂ) * x‖ ^ 2 = q ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq]
    ring
  have hby : ‖(b : ℂ) * y‖ ^ 2 = b ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
    ring
  have hcross :
      (((q : ℂ) * x) * starRingEnd ℂ ((b : ℂ) * y)).re =
        q * b * (x * starRingEnd ℂ y).re := by
    have hcpx :
        ((q : ℂ) * x) * starRingEnd ℂ ((b : ℂ) * y) =
          ((q * b : ℝ) : ℂ) * (x * starRingEnd ℂ y) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [hcpx, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [norm_add_sq, hqx, hby, hcross, norm_sub_sq]
  have hq' : q = 1 - b := by linarith
  rw [hq']
  ring

/-- Decisive radial/relative-phase coercivity.  It requires no selected
argument and hence simultaneously covers `a=0`, `c=0`, and both-zero cases. -/
theorem radial_relativePhase_coercivity
    (q b : ℝ) (phase a c : ℂ)
    (hq : 0 ≤ q) (hb : 0 ≤ b) (hqb : q + b = 1)
    (hphase : ‖phase‖ = 1) (ha : ‖a‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    q * (1 - ‖a‖ ^ 2) + b * (1 - ‖c‖ ^ 2) +
        q * b * ‖a - phase * c‖ ^ 2 ≤
      2 * (1 - ‖(q : ℂ) * a + (b : ℂ) * phase * c‖) := by
  let m := ‖(q : ℂ) * a + (b : ℂ) * phase * c‖
  have hm0 : 0 ≤ m := norm_nonneg _
  have hm1 : m ≤ 1 := by
    calc
      m ≤ q * ‖a‖ + b * ‖c‖ := by
        dsimp [m]
        calc
          ‖(q : ℂ) * a + (b : ℂ) * phase * c‖ ≤
              ‖(q : ℂ) * a‖ + ‖(b : ℂ) * phase * c‖ := norm_add_le _ _
          _ = q * ‖a‖ + b * ‖c‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg hq, norm_mul, norm_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_nonneg hb, hphase]
            ring
      _ ≤ q * 1 + b * 1 := add_le_add
        (mul_le_mul_of_nonneg_left ha hq)
        (mul_le_mul_of_nonneg_left hc hb)
      _ = 1 := by linarith
  have hid := weighted_norm_sq_identity q b a (phase * c) hq hb hqb
  rw [norm_mul, hphase, one_mul] at hid
  have hsquare : 1 - m ^ 2 ≤ 2 * (1 - m) := by
    nlinarith [sq_nonneg (1 - m)]
  have hid' :
      q * (1 - ‖a‖ ^ 2) + b * (1 - ‖c‖ ^ 2) +
          q * b * ‖a - phase * c‖ ^ 2 =
        1 - ‖(q : ℂ) * a + (b : ℂ) * phase * c‖ ^ 2 := by
    rw [show (b : ℂ) * phase * c = (b : ℂ) * (phase * c) by ring, hid]
    nlinarith [hqb]
  rw [hid']
  exact hsquare

/-- A cleaner chordal estimate when the summands themselves have unit norm. -/
theorem two_vector_deficit_chordal
    (A B : ℝ) (u v : ℂ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    A * B * ‖u - v‖ ^ 2 ≤
      (A + B) * 2 * (A + B - ‖(A : ℂ) * u + (B : ℂ) * v‖) := by
  by_cases hsum : A + B = 0
  · have hAz : A = 0 := by linarith
    have hBz : B = 0 := by linarith
    simp [hAz, hBz]
  · have hsumpos : 0 < A + B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm hsum)
    let q := A / (A + B)
    let b := B / (A + B)
    have hq : 0 ≤ q := div_nonneg hA hsumpos.le
    have hb : 0 ≤ b := div_nonneg hB hsumpos.le
    have hqb : q + b = 1 := by
      dsimp [q, b]
      field_simp
    have hcoerc := radial_relativePhase_coercivity q b 1 u v
      hq hb hqb (by simp) (by rw [hu]) (by rw [hv])
    simp only [hu, hv, one_pow, sub_self, mul_zero, zero_add, one_mul] at hcoerc
    dsimp [q, b] at hcoerc
    have hnormscale :
        ‖((A / (A + B) : ℝ) : ℂ) * u +
          ((B / (A + B) : ℝ) : ℂ) * v‖ =
        ‖(A : ℂ) * u + (B : ℂ) * v‖ / (A + B) := by
      have heq :
          ((A / (A + B) : ℝ) : ℂ) * u +
              ((B / (A + B) : ℝ) : ℂ) * v =
            ((A : ℂ) * u + (B : ℂ) * v) / (A + B : ℂ) := by
        push_cast
        field_simp
      rw [heq, norm_div, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hsumpos]
    rw [show ((b : ℂ) * (1 : ℂ)) * v = (b : ℂ) * v by ring] at hcoerc
    rw [hnormscale] at hcoerc
    have hs0 : 0 ≤ ‖(A : ℂ) * u + (B : ℂ) * v‖ := norm_nonneg _
    field_simp [hsum] at hcoerc ⊢
    nlinarith [sq_nonneg (A + B)]

/-- `1-t ≤ exp(-t)`, the scalar bridge from paid relative decrement to
multiplicative decay. -/
theorem one_sub_le_exp_neg (t : ℝ) : 1 - t ≤ Real.exp (-t) := by
  have h := Real.add_one_le_exp (-t)
  linarith

/-- Product/telescope lemma for nonnegative step energies. -/
theorem exp_decay_of_step
    {α : Type*} (s : List α) (energy : α → ℝ)
    (c : ℝ) (N : α → ℝ → ℝ)
    (hstep : ∀ a x, 0 ≤ x →
      0 ≤ N a x ∧ N a x ≤ Real.exp (-c * energy a) * x) :
    ∀ x, 0 ≤ x →
      List.foldl (fun y a => N a y) x s ≤
        Real.exp (-c * (s.map energy).sum) * x := by
  intro x hx
  induction s generalizing x with
  | nil => simp
  | cons a s ih =>
      simp only [List.map_cons, List.sum_cons, List.foldl_cons]
      have hs := (hstep a x hx).2
      have hNx := (hstep a x hx).1
      calc
        List.foldl (fun y a => N a y) (N a x) s ≤
            Real.exp (-c * (s.map energy).sum) * N a x := ih (N a x) hNx
        _ ≤ Real.exp (-c * (s.map energy).sum) *
              (Real.exp (-c * energy a) * x) :=
          mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
        _ = Real.exp (-c * (energy a + (s.map energy).sum)) * x := by
          rw [show -c * (energy a + (s.map energy).sum) =
            (-c * (s.map energy).sum) + (-c * energy a) by ring,
            Real.exp_add]
          ring

end
end AppendixA
end Forest
end Erdos993
