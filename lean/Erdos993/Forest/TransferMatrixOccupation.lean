import Erdos993.Forest.TransferMatrixSideRoot

/-!
# Relative-decrement summation for the actual transfer path

This file isolates the finite real-variable bookkeeping behind (A.55).  The
hypotheses are later discharged by the genuine hard-core transfer rows; no
contraction hypothesis is postulated.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open ActualRootedVariance UniformFourthMoment

/-- Relative decrement of a positive nonincreasing sequence. -/
noncomputable def relativeDrop (N : ℕ → ℝ) (k : ℕ) : ℝ :=
  (N k - N (k + 1)) / N k

/-- The local real-variable bookkeeping used in A.55.  A two-row payment when
the first coordinate is large, together with the transfer formula for the
second coordinate and a barrier-assisted comparison of adjacent occupations,
pays every non-final occupation by three neighboring relative decrements and
one preceding barrier. -/
theorem occupation_pointwise_relativeDrop
    (n : ℕ) (h C B : ℝ) (N X b Λ : ℕ → ℝ)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hC0 : 0 ≤ C) (hB0 : 0 ≤ B)
    (hNpos : ∀ k, k ≤ n → 0 < N k)
    (hNmono : ∀ k, k < n → N (k + 1) ≤ N k)
    (hX0 : X 0 = N 0)
    (hXnonneg : ∀ k, k ≤ n → 0 ≤ X k)
    (hXle : ∀ k, k ≤ n → X k ≤ N k)
    (hb0 : ∀ k, k < n → 0 ≤ b k)
    (hb1 : ∀ k, k < n → b k ≤ 1)
    (hΛ0 : ∀ k, k < n → 0 ≤ Λ k)
    (hsecond : ∀ k, k < n → N (k + 1) - X (k + 1) ≤ b k * X k)
    (hshift : ∀ k, k + 1 < n → b (k + 1) ≤ B * (b k + Λ k))
    (hpay : ∀ k, k + 1 < n →
      X k * b k * h ≤ C *
        ((N k - N (k + 1)) + (N (k + 1) - N (k + 2))))
    (k : ℕ) (hk : k + 1 < n) :
    h * b k ≤ (2 + 2 * C + 4 * B * C + B) *
      (relativeDrop N k + relativeDrop N (k + 1) +
        (if k = 0 then 0 else
          relativeDrop N (k - 1) + h * Λ (k - 1))) := by
  let M := 2 + 2 * C + 4 * B * C + B
  have hkn : k < n := by omega
  have hk1n : k + 1 < n := hk
  have hk2le : k + 2 ≤ n := by omega
  have hNk : 0 < N k := hNpos k (by omega)
  have hNk1 : 0 < N (k + 1) := hNpos (k + 1) (by omega)
  have hNk2 : 0 < N (k + 2) := hNpos (k + 2) hk2le
  have hmonok := hNmono k hkn
  have hmonok1 := hNmono (k + 1) hk1n
  have hd0 : 0 ≤ relativeDrop N k := by
    exact div_nonneg (sub_nonneg.mpr hmonok) hNk.le
  have hd10 : 0 ≤ relativeDrop N (k + 1) := by
    exact div_nonneg (sub_nonneg.mpr hmonok1) hNk1.le
  have hM2C : 2 * C ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg hB0 hC0]
  have hM2 : 2 ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg hB0 hC0]
  have hM4BC : 4 * B * C ≤ M := by
    dsimp [M]
    nlinarith
  have hMB : B ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg hB0 hC0]
  by_cases hlarge : N k ≤ 2 * X k
  · have hbh0 : 0 ≤ b k * h := mul_nonneg (hb0 k hkn) hh0
    have hNpay : N k * (b k * h) ≤
        2 * C * ((N k - N (k + 1)) + (N (k + 1) - N (k + 2))) := by
      calc
        N k * (b k * h) ≤ (2 * X k) * (b k * h) :=
          mul_le_mul_of_nonneg_right hlarge hbh0
        _ = 2 * (X k * b k * h) := by ring
        _ ≤ 2 * (C * ((N k - N (k + 1)) +
              (N (k + 1) - N (k + 2)))) :=
          mul_le_mul_of_nonneg_left (hpay k hk) (by norm_num)
        _ = 2 * C * ((N k - N (k + 1)) +
              (N (k + 1) - N (k + 2))) := by ring
    have hratioNext :
        (N (k + 1) - N (k + 2)) / N k ≤
          relativeDrop N (k + 1) := by
      dsimp [relativeDrop]
      exact div_le_div₀ (sub_nonneg.mpr hmonok1) le_rfl hNk1 hmonok
    have hratio :
        ((N k - N (k + 1)) + (N (k + 1) - N (k + 2))) / N k ≤
          relativeDrop N k + relativeDrop N (k + 1) := by
      dsimp [relativeDrop]
      rw [add_div]
      exact add_le_add le_rfl hratioNext
    have hlocal : h * b k ≤
        2 * C * (relativeDrop N k + relativeDrop N (k + 1)) := by
      calc
        h * b k = b k * h := by ring
        _ ≤ (2 * C * ((N k - N (k + 1)) +
              (N (k + 1) - N (k + 2)))) / N k := by
          apply (le_div_iff₀ hNk).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using hNpay
        _ = 2 * C * (((N k - N (k + 1)) +
              (N (k + 1) - N (k + 2))) / N k) := by ring
        _ ≤ 2 * C * (relativeDrop N k + relativeDrop N (k + 1)) :=
          mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hC0)
    have hcharge0 : 0 ≤
        relativeDrop N k + relativeDrop N (k + 1) +
          (if k = 0 then 0 else relativeDrop N (k - 1) + h * Λ (k - 1)) := by
      split_ifs
      · positivity
      · have hprevn : k - 1 < n := by omega
        have hprevmono := hNmono (k - 1) hprevn
        have hprevpos := hNpos (k - 1) (by omega)
        have hdprev : 0 ≤ relativeDrop N (k - 1) :=
          div_nonneg (sub_nonneg.mpr hprevmono) hprevpos.le
        have hΛprev := hΛ0 (k - 1) hprevn
        positivity
    calc
      h * b k ≤ 2 * C * (relativeDrop N k + relativeDrop N (k + 1)) := hlocal
      _ ≤ M * (relativeDrop N k + relativeDrop N (k + 1)) :=
        mul_le_mul_of_nonneg_right hM2C (add_nonneg hd0 hd10)
      _ ≤ M * (relativeDrop N k + relativeDrop N (k + 1) +
          (if k = 0 then 0 else relativeDrop N (k - 1) + h * Λ (k - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (le_trans (by norm_num) hM2)
        split_ifs
        · simp
        · have hprevn : k - 1 < n := by omega
          have hpmono := hNmono (k - 1) hprevn
          have hppos := hNpos (k - 1) (by omega)
          have hdp : 0 ≤ relativeDrop N (k - 1) :=
            div_nonneg (sub_nonneg.mpr hpmono) hppos.le
          have hΛp := hΛ0 (k - 1) hprevn
          have hhΛ : 0 ≤ h * Λ (k - 1) := mul_nonneg hh0 hΛp
          nlinarith
  · have hsmall : 2 * X k < N k := lt_of_not_ge hlarge
    have hk0 : k ≠ 0 := by
      intro heq
      subst k
      rw [hX0] at hsmall
      nlinarith [hNpos 0 (by omega)]
    let j := k - 1
    have hjk : j + 1 = k := by dsimp [j]; omega
    have hjn : j < n := by omega
    have hjpay : j + 1 < n := by omega
    have hNj : 0 < N j := hNpos j (by omega)
    have hmonoj : N (j + 1) ≤ N j := hNmono j hjn
    have hmonoj' : N k ≤ N j := by simpa [hjk] using hmonoj
    have hdj0 : 0 ≤ relativeDrop N j :=
      div_nonneg (sub_nonneg.mpr hmonoj) hNj.le
    have hy : N k - X k ≤ b j * X j := by
      simpa [hjk] using hsecond j hjn
    have hbj0 := hb0 j hjn
    have hbj1 := hb1 j hjn
    have hXj0 := hXnonneg j (by omega)
    have hyX : N k - X k ≤ X j := by
      exact hy.trans (by
        calc
          b j * X j ≤ 1 * X j := mul_le_mul_of_nonneg_right hbj1 hXj0
          _ = X j := one_mul _)
    by_cases hdrop : N j > 2 * N k
    · have hdjhalf : 1 / 2 < relativeDrop N j := by
        dsimp [relativeDrop]
        rw [hjk]
        apply (lt_div_iff₀ hNj).2
        nlinarith
      have hbh1 : h * b k ≤ 1 := by
        calc
          h * b k ≤ h * 1 := mul_le_mul_of_nonneg_left (hb1 k hkn) hh0
          _ = h := mul_one h
          _ ≤ 1 := hh1
      have hlocal : h * b k ≤ 2 * relativeDrop N j := by nlinarith
      have hΛj := hΛ0 j hjn
      have hcharge : 0 ≤ relativeDrop N k + relativeDrop N (k + 1) +
          (relativeDrop N j + h * Λ j) := by positivity
      rw [if_neg hk0]
      change h * b k ≤ M * (relativeDrop N k + relativeDrop N (k + 1) +
        (relativeDrop N j + h * Λ j))
      calc
        h * b k ≤ 2 * relativeDrop N j := hlocal
        _ ≤ 2 * (relativeDrop N k + relativeDrop N (k + 1) +
            (relativeDrop N j + h * Λ j)) := by nlinarith
        _ ≤ M * (relativeDrop N k + relativeDrop N (k + 1) +
            (relativeDrop N j + h * Λ j)) :=
          mul_le_mul_of_nonneg_right hM2 hcharge
    · have hNjle : N j ≤ 2 * N k := le_of_not_gt hdrop
      have hXjlarge : N j ≤ 4 * X j := by nlinarith [hyX]
      have hbjh0 : 0 ≤ b j * h := mul_nonneg hbj0 hh0
      have hNpay : N j * (b j * h) ≤
          4 * C * ((N j - N (j + 1)) + (N (j + 1) - N (j + 2))) := by
        calc
          N j * (b j * h) ≤ (4 * X j) * (b j * h) :=
            mul_le_mul_of_nonneg_right hXjlarge hbjh0
          _ = 4 * (X j * b j * h) := by ring
          _ ≤ 4 * (C * ((N j - N (j + 1)) +
                (N (j + 1) - N (j + 2)))) :=
            mul_le_mul_of_nonneg_left (hpay j hjpay) (by norm_num)
          _ = 4 * C * ((N j - N (j + 1)) +
                (N (j + 1) - N (j + 2))) := by ring
      have hratioK :
          (N (j + 1) - N (j + 2)) / N j ≤ relativeDrop N k := by
        have hj2 : j + 2 = k + 1 := by omega
        dsimp [relativeDrop]
        rw [hjk, hj2]
        exact div_le_div₀ (sub_nonneg.mpr hmonok) le_rfl hNk hmonoj'
      have hratio :
          ((N j - N (j + 1)) + (N (j + 1) - N (j + 2))) / N j ≤
            relativeDrop N j + relativeDrop N k := by
        dsimp [relativeDrop]
        rw [add_div]
        exact add_le_add le_rfl hratioK
      have hbjpay : h * b j ≤
          4 * C * (relativeDrop N j + relativeDrop N k) := by
        calc
          h * b j = b j * h := by ring
          _ ≤ (4 * C * ((N j - N (j + 1)) +
                (N (j + 1) - N (j + 2)))) / N j := by
            apply (le_div_iff₀ hNj).2
            simpa [mul_assoc, mul_left_comm, mul_comm] using hNpay
          _ = 4 * C * (((N j - N (j + 1)) +
                (N (j + 1) - N (j + 2))) / N j) := by ring
          _ ≤ 4 * C * (relativeDrop N j + relativeDrop N k) :=
            mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hC0)
      have hshiftk : b k ≤ B * (b j + Λ j) := by
        simpa [hjk] using hshift j hjpay
      have hΛj := hΛ0 j hjn
      have hshiftPay : h * b k ≤ B *
          (4 * C * (relativeDrop N j + relativeDrop N k) + h * Λ j) := by
        calc
          h * b k ≤ h * (B * (b j + Λ j)) :=
            mul_le_mul_of_nonneg_left hshiftk hh0
          _ = B * (h * b j + h * Λ j) := by ring
          _ ≤ B * (4 * C * (relativeDrop N j + relativeDrop N k) +
                h * Λ j) :=
            mul_le_mul_of_nonneg_left (add_le_add hbjpay le_rfl) hB0
      have hcharge : 0 ≤ relativeDrop N k + relativeDrop N (k + 1) +
          (relativeDrop N j + h * Λ j) := by positivity
      rw [if_neg hk0]
      change h * b k ≤ M * (relativeDrop N k + relativeDrop N (k + 1) +
        (relativeDrop N j + h * Λ j))
      calc
        h * b k ≤ B * (4 * C * (relativeDrop N j + relativeDrop N k) +
            h * Λ j) := hshiftPay
        _ = (4 * B * C) * relativeDrop N j +
              (4 * B * C) * relativeDrop N k + B * (h * Λ j) := by ring
        _ ≤ M * relativeDrop N j + M * relativeDrop N k +
              M * (h * Λ j) := by
          exact add_le_add
            (add_le_add
              (mul_le_mul_of_nonneg_right hM4BC hdj0)
              (mul_le_mul_of_nonneg_right hM4BC hd0))
            (mul_le_mul_of_nonneg_right hMB (mul_nonneg hh0 hΛj))
        _ ≤ M * (relativeDrop N k + relativeDrop N (k + 1) +
            (relativeDrop N j + h * Λ j)) := by
          have hM0 : 0 ≤ M := le_trans (by norm_num) hM2
          have := mul_nonneg hM0 hd10
          nlinarith

/-- Summing a one-step forward shift loses only the new zeroth term. -/
theorem sum_range_succ_shift_le (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (n : ℕ) :
    (∑ k ∈ Finset.range n, f (k + 1)) ≤
      ∑ k ∈ Finset.range (n + 1), f k := by
  induction n with
  | zero => simp [hf]
  | succ n ih =>
      simpa [Finset.sum_range_succ] using
        add_le_add_right ih (f (n + 1))

/-- Exact sum identity for the zero-safe predecessor convention. -/
theorem sum_range_predecessor (f : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else f (k - 1)) =
      ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (∑ k ∈ Finset.range (n + 1 + 1),
            if k = 0 then 0 else f (k - 1)) =
            (∑ k ∈ Finset.range (n + 1),
              if k = 0 then 0 else f (k - 1)) + f n := by
                rw [Finset.sum_range_succ]
                simp
        _ = (∑ k ∈ Finset.range n, f k) + f n := by rw [ih]
        _ = ∑ k ∈ Finset.range (n + 1), f k := by
          rw [Finset.sum_range_succ]

/-- Restricting a range can only decrease a sum of nonnegative terms. -/
theorem sum_range_le_sum_range (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Finset.range m, f k) ≤ ∑ k ∈ Finset.range n, f k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hmn
  · intro i hi hin
    exact hf i

/-- Each relative decrement is charged at most three times by the local
three-row bookkeeping; each preceding barrier is charged at most once. -/
theorem sum_neighborCharges_le
    (n : ℕ) (d L : ℕ → ℝ) (hd : ∀ k, 0 ≤ d k) (hL : ∀ k, 0 ≤ L k) :
    (∑ k ∈ Finset.range (n - 1),
      (d k + d (k + 1) + (if k = 0 then 0 else d (k - 1) + L (k - 1)))) ≤
      3 * (∑ k ∈ Finset.range n, d k) +
        ∑ k ∈ Finset.range n, L k := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero =>
          have hz : 0 ≤ 3 * d 0 + L 0 :=
            add_nonneg (mul_nonneg (by norm_num) (hd 0)) (hL 0)
          simpa using hz
      | succ m =>
          have hfirst :
              (∑ k ∈ Finset.range (m + 1), d k) ≤
                ∑ k ∈ Finset.range (m + 2), d k :=
            sum_range_le_sum_range d hd (by omega)
          have hnext :
              (∑ k ∈ Finset.range (m + 1), d (k + 1)) ≤
                ∑ k ∈ Finset.range (m + 2), d k := by
            simpa [Nat.add_assoc] using sum_range_succ_shift_le d hd (m + 1)
          have hprev :
              (∑ k ∈ Finset.range (m + 1),
                if k = 0 then 0 else d (k - 1)) ≤
                ∑ k ∈ Finset.range (m + 2), d k := by
            rw [sum_range_predecessor d m]
            exact sum_range_le_sum_range d hd (by omega)
          have hprevL :
              (∑ k ∈ Finset.range (m + 1),
                if k = 0 then 0 else L (k - 1)) ≤
                ∑ k ∈ Finset.range (m + 2), L k := by
            rw [sum_range_predecessor L m]
            exact sum_range_le_sum_range L hL (by omega)
          simp only [Nat.add_sub_cancel, Finset.sum_add_distrib]
          have hif :
              (∑ x ∈ Finset.range (m + 1),
                if x = 0 then 0 else d (x - 1) + L (x - 1)) =
              (∑ x ∈ Finset.range (m + 1),
                if x = 0 then 0 else d (x - 1)) +
              (∑ x ∈ Finset.range (m + 1),
                if x = 0 then 0 else L (x - 1)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hx0 : x = 0 <;> simp [hx0]
          rw [hif]
          linarith

/-- Summed form of the local occupation payment.  The only unpaid term is the
final coefficient occupation, bounded by one. -/
theorem occupation_sum_relativeDrop
    (n : ℕ) (h C B : ℝ) (N X b Λ : ℕ → ℝ)
    (hnpos : 0 < n)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hC0 : 0 ≤ C) (hB0 : 0 ≤ B)
    (hNpos : ∀ k, k ≤ n → 0 < N k)
    (hNmono : ∀ k, k < n → N (k + 1) ≤ N k)
    (hX0 : X 0 = N 0)
    (hXnonneg : ∀ k, k ≤ n → 0 ≤ X k)
    (hXle : ∀ k, k ≤ n → X k ≤ N k)
    (hb0 : ∀ k, k < n → 0 ≤ b k)
    (hb1 : ∀ k, k < n → b k ≤ 1)
    (hΛ0 : ∀ k, k < n → 0 ≤ Λ k)
    (hsecond : ∀ k, k < n → N (k + 1) - X (k + 1) ≤ b k * X k)
    (hshift : ∀ k, k + 1 < n → b (k + 1) ≤ B * (b k + Λ k))
    (hpay : ∀ k, k + 1 < n →
      X k * b k * h ≤ C *
        ((N k - N (k + 1)) + (N (k + 1) - N (k + 2)))) :
    h * (∑ k ∈ Finset.range n, b k) ≤
      1 + (2 + 2 * C + 4 * B * C + B) *
        (3 * (∑ k ∈ Finset.range n, relativeDrop N k) +
          h * (∑ k ∈ Finset.range n, Λ k)) := by
  let M := 2 + 2 * C + 4 * B * C + B
  have hM0 : 0 ≤ M := by
    dsimp [M]
    nlinarith [mul_nonneg hB0 hC0]
  let d : ℕ → ℝ := fun k => if k < n then relativeDrop N k else 0
  let L : ℕ → ℝ := fun k => if k < n then h * Λ k else 0
  have hd : ∀ k, 0 ≤ d k := by
    intro k
    dsimp [d]
    split_ifs with hk
    · exact div_nonneg (sub_nonneg.mpr (hNmono k hk))
        (hNpos k (by omega)).le
    · exact le_rfl
  have hL : ∀ k, 0 ≤ L k := by
    intro k
    dsimp [L]
    split_ifs with hk
    · exact mul_nonneg hh0 (hΛ0 k hk)
    · exact le_rfl
  have hpoint :
      (∑ k ∈ Finset.range (n - 1), h * b k) ≤
        ∑ k ∈ Finset.range (n - 1),
          M * (d k + d (k + 1) +
            (if k = 0 then 0 else d (k - 1) + L (k - 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkr : k < n - 1 := Finset.mem_range.mp hk
    have hkmain : k + 1 < n := by omega
    have hp := occupation_pointwise_relativeDrop n h C B N X b Λ
      hh0 hh1 hC0 hB0 hNpos hNmono hX0 hXnonneg hXle hb0 hb1 hΛ0
      hsecond hshift hpay k hkmain
    dsimp [M, d, L]
    simp only [if_pos (show k < n by omega),
      if_pos (show k + 1 < n by omega)]
    by_cases hk0 : k = 0
    · simp [hk0] at hp ⊢
      exact hp
    · have hprev : k - 1 < n := by omega
      simp [hk0, hprev] at hp ⊢
      exact hp
  have hcharges := sum_neighborCharges_le n d L hd hL
  have hpaid :
      (∑ k ∈ Finset.range (n - 1), h * b k) ≤
        M * (3 * (∑ k ∈ Finset.range n, relativeDrop N k) +
          h * (∑ k ∈ Finset.range n, Λ k)) := by
    calc
      (∑ k ∈ Finset.range (n - 1), h * b k) ≤
          ∑ k ∈ Finset.range (n - 1),
            M * (d k + d (k + 1) +
              (if k = 0 then 0 else d (k - 1) + L (k - 1))) := hpoint
      _ = M * (∑ k ∈ Finset.range (n - 1),
            (d k + d (k + 1) +
              (if k = 0 then 0 else d (k - 1) + L (k - 1)))) := by
          rw [Finset.mul_sum]
      _ ≤ M * (3 * (∑ k ∈ Finset.range n, d k) +
            ∑ k ∈ Finset.range n, L k) :=
          mul_le_mul_of_nonneg_left hcharges hM0
      _ = M * (3 * (∑ k ∈ Finset.range n, relativeDrop N k) +
          h * (∑ k ∈ Finset.range n, Λ k)) := by
          apply congrArg (fun x : ℝ => M * x)
          have hdSum : (∑ k ∈ Finset.range n, d k) =
              ∑ k ∈ Finset.range n, relativeDrop N k := by
            apply Finset.sum_congr rfl
            intro k hk
            simp [d, Finset.mem_range.mp hk]
          have hLSum : (∑ k ∈ Finset.range n, L k) =
              h * (∑ k ∈ Finset.range n, Λ k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            simp [L, Finset.mem_range.mp hk]
          rw [hdSum, hLSum]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hlast0 : 0 ≤ b m := hb0 m (by omega)
  have hlast1 : b m ≤ 1 := hb1 m (by omega)
  have hlast : h * b m ≤ 1 := by nlinarith
  simp only [Finset.sum_range_succ] at hpaid ⊢
  rw [← Finset.mul_sum] at hpaid
  dsimp [M] at hpaid
  nlinarith

/-- Exponential telescope for positive nonincreasing sequences, stated in
terms of the relative decrements used above. -/
theorem relativeDrop_exponential_telescope
    (N : ℕ → ℝ) (n : ℕ)
    (hNpos : ∀ k, k ≤ n → 0 < N k)
    (hNmono : ∀ k, k < n → N (k + 1) ≤ N k) :
    N n ≤ Real.exp (-(∑ k ∈ Finset.range n, relativeDrop N k)) * N 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hnpos : 0 < N n := hNpos n (by omega)
      have hnextpos : 0 < N (n + 1) := hNpos (n + 1) (by omega)
      have hmono : N (n + 1) ≤ N n := hNmono n (by omega)
      have ih' : N n ≤
          Real.exp (-(∑ k ∈ Finset.range n, relativeDrop N k)) * N 0 := by
        apply ih
        · intro k hk
          exact hNpos k (by omega)
        · intro k hk
          exact hNmono k (by omega)
      have hstep : N (n + 1) ≤
          Real.exp (-relativeDrop N n) * N n := by
        have heq : N (n + 1) = (1 - relativeDrop N n) * N n := by
          dsimp [relativeDrop]
          field_simp [hnpos.ne']
          ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (one_sub_le_exp_neg _) hnpos.le
      calc
        N (n + 1) ≤ Real.exp (-relativeDrop N n) * N n := hstep
        _ ≤ Real.exp (-relativeDrop N n) *
            (Real.exp (-(∑ k ∈ Finset.range n, relativeDrop N k)) * N 0) :=
          mul_le_mul_of_nonneg_left ih' (Real.exp_pos _).le
        _ = (Real.exp (-relativeDrop N n) *
              Real.exp (-(∑ k ∈ Finset.range n, relativeDrop N k))) * N 0 := by ring
        _ = Real.exp (-relativeDrop N n +
              -(∑ k ∈ Finset.range n, relativeDrop N k)) * N 0 := by
          rw [Real.exp_add]
        _ = Real.exp (-(∑ k ∈ Finset.range (n + 1), relativeDrop N k)) * N 0 := by
          rw [Finset.sum_range_succ]
          congr 2
          ring

/-! ## Concrete path indexing -/

universe u
variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

namespace DownwardPath

variable {R : ComponentRooting G}

/-- Number of genuine transfer edges in a nontrivial downward path. -/
def edgeCount (P : DownwardPath R) : ℕ := P.vertices.length - 1

/-- Total path-vertex accessor; substantive uses are always in range. -/
def vertexAt (P : DownwardPath R) (k : ℕ) : V :=
  (P.vertices[k]?).getD P.start

/-- The genuine hard-core transfer coefficient at path edge `k`. -/
noncomputable def actualTransferCoefficientAt (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (k : ℕ) : TransferCoefficient :=
  actualTransferCoefficient R z hz θ (P.vertexAt k) (P.vertexAt (k + 1))

/-- The row after the first `k` genuine transfer coefficients. -/
noncomputable def actualTransferRowAt (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) (k : ℕ) : ComplexRow :=
  applyTransferList ⟨1, 0⟩
    ((actualTransferCoefficients R z hz θ P.vertices).take k)

/-- Actual occupation at the parent of path edge `k`. -/
noncomputable def actualOccupationAt (P : DownwardPath R) (z : ℝ) (k : ℕ) : ℝ :=
  rootedOccupationProbabilityAt R z (P.vertexAt k)

/-- Actual side logarithmic barrier at path edge `k`. -/
noncomputable def actualSideLogBarrierAt (P : DownwardPath R) (z : ℝ) (k : ℕ) : ℝ :=
  sideLogBarrier R z (P.vertexAt k) (P.vertexAt (k + 1))

@[simp] theorem edgeCount_eq (P : DownwardPath R) :
    P.edgeCount = P.tail.length + 1 := by
  simp [edgeCount, DownwardPath.vertices]

@[simp] theorem edgeCount_pos (P : DownwardPath R) : 0 < P.edgeCount := by
  simp [P.edgeCount_eq]

end DownwardPath

/-- Number of adjacent-pair transfer coefficients. -/
@[simp] theorem actualTransferCoefficients_length
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    ∀ l : List V,
      (actualTransferCoefficients R z hz θ l).length = l.length - 1
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
      simp [actualTransferCoefficients,
        actualTransferCoefficients_length R z hz θ (v :: rest)]

/-- Indexed adjacent-pair identification for the genuine coefficient list. -/
theorem actualTransferCoefficients_getElem?_eq
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    ∀ (l : List V) (d : V) (k : ℕ), k + 1 < l.length →
      (actualTransferCoefficients R z hz θ l)[k]? =
        some (actualTransferCoefficient R z hz θ
          ((l[k]?).getD d) ((l[k + 1]?).getD d))
  | [], d, k, hk => by simp at hk
  | [_], d, k, hk => by simp at hk
  | u :: v :: rest, d, 0, hk => by
      simp [actualTransferCoefficients]
  | u :: v :: rest, d, k + 1, hk => by
      simp only [actualTransferCoefficients, List.getElem?_cons_succ]
      exact actualTransferCoefficients_getElem?_eq R z hz θ (v :: rest) d k (by
        simpa using hk)

/-- Transfer-list application respects concatenation. -/
theorem applyTransferList_append (r : ComplexRow)
    (Ks Js : List TransferCoefficient) :
    applyTransferList r (Ks ++ Js) =
      applyTransferList (applyTransferList r Ks) Js := by
  induction Ks generalizing r with
  | nil => rfl
  | cons K Ks ih =>
      simp only [List.cons_append, applyTransferList_cons]
      exact ih (K.applyRow r)

namespace DownwardPath

variable {R : ComponentRooting G}

/-- Every valid path edge is a genuine parent-to-child edge. -/
theorem isChild_vertexAt (P : DownwardPath R) {k : ℕ} (hk : k < P.edgeCount) :
    R.IsChild (G := G) (P.vertexAt k) (P.vertexAt (k + 1)) := by
  have hkV : k + 1 < P.vertices.length := by
    unfold edgeCount at hk
    omega
  have hc := (List.isChain_iff_getElem.mp P.isChain) k hkV
  have hk0 : k < P.vertices.length := by omega
  rw [vertexAt, vertexAt, List.getElem?_eq_getElem hk0,
    List.getElem?_eq_getElem hkV]
  simpa using hc

/-- Coefficient-list indexing agrees with the concrete path accessor. -/
theorem actualTransferCoefficients_getElem?_eq_at
    (P : DownwardPath R) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    {k : ℕ} (hk : k < P.edgeCount) :
    (actualTransferCoefficients R z hz θ P.vertices)[k]? =
      some (P.actualTransferCoefficientAt z hz θ k) := by
  have hkV : k + 1 < P.vertices.length := by
    unfold edgeCount at hk
    omega
  rw [actualTransferCoefficients_getElem?_eq R z hz θ P.vertices P.start k hkV]
  rfl

@[simp] theorem actualTransferRowAt_zero (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    P.actualTransferRowAt z hz θ 0 = ⟨1, 0⟩ := by
  simp [actualTransferRowAt]

/-- Prefix-row recurrence at a valid edge. -/
theorem actualTransferRowAt_succ (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ)
    {k : ℕ} (hk : k < P.edgeCount) :
    P.actualTransferRowAt z hz θ (k + 1) =
      (P.actualTransferCoefficientAt z hz θ k).applyRow
        (P.actualTransferRowAt z hz θ k) := by
  let Ks := actualTransferCoefficients R z hz θ P.vertices
  have hkK : k < Ks.length := by
    dsimp [Ks]
    rw [actualTransferCoefficients_length]
    exact hk
  have hget : Ks[k] = P.actualTransferCoefficientAt z hz θ k := by
    have hg := P.actualTransferCoefficients_getElem?_eq_at z hz θ hk
    rw [List.getElem?_eq_getElem hkK] at hg
    exact Option.some.inj hg
  rw [actualTransferRowAt, List.take_succ_eq_append_getElem hkK,
    applyTransferList_append]
  simp only [applyTransferList_cons, applyTransferList_nil, hget]
  rfl

@[simp] theorem actualTransferRowAt_edgeCount (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    P.actualTransferRowAt z hz θ P.edgeCount =
      P.actualTransferRow z hz θ := by
  unfold actualTransferRowAt actualTransferRow edgeCount
  have hlen := actualTransferCoefficients_length R z hz θ P.vertices
  rw [← hlen, List.take_length]

/-- The path initial sum is exactly the range sum over the total accessor. -/
theorem initialSum_eq_sum_getD (f : V → ℝ) :
    ∀ (l : List V) (d : V),
      DownwardPath.initialSum f l =
        ∑ k ∈ Finset.range (l.length - 1), f ((l[k]?).getD d)
  | [], d => by simp [DownwardPath.initialSum]
  | [_], d => by simp [DownwardPath.initialSum]
  | u :: v :: rest, d => by
      rw [DownwardPath.initialSum,
        initialSum_eq_sum_getD f (v :: rest) d]
      have hlen : (u :: v :: rest).length - 1 =
          ((v :: rest).length - 1) + 1 := by simp
      rw [hlen, Finset.sum_range_succ']
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      ring

/-- The actual occupation mass is the exact sum over coefficient parents. -/
theorem sum_range_actualOccupationAt (P : DownwardPath R) (z : ℝ) :
    (∑ k ∈ Finset.range P.edgeCount, P.actualOccupationAt z k) =
      P.occupationMass R z := by
  rw [DownwardPath.occupationMass, edgeCount,
    initialSum_eq_sum_getD (rootedOccupationProbabilityAt R z) P.vertices P.start]
  rfl

/-- The concrete side-barrier list is exactly the indexed edge sum. -/
theorem actualSideLogBarrierSumList_eq_sum_getD
    (R : ComponentRooting G) (z : ℝ) :
    ∀ (l : List V) (d : V),
      actualSideLogBarrierSumList R z l =
        ∑ k ∈ Finset.range (l.length - 1),
          sideLogBarrier R z ((l[k]?).getD d) ((l[k + 1]?).getD d)
  | [], d => by simp [actualSideLogBarrierSumList]
  | [_], d => by simp [actualSideLogBarrierSumList]
  | u :: v :: rest, d => by
      rw [actualSideLogBarrierSumList,
        actualSideLogBarrierSumList_eq_sum_getD R z (v :: rest) d]
      have hlen : (u :: v :: rest).length - 1 =
          ((v :: rest).length - 1) + 1 := by simp
      rw [hlen, Finset.sum_range_succ']
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.getD_some]
      ring

/-- The concrete indexed edge barriers sum to the path barrier. -/
theorem sum_range_actualSideLogBarrierAt (P : DownwardPath R) (z : ℝ) :
    (∑ k ∈ Finset.range P.edgeCount, P.actualSideLogBarrierAt z k) =
      P.actualSideLogBarrierSum z := by
  rw [DownwardPath.actualSideLogBarrierSum, edgeCount,
    actualSideLogBarrierSumList_eq_sum_getD R z P.vertices P.start]
  rfl

end DownwardPath

/-- A full admissible transfer list is no larger than any prefix row. -/
theorem applyTransferList_normOne_le_take
    (r : ComplexRow) (Ks : List TransferCoefficient)
    (hKs : ∀ K ∈ Ks, K.Admissible) (k : ℕ) :
    (applyTransferList r Ks).normOne ≤
      (applyTransferList r (Ks.take k)).normOne := by
  calc
    (applyTransferList r Ks).normOne =
        (applyTransferList
          (applyTransferList r (Ks.take k)) (Ks.drop k)).normOne := by
      rw [← applyTransferList_append, List.take_append_drop]
    _ ≤ (applyTransferList r (Ks.take k)).normOne := by
      apply applyTransferList_normOne_le
      intro K hK
      apply hKs K
      rw [← List.take_append_drop k Ks, List.mem_append]
      exact Or.inr hK

/-- Exact second-coordinate estimate for an admissible transfer row. -/
theorem TransferCoefficient.norm_applyRow_snd_le
    (K : TransferCoefficient) (r : ComplexRow) (hK : K.Admissible) :
    ‖(K.applyRow r).snd‖ ≤ K.b * ‖r.fst‖ := by
  rw [K.applyRow_snd, norm_mul, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK.b_nonneg,
    hK.norm_phase]
  have hc := mul_le_mul_of_nonneg_left hK.norm_c_le_one hK.b_nonneg
  nlinarith [mul_le_mul_of_nonneg_right hc (norm_nonneg r.fst)]

end
end AppendixA
end Forest
end Erdos993
