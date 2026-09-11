import Erdos993.Forest.RootVarianceComparison
import Erdos993.Forest.IndexVarianceLocalization

/-!
# Characteristic-function algebra for Appendix A

This focused module starts the arbitrary-activity complex bridge needed for the
parent-vacant mixture (A.33).
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance
open ActualRootedVariance.ComponentRooting

universe u

noncomputable local instance finiteSubtypeCT
    {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x : α // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

private theorem characteristicModulus_eq_norm_characteristic
    {α : Type*} [Fintype α]
    (L : FiniteLatticeLaw α) (θ : ℝ) :
    L.characteristicModulus θ = ‖L.characteristic θ‖ := by
  rw [FiniteLatticeLaw.characteristicModulus,
    FiniteLatticeLaw.norm_centeredCharacteristic_eq]

/-- The hard-core characteristic function is the independence polynomial
normalized at the positive real partition function and evaluated at the
complex activity `z exp(iθ)`. -/
theorem hardCoreLaw_characteristic_eq_eval₂
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw H z hz).characteristic θ =
      Polynomial.eval₂ (Nat.castRingHom ℂ)
          ((z : ℂ) * FiniteLatticeLaw.phase θ 1)
          (independencePolynomial H) /
        (independenceEval H z : ℂ) := by
  classical
  change (∑ I : IndepFinset H,
      ((z ^ I.val.card / independenceEval H z : ℝ) : ℂ) *
        FiniteLatticeLaw.phase θ (I.val.card : ℝ)) = _
  simp only [Complex.ofReal_div, Complex.ofReal_pow]
  rw [show (∑ I : IndepFinset H,
        (z : ℂ) ^ I.val.card / (independenceEval H z : ℂ) *
          FiniteLatticeLaw.phase θ (I.val.card : ℝ)) =
      (∑ I : IndepFinset H,
        (z : ℂ) ^ I.val.card *
          FiniteLatticeLaw.phase θ (I.val.card : ℝ)) /
        (independenceEval H z : ℂ) by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro I hI
    ring]
  congr 1
  rw [independencePolynomial_eq_sum, Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro I hI
  simp only [Polynomial.eval₂_X, Polynomial.eval₂_pow]
  rw [mul_pow, FiniteLatticeLaw.phase_natCast]

private theorem independenceEval_deleteVertex_child_factorAt
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) (z : ℝ) :
    independenceEval (deleteVertex G p) z =
      independenceEval (R.Subtree (G := G) u) z *
        independenceEval
          (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) z := by
  classical
  simp only [independenceEval, independencePolynomialReal]
  rw [R.independencePolynomial_deleteVertex_child_factorAt hG hpu]
  simp [Polynomial.map_mul, Polynomial.eval_mul]

/-- Exact characteristic-function factorization of a parent-deleted forest
into a selected child subtree and the remaining outside forest. -/
theorem hardCoreLaw_characteristic_deleteVertex_child_factorAt
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw (deleteVertex G p) z hz).characteristic θ =
      (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristic θ *
        (hardCoreLaw
          (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) z hz).characteristic θ := by
  classical
  have hEval := independenceEval_deleteVertex_child_factorAt hG R hpu z
  rw [hardCoreLaw_characteristic_eq_eval₂,
    hardCoreLaw_characteristic_eq_eval₂,
    hardCoreLaw_characteristic_eq_eval₂]
  rw [R.independencePolynomial_deleteVertex_child_factorAt hG hpu,
    Polynomial.eval₂_mul, hEval]
  push_cast
  have hU : (independenceEval (R.Subtree (G := G) u) z : ℂ) ≠ 0 := by
    exact_mod_cast (independenceEval_pos (R.Subtree (G := G) u) hz).ne'
  have hO : (independenceEval
      (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) z : ℂ) ≠ 0 := by
    exact_mod_cast (independenceEval_pos
      (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) hz).ne'
  field_simp [hU, hO]

/-- The modulus of the parent-deleted law is the product of the child and
outside moduli. -/
theorem hardCoreLaw_characteristicModulus_deleteVertex_child_factorAt
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ =
      (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ *
        (hardCoreLaw
          (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) z hz).characteristicModulus θ := by
  rw [characteristicModulus_eq_norm_characteristic,
    hardCoreLaw_characteristic_deleteVertex_child_factorAt hG R hpu z θ hz,
    norm_mul,
    ← characteristicModulus_eq_norm_characteristic,
    ← characteristicModulus_eq_norm_characteristic]

private theorem independenceEval_vertexDeletion
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (z : ℝ) (p : V) :
    independenceEval G z =
      independenceEval (deleteVertex G p) z +
        z * independenceEval (deleteClosedNeighborhood G p) z := by
  classical
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_deleteVertex (G := G) (v := p)]
  simp [Polynomial.map_add, Polynomial.map_mul,
    Polynomial.eval_add, Polynomial.eval_mul]

/-- Exact vertex-deletion mixture identity for the uncentered hard-core
characteristic function. -/
theorem hardCoreLaw_characteristic_vertexDeletion
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (p : V)
    (z θ : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).characteristic θ =
      ((independenceEval (deleteVertex G p) z /
          independenceEval G z : ℝ) : ℂ) *
        (hardCoreLaw (deleteVertex G p) z hz).characteristic θ +
      ((z * independenceEval (deleteClosedNeighborhood G p) z /
          independenceEval G z : ℝ) : ℂ) *
        (FiniteLatticeLaw.phase θ 1 *
          (hardCoreLaw (deleteClosedNeighborhood G p) z hz).characteristic θ) := by
  classical
  rw [hardCoreLaw_characteristic_eq_eval₂,
    hardCoreLaw_characteristic_eq_eval₂,
    hardCoreLaw_characteristic_eq_eval₂]
  rw [independencePolynomial_deleteVertex (G := G) (v := p),
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X]
  push_cast
  have hG0 : (independenceEval G z : ℂ) ≠ 0 := by
    exact_mod_cast (independenceEval_pos G hz).ne'
  have hD0 : (independenceEval (deleteVertex G p) z : ℂ) ≠ 0 := by
    exact_mod_cast (independenceEval_pos (deleteVertex G p) hz).ne'
  have hC0 : (independenceEval (deleteClosedNeighborhood G p) z : ℂ) ≠ 0 := by
    exact_mod_cast (independenceEval_pos (deleteClosedNeighborhood G p) hz).ne'
  field_simp [hG0, hD0, hC0]

/-- Triangle-inequality form of the parent-vacant characteristic mixture. -/
theorem hardCoreLaw_characteristicModulus_vertexDeletion_le
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (p : V)
    (z θ : ℝ) (hz : 0 < z) :
    let q := independenceEval (deleteVertex G p) z / independenceEval G z
    (hardCoreLaw G z hz).characteristicModulus θ ≤
      q * (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ +
        (1 - q) := by
  classical
  dsimp
  let L := hardCoreLaw G z hz
  let D := hardCoreLaw (deleteVertex G p) z hz
  let C := hardCoreLaw (deleteClosedNeighborhood G p) z hz
  let q : ℝ := independenceEval (deleteVertex G p) z / independenceEval G z
  let b : ℝ := z * independenceEval (deleteClosedNeighborhood G p) z /
    independenceEval G z
  have hq : 0 ≤ q := by
    dsimp [q]
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hb : 0 ≤ b := by
    dsimp [b]
    exact (div_pos (mul_pos hz (independenceEval_pos _ hz))
      (independenceEval_pos _ hz)).le
  have hsum : q + b = 1 := by
    dsimp [q, b]
    rw [← add_div, ← independenceEval_vertexDeletion G z p]
    exact div_self (independenceEval_pos G hz).ne'
  have hmix' : L.characteristic θ =
      (q : ℂ) * D.characteristic θ +
        (b : ℂ) * (FiniteLatticeLaw.phase θ 1 * C.characteristic θ) := by
    simpa [L, D, C, q, b] using
      hardCoreLaw_characteristic_vertexDeletion G p z θ hz
  calc
    L.characteristicModulus θ = ‖L.characteristic θ‖ :=
      characteristicModulus_eq_norm_characteristic L θ
    _ = ‖(q : ℂ) * D.characteristic θ +
          (b : ℂ) * (FiniteLatticeLaw.phase θ 1 * C.characteristic θ)‖ :=
      congrArg norm hmix'
    _ ≤ ‖(q : ℂ) * D.characteristic θ‖ +
          ‖(b : ℂ) * (FiniteLatticeLaw.phase θ 1 * C.characteristic θ)‖ :=
      norm_add_le _ _
    _ = q * D.characteristicModulus θ + b * C.characteristicModulus θ := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq, abs_of_nonneg hb,
        FiniteLatticeLaw.norm_phase,
        ← characteristicModulus_eq_norm_characteristic,
        ← characteristicModulus_eq_norm_characteristic]
      ring
    _ ≤ q * D.characteristicModulus θ + b := by
      have hc : b * C.characteristicModulus θ ≤ b :=
        mul_le_of_le_one_right hb
          (FiniteLatticeLaw.characteristicModulus_le_one C θ)
      linarith
    _ = q * D.characteristicModulus θ + (1 - q) := by linarith

/-- Parent-vacant mixture (A.33 precursor), with its weight represented by the
exact parent-deletion partition ratio. -/
theorem characteristicModulus_le_parentVacant_mix_ratio
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u)
    (z θ : ℝ) (hz : 0 < z) :
    let w := independenceEval (deleteVertex G p) z / independenceEval G z
    (hardCoreLaw G z hz).characteristicModulus θ ≤
      w * (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ +
        (1 - w) := by
  classical
  dsimp
  let w := independenceEval (deleteVertex G p) z / independenceEval G z
  have hw : 0 ≤ w := by
    dsimp [w]
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hdel := hardCoreLaw_characteristicModulus_vertexDeletion_le G p z θ hz
  have hfactor := hardCoreLaw_characteristicModulus_deleteVertex_child_factorAt
    hG R hpu z θ hz
  have hout := FiniteLatticeLaw.characteristicModulus_le_one
    (hardCoreLaw
      (G.induce {x : V | x ∈ R.childOutsideAt (G := G) p u}) z hz) θ
  have hchild0 := FiniteLatticeLaw.characteristicModulus_nonneg
    (hardCoreLaw (R.Subtree (G := G) u) z hz) θ
  have hdelchild :
      (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ ≤
        (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ := by
    rw [hfactor]
    exact mul_le_of_le_one_right hchild0 hout
  calc
    (hardCoreLaw G z hz).characteristicModulus θ ≤
        w * (hardCoreLaw (deleteVertex G p) z hz).characteristicModulus θ +
          (1 - w) := by simpa [w] using hdel
    _ ≤ w * (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ +
          (1 - w) := by
      nlinarith [mul_le_mul_of_nonneg_left hdelchild hw]

private theorem hardCoreLaw_absentMass_eq_deleteVertex_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : V) (z : ℝ) (hz : 0 < z) :
    (∑ s ∈ Finset.univ.filter
        (fun s : IndepFinset G => p ∉ s.val),
      (hardCoreLaw G z hz).probability s) =
      independenceEval (deleteVertex G p) z / independenceEval G z := by
  classical
  letI : Fintype (AvoidingIndepFinset G p) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  letI : Fintype (ContainingIndepFinset G p) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  rw [Finset.sum_filter]
  calc
    (∑ s : IndepFinset G,
        if p ∉ s.val then (hardCoreLaw G z hz).probability s else 0) =
        ∑ q : AvoidingIndepFinset G p ⊕ ContainingIndepFinset G p,
          Sum.elim
            (fun s => z ^ s.val.val.card / independenceEval G z)
            (fun _ => 0) q := by
      apply Fintype.sum_equiv (indepFinsetPartitionEquiv G p)
      intro s
      by_cases h : p ∈ s.val <;>
        simp [indepFinsetPartitionEquiv, h, hardCoreLaw]
    _ = ∑ s : AvoidingIndepFinset G p,
          z ^ s.val.val.card / independenceEval G z := by
      rw [Fintype.sum_sum_type]
      simp
    _ = ∑ t : IndepFinset (deleteVertex G p),
          z ^ t.val.card / independenceEval G z := by
      symm
      apply Fintype.sum_equiv (avoidingEquiv G p)
      intro t
      rw [avoidingEquiv_card]
    _ = (∑ t : IndepFinset (deleteVertex G p), z ^ t.val.card) /
          independenceEval G z := by rw [Finset.sum_div]
    _ = independenceEval (deleteVertex G p) z / independenceEval G z := by
      congr 1
      exact (independenceEval_eq_sum (G := deleteVertex G p) z).symm

/-- A vertex is vacant with probability at least `(1+z)⁻¹`, expressed as the
parent-deletion partition ratio. -/
theorem one_div_one_add_le_deleteVertex_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : V) (z : ℝ) (hz : 0 < z) :
    1 / (1 + z) ≤
      independenceEval (deleteVertex G p) z / independenceEval G z := by
  classical
  have hocc := hardCoreLaw_vertex_marginal_le G z hz p
  have hpart :
      (∑ s ∈ Finset.univ.filter
          (fun s : IndepFinset G => p ∉ s.val),
        (hardCoreLaw G z hz).probability s) +
      (∑ s ∈ Finset.univ.filter
          (fun s : IndepFinset G => p ∈ s.val),
        (hardCoreLaw G z hz).probability s) = 1 := by
    calc
      _ = ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s := by
        simpa only using
          (Finset.sum_filter_not_add_sum_filter
            (Finset.univ : Finset (IndepFinset G))
            (fun s : IndepFinset G => p ∈ s.val)
            (hardCoreLaw G z hz).probability)
      _ = 1 := (hardCoreLaw G z hz).probability_sum
  have hid : 1 - z / (1 + z) = 1 / (1 + z) := by
    field_simp
    ring
  rw [← hardCoreLaw_absentMass_eq_deleteVertex_ratio G p z hz, ← hid]
  linarith

/-- The parent-vacant event mass is exactly the parent-deletion partition
ratio. -/
theorem hardCoreLaw_parentVacant_eventMass_eq_ratio
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : V) (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).eventMass (fun I => p ∉ I.val) =
      independenceEval (deleteVertex G p) z / independenceEval G z := by
  classical
  unfold FiniteLatticeLaw.eventMass
  exact hardCoreLaw_absentMass_eq_deleteVertex_ratio G p z hz

/-- The arbitrary-activity parent-vacant characteristic mixture requested in
(A.33). -/
theorem characteristicModulus_le_parentVacant_mix
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u)
    (z θ : ℝ) (hz : 0 < z) :
    let μT := hardCoreLaw G z hz
    let μU := hardCoreLaw (R.Subtree (G := G) u) z hz
    let w := μT.eventMass (fun I => p ∉ I.val)
    μT.characteristicModulus θ ≤
      w * μU.characteristicModulus θ + (1 - w) := by
  classical
  dsimp
  rw [hardCoreLaw_parentVacant_eventMass_eq_ratio]
  exact characteristicModulus_le_parentVacant_mix_ratio hG R hpu z θ hz

/-- The depth-free one-edge defect transfer, equation (A.33). -/
theorem one_sub_subtreeCharacteristicModulus_le_one_add_ceiling_mul
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    1 - (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ ≤
      (1 + Z) * (1 - (hardCoreLaw G z hz).characteristicModulus θ) := by
  classical
  let w := independenceEval (deleteVertex G p) z / independenceEval G z
  let MT := (hardCoreLaw G z hz).characteristicModulus θ
  let MU := (hardCoreLaw (R.Subtree (G := G) u) z hz).characteristicModulus θ
  have hmix := characteristicModulus_le_parentVacant_mix_ratio hG R hpu z θ hz
  have hweighted : w * (1 - MU) ≤ 1 - MT := by
    dsimp [w, MT, MU] at *
    linarith
  have hwz : 1 / (1 + z) ≤ w := by
    dsimp [w]
    exact one_div_one_add_le_deleteVertex_ratio G p z hz
  have hZpos : 0 < Z := lt_of_lt_of_le hz hzZ
  have hzden : 0 < 1 + z := by linarith
  have hZden : 0 < 1 + Z := by linarith
  have hmono : 1 / (1 + Z) ≤ 1 / (1 + z) := by
    apply (div_le_div_iff₀ hZden hzden).2
    nlinarith
  have hw : 1 / (1 + Z) ≤ w := hmono.trans hwz
  have hMU : 0 ≤ 1 - MU := sub_nonneg.mpr
    (FiniteLatticeLaw.characteristicModulus_le_one _ _)
  have heta : (1 / (1 + Z)) * (1 - MU) ≤ 1 - MT := by
    calc
      (1 / (1 + Z)) * (1 - MU) ≤ w * (1 - MU) :=
        mul_le_mul_of_nonneg_right hw hMU
      _ ≤ 1 - MT := hweighted
  change 1 - MU ≤ (1 + Z) * (1 - MT)
  calc
    1 - MU = (1 + Z) * ((1 / (1 + Z)) * (1 - MU)) := by
      field_simp [hZden.ne']
    _ ≤ (1 + Z) * (1 - MT) :=
      mul_le_mul_of_nonneg_left heta hZden.le

end
end AppendixA
end Forest
end Erdos993
