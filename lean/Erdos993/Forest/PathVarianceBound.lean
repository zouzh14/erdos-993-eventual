import Erdos993.Forest.PathVarianceEnergy

/-!
# Depth-free variance along a decorated downward path

This module proves Appendix A, Lemma A.7 (A.40).  The proof first establishes
a stable scalar recurrence for the unconditioned local energies along the path,
then combines it with the intrinsic descendant-energy telescope.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance
open UniformFourthMoment

universe u

noncomputable local instance pathBoundDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α
noncomputable local instance pathBoundFiniteSubtype {α : Type*} [Fintype α]
    (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Uniform occupation cap along a path. -/
noncomputable def pathOccupationRatio (Z : ℝ) : ℝ := Z / (1 + Z)

/-- The unconditioned scalar energy `b_v d_v²`; the actual Bernoulli energy is
this quantity times `q_v`. -/
noncomputable def rootedFreeEnergyAt (R : ComponentRooting G) (z : ℝ)
    (hz : 0 < z) (u : V) : ℝ :=
  rootedOccupationProbabilityAt R z u * rootedDisplacementAt R z hz u ^ 2

/-- A concrete constant for the path-energy estimate. -/
noncomputable def pathEnergyConstant (Z : ℝ) : ℝ := 2 * (1 + Z) ^ 3

/-- The final A.7 constant. -/
noncomputable def pathVarianceConstant (Z : ℝ) : ℝ :=
  (pathEnergyConstant Z + 1) * (1 + Z)

/-- The path ratio lies strictly between zero and one. -/
theorem pathOccupationRatio_pos_lt_one (Z : ℝ) (hZ : 0 < Z) :
    0 < pathOccupationRatio Z ∧ pathOccupationRatio Z < 1 := by
  unfold pathOccupationRatio
  constructor
  · exact div_pos hZ (by linarith)
  · exact (div_lt_one (by linarith)).2 (by linarith)

/-- The explicit path-energy constant is positive. -/
theorem pathEnergyConstant_pos (Z : ℝ) (hZ : 0 < Z) : 0 < pathEnergyConstant Z := by
  unfold pathEnergyConstant
  positivity

/-- The explicit A.7 constant is positive (and is a finite real by type). -/
theorem pathVarianceConstant_pos (Z : ℝ) (hZ : 0 < Z) : 0 < pathVarianceConstant Z := by
  unfold pathVarianceConstant
  exact mul_pos (by linarith [pathEnergyConstant_pos Z hZ]) (by linarith)

/-- Weighted two-term square inequality used for the stable path recurrence. -/
theorem add_sq_le_div_add_div (r x y : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    (x + y) ^ 2 ≤ x ^ 2 / r + y ^ 2 / (1 - r) := by
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hs0 : 0 < 1 - r := sub_pos.mpr hr1
  have hsne : 1 - r ≠ 0 := ne_of_gt hs0
  have hden : 0 < r * (1 - r) := mul_pos hr0 hs0
  have hmul : r * (1 - r) * (x + y) ^ 2 ≤
      (1 - r) * x ^ 2 + r * y ^ 2 := by
    nlinarith [sq_nonneg ((1 - r) * x - r * y)]
  calc
    (x + y) ^ 2 =
        (r * (1 - r) * (x + y) ^ 2) / (r * (1 - r)) := by
          field_simp [hrne, hsne]
    _ ≤ ((1 - r) * x ^ 2 + r * y ^ 2) / (r * (1 - r)) :=
      div_le_div_of_nonneg_right hmul hden.le
    _ = x ^ 2 / r + y ^ 2 / (1 - r) := by
      field_simp [hrne, hsne]

/-- Elementary bound for the inhomogeneous term. -/
theorem one_sub_sq_le_two_mul (c : ℝ) :
    (1 - c) ^ 2 ≤ 2 * (1 + c ^ 2) := by
  nlinarith [sq_nonneg (c + 1)]

/-- Free energy is nonnegative. -/
theorem rootedFreeEnergyAt_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 ≤ rootedFreeEnergyAt R z hz u := by
  unfold rootedFreeEnergyAt
  exact mul_nonneg (rootedOccupationProbabilityAt_pos R z hz u).le (sq_nonneg _)

/-- The root energy is one of the nonnegative terms in descendant energy. -/
theorem rootedEnergyAt_le_descendantEnergyAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (u : V) :
    rootedEnergyAt R z hz u ≤ descendantEnergyAt R z hz u := by
  rw [descendantEnergyAt_eq_root_add_sum_children hG R z hz u]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun v hv => descendantEnergyAt_nonneg R z hz v)

/-- Actual rooted energy is at most free energy. -/
theorem rootedEnergyAt_le_rootedFreeEnergyAt
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedEnergyAt R z hz u ≤ rootedFreeEnergyAt R z hz u := by
  let b := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let d := rootedDisplacementAt R z hz u
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hq0 : 0 ≤ q := by
    dsimp [q]
    unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
    exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le
  have hq1 : q ≤ 1 := by
    dsimp [q, b]
    linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
      rootedOccupationProbabilityAt_pos R z hz u]
  change b * q * d ^ 2 ≤ b * d ^ 2
  nlinarith [mul_nonneg hb0 (sq_nonneg d),
    mul_le_mul_of_nonneg_left hq1 hb0]

/-- Uniform vacancy converts free energy back to actual rooted energy. -/
theorem rootedFreeEnergyAt_le_one_add_Z_mul_rootedEnergyAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    rootedFreeEnergyAt R z hz u ≤ (1 + Z) * rootedEnergyAt R z hz u := by
  let b := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let d := rootedDisplacementAt R z hz u
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hZ1 : 0 < 1 + Z := by linarith
  have hq : 1 / (1 + Z) ≤ q := by
    dsimp [q]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
      hG R z Z hz hzZ u
  have hf0 : 0 ≤ b * d ^ 2 :=
    mul_nonneg (rootedOccupationProbabilityAt_pos R z hz u).le (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hq hf0
  change b * d ^ 2 ≤ (1 + Z) * (b * q * d ^ 2)
  calc
    b * d ^ 2 = (1 + Z) * ((1 / (1 + Z)) * (b * d ^ 2)) := by
      field_simp
    _ ≤ (1 + Z) * (q * (b * d ^ 2)) :=
      mul_le_mul_of_nonneg_left hmul hZ1.le
    _ = (1 + Z) * (b * q * d ^ 2) := by ring

/-- Weighted Cauchy--Schwarz for the side children of a chosen path edge. -/
theorem side_occupation_displacement_sum_sq_le_odds_mul_energy
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    (∑ w ∈ (R.children (G := G) u).erase v,
      rootedOccupationProbabilityAt R z w * rootedDisplacementAt R z hz w) ^ 2 ≤
      (∑ w ∈ (R.children (G := G) u).erase v,
        rootedOccupationProbabilityAt R z w /
          rootedVacancyProbabilityAt R z w) *
      ∑ w ∈ (R.children (G := G) u).erase v,
        rootedEnergyAt R z hz w := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro w hw
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz w).le
      (by
        unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
        exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le)
  · intro w hw
    exact rootedEnergyAt_nonneg R z hz w
  · intro w hw
    unfold rootedEnergyAt
    have hqne : rootedVacancyProbabilityAt R z w ≠ 0 := by
      unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
      exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).ne'
    field_simp [hqne]

/-- The side-child odds retain the root-scaled bound from (A.28). -/
theorem rootedOccupation_mul_sideOddsSum_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u v : V) :
    rootedOccupationProbabilityAt R z u *
        (∑ w ∈ (R.children (G := G) u).erase v,
          rootedOccupationProbabilityAt R z w /
            rootedVacancyProbabilityAt R z w) ≤ Z := by
  have hsum : (∑ w ∈ (R.children (G := G) u).erase v,
      rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w) ≤
      ∑ w ∈ R.children (G := G) u,
        rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    intro w hw hnot
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz w).le
      (by
        unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
        exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le)
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
  calc
    rootedOccupationProbabilityAt R z u *
        (∑ w ∈ (R.children (G := G) u).erase v,
          rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w) ≤
      rootedOccupationProbabilityAt R z u *
        (∑ w ∈ R.children (G := G) u,
          rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w) :=
      mul_le_mul_of_nonneg_left hsum hb0
    _ ≤ Z := rootedOccupation_mul_childOddsSum_le hG R Z z hz hzZ u

/-- Isolate the selected path child in the displacement recurrence. -/
theorem rootedDisplacementAt_eq_pathChild_side
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    rootedDisplacementAt R z hz u =
      1 - rootedOccupationProbabilityAt R z v * rootedDisplacementAt R z hz v -
        ∑ w ∈ (R.children (G := G) u).erase v,
          rootedOccupationProbabilityAt R z w * rootedDisplacementAt R z hz w := by
  have hv : v ∈ R.children (G := G) u :=
    (R.mem_children (G := G) u v).mpr huv
  rw [rootedDisplacementAt_eq_one_sub_sum hG R z hz u]
  rw [← Finset.sum_erase_add _ _ hv]
  ring

/-- Stable one-edge estimate for the free energies.  Its contraction factor is
`Z/(1+Z)<1`, while the forcing consists only of the current occupation mass
and side-child rooted energies. -/
theorem rootedFreeEnergyAt_path_step
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) {u v : V}
    (huv : R.IsChild (G := G) u v) :
    rootedFreeEnergyAt R z hz u ≤
      pathOccupationRatio Z * rootedFreeEnergyAt R z hz v +
      2 * (1 + Z) * rootedOccupationProbabilityAt R z u +
      2 * Z * (1 + Z) *
        (∑ w ∈ (R.children (G := G) u).erase v,
          rootedEnergyAt R z hz w) := by
  let r := pathOccupationRatio Z
  let b := rootedOccupationProbabilityAt R z u
  let bv := rootedOccupationProbabilityAt R z v
  let d := rootedDisplacementAt R z hz u
  let dv := rootedDisplacementAt R z hz v
  let c := ∑ w ∈ (R.children (G := G) u).erase v,
    rootedOccupationProbabilityAt R z w * rootedDisplacementAt R z hz w
  let O := ∑ w ∈ (R.children (G := G) u).erase v,
    rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w
  let E := ∑ w ∈ (R.children (G := G) u).erase v,
    rootedEnergyAt R z hz w
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hr := pathOccupationRatio_pos_lt_one Z hZ
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hbv0 : 0 ≤ bv := by
    dsimp [bv]
    exact (rootedOccupationProbabilityAt_pos R z hz v).le
  have hbr : b ≤ r := by
    dsimp [b, r]
    exact rootedOccupationProbabilityAt_le_ceiling_ratio hG R z Z hz hzZ u
  have hbvr : bv ≤ r := by
    dsimp [bv, r]
    exact rootedOccupationProbabilityAt_le_ceiling_ratio hG R z Z hz hzZ v
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun w hw => rootedEnergyAt_nonneg R z hz w
  have hO0 : 0 ≤ O := by
    dsimp [O]
    apply Finset.sum_nonneg
    intro w hw
    exact div_nonneg (rootedOccupationProbabilityAt_pos R z hz w).le
      (by
        unfold rootedVacancyProbabilityAt rootedQAt rootedPAt
        exact (div_pos (independenceEval_pos _ hz) (independenceEval_pos _ hz)).le)
  have hrec : d = -(bv * dv) + (1 - c) := by
    dsimp [d, bv, dv, c]
    rw [rootedDisplacementAt_eq_pathChild_side hG R z hz huv]
    ring
  have hsq : d ^ 2 ≤ (bv * dv) ^ 2 / r + (1 - c) ^ 2 / (1 - r) := by
    rw [hrec]
    simpa only [neg_sq] using add_sq_le_div_add_div r (-(bv * dv)) (1 - c) hr.1 hr.2
  have hbb : b * bv ≤ r * r :=
    mul_le_mul hbr hbvr hbv0 hr.1.le
  have hcoef : b * bv / r ≤ r := by
    apply (div_le_iff₀ hr.1).2
    simpa [mul_assoc] using hbb
  have hfreev0 : 0 ≤ bv * dv ^ 2 := mul_nonneg hbv0 (sq_nonneg _)
  have hchild : b * ((bv * dv) ^ 2 / r) ≤ r * (bv * dv ^ 2) := by
    calc
      b * ((bv * dv) ^ 2 / r) = (b * bv / r) * (bv * dv ^ 2) := by
        field_simp [ne_of_gt hr.1]
      _ ≤ r * (bv * dv ^ 2) :=
        mul_le_mul_of_nonneg_right hcoef hfreev0
  have hcs : c ^ 2 ≤ O * E := by
    dsimp [c, O, E]
    exact side_occupation_displacement_sum_sq_le_odds_mul_energy R z hz u v
  have hOdds : b * O ≤ Z := by
    dsimp [b, O]
    exact rootedOccupation_mul_sideOddsSum_le hG R Z z hz hzZ u v
  have hbc : b * c ^ 2 ≤ Z * E := by
    calc
      b * c ^ 2 ≤ b * (O * E) := mul_le_mul_of_nonneg_left hcs hb0
      _ = (b * O) * E := by ring
      _ ≤ Z * E := mul_le_mul_of_nonneg_right hOdds hE0
  have heta : 1 - r = 1 / (1 + Z) := by
    dsimp [r, pathOccupationRatio]
    field_simp
    ring
  have hinv : 1 / (1 - r) = 1 + Z := by
    rw [heta]
    field_simp
  have hside : b * ((1 - c) ^ 2 / (1 - r)) ≤
      2 * (1 + Z) * b + 2 * Z * (1 + Z) * E := by
    have hysq := one_sub_sq_le_two_mul c
    have hden0 : 0 ≤ 1 / (1 - r) := (div_pos (by norm_num) (sub_pos.mpr hr.2)).le
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hysq hden0) hb0
    calc
      b * ((1 - c) ^ 2 / (1 - r)) ≤
          b * (2 * (1 + c ^ 2) * (1 / (1 - r))) := by
            simpa [div_eq_mul_inv, mul_assoc] using hmul
      _ = 2 * (1 + Z) * b + 2 * (1 + Z) * (b * c ^ 2) := by
        rw [hinv]
        ring
      _ ≤ 2 * (1 + Z) * b + 2 * (1 + Z) * (Z * E) := by
        exact add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left hbc (by positivity : 0 ≤ 2 * (1 + Z)))
      _ = 2 * (1 + Z) * b + 2 * Z * (1 + Z) * E := by ring
  change b * d ^ 2 ≤
    r * (bv * dv ^ 2) + 2 * (1 + Z) * b + 2 * Z * (1 + Z) * E
  calc
    b * d ^ 2 ≤ b * ((bv * dv) ^ 2 / r + (1 - c) ^ 2 / (1 - r)) :=
      mul_le_mul_of_nonneg_left hsq hb0
    _ = b * ((bv * dv) ^ 2 / r) + b * ((1 - c) ^ 2 / (1 - r)) := by ring
    _ ≤ r * (bv * dv ^ 2) +
        (2 * (1 + Z) * b + 2 * Z * (1 + Z) * E) := add_le_add hchild hside
    _ = r * (bv * dv ^ 2) + 2 * (1 + Z) * b +
        2 * Z * (1 + Z) * E := by ring

/-- Initial-list sums preserve pointwise inequalities. -/
theorem DownwardPath.initialSum_mono
    (f g : V → ℝ) (hfg : ∀ u, f u ≤ g u) : ∀ l : List V,
    DownwardPath.initialSum f l ≤ DownwardPath.initialSum g l
  | [] => by simp [DownwardPath.initialSum]
  | [_] => by simp [DownwardPath.initialSum]
  | u :: v :: rest => by
      simp only [DownwardPath.initialSum]
      exact add_le_add (hfg u)
        (DownwardPath.initialSum_mono f g hfg (v :: rest))

/-- The initial sum of the zero function vanishes. -/
theorem DownwardPath.initialSum_zero : ∀ l : List V,
    DownwardPath.initialSum (fun _ => 0) l = 0
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
      simp only [DownwardPath.initialSum, zero_add]
      exact DownwardPath.initialSum_zero (v :: rest)

/-- Initial-list sums of nonnegative functions are nonnegative. -/
theorem DownwardPath.initialSum_nonneg
    (f : V → ℝ) (hf : ∀ u, 0 ≤ f u) (l : List V) :
    0 ≤ DownwardPath.initialSum f l := by
  rw [← DownwardPath.initialSum_zero l]
  exact DownwardPath.initialSum_mono (fun _ => 0) f hf l

/-- Terminal evaluation preserves pointwise inequalities. -/
theorem DownwardPath.terminalValue_mono
    (f g : V → ℝ) (hfg : ∀ u, f u ≤ g u) : ∀ l : List V,
    DownwardPath.terminalValue f l ≤ DownwardPath.terminalValue g l
  | [] => by simp [DownwardPath.terminalValue]
  | [_] => by simp [DownwardPath.terminalValue, hfg]
  | u :: v :: rest => by
      simp only [DownwardPath.terminalValue]
      exact DownwardPath.terminalValue_mono f g hfg (v :: rest)

/-- Terminal evaluation of the zero function vanishes. -/
theorem DownwardPath.terminalValue_zero : ∀ l : List V,
    DownwardPath.terminalValue (fun _ => 0) l = 0
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
      simp only [DownwardPath.terminalValue]
      exact DownwardPath.terminalValue_zero (v :: rest)

/-- Terminal evaluation commutes with multiplication by a constant. -/
theorem DownwardPath.terminalValue_const_mul
    (c : ℝ) (f : V → ℝ) : ∀ l : List V,
    DownwardPath.terminalValue (fun u => c * f u) l =
      c * DownwardPath.terminalValue f l
  | [] => by simp [DownwardPath.terminalValue]
  | [_] => by simp [DownwardPath.terminalValue]
  | u :: v :: rest => by
      simp only [DownwardPath.terminalValue]
      exact DownwardPath.terminalValue_const_mul c f (v :: rest)

/-- Terminal evaluation of a nonnegative function is nonnegative. -/
theorem DownwardPath.terminalValue_nonneg
    (f : V → ℝ) (hf : ∀ u, 0 ≤ f u) (l : List V) :
    0 ≤ DownwardPath.terminalValue f l := by
  rw [← DownwardPath.terminalValue_zero l]
  exact DownwardPath.terminalValue_mono (fun _ => 0) f hf l

/-- Side-child sums preserve pointwise inequalities. -/
theorem DownwardPath.sideSum_mono
    (R : ComponentRooting G) (f g : V → ℝ) (hfg : ∀ u, f u ≤ g u) :
    ∀ l : List V, DownwardPath.sideSum R f l ≤ DownwardPath.sideSum R g l
  | [] => by simp [DownwardPath.sideSum]
  | [_] => by simp [DownwardPath.sideSum]
  | u :: v :: rest => by
      simp only [DownwardPath.sideSum]
      exact add_le_add
        (Finset.sum_le_sum fun w hw => hfg w)
        (DownwardPath.sideSum_mono R f g hfg (v :: rest))

/-- The side-child sum of the zero function vanishes. -/
theorem DownwardPath.sideSum_zero (R : ComponentRooting G) : ∀ l : List V,
    DownwardPath.sideSum R (fun _ => 0) l = 0
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
      simp only [DownwardPath.sideSum, Finset.sum_const_zero, zero_add]
      exact DownwardPath.sideSum_zero R (v :: rest)

/-- Side-child summation commutes with multiplication by a constant. -/
theorem DownwardPath.sideSum_const_mul
    (R : ComponentRooting G) (c : ℝ) (f : V → ℝ) : ∀ l : List V,
    DownwardPath.sideSum R (fun u => c * f u) l =
      c * DownwardPath.sideSum R f l
  | [] => by simp [DownwardPath.sideSum]
  | [_] => by simp [DownwardPath.sideSum]
  | u :: v :: rest => by
      simp only [DownwardPath.sideSum]
      rw [DownwardPath.sideSum_const_mul R c f (v :: rest)]
      rw [← Finset.mul_sum]
      ring

/-- Side-child sums of nonnegative functions are nonnegative. -/
theorem DownwardPath.sideSum_nonneg
    (R : ComponentRooting G) (f : V → ℝ) (hf : ∀ u, 0 ≤ f u)
    (l : List V) : 0 ≤ DownwardPath.sideSum R f l := by
  rw [← DownwardPath.sideSum_zero R l]
  exact DownwardPath.sideSum_mono R (fun _ => 0) f hf l

/-- Solving one scalar contraction inequality. -/
theorem le_div_one_sub_of_le_contraction
    (r S T D : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (h : S ≤ r * (S + T) + D) :
    S ≤ (r * T + D) / (1 - r) := by
  apply (le_div_iff₀ (sub_pos.mpr hr1)).2
  nlinarith

/-- Summing the stable one-edge estimate over any child chain. -/
theorem pathFreeEnergy_initialSum_le_tail
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) :
    ∀ (l : List V), l.IsChain (R.IsChild (G := G)) →
    DownwardPath.initialSum (rootedFreeEnergyAt R z hz) l ≤
      pathOccupationRatio Z *
        ((l.tail.map (rootedFreeEnergyAt R z hz)).sum) +
      2 * (1 + Z) *
        DownwardPath.initialSum (rootedOccupationProbabilityAt R z) l +
      2 * Z * (1 + Z) *
        DownwardPath.sideSum R (rootedEnergyAt R z hz) l
  | [], _ => by simp [DownwardPath.initialSum, DownwardPath.sideSum]
  | [_], _ => by simp [DownwardPath.initialSum, DownwardPath.sideSum]
  | u :: v :: rest, hchain => by
      have huv : R.IsChild (G := G) u v := hchain.rel_head
      have htail : (v :: rest).IsChain (R.IsChild (G := G)) := hchain.tail
      have hstep := rootedFreeEnergyAt_path_step hG R Z z hz hzZ huv
      have ih := pathFreeEnergy_initialSum_le_tail hG R Z z hz hzZ
        (v :: rest) htail
      simp only [DownwardPath.initialSum, DownwardPath.sideSum,
        List.tail_cons, List.map_cons, List.sum_cons]
      simp only [DownwardPath.initialSum, DownwardPath.sideSum,
        List.tail_cons, List.map_cons, List.sum_cons] at ih
      nlinarith

/-- The free energies on the nonterminal vertices are controlled without a
factor depending on the length of the path. -/
theorem pathFreeEnergy_initialSum_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (P : DownwardPath R) :
    DownwardPath.initialSum (rootedFreeEnergyAt R z hz) P.vertices ≤
      (1 + Z) *
        (pathOccupationRatio Z *
            DownwardPath.terminalValue (rootedFreeEnergyAt R z hz) P.vertices +
          2 * (1 + Z) *
            DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
          2 * Z * (1 + Z) *
            DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices) := by
  let f := rootedFreeEnergyAt R z hz
  let S := DownwardPath.initialSum f P.vertices
  let T := DownwardPath.terminalValue f P.vertices
  let B := DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices
  let E := DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices
  let r := pathOccupationRatio Z
  let D := 2 * (1 + Z) * B + 2 * Z * (1 + Z) * E
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hr := pathOccupationRatio_pos_lt_one Z hZ
  have hagg := pathFreeEnergy_initialSum_le_tail hG R Z z hz hzZ
    P.vertices P.isChain
  have htail : ((P.vertices.tail.map f).sum) ≤ S + T := by
    dsimp [S, T, f]
    exact DownwardPath.sum_tail_le_initial_add_terminal
      (rootedFreeEnergyAt R z hz) (rootedFreeEnergyAt_nonneg R z hz) P.vertices
  have hcon : S ≤ r * (S + T) + D := by
    dsimp [S, T, B, E, r, D, f] at hagg ⊢
    calc
      DownwardPath.initialSum (rootedFreeEnergyAt R z hz) P.vertices ≤
          pathOccupationRatio Z *
              ((P.vertices.tail.map (rootedFreeEnergyAt R z hz)).sum) +
            2 * (1 + Z) *
              DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
            2 * Z * (1 + Z) *
              DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices := hagg
      _ ≤ pathOccupationRatio Z *
              (DownwardPath.initialSum (rootedFreeEnergyAt R z hz) P.vertices +
                DownwardPath.terminalValue (rootedFreeEnergyAt R z hz) P.vertices) +
            2 * (1 + Z) *
              DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
            2 * Z * (1 + Z) *
              DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices := by
          have hm := mul_le_mul_of_nonneg_left htail hr.1.le
          nlinarith
      _ = pathOccupationRatio Z *
              (DownwardPath.initialSum (rootedFreeEnergyAt R z hz) P.vertices +
                DownwardPath.terminalValue (rootedFreeEnergyAt R z hz) P.vertices) +
            (2 * (1 + Z) *
              DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
            2 * Z * (1 + Z) *
              DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices) := by ring
  have hsolve := le_div_one_sub_of_le_contraction r S T D hr.1 hr.2 hcon
  have heta : 1 - r = 1 / (1 + Z) := by
    dsimp [r, pathOccupationRatio]
    field_simp
    ring
  have hresult : S ≤ (1 + Z) * (r * T + D) := by
    rw [heta] at hsolve
    convert hsolve using 1 <;> field_simp <;> ring
  dsimp [S, T, B, E, r, D, f] at hresult ⊢
  convert hresult using 1 <;> ring

/-- Every rooted energy on the path is bounded by one common, depth-free
constant times occupation mass plus side and terminal rooted energies. -/
theorem pathEnergy_initialSum_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (P : DownwardPath R) :
    DownwardPath.initialSum (rootedEnergyAt R z hz) P.vertices ≤
      pathEnergyConstant Z *
        (DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
          DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices +
          DownwardPath.terminalValue (rootedEnergyAt R z hz) P.vertices) := by
  let BI := DownwardPath.initialSum
    (rootedOccupationProbabilityAt R z) P.vertices
  let ES := DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices
  let ET := DownwardPath.terminalValue (rootedEnergyAt R z hz) P.vertices
  let FT := DownwardPath.terminalValue (rootedFreeEnergyAt R z hz) P.vertices
  let r := pathOccupationRatio Z
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hIF := DownwardPath.initialSum_mono
    (rootedEnergyAt R z hz) (rootedFreeEnergyAt R z hz)
    (rootedEnergyAt_le_rootedFreeEnergyAt R z hz) P.vertices
  have hmain := pathFreeEnergy_initialSum_le hG R Z z hz hzZ P
  have hterm := DownwardPath.terminalValue_mono
    (rootedFreeEnergyAt R z hz)
    (fun u => (1 + Z) * rootedEnergyAt R z hz u)
    (rootedFreeEnergyAt_le_one_add_Z_mul_rootedEnergyAt hG R Z z hz hzZ)
    P.vertices
  have hterm' : FT ≤ (1 + Z) * ET := by
    dsimp [FT, ET]
    convert hterm using 1
    exact (DownwardPath.terminalValue_const_mul (1 + Z)
      (rootedEnergyAt R z hz) P.vertices).symm
  have hBI0 : 0 ≤ BI := DownwardPath.initialSum_nonneg _
    (fun u => (rootedOccupationProbabilityAt_pos R z hz u).le) _
  have hES0 : 0 ≤ ES := DownwardPath.sideSum_nonneg R _
    (rootedEnergyAt_nonneg R z hz) _
  have hET0 : 0 ≤ ET := DownwardPath.terminalValue_nonneg _
    (rootedEnergyAt_nonneg R z hz) _
  have hr := pathOccupationRatio_pos_lt_one Z hZ
  have hupper :
      DownwardPath.initialSum (rootedEnergyAt R z hz) P.vertices ≤
        (1 + Z) * (r * ((1 + Z) * ET) +
          2 * (1 + Z) * BI + 2 * Z * (1 + Z) * ES) := by
    calc
      _ ≤ DownwardPath.initialSum (rootedFreeEnergyAt R z hz) P.vertices := hIF
      _ ≤ (1 + Z) * (r * FT + 2 * (1 + Z) * BI +
          2 * Z * (1 + Z) * ES) := by simpa [FT, BI, ES] using hmain
      _ ≤ (1 + Z) * (r * ((1 + Z) * ET) +
          2 * (1 + Z) * BI + 2 * Z * (1 + Z) * ES) := by
        have hrt := mul_le_mul_of_nonneg_left hterm' hr.1.le
        have hins : r * FT + 2 * (1 + Z) * BI + 2 * Z * (1 + Z) * ES ≤
            r * ((1 + Z) * ET) + 2 * (1 + Z) * BI +
              2 * Z * (1 + Z) * ES := by
          nlinarith
        exact mul_le_mul_of_nonneg_left hins (by linarith)
  have hcT : (1 + Z) * (r * ((1 + Z) * ET)) ≤
      pathEnergyConstant Z * ET := by
    have hcoef : (1 + Z) * (r * (1 + Z)) ≤ pathEnergyConstant Z := by
      dsimp [r, pathOccupationRatio, pathEnergyConstant]
      field_simp
      nlinarith [sq_nonneg Z, mul_pos (by linarith : 0 < 1 + Z)
        (by positivity : 0 < (1 + Z) ^ 2)]
    convert mul_le_mul_of_nonneg_right hcoef hET0 using 1 <;> ring
  have hcB : (1 + Z) * (2 * (1 + Z) * BI) ≤
      pathEnergyConstant Z * BI := by
    have hcoef : (1 + Z) * (2 * (1 + Z)) ≤ pathEnergyConstant Z := by
      dsimp [pathEnergyConstant]
      nlinarith [sq_nonneg Z, mul_nonneg (by linarith : 0 ≤ 1 + Z)
        (sq_nonneg (1 + Z))]
    convert mul_le_mul_of_nonneg_right hcoef hBI0 using 1 <;> ring
  have hcS : (1 + Z) * (2 * Z * (1 + Z) * ES) ≤
      pathEnergyConstant Z * ES := by
    have hcoef : (1 + Z) * (2 * Z * (1 + Z)) ≤ pathEnergyConstant Z := by
      dsimp [pathEnergyConstant]
      nlinarith [sq_nonneg Z, mul_nonneg (by linarith : 0 ≤ 1 + Z)
        (sq_nonneg (1 + Z))]
    convert mul_le_mul_of_nonneg_right hcoef hES0 using 1 <;> ring
  calc
    _ ≤ (1 + Z) * (r * ((1 + Z) * ET) +
          2 * (1 + Z) * BI + 2 * Z * (1 + Z) * ES) := hupper
    _ = (1 + Z) * (r * ((1 + Z) * ET)) +
          (1 + Z) * (2 * (1 + Z) * BI) +
          (1 + Z) * (2 * Z * (1 + Z) * ES) := by ring
    _ ≤ pathEnergyConstant Z * ET + pathEnergyConstant Z * BI +
          pathEnergyConstant Z * ES := add_le_add (add_le_add hcT hcB) hcS
    _ = pathEnergyConstant Z * (BI + ES + ET) := by ring

/-- Raw descendant energy decomposes exactly into energies on the path, raw
energies in the decorated side forest, and the terminal descendant subtree. -/
theorem descendantEnergyAt_eq_path_decomposition
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) :
    ∀ (u : V) (rest : List V),
      (u :: rest).IsChain (R.IsChild (G := G)) →
      descendantEnergyAt R z hz u =
        DownwardPath.initialSum (rootedEnergyAt R z hz) (u :: rest) +
        DownwardPath.sideSum R (descendantEnergyAt R z hz) (u :: rest) +
        DownwardPath.terminalValue (descendantEnergyAt R z hz) (u :: rest)
  | u, [], _ => by
      simp [DownwardPath.initialSum, DownwardPath.sideSum,
        DownwardPath.terminalValue]
  | u, v :: rest, hchain => by
      have huv : R.IsChild (G := G) u v := hchain.rel_head
      have hv : v ∈ R.children (G := G) u :=
        (R.mem_children (G := G) u v).mpr huv
      have htail : (v :: rest).IsChain (R.IsChild (G := G)) := hchain.tail
      have ih := descendantEnergyAt_eq_path_decomposition hG R z hz v rest htail
      rw [descendantEnergyAt_eq_root_add_sum_children hG R z hz u]
      rw [← Finset.sum_erase_add _ _ hv]
      rw [ih]
      simp only [DownwardPath.initialSum, DownwardPath.sideSum,
        DownwardPath.terminalValue]
      ring

/-- Exact decorated-side-forest decomposition for a structurally nontrivial
`DownwardPath`. -/
theorem DownwardPath.descendantEnergyAt_start_eq_decomposition
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z : ℝ) (hz : 0 < z) (P : DownwardPath R) :
    descendantEnergyAt R z hz P.start =
      DownwardPath.initialSum (rootedEnergyAt R z hz) P.vertices +
      DownwardPath.sideSum R (descendantEnergyAt R z hz) P.vertices +
      DownwardPath.terminalValue (descendantEnergyAt R z hz) P.vertices := by
  exact descendantEnergyAt_eq_path_decomposition hG R z hz P.start
    (P.next :: P.tail) P.isChain

/-- Occupation mass over the nonterminal vertices of a downward path. -/
noncomputable def DownwardPath.occupationMass
    (R : ComponentRooting G) (z : ℝ) (P : DownwardPath R) : ℝ :=
  DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices

/-- Total variance of the terminal rooted subtree. -/
noncomputable def DownwardPath.terminalSubtreeVariance
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (P : DownwardPath R) : ℝ :=
  DownwardPath.terminalValue (subtreeVarianceAt R z hz) P.vertices

/-- Total variance of all side subtrees decorating a downward path. -/
noncomputable def DownwardPath.sideForestVariance
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    (P : DownwardPath R) : ℝ :=
  DownwardPath.sideSum R (subtreeVarianceAt R z hz) P.vertices

/-- **Appendix A, Lemma A.7, equation (A.40).**  Along every finite downward
path, the variance at its first vertex is bounded by occupation mass along the
path plus the variances of the terminal subtree and decorated side forest.  The
constant is independent of the path length, tree depth, graph, and rooting. -/
theorem varianceAlongDownwardPath_le
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (P : DownwardPath R) :
    subtreeVarianceAt R z hz P.start ≤
      pathVarianceConstant Z *
        (P.occupationMass R z + P.terminalSubtreeVariance R z hz +
          P.sideForestVariance R z hz) := by
  let BI := P.occupationMass R z
  let DS := DownwardPath.sideSum R (descendantEnergyAt R z hz) P.vertices
  let DT := DownwardPath.terminalValue (descendantEnergyAt R z hz) P.vertices
  let VS := P.sideForestVariance R z hz
  let VT := P.terminalSubtreeVariance R z hz
  let EI := DownwardPath.initialSum (rootedEnergyAt R z hz) P.vertices
  let C := pathEnergyConstant Z
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hBI0 : 0 ≤ BI := by
    dsimp [BI, DownwardPath.occupationMass]
    exact DownwardPath.initialSum_nonneg _
      (fun u => (rootedOccupationProbabilityAt_pos R z hz u).le) _
  have hDS0 : 0 ≤ DS := by
    dsimp [DS]
    exact DownwardPath.sideSum_nonneg R _
      (descendantEnergyAt_nonneg R z hz) _
  have hDT0 : 0 ≤ DT := by
    dsimp [DT]
    exact DownwardPath.terminalValue_nonneg _
      (descendantEnergyAt_nonneg R z hz) _
  have hVS0 : 0 ≤ VS := by
    dsimp [VS, DownwardPath.sideForestVariance]
    exact DownwardPath.sideSum_nonneg R _
      (fun u => (R.subtreeLawAt z hz u).variance_nonneg) _
  have hVT0 : 0 ≤ VT := by
    dsimp [VT, DownwardPath.terminalSubtreeVariance]
    exact DownwardPath.terminalValue_nonneg _
      (fun u => (R.subtreeLawAt z hz u).variance_nonneg) _
  have hES : DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices ≤ DS := by
    dsimp [DS]
    exact DownwardPath.sideSum_mono R _ _
      (rootedEnergyAt_le_descendantEnergyAt hG R z hz) _
  have hET : DownwardPath.terminalValue (rootedEnergyAt R z hz) P.vertices ≤ DT := by
    dsimp [DT]
    exact DownwardPath.terminalValue_mono _ _
      (rootedEnergyAt_le_descendantEnergyAt hG R z hz) _
  have hpath := pathEnergy_initialSum_le hG R Z z hz hzZ P
  have hC0 : 0 ≤ C := (pathEnergyConstant_pos Z hZ).le
  have hEI : EI ≤ C * (BI + DS + DT) := by
    dsimp [EI, C, BI, DownwardPath.occupationMass] at hpath ⊢
    calc
      _ ≤ pathEnergyConstant Z *
          (DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
            DownwardPath.sideSum R (rootedEnergyAt R z hz) P.vertices +
            DownwardPath.terminalValue (rootedEnergyAt R z hz) P.vertices) := hpath
      _ ≤ pathEnergyConstant Z *
          (DownwardPath.initialSum (rootedOccupationProbabilityAt R z) P.vertices +
            DS + DT) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl hES) hET) hC0
  have hdec := P.descendantEnergyAt_start_eq_decomposition hG R z hz
  have hdesc : descendantEnergyAt R z hz P.start ≤
      (C + 1) * (BI + DS + DT) := by
    change descendantEnergyAt R z hz P.start = EI + DS + DT at hdec
    rw [hdec]
    nlinarith
  have hDS : DS ≤ (1 + Z) * VS := by
    dsimp [DS, VS, DownwardPath.sideForestVariance]
    have hmono := DownwardPath.sideSum_mono R
      (descendantEnergyAt R z hz)
      (fun u => (1 + Z) * subtreeVarianceAt R z hz u)
      (descendantEnergyAt_le_one_add_Z_mul_subtreeVarianceAt hG R Z z hz hzZ)
      P.vertices
    rw [DownwardPath.sideSum_const_mul] at hmono
    exact hmono
  have hDT : DT ≤ (1 + Z) * VT := by
    dsimp [DT, VT, DownwardPath.terminalSubtreeVariance]
    have hmono := DownwardPath.terminalValue_mono
      (descendantEnergyAt R z hz)
      (fun u => (1 + Z) * subtreeVarianceAt R z hz u)
      (descendantEnergyAt_le_one_add_Z_mul_subtreeVarianceAt hG R Z z hz hzZ)
      P.vertices
    rw [DownwardPath.terminalValue_const_mul] at hmono
    exact hmono
  have hsum : BI + DS + DT ≤ (1 + Z) * (BI + VT + VS) := by
    nlinarith
  have hvarstart := subtreeVarianceAt_le_descendantEnergyAt hG R z hz P.start
  calc
    subtreeVarianceAt R z hz P.start ≤ descendantEnergyAt R z hz P.start := hvarstart
    _ ≤ (C + 1) * (BI + DS + DT) := hdesc
    _ ≤ (C + 1) * ((1 + Z) * (BI + VT + VS)) :=
      mul_le_mul_of_nonneg_left hsum (by linarith [pathEnergyConstant_pos Z hZ])
    _ = pathVarianceConstant Z * (BI + VT + VS) := by
      dsimp [C, pathVarianceConstant]
      ring

/-- Quantifier form emphasizing that a single positive finite real constant,
depending only on `Z`, works for every finite forest, rooting, activity, and
nontrivial downward path. -/
theorem exists_varianceAlongDownwardPath_constant (Z : ℝ) (hZ : 0 < Z) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}, G.IsAcyclic →
      ∀ (R : ComponentRooting G) (z : ℝ) (hz : 0 < z), z ≤ Z →
      ∀ P : DownwardPath R,
        subtreeVarianceAt R z hz P.start ≤
          C * (P.occupationMass R z +
            P.terminalSubtreeVariance R z hz +
            P.sideForestVariance R z hz) := by
  refine ⟨pathVarianceConstant Z, pathVarianceConstant_pos Z hZ, ?_⟩
  intro V inst G hG R z hz hzZ P
  exact varianceAlongDownwardPath_le hG R Z z hz hzZ P

end
end AppendixA
end Forest
end Erdos993
