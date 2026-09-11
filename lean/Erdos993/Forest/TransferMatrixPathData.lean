import Erdos993.Forest.TransferMatrixAlgebra
import Erdos993.Forest.PathVarianceBound
import Erdos993.Forest.CharacteristicTransfer
import Erdos993.Forest.IndependentComponentFourier

/-!
# Actual transfer data along a decorated downward path

This module defines the coefficients in Appendix A, (A.42)--(A.44), directly
from the hard-core laws at the unchanged global activity.  No abstract factor
or probability field is stored: side factors, root probabilities, and the
bottom vector are all derived from the rooted forest.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

noncomputable local instance classicalDecidableEqA8 (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtypeA8 {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment

universe u

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- The normalized independence-polynomial factor contributed by all side
subtrees at the edge `u → v`.  This is `a_k` in (A.42). -/
noncomputable def sideCharacteristicA
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) : ℂ :=
  ∏ w ∈ (R.children (G := G) u).erase v,
    (R.subtreeLawAt z hz w).characteristic θ

/-- The normalized root-deleted factor contributed by all side subtrees at
`u → v`.  This is `c_k` in (A.42). -/
noncomputable def sideCharacteristicC
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) : ℂ :=
  ∏ w ∈ (R.children (G := G) u).erase v,
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) w) (R.subtreeRoot (G := G) w))
      z hz).characteristic θ

/-- Product of the actual side-root vacancy probabilities. -/
noncomputable def sideVacancyProduct
    (R : ComponentRooting G) (z : ℝ) (u v : V) : ℝ :=
  ∏ w ∈ (R.children (G := G) u).erase v,
    rootedVacancyProbabilityAt R z w

/-- The side logarithmic barrier `Λ_k` from (A.42). -/
noncomputable def sideLogBarrier
    (R : ComponentRooting G) (z : ℝ) (u v : V) : ℝ :=
  -Real.log (sideVacancyProduct R z u v)

/-- The genuine transfer coefficient attached to the downward edge `u → v`.
Its weights are the actual occupation/vacancy probabilities of `u`, and its
complex factors are the normalized hard-core side-forest factors. -/
noncomputable def actualTransferCoefficient
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) : TransferCoefficient where
  q := rootedVacancyProbabilityAt R z u
  b := rootedOccupationProbabilityAt R z u
  a := sideCharacteristicA R z hz θ u v
  c := sideCharacteristicC R z hz θ u v
  phase := FiniteLatticeLaw.phase θ 1

/-- Sum of the genuine side logarithmic barriers over all path edges. -/
noncomputable def actualSideLogBarrierSumList
    (R : ComponentRooting G) (z : ℝ) : List V → ℝ
  | u :: v :: rest => sideLogBarrier R z u v +
      actualSideLogBarrierSumList R z (v :: rest)
  | _ => 0

/-- The side logarithmic mass in (A.43) for a downward path. -/
noncomputable def DownwardPath.actualSideLogBarrierSum
    {R : ComponentRooting G} (P : DownwardPath R) (z : ℝ) : ℝ :=
  actualSideLogBarrierSumList R z P.vertices

/-- Coefficients for all adjacent pairs of a vertex list. -/
noncomputable def actualTransferCoefficients
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    List V → List TransferCoefficient
  | u :: v :: rest =>
      actualTransferCoefficient R z hz θ u v ::
        actualTransferCoefficients R z hz θ (v :: rest)
  | _ => []

/-- Last vertex of a structurally nontrivial downward path. -/
noncomputable def DownwardPath.terminalVertex
    {R : ComponentRooting G} (P : DownwardPath R) : V :=
  P.vertices.getLast P.vertices_ne_nil

/-- The actual normalized complex bottom vector in Lemma A.8.  The first
coordinate is the bottom-subtree characteristic function and the second is
its root-vacant characteristic function. -/
noncomputable def DownwardPath.actualBottomVector
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) : ComplexRow :=
  ⟨(R.subtreeLawAt z hz P.terminalVertex).characteristic θ,
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) P.terminalVertex)
        (R.subtreeRoot (G := G) P.terminalVertex)) z hz).characteristic θ⟩

/-- The genuine row obtained from `e₁ᵀ` by all actual transfer matrices. -/
noncomputable def DownwardPath.actualTransferRow
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) : ComplexRow :=
  applyTransferList ⟨1, 0⟩
    (actualTransferCoefficients R z hz θ P.vertices)

/-- The exact left side of (A.43), expressed as the row/bottom-vector pairing. -/
noncomputable def DownwardPath.actualTransferAmplitude
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) : ℂ :=
  (P.actualTransferRow z hz θ).pair (P.actualBottomVector z hz θ)

/-- The norm of every finite-law characteristic function is at most one. -/
theorem norm_characteristic_le_one
    {α : Type*} [Fintype α] (L : FiniteLatticeLaw α) (θ : ℝ) :
    ‖L.characteristic θ‖ ≤ 1 := by
  rw [← L.norm_centeredCharacteristic_eq,
    ← FiniteLatticeLaw.characteristicModulus]
  exact L.characteristicModulus_le_one θ

/-- Actual vacancy probabilities are strictly positive. -/
theorem rootedVacancyProbabilityAt_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    0 < rootedVacancyProbabilityAt R z u := by
  unfold rootedVacancyProbabilityAt
  exact div_pos (UniformFourthMoment.rootedQAt_pos R z hz u)
    (independenceEval_pos _ hz)

/-- Actual vacancy probabilities are at most one. -/
theorem rootedVacancyProbabilityAt_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedVacancyProbabilityAt R z u ≤ 1 := by
  linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
    rootedOccupationProbabilityAt_pos R z hz u]

/-- The side `a` factor has modulus at most one, including the empty product. -/
theorem norm_sideCharacteristicA_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) :
    ‖sideCharacteristicA R z hz θ u v‖ ≤ 1 := by
  classical
  rw [sideCharacteristicA, norm_prod]
  exact Finset.prod_le_one
    (fun w hw => norm_nonneg _)
    (fun w hw => norm_characteristic_le_one (R.subtreeLawAt z hz w) θ)

/-- The side `c` factor has modulus at most one, including the empty product. -/
theorem norm_sideCharacteristicC_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) :
    ‖sideCharacteristicC R z hz θ u v‖ ≤ 1 := by
  classical
  rw [sideCharacteristicC, norm_prod]
  exact Finset.prod_le_one
    (fun w hw => norm_nonneg _)
    (fun w hw => norm_characteristic_le_one
      (hardCoreLaw
        (deleteVertex (R.Subtree (G := G) w) (R.subtreeRoot (G := G) w))
        z hz) θ)

/-- Every genuine hard-core edge coefficient is admissible for the scalar
transfer algebra. -/
theorem actualTransferCoefficient_admissible
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (u v : V) :
    (actualTransferCoefficient R z hz θ u v).Admissible := by
  refine ⟨(rootedVacancyProbabilityAt_pos R z hz u).le,
    (rootedOccupationProbabilityAt_pos R z hz u).le, ?_, ?_, ?_, ?_⟩
  · simpa [actualTransferCoefficient, add_comm] using
      rootedOccupationProbabilityAt_add_vacancy R z hz u
  · exact FiniteLatticeLaw.norm_phase θ 1
  · exact norm_sideCharacteristicA_le_one R z hz θ u v
  · exact norm_sideCharacteristicC_le_one R z hz θ u v

/-- Every coefficient in an actual path list is admissible. -/
theorem actualTransferCoefficients_admissible
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    ∀ l : List V,
      ∀ K ∈ actualTransferCoefficients R z hz θ l, K.Admissible
  | _ :: _ :: rest, K, hK => by
      simp only [actualTransferCoefficients, List.mem_cons] at hK
      rcases hK with rfl | hK
      · exact actualTransferCoefficient_admissible R z hz θ _ _
      · exact actualTransferCoefficients_admissible R z hz θ (_ :: rest) K hK
  | [], K, hK => by simp [actualTransferCoefficients] at hK
  | [_], K, hK => by simp [actualTransferCoefficients] at hK

/-- The actual bottom vector has both coordinate moduli at most one. -/
theorem DownwardPath.actualBottomVector_norms
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    ‖(P.actualBottomVector z hz θ).fst‖ ≤ 1 ∧
      ‖(P.actualBottomVector z hz θ).snd‖ ≤ 1 := by
  constructor
  · exact norm_characteristic_le_one
      (R.subtreeLawAt z hz P.terminalVertex) θ
  · exact norm_characteristic_le_one
      (hardCoreLaw
        (deleteVertex (R.Subtree (G := G) P.terminalVertex)
          (R.subtreeRoot (G := G) P.terminalVertex)) z hz) θ

/-- Exact hard-core recursion in probability form: root occupation equals root
vacancy times activity times the product of all child vacancies. -/
theorem rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_prod_children
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u : V) :
    rootedOccupationProbabilityAt R z u =
      rootedVacancyProbabilityAt R z u * z *
        ∏ w ∈ R.children (G := G) u, rootedVacancyProbabilityAt R z w := by
  classical
  unfold rootedOccupationProbabilityAt rootedVacancyProbabilityAt
  rw [UniformFourthMoment.rootedAAt_eq_z_mul_prod_rootedQAt hG,
    UniformFourthMoment.rootedQAt_eq_prod_rootedPAt hG]
  have hP : rootedPAt R z u ≠ 0 := by
    rw [UniformFourthMoment.rootedPAt_eq_rootedQAt_add_rootedAAt]
    exact (add_pos (UniformFourthMoment.rootedQAt_pos R z hz u)
      (UniformFourthMoment.rootedAAt_pos R z hz u)).ne'
  have hPv (w : V) : rootedPAt R z w ≠ 0 := by
    rw [UniformFourthMoment.rootedPAt_eq_rootedQAt_add_rootedAAt]
    exact (add_pos (UniformFourthMoment.rootedQAt_pos R z hz w)
      (UniformFourthMoment.rootedAAt_pos R z hz w)).ne'
  have hprodP : (∏ w ∈ R.children (G := G) u, rootedPAt R z w) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun w hw => hPv w)
  rw [Finset.prod_div_distrib]
  field_simp [hP, hprodP]

/-- Exact distinguished-child odds identity from (A.58). -/
theorem rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_child_vacancy_mul_side
    (hG : G.IsAcyclic) (R : ComponentRooting G) (z : ℝ) (hz : 0 < z)
    {u v : V} (huv : R.IsChild (G := G) u v) :
    rootedOccupationProbabilityAt R z u =
      rootedVacancyProbabilityAt R z u * z *
        rootedVacancyProbabilityAt R z v * sideVacancyProduct R z u v := by
  classical
  rw [rootedOccupationProbabilityAt_eq_vacancy_mul_z_mul_prod_children hG R z hz u]
  have hv : v ∈ R.children (G := G) u :=
    (R.mem_children (G := G) u v).mpr huv
  rw [← Finset.prod_erase_mul _ _ hv]
  simp only [sideVacancyProduct]
  ring

/-- Every genuine side-vacancy product is positive. -/
theorem sideVacancyProduct_pos
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    0 < sideVacancyProduct R z u v := by
  classical
  unfold sideVacancyProduct
  exact Finset.prod_pos fun w hw => rootedVacancyProbabilityAt_pos R z hz w

/-- Every genuine side-vacancy product is at most one. -/
theorem sideVacancyProduct_le_one
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    sideVacancyProduct R z u v ≤ 1 := by
  classical
  unfold sideVacancyProduct
  exact Finset.prod_le_one
    (fun w hw => (rootedVacancyProbabilityAt_pos R z hz w).le)
    (fun w hw => rootedVacancyProbabilityAt_le_one R z hz w)

/-- The actual side logarithmic barrier is nonnegative. -/
theorem sideLogBarrier_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    0 ≤ sideLogBarrier R z u v := by
  unfold sideLogBarrier
  exact neg_nonneg.mpr (Real.log_nonpos
    (sideVacancyProduct_pos R z hz u v).le
    (sideVacancyProduct_le_one R z hz u v))

/-- The quantitative variance lower bound used in (A.46): every rooted
hard-core subtree pays a fixed `Z`-dependent fraction of its root occupation.
This is derived from the actual total-variance recurrence, child energy, and
child-odds estimate; it is not an abstract probability hypothesis. -/
theorem one_div_one_add_ceiling_sq_mul_occupation_le_subtreeVarianceAt
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    (1 / (1 + Z)) ^ 2 * rootedOccupationProbabilityAt R z u ≤
      subtreeVarianceAt R z hz u := by
  let η : ℝ := 1 / (1 + Z)
  let b := rootedOccupationProbabilityAt R z u
  let q := rootedVacancyProbabilityAt R z u
  let d := rootedDisplacementAt R z hz u
  let S := ∑ w ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z w * rootedDisplacementAt R z hz w
  let O := ∑ w ∈ R.children (G := G) u,
    rootedOccupationProbabilityAt R z w / rootedVacancyProbabilityAt R z w
  let E := ∑ w ∈ R.children (G := G) u, rootedEnergyAt R z hz w
  let VQ := rootVacantVarianceAt R z hz u
  let VR := rootOccupiedVarianceAt R z hz u
  let V := subtreeVarianceAt R z hz u
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    exact (div_le_one (by linarith)).2 (by linarith)
  have hηid : η * (1 + Z) = 1 := by
    dsimp [η]
    field_simp
  have hb0 : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hqη : η ≤ q := by
    dsimp [η, q]
    exact one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
      hG R z Z hz hzZ u
  have hE0 : 0 ≤ E := by
    dsimp [E]
    exact Finset.sum_nonneg fun w hw => by
      unfold rootedEnergyAt
      exact mul_nonneg
        (mul_nonneg (rootedOccupationProbabilityAt_pos R z hz w).le
          (rootedVacancyProbabilityAt_pos R z hz w).le)
        (sq_nonneg _)
  have hVQ0 : 0 ≤ VQ := by
    change 0 ≤ R.vacantVarianceAt z hz u
    exact FiniteLatticeLaw.variance_nonneg _
  have hVR0 : 0 ≤ VR := by
    change 0 ≤ R.occupiedVarianceAt z hz u
    exact FiniteLatticeLaw.variance_nonneg _
  have hrec : d = 1 - S := by
    simpa [d, S] using rootedDisplacementAt_eq_one_sub_sum hG R z hz u
  have hCS : S ^ 2 ≤ O * E := by
    simpa [S, O, E] using
      child_occupation_displacement_sum_sq_le_odds_mul_energy R z hz u
  have hOdds : b * O ≤ Z := by
    simpa [b, O] using
      rootedOccupation_mul_childOddsSum_le hG R Z z hz hzZ u
  have hbS : b * S ^ 2 ≤ Z * E := by
    calc
      b * S ^ 2 ≤ b * (O * E) := mul_le_mul_of_nonneg_left hCS hb0
      _ = (b * O) * E := by ring
      _ ≤ Z * E := mul_le_mul_of_nonneg_right hOdds hE0
  have hquad : Z * d ^ 2 + S ^ 2 ≥ Z * η := by
    rw [hrec]
    have hηid' : (1 + Z) * η = 1 := by nlinarith [hηid]
    have hden : 0 < 1 + Z := by linarith
    have hid : (1 + Z) * (Z * (1 - S) ^ 2 + S ^ 2 - Z * η) =
        ((1 + Z) * S - Z) ^ 2 := by
      nlinarith
    have hnon : 0 ≤ Z * (1 - S) ^ 2 + S ^ 2 - Z * η :=
      (mul_nonneg_iff_of_pos_left hden).mp (by rw [hid]; exact sq_nonneg _)
    linarith
  have hbase : η * b ≤ b * d ^ 2 + E := by
    have hmul := mul_le_mul_of_nonneg_left hquad hb0
    nlinarith [hbS]
  have hEle : E ≤ VQ := by
    simpa [E, VQ] using child_energy_sum_le_rootVacantVarianceAt hG R z hz u
  have hVformula : V = q * VQ + b * VR + b * q * d ^ 2 := by
    change (R.subtreeLawAt z hz u).variance =
      q * R.vacantVarianceAt z hz u + b * R.occupiedVarianceAt z hz u +
        b * q * d ^ 2
    rw [R.subtreeVarianceAt_law_total_variance z hz u]
    simp only [vacancyProbabilityAt_eq_rooted, occupationProbabilityAt_eq_rooted]
    rfl
  have hqVQ : η * E ≤ q * VQ := by
    calc
      η * E ≤ η * VQ := mul_le_mul_of_nonneg_left hEle hη.le
      _ ≤ q * VQ := mul_le_mul_of_nonneg_right hqη hVQ0
  have hroot : η * b * d ^ 2 ≤ b * q * d ^ 2 := by
    nlinarith [mul_nonneg hb0 (sq_nonneg d),
      mul_le_mul_of_nonneg_right hqη (mul_nonneg hb0 (sq_nonneg d))]
  have hlower : η * (b * d ^ 2 + E) ≤ V := by
    rw [hVformula]
    have hbr0 : 0 ≤ b * VR := mul_nonneg hb0 hVR0
    nlinarith
  change η ^ 2 * b ≤ V
  calc
    η ^ 2 * b = η * (η * b) := by ring
    _ ≤ η * (b * d ^ 2 + E) := mul_le_mul_of_nonneg_left hbase hη.le
    _ ≤ V := hlower

/-- Concrete positive coefficient in the A.46--A.47 modulus gap. -/
noncomputable def sideRootGapConstant (Z : ℝ) : ℝ :=
  uniformGapConstant Z * (1 / (1 + Z)) ^ 2

/-- Rooted subtree modulus loss pays the actual root occupation, uniformly in
subtree size.  This is A.47 for one genuine rooted component. -/
theorem occupation_mul_sin_sq_le_rootedCharacteristic_defect
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (u : V) :
    sideRootGapConstant Z * rootedOccupationProbabilityAt R z u *
        Real.sin (θ / 2) ^ 2 ≤
      1 - ‖(R.subtreeLawAt z hz u).characteristic θ‖ := by
  classical
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  let μ := R.subtreeLawAt z hz u
  let b := rootedOccupationProbabilityAt R z u
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hη0 : 0 ≤ (1 / (1 + Z) : ℝ) ^ 2 := sq_nonneg _
  have hb1 : (1 / (1 + Z)) ^ 2 * b ≤ 1 := by
    have hb_le : b ≤ 1 := by
      linarith [rootedOccupationProbabilityAt_add_vacancy R z hz u,
        rootedVacancyProbabilityAt_pos R z hz u]
    have hη_le : (1 / (1 + Z) : ℝ) ≤ 1 :=
      (div_le_one (by linarith)).2 (by linarith)
    have hη_nonneg : 0 ≤ (1 / (1 + Z) : ℝ) := by positivity
    have hη_sq_le : (1 / (1 + Z) : ℝ) ^ 2 ≤ 1 := by
      simpa using (pow_le_pow_left₀ hη_nonneg hη_le 2)
    calc
      (1 / (1 + Z)) ^ 2 * b ≤ 1 * b :=
        mul_le_mul_of_nonneg_right hη_sq_le hb0
      _ ≤ 1 := by simpa using hb_le
  have hvar := one_div_one_add_ceiling_sq_mul_occupation_le_subtreeVarianceAt
    hG R Z z hz hzZ u
  have hmin : (1 / (1 + Z)) ^ 2 * b ≤ min μ.variance 1 :=
    le_min (by simpa [μ, b] using hvar) hb1
  haveI : Nonempty {v // v ∈ R.descendants (G := G) u} :=
    ⟨⟨u, R.self_mem_descendants (G := G) u⟩⟩
  have hgap := SimpleGraph.IsAcyclic.uniform_characteristic_modulus_gap_nonempty
    (R.Subtree (G := G) u) (R.subtree_isAcyclic (G := G) hG u)
      Z z θ hZ hz hzZ hθ
  have hκ0 : 0 ≤ uniformGapConstant Z := uniformGapConstant_nonneg hZ.le
  have hh0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
  change 1 - μ.characteristicModulus θ ≥
    uniformGapConstant Z * min μ.variance 1 * Real.sin (θ / 2) ^ 2 at hgap
  have hscaled :
      uniformGapConstant Z * ((1 / (1 + Z)) ^ 2 * b) *
          Real.sin (θ / 2) ^ 2 ≤
        uniformGapConstant Z * min μ.variance 1 * Real.sin (θ / 2) ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmin hκ0) hh0
  rw [FiniteLatticeLaw.characteristicModulus,
    FiniteLatticeLaw.norm_centeredCharacteristic_eq] at hgap
  dsimp [sideRootGapConstant]
  nlinarith

/-- The norm of the actual `a` factor pays the sum of side-root
occupations exponentially.  Unlike a linear product-defect estimate, this
remains valid for arbitrarily many side components. -/
theorem norm_sideCharacteristicA_le_exp_neg_sideOccupationMass
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (u v : V) :
    ‖sideCharacteristicA R z hz θ u v‖ ≤
      Real.exp (-(sideRootGapConstant Z *
        (∑ w ∈ (R.children (G := G) u).erase v,
          rootedOccupationProbabilityAt R z w) * Real.sin (θ / 2) ^ 2)) := by
  classical
  let s := (R.children (G := G) u).erase v
  let x := fun w => sideRootGapConstant Z *
    rootedOccupationProbabilityAt R z w * Real.sin (θ / 2) ^ 2
  let r := fun w => ‖(R.subtreeLawAt z hz w).characteristic θ‖
  have hpoint : ∀ w ∈ s, r w ≤ Real.exp (-x w) := by
    intro w hw
    have hdef := occupation_mul_sin_sq_le_rootedCharacteristic_defect
      hG R Z z θ hz hzZ hθ w
    have hrx : r w ≤ 1 - x w := by
      dsimp [r, x]
      linarith
    exact hrx.trans (Real.one_sub_le_exp_neg (x w))
  have hprod : ∏ w ∈ s, r w ≤ ∏ w ∈ s, Real.exp (-x w) :=
    Finset.prod_le_prod (fun w hw => norm_nonneg _) hpoint
  rw [← Real.exp_sum] at hprod
  rw [sideCharacteristicA, norm_prod]
  calc
    ∏ w ∈ (R.children (G := G) u).erase v,
        ‖(R.subtreeLawAt z hz w).characteristic θ‖ ≤
      Real.exp (∑ w ∈ s, -x w) := hprod
    _ = Real.exp (-(sideRootGapConstant Z *
        (∑ w ∈ (R.children (G := G) u).erase v,
          rootedOccupationProbabilityAt R z w) * Real.sin (θ / 2) ^ 2)) := by
      congr 1
      dsimp [s, x]
      simp_rw [Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul]

/-- Every actual side logarithmic barrier is bounded by the sum of its side
root occupations, using the uniform vacancy floor. -/
theorem sideLogBarrier_le_one_add_Z_mul_sideOccupationMass
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u v : V) :
    sideLogBarrier R z u v ≤
      (1 + Z) * ∑ w ∈ (R.children (G := G) u).erase v,
        rootedOccupationProbabilityAt R z w := by
  classical
  unfold sideLogBarrier sideVacancyProduct
  rw [Real.log_prod (fun w hw =>
    (rootedVacancyProbabilityAt_pos R z hz w).ne')]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro w hw
  let q := rootedVacancyProbabilityAt R z w
  let b := rootedOccupationProbabilityAt R z w
  have hqpos : 0 < q := rootedVacancyProbabilityAt_pos R z hz w
  have hqη : 1 / (1 + Z) ≤ q :=
    one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
      hG R z Z hz hzZ w
  have hsum : b + q = 1 := by
    simpa [b, q] using rootedOccupationProbabilityAt_add_vacancy R z hz w
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 / q by positivity)
  rw [Real.log_div one_ne_zero hqpos.ne', Real.log_one, zero_sub] at hlog
  have hqmul : (1 + Z) * q ≥ 1 := by
    have hden : 0 < 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
    have := mul_le_mul_of_nonneg_left hqη hden.le
    field_simp at this
    exact this
  have hinv : 1 / q ≤ 1 + Z := (div_le_iff₀ hqpos).2 (by linarith)
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz w).le
  have hfrac : 1 / q - 1 = b / q := by
    field_simp
    linarith
  calc
    -Real.log (rootedVacancyProbabilityAt R z w) = -Real.log q := rfl
    _ ≤ 1 / q - 1 := hlog
    _ = b / q := hfrac
    _ ≤ (1 + Z) * b := by
      have := mul_le_mul_of_nonneg_left hinv hb0
      dsimp [b]
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

/-- A.57 in zero-safe exponential form: the norm of the actual `a` factor
pays the full side logarithmic barrier. -/
theorem norm_sideCharacteristicA_le_exp_neg_sideLogBarrier
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (hθ : |θ| ≤ Real.pi)
    (u v : V) :
    ‖sideCharacteristicA R z hz θ u v‖ ≤
      Real.exp (-((sideRootGapConstant Z / (1 + Z)) *
        sideLogBarrier R z u v * Real.sin (θ / 2) ^ 2)) := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have hκ0 : 0 ≤ sideRootGapConstant Z := by
    unfold sideRootGapConstant
    exact mul_nonneg (uniformGapConstant_nonneg hZ.le) (sq_nonneg _)
  have hbar := sideLogBarrier_le_one_add_Z_mul_sideOccupationMass
    hG R Z z hz hzZ u v
  have hmass := norm_sideCharacteristicA_le_exp_neg_sideOccupationMass
    hG R Z z θ hz hzZ hθ u v
  have hh0 : 0 ≤ Real.sin (θ / 2) ^ 2 := sq_nonneg _
  have hden : 0 < 1 + Z := by linarith
  apply hmass.trans
  rw [Real.exp_le_exp]
  have hscaled :
      (sideRootGapConstant Z / (1 + Z)) * sideLogBarrier R z u v *
          Real.sin (θ / 2) ^ 2 ≤
        sideRootGapConstant Z *
          (∑ w ∈ (R.children (G := G) u).erase v,
            rootedOccupationProbabilityAt R z w) * Real.sin (θ / 2) ^ 2 := by
    calc
      (sideRootGapConstant Z / (1 + Z)) * sideLogBarrier R z u v *
          Real.sin (θ / 2) ^ 2 ≤
        (sideRootGapConstant Z / (1 + Z)) *
          ((1 + Z) * ∑ w ∈ (R.children (G := G) u).erase v,
            rootedOccupationProbabilityAt R z w) * Real.sin (θ / 2) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hbar (div_nonneg hκ0 hden.le)) hh0
      _ = sideRootGapConstant Z *
          (∑ w ∈ (R.children (G := G) u).erase v,
            rootedOccupationProbabilityAt R z w) * Real.sin (θ / 2) ^ 2 := by
          field_simp
  linarith

/-- The exact A.43 amplitude is bounded by the final row one-norm. -/
theorem DownwardPath.norm_actualTransferAmplitude_le_normOne
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    ‖P.actualTransferAmplitude z hz θ‖ ≤
      (P.actualTransferRow z hz θ).normOne := by
  exact ComplexRow.norm_pair_le_normOne _ _
    (P.actualBottomVector_norms z hz θ).1
    (P.actualBottomVector_norms z hz θ).2

/-- The actual transfer row is nonexpansive. -/
theorem DownwardPath.actualTransferRow_normOne_le_one
    {R : ComponentRooting G} (P : DownwardPath R)
    (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    (P.actualTransferRow z hz θ).normOne ≤ 1 := by
  unfold DownwardPath.actualTransferRow
  have h := applyTransferList_normOne_le ⟨1, 0⟩
    (actualTransferCoefficients R z hz θ P.vertices)
    (actualTransferCoefficients_admissible R z hz θ P.vertices)
  simpa [ComplexRow.normOne] using h

end
end AppendixA
end Forest
end Erdos993
