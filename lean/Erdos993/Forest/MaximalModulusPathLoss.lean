import Erdos993.Forest.MaximalModulusPath
import Erdos993.Forest.TransferMatrixContraction

/-!
# Exact logarithmic-loss iteration along the maximal-modulus path
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section
open scoped BigOperators ENNReal
open ActualRootedVariance UniformFourthMoment
open ActualRootedVariance.ComponentRooting

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA9Loss (α : Type*) : DecidableEq α :=
  Classical.decEq α

noncomputable local instance finiteSubtypeA9Loss {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Exact triangle-inequality root mixture retaining both deletion moduli. -/
theorem subtreeCharacteristicModulus_le_weighted_deletions
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u : V) :
    (R.subtreeLawAt z hz u).characteristicModulus θ ≤
      rootedVacancyProbabilityAt R z u * vacantCharacteristicModulusAt R z hz θ u +
        rootedOccupationProbabilityAt R z u * occupiedCharacteristicModulusAt R z hz θ u := by
  let q := rootedVacancyProbabilityAt R z u
  let b := rootedOccupationProbabilityAt R z u
  let a := (hardCoreLaw
    (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
    z hz).characteristic θ
  let c := (hardCoreLaw
    (deleteClosedNeighborhood (R.Subtree (G := G) u)
      (R.subtreeRoot (G := G) u)) z hz).characteristic θ
  have hq0 : 0 ≤ q := (rootedVacancyProbabilityAt_pos R z hz u).le
  have hb0 : 0 ≤ b := (rootedOccupationProbabilityAt_pos R z hz u).le
  rw [FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66,
    subtreeCharacteristic_eq_vacant_add_occupied R z θ hz u]
  calc
    _ ≤ ‖(q : ℂ) * a‖ + ‖(b : ℂ) * (FiniteLatticeLaw.phase θ 1 * c)‖ :=
      norm_add_le _ _
    _ = q * ‖a‖ + b * ‖c‖ := by
      simp [q, b, a, c, abs_of_nonneg hq0, abs_of_nonneg hb0,
        FiniteLatticeLaw.phase]
    _ = _ := by
      rw [← FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66,
        ← FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66]
      rfl


/-- Logarithmic loss reverses a comparison of characteristic moduli. -/
theorem FiniteLatticeLaw.logarithmicLoss_anti_of_modulus_le
    {α β : Type*} [Fintype α] [Fintype β]
    (L : FiniteLatticeLaw α) (M : FiniteLatticeLaw β) (θ : ℝ)
    (h : L.characteristicModulus θ ≤ M.characteristicModulus θ) :
    M.logarithmicLoss θ ≤ L.logarithmicLoss θ := by
  unfold FiniteLatticeLaw.logarithmicLoss
  exact EReal.negOrderIso.monotone
    (ENNReal.log_le_log (ENNReal.ofReal_le_ofReal h))

/-- If Q has the larger deletion modulus, the parent loss dominates Q-loss. -/
theorem vacantDeletionLoss_le_subtreeLoss_of_max
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u : V)
    (hmax : occupiedCharacteristicModulusAt R z hz θ u ≤
      vacantCharacteristicModulusAt R z hz θ u) :
    (hardCoreLaw
      (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
      z hz).logarithmicLoss θ ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  apply FiniteLatticeLaw.logarithmicLoss_anti_of_modulus_le
  have hm := subtreeCharacteristicModulus_le_weighted_deletions R z θ hz u
  have hq0 := (rootedVacancyProbabilityAt_pos R z hz u).le
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hsum := rootedOccupationProbabilityAt_add_vacancy R z hz u
  dsimp [vacantCharacteristicModulusAt, occupiedCharacteristicModulusAt] at hm hmax ⊢
  have hweighted := mul_le_mul_of_nonneg_left hmax hb0
  calc
    _ ≤ rootedVacancyProbabilityAt R z u *
          (hardCoreLaw
            (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
            z hz).characteristicModulus θ +
        rootedOccupationProbabilityAt R z u *
          (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).characteristicModulus θ := hm
    _ ≤ rootedVacancyProbabilityAt R z u *
          (hardCoreLaw
            (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
            z hz).characteristicModulus θ +
        rootedOccupationProbabilityAt R z u *
          (hardCoreLaw
            (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
            z hz).characteristicModulus θ :=
      add_le_add_right hweighted _
    _ = _ := by
      rw [← add_mul]
      have hqb : rootedVacancyProbabilityAt R z u +
          rootedOccupationProbabilityAt R z u = 1 := by linarith [hsum]
      rw [hqb, one_mul]

/-- If R has the larger deletion modulus, the parent loss dominates R-loss. -/
theorem occupiedDeletionLoss_le_subtreeLoss_of_max
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u : V)
    (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
      occupiedCharacteristicModulusAt R z hz θ u) :
    (hardCoreLaw
      (deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u)) z hz).logarithmicLoss θ ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  apply FiniteLatticeLaw.logarithmicLoss_anti_of_modulus_le
  have hm := subtreeCharacteristicModulus_le_weighted_deletions R z θ hz u
  have hq0 := (rootedVacancyProbabilityAt_pos R z hz u).le
  have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
  have hsum := rootedOccupationProbabilityAt_add_vacancy R z hz u
  dsimp [vacantCharacteristicModulusAt, occupiedCharacteristicModulusAt] at hm hmax ⊢
  have hweighted := mul_le_mul_of_nonneg_left hmax hq0
  calc
    _ ≤ rootedVacancyProbabilityAt R z u *
          (hardCoreLaw
            (deleteVertex (R.Subtree (G := G) u) (R.subtreeRoot (G := G) u))
            z hz).characteristicModulus θ +
        rootedOccupationProbabilityAt R z u *
          (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).characteristicModulus θ := hm
    _ ≤ rootedVacancyProbabilityAt R z u *
          (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).characteristicModulus θ +
        rootedOccupationProbabilityAt R z u *
          (hardCoreLaw
            (deleteClosedNeighborhood (R.Subtree (G := G) u)
              (R.subtreeRoot (G := G) u)) z hz).characteristicModulus θ :=
      add_le_add_left hweighted _
    _ = _ := by
      rw [← add_mul]
      have hqb : rootedVacancyProbabilityAt R z u +
          rootedOccupationProbabilityAt R z u = 1 := by linarith [hsum]
      rw [hqb, one_mul]

/-- Exact additivity of logarithmic loss for the occupied deletion forest over
all child-vacant forests. -/
theorem hardCoreLaw_logarithmicLoss_deleteClosedSubtreeRoot_eq_sum_childVacant
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) (u : V) :
    (hardCoreLaw
      (deleteClosedNeighborhood (R.Subtree (G := G) u)
        (R.subtreeRoot (G := G) u)) z hz).logarithmicLoss θ =
      ∑ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z hz).logarithmicLoss θ := by
  rw [hardCoreLaw_logarithmicLoss_iso
    (R.deleteClosedSubtreeRootIsoProperChildUnion (G := G) hG u) z θ hz]
  have hfac := hardCoreLaw_logarithmicLoss_induceFinset_biUnion
    G (R.children (G := G) u)
      (fun v => R.properDescendants (G := G) v)
      (fun i hi j hj hij =>
        (R.children_pairwiseDisjoint_descendants (G := G) hG u hi hj hij).mono
          (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      (fun i hi j hj hij x y hx hy =>
        R.not_adj_of_distinct_child_descendants (G := G) hG
          ((R.mem_children (G := G) u i).mp hi)
          ((R.mem_children (G := G) u j).mp hj) hij
          ((R.mem_descendants (G := G) i x).mp (Finset.mem_erase.mp hx).2)
          ((R.mem_descendants (G := G) j y).mp (Finset.mem_erase.mp hy).2)) z θ hz
  calc
    (hardCoreLaw
        (G.induce {x | x ∈ (R.children (G := G) u).biUnion
          (fun v => R.properDescendants (G := G) v)}) z hz).logarithmicLoss θ =
      ∑ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (G.induce (↑(R.properDescendants (G := G) v) : Set V))
          z hz).logarithmicLoss θ := by
            simpa only [Set.mem_setOf_eq] using hfac
    _ = ∑ v ∈ R.children (G := G) u,
        (hardCoreLaw
          (deleteVertex (R.Subtree (G := G) v)
            (R.subtreeRoot (G := G) v)) z hz).logarithmicLoss θ := by
      apply Finset.sum_congr rfl
      intro v hv
      exact (hardCoreLaw_logarithmicLoss_iso
        (R.deleteSubtreeRootIsoProperDescendants (G := G) v) z θ hz).symm

/-- The side barrier is exactly the sum of the omitted child log-vacancy
charges. -/
theorem sideLogBarrier_eq_sum_neg_log_vacancy
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (u v : V) :
    sideLogBarrier R z u v =
      ∑ w ∈ (R.children (G := G) u).erase v,
        -Real.log (rootedVacancyProbabilityAt R z w) := by
  classical
  unfold sideLogBarrier sideVacancyProduct
  rw [Real.log_prod (fun w hw =>
    (rootedVacancyProbabilityAt_pos R z hz w).ne')]
  simpa only [Finset.sum_neg_distrib]

/-- The log-vacancy charge of one path child is bounded by its occupation
mass, with a coefficient depending only on the activity ceiling. -/
theorem neg_log_vacancy_le_one_add_ceiling_mul_occupation
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) (u : V) :
    -Real.log (rootedVacancyProbabilityAt R z u) ≤
      (1 + Z) * rootedOccupationProbabilityAt R z u := by
  let q := rootedVacancyProbabilityAt R z u
  let b := rootedOccupationProbabilityAt R z u
  have hZ : 0 < 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  have hq : 0 < q := by
    dsimp [q]
    exact rootedVacancyProbabilityAt_pos R z hz u
  have hb : 0 ≤ b := by
    dsimp [b]
    exact (rootedOccupationProbabilityAt_pos R z hz u).le
  have hsum : b + q = 1 := by
    dsimp [b, q]
    exact rootedOccupationProbabilityAt_add_vacancy R z hz u
  have hlow : (1 + Z)⁻¹ ≤ q := by
    simpa only [one_div] using
      one_div_one_add_ceiling_le_rootedVacancyProbabilityAt
        hG R z Z hz hzZ u
  have hinv : q⁻¹ ≤ 1 + Z := by
    have hi := (inv_le_inv₀ hq (inv_pos.mpr hZ)).2 hlow
    simpa using hi
  have hlog0 := Real.one_sub_inv_le_log_of_pos hq
  have hlog : -Real.log q ≤ q⁻¹ - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hinv hb
  change -Real.log q ≤ (1 + Z) * b
  calc
    -Real.log q ≤ q⁻¹ - 1 := hlog
    _ = b * q⁻¹ := by
      field_simp [hq.ne']
      nlinarith [hsum]
    _ ≤ b * (1 + Z) := hmul
    _ = (1 + Z) * b := mul_comm _ _

namespace MaximalModulusTrace

/-- The terminal-subtree loss of a concrete trace. -/
noncomputable def terminalLoss
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) : EReal :=
  (R.subtreeLawAt z hz τ.terminalRoot).logarithmicLoss θ

/-- Loss of the Q-components discarded at one Q-step. -/
noncomputable def qDiscardedLoss
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z) (u v : V) : EReal :=
  ∑ w ∈ (R.children (G := G) u).erase v,
    (R.subtreeLawAt z hz w).logarithmicLoss θ

/-- Loss of all R-components discarded at one R-step. -/
noncomputable def rDiscardedLoss
    (R : ComponentRooting G) (z θ : ℝ) (hz : 0 < z)
    (u c v : V) : EReal :=
  (∑ w ∈ (R.children (G := G) c).erase v,
      (R.subtreeLawAt z hz w).logarithmicLoss θ) +
    ∑ d ∈ (R.children (G := G) u).erase c,
      ∑ w ∈ R.children (G := G) d,
        (R.subtreeLawAt z hz w).logarithmicLoss θ

/-- Repeated-substitution loss, with every newly discarded component inserted
exactly at the step where it leaves the distinguished subtree. -/
noncomputable def accountedLoss
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → EReal
  | .stop u => (R.subtreeLawAt z hz u).logarithmicLoss θ
  | .qStep (u := u) (v := v) _ _ tail =>
      qDiscardedLoss R z θ hz u v + tail.accountedLoss
  | .rStep (u := u) (c := c) (v := v) _ _ _ tail =>
      rDiscardedLoss R z θ hz u c v + tail.accountedLoss

/-- Appendix A, (A.64), in its exact repeated-factorization form. -/
theorem accountedLoss_le_subtreeLoss_A64
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (z θ : ℝ) (hz : 0 < z) {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.accountedLoss ≤ (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  induction τ with
  | stop u => rfl
  | @qStep u v huv hmax tail ih =>
      have hv : v ∈ R.children (G := G) u :=
        (R.mem_children (G := G) u v).mpr huv
      have hroot := vacantDeletionLoss_le_subtreeLoss_of_max R z θ hz u hmax
      rw [hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
        hG R z θ hz u] at hroot
      rw [← Finset.sum_erase_add _ _ hv] at hroot
      change qDiscardedLoss R z θ hz u v + tail.accountedLoss ≤ _
      apply le_trans (add_le_add_right ih _)
      simpa [qDiscardedLoss, add_comm] using hroot
  | @rStep u c v huc hcv hmax tail ih =>
      have hc : c ∈ R.children (G := G) u :=
        (R.mem_children (G := G) u c).mpr huc
      have hv : v ∈ R.children (G := G) c :=
        (R.mem_children (G := G) c v).mpr hcv
      have hroot := occupiedDeletionLoss_le_subtreeLoss_of_max R z θ hz u hmax
      rw [hardCoreLaw_logarithmicLoss_deleteClosedSubtreeRoot_eq_sum_childVacant
        hG R z θ hz u] at hroot
      have hchild (d : V) :
          (hardCoreLaw
            (deleteVertex (R.Subtree (G := G) d)
              (R.subtreeRoot (G := G) d)) z hz).logarithmicLoss θ =
            ∑ w ∈ R.children (G := G) d,
              (R.subtreeLawAt z hz w).logarithmicLoss θ :=
        hardCoreLaw_logarithmicLoss_deleteSubtreeRoot_eq_sum_children
          hG R z θ hz d
      simp_rw [hchild] at hroot
      rw [← Finset.sum_erase_add _ _ hc] at hroot
      rw [← Finset.sum_erase_add _ _ hv] at hroot
      change rDiscardedLoss R z θ hz u c v + tail.accountedLoss ≤ _
      apply le_trans (add_le_add_right ih _)
      simpa [rDiscardedLoss, add_assoc, add_comm, add_left_comm] using hroot

/-- Nonnegativity of every actual side-barrier list sum. -/
theorem actualSideLogBarrierSumList_nonneg
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) :
    ∀ l : List V, 0 ≤ actualSideLogBarrierSumList R z l
  | u :: v :: rest =>
      add_nonneg (sideLogBarrier_nonneg R z hz u v)
        (actualSideLogBarrierSumList_nonneg R z hz (v :: rest))
  | [] => by simp [actualSideLogBarrierSumList]
  | [_] => by simp [actualSideLogBarrierSumList]

/-- The R-choice barriers charged in `K` are paid by the actual filled-path
side barriers plus the occupation masses of the intervening path children. -/
theorem rBarrierMass_le_actualSide_add_ceiling_mul_pathOccupation
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z : ℝ) (hz : 0 < z) (hzZ : z ≤ Z) {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.rBarrierMass ≤
      actualSideLogBarrierSumList R z τ.vertices +
        (1 + Z) * τ.pathOccupationMass := by
  have hC0 : 0 ≤ 1 + Z := by linarith [lt_of_lt_of_le hz hzZ]
  induction τ with
  | stop u =>
      simp [rBarrierMass, vertices, pathOccupationMass,
        actualSideLogBarrierSumList, DownwardPath.initialSum]
  | @qStep u v huv hmax tail ih =>
      change tail.rBarrierMass ≤
        actualSideLogBarrierSumList R z (u :: tail.vertices) +
          (1 + Z) *
            DownwardPath.initialSum (rootedOccupationProbabilityAt R z)
              (u :: tail.vertices)
      rw [tail.vertices_eq_cons_tail]
      simp only [actualSideLogBarrierSumList, DownwardPath.initialSum]
      rw [← tail.vertices_eq_cons_tail]
      change tail.rBarrierMass ≤
        sideLogBarrier R z u v +
          actualSideLogBarrierSumList R z tail.vertices +
            (1 + Z) *
              (rootedOccupationProbabilityAt R z u +
                DownwardPath.initialSum (rootedOccupationProbabilityAt R z)
                  tail.vertices)
      unfold pathOccupationMass at ih
      have hs0 := sideLogBarrier_nonneg R z hz u v
      have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
      have hcb0 : 0 ≤ (1 + Z) * rootedOccupationProbabilityAt R z u :=
        mul_nonneg hC0 hb0
      nlinarith
  | @rStep u c v huc hcv hmax tail ih =>
      change rootVarianceLogBarrierAt R z u + tail.rBarrierMass ≤
        actualSideLogBarrierSumList R z (u :: c :: tail.vertices) +
          (1 + Z) *
            DownwardPath.initialSum (rootedOccupationProbabilityAt R z)
              (u :: c :: tail.vertices)
      rw [tail.vertices_eq_cons_tail]
      simp only [actualSideLogBarrierSumList, DownwardPath.initialSum]
      rw [← tail.vertices_eq_cons_tail]
      change rootVarianceLogBarrierAt R z u + tail.rBarrierMass ≤
        sideLogBarrier R z u c +
          (sideLogBarrier R z c v +
            actualSideLogBarrierSumList R z tail.vertices) +
            (1 + Z) *
              (rootedOccupationProbabilityAt R z u +
                (rootedOccupationProbabilityAt R z c +
                  DownwardPath.initialSum (rootedOccupationProbabilityAt R z)
                    tail.vertices))
      unfold pathOccupationMass at ih
      have hlocal := neg_log_vacancy_le_one_add_ceiling_mul_occupation
        hG R Z z hz hzZ c
      have hc : c ∈ R.children (G := G) u :=
        (R.mem_children (G := G) u c).mpr huc
      have hroot :
          rootVarianceLogBarrierAt R z u ≤
            sideLogBarrier R z u c +
              (1 + Z) * rootedOccupationProbabilityAt R z c := by
        unfold rootVarianceLogBarrierAt
        rw [← Finset.sum_erase_add _ _ hc]
        rw [sideLogBarrier_eq_sum_neg_log_vacancy R z hz u c]
        linarith
      have hs0 := sideLogBarrier_nonneg R z hz c v
      have hb0 := (rootedOccupationProbabilityAt_pos R z hz u).le
      have hcb0 : 0 ≤ (1 + Z) * rootedOccupationProbabilityAt R z u :=
        mul_nonneg hC0 hb0
      nlinarith

end MaximalModulusTrace

/-- Public A.65 decay rate, depending only on the activity ceiling. -/
noncomputable def maximalModulusPathLossRateConstant (Z : ℝ) : ℝ :=
  actualA43RateConstant Z / ((2 + Z) * Real.pi ^ 2)

/-- Public A.65 additive offset, depending only on the activity ceiling. -/
noncomputable def maximalModulusPathLossOffsetConstant (Z : ℝ) : ℝ :=
  actualA43RateConstant Z

namespace MaximalModulusTrace

/-- The A.65 rate is strictly positive. -/
theorem maximalModulusPathLossRateConstant_pos {Z : ℝ} (hZ : 0 < Z) :
    0 < maximalModulusPathLossRateConstant Z := by
  unfold maximalModulusPathLossRateConstant
  exact div_pos (actualA43RateConstant_pos hZ)
    (mul_pos (by linarith) (sq_pos_of_pos Real.pi_pos))

/-- Appendix A, (A.65), obtained from the genuine A.8 transfer-amplitude
estimate on the concrete filled trace path. -/
theorem logarithmicLoss_ge_K_A65
    (hG : G.IsAcyclic) (R : ComponentRooting G)
    (Z z θ : ℝ) (hz : 0 < z) (hzZ : z ≤ Z)
    (hθ : |θ| ≤ Real.pi) {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    ((maximalModulusPathLossRateConstant Z * τ.K -
        maximalModulusPathLossOffsetConstant Z : ℝ) : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  have ha0 : 0 ≤ actualA43RateConstant Z :=
    (actualA43RateConstant_pos hZ).le
  have hnonneg : (0 : EReal) ≤
      (R.subtreeLawAt z hz u).logarithmicLoss θ := by
    apply FiniteLatticeLaw.coe_le_logarithmicLoss_of_modulus_le_exp_neg
      (R.subtreeLawAt z hz u) θ 0 (le_refl 0)
    simpa using (R.subtreeLawAt z hz u).characteristicModulus_le_one θ
  by_cases hτ : τ.choiceCount = 0
  · cases τ with
    | stop u =>
        have hs : maximalModulusPathLossRateConstant Z *
            (MaximalModulusTrace.stop (R := R) (z := z) (hz := hz)
              (θ := θ) u).K - maximalModulusPathLossOffsetConstant Z ≤ 0 := by
          simp [K, pathOccupationMass, rBarrierMass,
            DownwardPath.initialSum, maximalModulusPathLossOffsetConstant, ha0]
        exact (EReal.coe_nonpos.mpr hs).trans hnonneg
    | qStep huv hmax tail => simp [choiceCount] at hτ
    | rStep huc hcv hmax tail => simp [choiceCount] at hτ
  · let P := τ.toDownwardPath hτ
    have hverts : P.vertices = τ.vertices := τ.toDownwardPath_vertices hτ
    have hstart : P.start = u := by
      dsimp [P]
      cases τ with
      | stop u => exact False.elim (hτ rfl)
      | qStep huv hmax tail => rfl
      | rStep huc hcv hmax tail => rfl
    have hO : P.occupationMass R z = τ.pathOccupationMass := by
      unfold DownwardPath.occupationMass pathOccupationMass
      rw [hverts]
    have hL : P.actualSideLogBarrierSum z =
        actualSideLogBarrierSumList R z τ.vertices := by
      unfold DownwardPath.actualSideLogBarrierSum
      rw [hverts]
    have h8 := P.norm_actualTransferAmplitude_le_A43
      hG R Z z θ hz hzZ hθ
    rw [P.actualTransferAmplitude_eq_startCharacteristic hG R z θ hz,
      hstart, ← FiniteLatticeLaw.characteristicModulus_eq_norm_characteristic_A66,
      hO, hL] at h8
    let O := τ.pathOccupationMass
    let B := τ.rBarrierMass
    let L := actualSideLogBarrierSumList R z τ.vertices
    let a := actualA43RateConstant Z
    let h := Real.sin (θ / 2) ^ 2
    have hO0 : 0 ≤ O := by dsimp [O]; exact τ.nonneg_pathOccupationMass
    have hB0 : 0 ≤ B := by dsimp [B]; exact τ.nonneg_rBarrierMass
    have hL0 : 0 ≤ L := by
      dsimp [L]
      exact actualSideLogBarrierSumList_nonneg R z hz τ.vertices
    have hC : 0 < 2 + Z := by linarith
    have hrel : B ≤ L + (1 + Z) * O := by
      dsimp [B, L, O]
      exact τ.rBarrierMass_le_actualSide_add_ceiling_mul_pathOccupation
        hG R Z z hz hzZ
    have hmass : O + B ≤ (2 + Z) * (O + L) := by
      nlinarith
    have hsin := sq_div_pi_sq_le_sin_half_sq hθ
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hsin' : θ ^ 2 ≤ Real.pi ^ 2 * h := by
      dsimp [h]
      simpa only [mul_comm] using (div_le_iff₀ hpi).mp hsin
    have hc0 : 0 ≤ maximalModulusPathLossRateConstant Z :=
      (maximalModulusPathLossRateConstant_pos hZ).le
    have hfirst := mul_le_mul_of_nonneg_right hsin' (add_nonneg hO0 hB0)
    have hfirst' := mul_le_mul_of_nonneg_left hfirst hc0
    have hsecond := mul_le_mul_of_nonneg_left hmass
      (mul_nonneg (mul_nonneg hc0 hpi.le) (sq_nonneg (Real.sin (θ / 2))))
    have hrateid : maximalModulusPathLossRateConstant Z *
        Real.pi ^ 2 * (2 + Z) = a := by
      dsimp [a]
      unfold maximalModulusPathLossRateConstant
      field_simp [hC.ne', hpi.ne']
    have hdecay : maximalModulusPathLossRateConstant Z * τ.K ≤
        a * h * (O + L) := by
      unfold K
      dsimp [O, B] at hfirst' ⊢
      calc
        _ ≤ maximalModulusPathLossRateConstant Z *
            (Real.pi ^ 2 * h * (O + B)) := by
          simpa [mul_assoc] using hfirst'
        _ ≤ maximalModulusPathLossRateConstant Z * Real.pi ^ 2 * h *
            ((2 + Z) * (O + L)) := by
          simpa [mul_assoc] using hsecond
        _ = a * h * (O + L) := by rw [← hrateid]; ring
    have hMexp : (R.subtreeLawAt z hz u).characteristicModulus θ ≤
        Real.exp (-(a * h * (O + L) - a)) := by
      calc
        _ ≤ actualA43PrefactorConstant Z *
            Real.exp (-actualA43RateConstant Z *
              Real.sin (θ / 2) ^ 2 *
                (τ.pathOccupationMass + L)) := by
          simpa [O, L, a, h] using h8
        _ = Real.exp (-(a * h * (O + L) - a)) := by
          unfold actualA43PrefactorConstant
          dsimp [a, h, O]
          rw [← Real.exp_add]
          congr 1
          ring
    let s := maximalModulusPathLossRateConstant Z * τ.K -
      maximalModulusPathLossOffsetConstant Z
    have hsdecay : s ≤ a * h * (O + L) - a := by
      dsimp [s, a]
      unfold maximalModulusPathLossOffsetConstant
      linarith
    by_cases hs : 0 ≤ s
    · apply FiniteLatticeLaw.coe_le_logarithmicLoss_of_modulus_le_exp_neg
        (R.subtreeLawAt z hz u) θ s hs
      exact hMexp.trans (Real.exp_le_exp.mpr (neg_le_neg hsdecay))
    · exact (EReal.coe_nonpos.mpr (le_of_not_ge hs)).trans hnonneg

end MaximalModulusTrace
end
end AppendixA
end Forest
end Erdos993
