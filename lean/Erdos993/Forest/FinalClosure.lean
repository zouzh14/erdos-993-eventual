import Erdos993.Forest.Localization
import Erdos993.Forest.CanonicalLaw
import Erdos993.Forest.RootedVariance
import Erdos993.Forest.SublinearDisplacement

/-!
# Conditional Phase 0+1 vertical closure

This module assembles the finite contradiction in Sections 6-7 from the named
interfaces in `VerticalClosureAssumptions`.  Those interfaces, canonical-state
existence, and rooted-realization existence are not proved here.  Consequently
the results below are conditional closure theorems, not the unconditional Main
Theorem from the manuscript.
-/

namespace Erdos993
namespace Forest

noncomputable section

open Filter

universe u

/-- Any fixed variance cutoff follows from a sufficiently large ambient order
via the compiled localization lower bound at activity ceiling `27`. -/
theorem LocalizationInterface.exists_orderThreshold_for_variance
    (L : LocalizationInterface.{u}) (varianceThreshold : ℝ) :
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G),
        orderThreshold ≤ C.order → varianceThreshold ≤ C.variance := by
  have hnatCast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hnatCast
  have hscale : 0 < (1 / (8 * 28 ^ 4) : ℝ) := by norm_num
  have hlower :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) / (8 * 28 ^ 4)) atTop atTop := by
    simpa [div_eq_mul_inv] using hsqrt.atTop_mul_const hscale
  have heventually : ∀ᶠ n : ℕ in atTop,
      varianceThreshold ≤ Real.sqrt (n : ℝ) / (8 * 28 ^ 4) :=
    (tendsto_atTop.1 hlower) varianceThreshold
  rw [eventually_atTop] at heventually
  obtain ⟨orderThreshold, hthreshold⟩ := heventually
  refine ⟨orderThreshold, ?_⟩
  intro V _ G C horder
  exact le_trans (hthreshold C.order horder) (L.variance_lower_bound_at_27 C)

/-- Pointwise large-state exclusion under the still-unformalized manuscript
interfaces.  The rooted realization is an explicit argument; this statement
does not assume that the realization type is inhabited. -/
theorem exists_orderThreshold_excluding_canonical_state_of_verticalClosureAssumptions
    (A : VerticalClosureAssumptions.{u}) :
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G)
        (_r : A.rootedFamily.Realization C),
        orderThreshold ≤ C.order → False := by
  let c := A.macroscopicContribution.kappa27
  let rho := A.occupationBalance.rho c
  let delta := 2 * Real.sqrt (c * A.firstRecoveryScale.cV) /
    A.firstRecoveryScale.CN
  have hc : 0 < c := A.macroscopicContribution.kappa27_pos
  have hrho : 0 < rho := A.occupationBalance.rho_pos hc
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos
      (mul_pos (by norm_num)
        (Real.sqrt_pos.2 (mul_pos hc A.firstRecoveryScale.cV_pos)))
      A.firstRecoveryScale.CN_pos
  obtain ⟨K, hK, hexclude⟩ :=
    exists_constant_strictly_excluding_linear_lower
      A.sublinearConditionalMean (Z := 27) (rho := rho) (delta := delta)
      (by norm_num) hrho hdelta
  let varianceThreshold := max A.macroscopicContribution.varianceThreshold27
    (max (A.occupationBalance.varianceThreshold c)
      A.firstRecoveryScale.varianceThreshold)
  obtain ⟨varianceOrder, hvarianceOrder⟩ :=
    A.localization.exists_orderThreshold_for_variance varianceThreshold
  obtain ⟨strictOrder, hstrictOrder⟩ := exists_nat_gt (2 * K / delta)
  refine ⟨max varianceOrder strictOrder, ?_⟩
  intro V _ G C r horder
  have hvarianceOrder' : varianceOrder ≤ C.order :=
    le_trans (Nat.le_max_left _ _) horder
  have hstrictOrder' : strictOrder ≤ C.order :=
    le_trans (Nat.le_max_right _ _) horder
  have hvariance : varianceThreshold ≤ C.variance :=
    hvarianceOrder C hvarianceOrder'
  have hmacroThreshold :
      A.macroscopicContribution.varianceThreshold27 ≤ C.variance :=
    le_trans (le_max_left _ _) hvariance
  have hbalanceThreshold :
      A.occupationBalance.varianceThreshold c ≤ C.variance :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hvariance
  have hscaleThreshold :
      A.firstRecoveryScale.varianceThreshold ≤ C.variance :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hvariance
  have hactivityLt : C.activity < 27 := A.localization.activity_lt_27 C
  have hactivityLe : C.activity ≤ 27 := le_of_lt hactivityLt
  obtain ⟨v, hmacro⟩ :=
    A.macroscopicContribution.conclusion C r hactivityLt hmacroThreshold
  have hbalanced := A.occupationBalance.conclusion C r v c hc hactivityLt
    hbalanceThreshold hmacro
  have hscale := A.firstRecoveryScale.conclusion C hactivityLt hscaleThreshold
  have hlower : delta * (C.order : ℝ) ≤
      |(A.rootedFamily.observables C r).conditionalMeanDifference v| := by
    simpa [delta] using
      (A.rootedFamily.observables C r).linear_displacement_lower_bound v
        c A.firstRecoveryScale.cV A.firstRecoveryScale.CV
        A.firstRecoveryScale.cN A.firstRecoveryScale.CN hc
        A.firstRecoveryScale.cV_pos A.firstRecoveryScale.CN_pos hmacro hscale
  have hstrictOrderReal : (strictOrder : ℝ) ≤ (C.order : ℝ) := by
    exact_mod_cast hstrictOrder'
  have hlarge : 2 * K / delta < (C.order : ℝ) :=
    lt_of_lt_of_le hstrictOrder hstrictOrderReal
  exact hexclude C r v hactivityLe hbalanced.1 hlarge hlower

/-- No explicitly rooted sequence of canonical first-recovery states can have
ambient orders tending to infinity under `VerticalClosureAssumptions`. -/
theorem no_unbounded_rooted_canonical_sequence_of_verticalClosureAssumptions
    (A : VerticalClosureAssumptions.{u})
    (V : ℕ → Type u) [∀ n, Fintype (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (G n))
    (r : ∀ n, A.rootedFamily.Realization (C n))
    (horder : Tendsto (fun n => (C n).order) atTop atTop) : False := by
  obtain ⟨orderThreshold, hexclude⟩ :=
    exists_orderThreshold_excluding_canonical_state_of_verticalClosureAssumptions A
  have heventually : ∀ᶠ n in atTop, orderThreshold ≤ (C n).order :=
    (tendsto_atTop.1 horder) orderThreshold
  rw [eventually_atTop] at heventually
  obtain ⟨n, hn⟩ := heventually
  exact hexclude (C n) (r n) (hn n le_rfl)

/-- Manuscript-literal sequence exclusion: no explicitly rooted canonical
first-recovery sequence can have variances tending to infinity. -/
theorem no_varianceDivergent_rooted_canonical_sequence_of_verticalClosureAssumptions
    (A : VerticalClosureAssumptions.{u})
    (V : ℕ → Type u) [∀ n, Fintype (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (G n))
    (r : ∀ n, A.rootedFamily.Realization (C n))
    (hvariance : Tendsto (fun n => (C n).variance) atTop atTop) : False := by
  obtain ⟨orderThreshold, hexclude⟩ :=
    exists_orderThreshold_excluding_canonical_state_of_verticalClosureAssumptions A
  have heventually : ∀ᶠ n in atTop,
      (orderThreshold : ℝ) ^ 2 + 1 ≤ (C n).variance :=
    (tendsto_atTop.1 hvariance) ((orderThreshold : ℝ) ^ 2 + 1)
  rw [eventually_atTop] at heventually
  obtain ⟨n, hn⟩ := heventually
  have hlarge := hn n le_rfl
  have horderNotLarge : ¬orderThreshold ≤ (C n).order := by
    intro horder
    exact hexclude (C n) (r n) horder
  have horderLt : (C n).order < orderThreshold := Nat.lt_of_not_ge horderNotLarge
  have horderLtReal : ((C n).order : ℝ) < (orderThreshold : ℝ) := by
    exact_mod_cast horderLt
  have hvarianceUpper := (C n).variance_le_order_sq
  have horderNonneg : 0 ≤ ((C n).order : ℝ) := Nat.cast_nonneg _
  have hthresholdNonneg : 0 ≤ (orderThreshold : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- Conditional eventual weak unimodality.  Besides
`VerticalClosureAssumptions`, the statement explicitly requires canonical
activity existence at every first recovery and inhabitation of every associated
rooted-realization type. -/
theorem eventually_weaklyUnimodal_of_verticalClosureAssumptions
    (A : VerticalClosureAssumptions.{u})
    (hcanonicalActivity :
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V) (s : ℕ),
        IsFirstRecovery (independenceCoefficients G) s →
          ∃ z : ℝ, ∃ hz : 0 < z,
            (hardCoreLaw G z hz).mean = (s : ℝ))
    (hrooting :
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G),
          Nonempty (A.rootedFamily.Realization C)) :
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        G.IsAcyclic → orderThreshold ≤ Fintype.card V →
          WeaklyUnimodal (independenceCoefficients G) := by
  obtain ⟨orderThreshold, hexclude⟩ :=
    exists_orderThreshold_excluding_canonical_state_of_verticalClosureAssumptions A
  refine ⟨orderThreshold, ?_⟩
  intro V _ G hforest horder
  by_contra hnot
  obtain ⟨s, hs⟩ :=
    (exists_firstRecovery_iff (independenceCoefficients G)).2 hnot
  obtain ⟨z, hz, hmean⟩ := hcanonicalActivity G s hs
  let C : CanonicalFirstRecoveryState G := {
    isForest := hforest
    index := s
    firstRecovery := hs
    activity := z
    activity_pos := hz
    mean_eq_index := hmean
  }
  obtain ⟨r⟩ := hrooting C
  apply hexclude C r
  simpa [CanonicalFirstRecoveryState.order] using horder

end
end Forest
end Erdos993
