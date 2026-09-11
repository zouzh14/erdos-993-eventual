import Erdos993.Forest.Interfaces

/-!
# Arithmetic consequences of the sublinear displacement interface

This module does not prove the rooted-tree estimate in Lemma 5.1.  It proves
the exact uniform little-oh and incompatibility consequences of the named
`SublinearConditionalMeanInterface` assumption.
-/

namespace Erdos993
namespace Forest

noncomputable section

universe u

/-- Uniform `o(subtreeOrder)` in the epsilon-threshold form of (5.2). -/
def UniformlySublinearConditionalMean (F : RootedForestFamily.{u})
    (Z rho : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
        C.activity ≤ Z →
        rho ≤ (F.observables C r).occupationProbability v →
        orderThreshold ≤ (F.observables C r).subtreeOrder v →
          |(F.observables C r).conditionalMeanDifference v| ≤
            epsilon * ((F.observables C r).subtreeOrder v : ℝ)

/-- The fixed-parameter epsilon-plus-constant estimate implies the uniform
little-oh statement (5.2). -/
theorem uniformlySublinearConditionalMean_of_interface
    {F : RootedForestFamily.{u}} (S : SublinearConditionalMeanInterface F)
    {Z rho : ℝ} (hZ : 0 < Z) (hrho : 0 < rho) :
    UniformlySublinearConditionalMean F Z rho := by
  intro epsilon hepsilon
  obtain ⟨K, hK, hbound⟩ :=
    S.conclusion Z rho (epsilon / 2) hZ hrho (half_pos hepsilon)
  obtain ⟨orderThreshold, hthreshold⟩ :=
    exists_nat_ge (2 * K / epsilon)
  refine ⟨orderThreshold, ?_⟩
  intro V _ G C r v hactivity hoccupation horder
  let R := F.observables C r
  have hfinite := hbound C r v hactivity hoccupation
  have horderReal : (orderThreshold : ℝ) ≤ (R.subtreeOrder v : ℝ) := by
    exact_mod_cast horder
  have htwiceK : 2 * K ≤ (orderThreshold : ℝ) * epsilon :=
    (div_le_iff₀ hepsilon).mp hthreshold
  have hKabsorb : K ≤ (epsilon / 2) * (R.subtreeOrder v : ℝ) := by
    nlinarith
  unfold SublinearConditionalMeanAt at hfinite
  dsimp [R] at hfinite hKabsorb ⊢
  nlinarith

/-- Once the ambient order exceeds `2K / delta`, the epsilon-plus-constant
bound at slope `delta / 2` is strictly below `delta * order`.  The only
geometric input is `subtreeOrder ≤ order`. -/
theorem strict_ambient_upper_of_half_slope_bound
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {C : CanonicalFirstRecoveryState G} (R : RootedForestObservables C)
    (v : V) {delta K : ℝ} (hdelta : 0 < delta)
    (hbound : SublinearConditionalMeanAt R v (delta / 2) K)
    (hlarge : 2 * K / delta < (C.order : ℝ)) :
    |R.conditionalMeanDifference v| < delta * (C.order : ℝ) := by
  have hsubtree : (R.subtreeOrder v : ℝ) ≤ (C.order : ℝ) := by
    exact_mod_cast R.subtreeOrder_le_order v
  have htwiceK : 2 * K < (C.order : ℝ) * delta :=
    (div_lt_iff₀ hdelta).mp hlarge
  unfold SublinearConditionalMeanAt at hbound
  nlinarith

/-- The strict upper bound is incompatible with the macroscopic lower bound
`delta * order ≤ |Delta|` from Section 6. -/
theorem linear_lower_incompatible_with_half_slope_bound
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    {C : CanonicalFirstRecoveryState G} (R : RootedForestObservables C)
    (v : V) {delta K : ℝ} (hdelta : 0 < delta)
    (hbound : SublinearConditionalMeanAt R v (delta / 2) K)
    (hlarge : 2 * K / delta < (C.order : ℝ))
    (hlower : delta * (C.order : ℝ) ≤ |R.conditionalMeanDifference v|) :
    False :=
  (not_lt_of_ge hlower)
    (strict_ambient_upper_of_half_slope_bound R v hdelta hbound hlarge)

/-- Fixed `Z`, `rho`, and `delta` specialization of Lemma 5.1 in the exact
quantifier order needed by the Section 6 contradiction. -/
theorem exists_constant_strictly_excluding_linear_lower
    {F : RootedForestFamily.{u}} (S : SublinearConditionalMeanInterface F)
    {Z rho delta : ℝ} (hZ : 0 < Z) (hrho : 0 < rho)
    (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
        C.activity ≤ Z →
        rho ≤ (F.observables C r).occupationProbability v →
        2 * K / delta < (C.order : ℝ) →
        delta * (C.order : ℝ) ≤
          |(F.observables C r).conditionalMeanDifference v| →
        False := by
  obtain ⟨K, hK, hbound⟩ :=
    S.conclusion Z rho (delta / 2) hZ hrho (half_pos hdelta)
  refine ⟨K, hK, ?_⟩
  intro V _ G C r v hactivity hoccupation hlarge hlower
  exact linear_lower_incompatible_with_half_slope_bound
    (F.observables C r) v hdelta
    (hbound C r v hactivity hoccupation) hlarge hlower

/-- Along any sequence whose selected descendant-subtree orders diverge, the
normalized absolute conditional-mean displacement tends to zero.  The vertex
types may vary with the sequence index. -/
theorem conditionalMean_ratio_tendsto_zero
    {F : RootedForestFamily.{u}} (S : SublinearConditionalMeanInterface F)
    {Z rho : ℝ} (hZ : 0 < Z) (hrho : 0 < rho)
    (V : ℕ → Type u) [∀ n, Fintype (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (G n))
    (r : ∀ n, F.Realization (C n)) (v : ∀ n, V n)
    (hactivity : ∀ n, (C n).activity ≤ Z)
    (hoccupation : ∀ n,
      rho ≤ (F.observables (C n) (r n)).occupationProbability (v n))
    (hsize : Filter.Tendsto
      (fun n => (F.observables (C n) (r n)).subtreeOrder (v n))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto
      (fun n =>
        |(F.observables (C n) (r n)).conditionalMeanDifference (v n)| /
          ((F.observables (C n) (r n)).subtreeOrder (v n) : ℝ))
      Filter.atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro lower hlower
    filter_upwards [] with n
    have hdenom : 0 ≤
        ((F.observables (C n) (r n)).subtreeOrder (v n) : ℝ) :=
      Nat.cast_nonneg _
    have hratio : 0 ≤
        |(F.observables (C n) (r n)).conditionalMeanDifference (v n)| /
          ((F.observables (C n) (r n)).subtreeOrder (v n) : ℝ) :=
      div_nonneg (abs_nonneg _) hdenom
    linarith
  · intro epsilon hepsilon
    obtain ⟨orderThreshold, hthreshold⟩ :=
      uniformlySublinearConditionalMean_of_interface S hZ hrho
        (epsilon / 2) (half_pos hepsilon)
    have heventuallyOrder : ∀ᶠ n in Filter.atTop,
        orderThreshold ≤
          (F.observables (C n) (r n)).subtreeOrder (v n) :=
      (Filter.tendsto_atTop.mp hsize) orderThreshold
    filter_upwards [heventuallyOrder] with n hn
    have hlinear := hthreshold (C n) (r n) (v n)
      (hactivity n) (hoccupation n) hn
    have hdenom : 0 <
        ((F.observables (C n) (r n)).subtreeOrder (v n) : ℝ) := by
      exact_mod_cast (F.observables (C n) (r n)).subtreeOrder_pos (v n)
    have hratio :
        |(F.observables (C n) (r n)).conditionalMeanDifference (v n)| /
            ((F.observables (C n) (r n)).subtreeOrder (v n) : ℝ) ≤
          epsilon / 2 := by
      apply (div_le_iff₀ hdenom).mpr
      nlinarith
    linarith

end
end Forest
end Erdos993
