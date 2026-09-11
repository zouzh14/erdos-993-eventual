import Erdos993.Forest.Interfaces

/-!
# Consequences of the localization interface

The counting estimates in Propositions 2.1 and 2.2 remain explicit assumptions
through `LocalizationInterface`.  This module proves their finite specialization
at the uniform activity ceiling and the downstream divergence statement (2.4).
-/

namespace Erdos993
namespace Forest

noncomputable section

open Filter

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Proposition 2.1 specialized using the uniform activity bound from
Proposition 2.2. -/
theorem LocalizationInterface.localized_at_27 (L : LocalizationInterface.{u})
    (C : CanonicalFirstRecoveryState G) :
    Real.sqrt (C.order : ℝ) / 2 < (C.index : ℝ) ∧
      Real.sqrt (C.order : ℝ) / (8 * 28 ^ 4) ≤ C.variance := by
  have h := L.index_variance_size (G := G) C 27
    (le_of_lt (L.activity_lt_27 (G := G) C))
  rcases h with ⟨hindex, hvariance⟩
  refine ⟨hindex, ?_⟩
  norm_num at hvariance ⊢
  exact hvariance

/-- The finite variance lower bound in (2.4). -/
theorem LocalizationInterface.variance_lower_bound_at_27
    (L : LocalizationInterface.{u}) (C : CanonicalFirstRecoveryState G) :
    Real.sqrt (C.order : ℝ) / (8 * 28 ^ 4) ≤ C.variance :=
  (L.localized_at_27 C).2

/-- Under the localization interface, canonical variances diverge along every
sequence of finite forests whose orders tend to infinity. -/
theorem LocalizationInterface.variance_tendsto_atTop_of_order_tendsto_atTop
    (L : LocalizationInterface.{u})
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (G n))
    (horder : Tendsto (fun n => (C n).order) atTop atTop) :
    Tendsto (fun n => (C n).variance) atTop atTop := by
  have horderReal :
      Tendsto (fun n => ((C n).order : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr horder
  have hsqrt :
      Tendsto (fun n => Real.sqrt ((C n).order : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp horderReal
  have hscale : 0 < (1 / (8 * 28 ^ 4) : ℝ) := by norm_num
  have hlower :
      Tendsto (fun n => Real.sqrt ((C n).order : ℝ) / (8 * 28 ^ 4))
        atTop atTop := by
    simpa [div_eq_mul_inv] using hsqrt.atTop_mul_const hscale
  exact tendsto_atTop_mono
    (fun n => L.variance_lower_bound_at_27 (C n)) hlower

end
end Forest
end Erdos993
