import Erdos993.Forest.CanonicalActivity
import Erdos993.Forest.ActivityLocalization
import Erdos993.Forest.IndexVarianceLocalization
import Erdos993.Forest.Localization

/-!
# Assembly of the actual localization interface

This module combines the proved canonical-activity, activity-localization, and
index/variance-localization theorems.  In particular, `activity < 27` is
obtained by comparing the actual hard-core means at the canonical activity and
at activity `27`, then using strict monotonicity of the actual hard-core mean.
-/

namespace Erdos993
namespace Forest

noncomputable section

open Filter

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The activity in every canonical first-recovery state is strictly below
`27`.  This is the bridge from the actual mean barrier at activity `27` and the
stored canonical mean equality, with strict monotonicity of `hardCoreMean` on
positive activities. -/
theorem CanonicalFirstRecoveryState.activity_lt_twentySeven
    (C : CanonicalFirstRecoveryState G) : C.activity < 27 := by
  classical
  letI : Nonempty V := nonempty_vertex_of_firstRecovery G C.firstRecovery
  have hbarrier :=
    hardCoreLaw_mean_twentySeven_gt_firstRecoveryIndex_of_isAcyclic
      G C.isForest C.firstRecovery
  by_contra hnot
  have hle : (27 : ℝ) ≤ C.activity := le_of_not_gt hnot
  have hmono : hardCoreMean G 27 ≤ hardCoreMean G C.activity :=
    (hardCoreMean_strictMonoOn G).monotoneOn
      (by norm_num) C.activity_pos hle
  rw [← hardCoreLaw_mean_eq_hardCoreMean G 27 (by norm_num),
    ← hardCoreLaw_mean_eq_hardCoreMean G C.activity C.activity_pos,
    C.mean_eq_index] at hmono
  exact (not_lt_of_ge hmono) hbarrier

/-- The unconditional localization interface for actual canonical
first-recovery states.  Its variance field is filled directly by
`CanonicalFirstRecoveryState.indexVarianceSizeLocalized`. -/
noncomputable def actualLocalizationInterface : LocalizationInterface.{u} where
  activity_lt_27 := by
    intro V _ G C
    exact C.activity_lt_twentySeven
  index_variance_size := by
    intro V _ G C Z hCZ
    exact C.indexVarianceSizeLocalized Z hCZ

/-- The complete activity-`27` specialization of the actual localization
interface. -/
theorem actual_localized_at_twentySeven
    (C : CanonicalFirstRecoveryState G) :
    Real.sqrt (C.order : ℝ) / 2 < (C.index : ℝ) ∧
      Real.sqrt (C.order : ℝ) / (8 * 28 ^ 4) ≤ C.variance :=
  actualLocalizationInterface.localized_at_27 C

/-- The actual activity-`27` variance lower bound. -/
theorem actual_variance_lower_bound_at_twentySeven
    (C : CanonicalFirstRecoveryState G) :
    Real.sqrt (C.order : ℝ) / (8 * 28 ^ 4) ≤ C.variance :=
  actualLocalizationInterface.variance_lower_bound_at_27 C

/-- Actual canonical variances diverge along every sequence whose forest
orders diverge. -/
theorem actual_variance_tendsto_atTop_of_order_tendsto_atTop
    {V : ℕ → Type u} [∀ n, Fintype (V n)]
    (G : ∀ n, SimpleGraph (V n))
    (C : ∀ n, CanonicalFirstRecoveryState (G n))
    (horder : Tendsto (fun n => (C n).order) atTop atTop) :
    Tendsto (fun n => (C n).variance) atTop atTop :=
  actualLocalizationInterface.variance_tendsto_atTop_of_order_tendsto_atTop
    G C horder

end
end Forest
end Erdos993
