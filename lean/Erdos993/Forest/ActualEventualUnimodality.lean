import Erdos993.Forest.ActualPhase1Closure
import Erdos993.Forest.AppendixDUniformization
import Erdos993.Forest.OccupationBalance
import Erdos993.Forest.AppendixCFirstRecoveryScale

namespace Erdos993.Forest

universe u

noncomputable section

/-- Eventual weak unimodality for every sufficiently large finite forest,
obtained by assembling the proved Appendix D.1, occupation-balance, and
Appendix C.7 interfaces. -/
theorem eventual_forest_unimodality :
    ∃ orderThreshold : ℕ,
      ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
        G.IsAcyclic → orderThreshold ≤ Fintype.card V →
          WeaklyUnimodal (independenceCoefficients G) :=
  eventually_weaklyUnimodal_of_actualPhase1Closure
    actualMacroscopicContributionInterface.{u}
    ActualRootedVariance.actualOccupationBalanceInterface.{u}
    AppendixC.appendixC7FirstRecoveryScaleInterface.{u}

end

end Erdos993.Forest
