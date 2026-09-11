import Erdos993.Forest.ActualSublinearDisplacement

/-!
# Generic sublinear conditional-mean adapter

This module converts the fieldwise representation equalities supplied by
`SublinearConditionalMeanFieldwiseAdapterSpec` into the exact
`SublinearConditionalMeanInterface` consumed by the eventual-forest closure.
It reuses the proved local rooted-tree displacement theorem and does not
construct the fieldwise adapter for any actual rooted-family implementation.
-/

namespace Erdos993
namespace Forest

noncomputable section

universe u

namespace LocalRootedTree

/-- The three fieldwise representation equalities transport the proved raw
rooted-tree displacement estimate to the generic closure interface. -/
theorem SublinearConditionalMeanFieldwiseAdapterSpec.toInterface
    {F : RootedForestFamily.{u}}
    (A : SublinearConditionalMeanFieldwiseAdapterSpec F) :
    SublinearConditionalMeanInterface F where
  conclusion := by
    intro Z rho eta hZ hrho heta
    obtain ⟨K, hK, hbound⟩ :=
      exists_uniform_displacement_bound hZ hrho heta
    refine ⟨K, hK, ?_⟩
    intro V _ G C r v hactivity hoccupation
    rw [A.occupationProbability_eq C r v] at hoccupation
    unfold SublinearConditionalMeanAt
    rw [A.conditionalMeanDifference_eq C r v, A.subtreeOrder_eq C r v]
    exact hbound C.activity (A.localTree C r v)
      C.activity_pos hactivity hoccupation

end LocalRootedTree

end
end Forest
end Erdos993
