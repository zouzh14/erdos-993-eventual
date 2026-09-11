import Erdos993.Forest.ActualMartingaleProjection

/-!
# Exact conditional hard-core law on the unobserved allowed graph

This file proves the finite spatial-Markov factorization needed in Appendix D.3.
It conditions the original global hard-core law on an arbitrary observed set
`D`; no canonicity or first-recovery property is assigned to the induced graph.
-/

namespace Erdos993
namespace ActualMartingaleProjection

open scoped BigOperators
open Filter Topology

universe u

noncomputable local instance finiteSubtypeConditionalOutside
    {α : Type*} [Fintype α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable local instance classicalDecidableEqConditionalOutside
    {α : Type*} : DecidableEq α := Classical.decEq α

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- Vertices outside `D` which are not blocked by the fixed occupied pattern
on `D`. -/
noncomputable def allowedOutsideVertices
    (D : Finset V) (I : IndepFinset G) : Finset V := by
  classical
  exact Finset.univ.filter fun x =>
    x ∉ D ∧ ∀ y ∈ restriction D I, ¬ G.Adj x y

@[simp] theorem mem_allowedOutsideVertices
    (D : Finset V) (I : IndepFinset G) (x : V) :
    x ∈ allowedOutsideVertices D I ↔
      x ∉ D ∧ ∀ y ∈ restriction D I, ¬ G.Adj x y := by
  classical
  simp [allowedOutsideVertices]

/-- The genuine induced graph carrying the unobserved conditional hard-core
law.  Its activity remains the original global activity. -/
abbrev AllowedOutsideGraph
    (D : Finset V) (I : IndepFinset G) : SimpleGraph
      {x // x ∈ allowedOutsideVertices D I} :=
  G.induce {x | x ∈ allowedOutsideVertices D I}

/-- Lift an independent configuration of the allowed outside graph to the
ambient graph. -/
noncomputable def allowedOutsideLift
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) : IndepFinset G :=
  (indepFinsetInduceEquiv G
    (fun x => x ∈ allowedOutsideVertices D I) T).val

@[simp] theorem allowedOutsideLift_card
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) :
    (allowedOutsideLift D I T).val.card = T.val.card := by
  exact indepFinsetInduceEquiv_card G
    (fun x => x ∈ allowedOutsideVertices D I) T

 theorem allowedOutsideLift_mem
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) {x : V}
    (hx : x ∈ (allowedOutsideLift D I T).val) :
    x ∈ allowedOutsideVertices D I := by
  exact (indepFinsetInduceEquiv G
    (fun y => y ∈ allowedOutsideVertices D I) T).property x hx

/-- Glue a varying allowed-outside configuration to the fixed observed
pattern. -/
noncomputable def glueAllowedOutside
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) : IndepFinset G := by
  classical
  refine ⟨restriction D I ∪ (allowedOutsideLift D I T).val, ?_⟩
  intro x hx y hy hxy hAdj
  rcases Finset.mem_union.mp hx with hxD | hxO
  · rcases Finset.mem_union.mp hy with hyD | hyO
    · exact I.property (Finset.mem_inter.mp hxD).1
        (Finset.mem_inter.mp hyD).1 hxy hAdj
    · have hyAllowed := allowedOutsideLift_mem D I T hyO
      exact ((mem_allowedOutsideVertices D I y).mp hyAllowed).2 x hxD (G.symm hAdj)
  · rcases Finset.mem_union.mp hy with hyD | hyO
    · have hxAllowed := allowedOutsideLift_mem D I T hxO
      exact ((mem_allowedOutsideVertices D I x).mp hxAllowed).2 y hyD hAdj
    · exact (allowedOutsideLift D I T).property hxO hyO hxy hAdj

@[simp] theorem restriction_glueAllowedOutside
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) :
    restriction D (glueAllowedOutside D I T) = restriction D I := by
  classical
  ext x
  constructor
  · intro hx
    have hxD := (Finset.mem_inter.mp hx).2
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hxI | hxO
    · exact hxI
    · exact (((mem_allowedOutsideVertices D I x).mp
        (allowedOutsideLift_mem D I T hxO)).1 hxD).elim
  · intro hx
    exact Finset.mem_inter.mpr ⟨Finset.mem_union.mpr (Or.inl hx),
      (Finset.mem_inter.mp hx).2⟩

/-- Ambient allowed-outside part of a configuration in the observation fiber. -/
noncomputable def ambientAllowedOutsidePart
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    RestrictedIndepFinset G (fun x => x ∈ allowedOutsideVertices D I) := by
  classical
  refine ⟨⟨J.1.val ∩ allowedOutsideVertices D I,
    J.1.property.mono Finset.inter_subset_left⟩, ?_⟩
  intro x hx
  exact (Finset.mem_inter.mp hx).2

/-- Restrict a configuration in the observation fiber to its allowed outside
part. -/
noncomputable def allowedOutsidePart
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    IndepFinset (AllowedOutsideGraph D I) :=
  (indepFinsetInduceEquiv G
    (fun x => x ∈ allowedOutsideVertices D I)).symm
      (ambientAllowedOutsidePart D I J)

@[simp] theorem allowedOutsideLift_part_val
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    (allowedOutsideLift D I (allowedOutsidePart D I J)).val =
      J.1.val ∩ allowedOutsideVertices D I := by
  have h := (indepFinsetInduceEquiv G
    (fun x => x ∈ allowedOutsideVertices D I)).apply_symm_apply
      (ambientAllowedOutsidePart D I J)
  exact congrArg (fun K => K.val.val) h

/-- Every occupied unobserved vertex in a restriction fiber is an allowed
outside vertex. -/
theorem mem_allowedOutsideVertices_of_mem_fiber
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I})
    {x : V} (hxJ : x ∈ J.1.val) (hxD : x ∉ D) :
    x ∈ allowedOutsideVertices D I := by
  classical
  rw [mem_allowedOutsideVertices]
  refine ⟨hxD, ?_⟩
  intro y hy
  have hyJRestr : y ∈ restriction D J.1 := by rw [J.2]; exact hy
  have hyJ := (Finset.mem_inter.mp hyJRestr).1
  have hyD := (Finset.mem_inter.mp hy).2
  exact J.1.property hxJ hyJ (fun h => hxD (h ▸ hyD))

@[simp] theorem glueAllowedOutside_part
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    glueAllowedOutside D I (allowedOutsidePart D I J) = J.1 := by
  classical
  apply Subtype.ext
  ext x
  rw [show x ∈ (glueAllowedOutside D I (allowedOutsidePart D I J)).val ↔
      x ∈ restriction D I ∨
        x ∈ J.1.val ∩ allowedOutsideVertices D I by
    simp [glueAllowedOutside, allowedOutsideLift_part_val]]
  constructor
  · rintro (hxObs | hxOut)
    · have hxObsJ : x ∈ restriction D J.1 := by rw [J.2]; exact hxObs
      exact (Finset.mem_inter.mp hxObsJ).1
    · exact (Finset.mem_inter.mp hxOut).1
  · intro hxJ
    by_cases hxD : x ∈ D
    · left
      rw [← J.2]
      exact Finset.mem_inter.mpr ⟨hxJ, hxD⟩
    · right
      exact Finset.mem_inter.mpr ⟨hxJ,
        mem_allowedOutsideVertices_of_mem_fiber D I J hxJ hxD⟩

@[simp] theorem allowedOutsidePart_glue
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) :
    allowedOutsidePart D I
      ⟨glueAllowedOutside D I T, restriction_glueAllowedOutside D I T⟩ = T := by
  unfold allowedOutsidePart ambientAllowedOutsidePart
  apply (indepFinsetInduceEquiv G
    (fun x => x ∈ allowedOutsideVertices D I)).injective
  simp only [Equiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  ext x
  constructor
  · intro hx
    have hxAllowed := (Finset.mem_inter.mp hx).2
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hx).1 with hxObs | hxLift
    · exact (((mem_allowedOutsideVertices D I x).mp hxAllowed).1
        (Finset.mem_inter.mp hxObs).2).elim
    · exact hxLift
  · intro hx
    exact Finset.mem_inter.mpr ⟨
      Finset.mem_union.mpr (Or.inr hx), allowedOutsideLift_mem D I T hx⟩

/-- Exact configuration-space equivalence for conditioning on an arbitrary
observed set. -/
noncomputable def restrictionFiberAllowedEquiv
    (D : Finset V) (I : IndepFinset G) :
    {J : IndepFinset G // restriction D J = restriction D I} ≃
      IndepFinset (AllowedOutsideGraph D I) :=
  { toFun := allowedOutsidePart D I
    invFun := fun T =>
      ⟨glueAllowedOutside D I T, restriction_glueAllowedOutside D I T⟩
    left_inv := by intro J; apply Subtype.ext; exact glueAllowedOutside_part D I J
    right_inv := allowedOutsidePart_glue D I }

@[simp] theorem glueAllowedOutside_card
    (D : Finset V) (I : IndepFinset G)
    (T : IndepFinset (AllowedOutsideGraph D I)) :
    (glueAllowedOutside D I T).val.card =
      (restriction D I).card + T.val.card := by
  classical
  rw [show (glueAllowedOutside D I T).val =
      restriction D I ∪ (allowedOutsideLift D I T).val by rfl]
  rw [Finset.card_union_of_disjoint]
  · rw [allowedOutsideLift_card]
  · rw [Finset.disjoint_left]
    intro x hxD hxO
    exact ((mem_allowedOutsideVertices D I x).mp
      (allowedOutsideLift_mem D I T hxO)).1 (Finset.mem_inter.mp hxD).2

/-- The outside factor in the pointwise conditional hard-core identity. -/
noncomputable def allowedOutsideFiberFactor
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G) : ℝ :=
  C.activity ^ (restriction D I).card *
    independenceEval (AllowedOutsideGraph D I) C.activity /
      independenceEval G C.activity

/-- Exact D.3 pointwise factorization.  Conditional on the literal observed
pattern, the unobserved variables have the hard-core law on the genuine induced
allowed graph at the original global activity. -/
theorem law_probability_allowedOutside_factor
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    C.law.probability J.1 =
      allowedOutsideFiberFactor C D I *
        (Forest.hardCoreLaw (AllowedOutsideGraph D I)
          C.activity C.activity_pos).probability
            (restrictionFiberAllowedEquiv D I J) := by
  let T := restrictionFiberAllowedEquiv D I J
  have hglue : glueAllowedOutside D I T = J.1 := by
    exact glueAllowedOutside_part D I J
  change C.activity ^ J.1.val.card / independenceEval G C.activity =
    (C.activity ^ (restriction D I).card *
      independenceEval (AllowedOutsideGraph D I) C.activity /
        independenceEval G C.activity) *
      (C.activity ^ T.val.card /
        independenceEval (AllowedOutsideGraph D I) C.activity)
  rw [← hglue, glueAllowedOutside_card]
  have hG : independenceEval G C.activity ≠ 0 :=
    ne_of_gt (independenceEval_pos G C.activity_pos)
  have hH : independenceEval (AllowedOutsideGraph D I) C.activity ≠ 0 :=
    ne_of_gt (independenceEval_pos (AllowedOutsideGraph D I) C.activity_pos)
  field_simp [hG, hH]
  rw [pow_add]

/-- The normalization factor in the pointwise identity is exactly the mass of
the original global observation fiber. -/
theorem restrictionFiberMass_eq_allowedOutsideFiberFactor
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G) :
    restrictionFiberMass C D I = allowedOutsideFiberFactor C D I := by
  classical
  let H := Forest.hardCoreLaw (AllowedOutsideGraph D I)
    C.activity C.activity_pos
  have hsum :
      (∑ J ∈ restrictionFiber D I, C.law.probability J) =
        ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          C.law.probability J.1 := by
    apply Finset.sum_subtype
    intro J
    simp [restrictionFiber]
  unfold restrictionFiberMass
  rw [hsum]
  calc
    (∑ J : {J : IndepFinset G // restriction D J = restriction D I},
        C.law.probability J.1) =
      ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
        allowedOutsideFiberFactor C D I *
          H.probability (restrictionFiberAllowedEquiv D I J) := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact law_probability_allowedOutside_factor C D I J
    _ = allowedOutsideFiberFactor C D I *
        (∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          H.probability (restrictionFiberAllowedEquiv D I J)) := by
      rw [Finset.mul_sum]
    _ = allowedOutsideFiberFactor C D I *
        (∑ T : IndepFinset (AllowedOutsideGraph D I), H.probability T) := by
      congr 1
      simpa using (Equiv.sum_comp (restrictionFiberAllowedEquiv D I)
        (fun T : IndepFinset (AllowedOutsideGraph D I) => H.probability T))
    _ = allowedOutsideFiberFactor C D I := by
      rw [H.probability_sum]
      ring

/-- Exact normalized point-mass form of D.3. -/
theorem conditional_probability_allowedOutside
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G)
    (J : {J : IndepFinset G // restriction D J = restriction D I}) :
    C.law.probability J.1 / restrictionFiberMass C D I =
      (Forest.hardCoreLaw (AllowedOutsideGraph D I)
        C.activity C.activity_pos).probability
          (restrictionFiberAllowedEquiv D I J) := by
  rw [law_probability_allowedOutside_factor,
    restrictionFiberMass_eq_allowedOutsideFiberFactor]
  exact mul_div_cancel_left₀ _ (by
    rw [← restrictionFiberMass_eq_allowedOutsideFiberFactor]
    exact ne_of_gt (restrictionFiberMass_pos C D I))

/-- Full finite conditional-expectation transport.  The right side is an
ordinary hard-core law on an induced forest at the unchanged global activity;
there is no derived canonicity or first-recovery assertion. -/
theorem conditionalExpectation_eq_allowedOutside
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G)
    (f : IndepFinset G → ℝ) :
    conditionalExpectation C D f I =
      ∑ T : IndepFinset (AllowedOutsideGraph D I),
        (Forest.hardCoreLaw (AllowedOutsideGraph D I)
          C.activity C.activity_pos).probability T *
            f (glueAllowedOutside D I T) := by
  classical
  let H := Forest.hardCoreLaw (AllowedOutsideGraph D I)
    C.activity C.activity_pos
  let M := restrictionFiberMass C D I
  have hsum :
      (∑ J ∈ restrictionFiber D I, C.law.probability J * f J) =
        ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          C.law.probability J.1 * f J.1 := by
    apply Finset.sum_subtype
    intro J
    simp [restrictionFiber]
  have hnum :
      (∑ J ∈ restrictionFiber D I, C.law.probability J * f J) =
        M * ∑ T : IndepFinset (AllowedOutsideGraph D I),
          H.probability T * f (glueAllowedOutside D I T) := by
    rw [hsum]
    calc
      (∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          C.law.probability J.1 * f J.1) =
        ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          M * (H.probability (restrictionFiberAllowedEquiv D I J) * f J.1) := by
            apply Finset.sum_congr rfl
            intro J hJ
            rw [law_probability_allowedOutside_factor,
              ← restrictionFiberMass_eq_allowedOutsideFiberFactor]
            ring
      _ = M * ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          H.probability (restrictionFiberAllowedEquiv D I J) * f J.1 := by
            rw [Finset.mul_sum]
      _ = M * ∑ T : IndepFinset (AllowedOutsideGraph D I),
          H.probability T * f (glueAllowedOutside D I T) := by
            congr 1
            rw [← Equiv.sum_comp (restrictionFiberAllowedEquiv D I)
              (fun T : IndepFinset (AllowedOutsideGraph D I) =>
                H.probability T * f (glueAllowedOutside D I T))]
            apply Finset.sum_congr rfl
            intro J hJ
            simp [restrictionFiberAllowedEquiv]
  unfold conditionalExpectation
  rw [hnum]
  change M * (∑ T : IndepFinset (AllowedOutsideGraph D I),
      H.probability T * f (glueAllowedOutside D I T)) / M = _
  exact mul_div_cancel_left₀ _
    (ne_of_gt (restrictionFiberMass_pos C D I))

end ActualMartingaleProjection
end Erdos993
