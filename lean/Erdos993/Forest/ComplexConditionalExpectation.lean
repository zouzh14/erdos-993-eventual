import Erdos993.Forest.ConditionalOutsideLaw

namespace Erdos993
namespace ActualMartingaleProjection
open scoped BigOperators
universe u
noncomputable section
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable def conditionalExpectationComplex
    (C : Forest.CanonicalFirstRecoveryState G)
    (S : Finset V) (f : IndepFinset G → ℂ) (I : IndepFinset G) : ℂ :=
  (∑ J ∈ restrictionFiber S I, (C.law.probability J : ℂ) * f J) /
    (restrictionFiberMass C S I : ℂ)

theorem conditionalExpectationComplex_eq_of_restriction_eq
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (f : IndepFinset G → ℂ) {I I' : IndepFinset G}
    (h : restriction S I = restriction S I') :
    conditionalExpectationComplex C S f I =
      conditionalExpectationComplex C S f I' := by
  have hfiber : restrictionFiber S I = restrictionFiber S I' := by
    ext J
    simp only [mem_restrictionFiber]
    rw [h]
  simp [conditionalExpectationComplex, restrictionFiberMass, hfiber]

theorem lawExpectation_conditionalExpectationComplex
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (f : IndepFinset G → ℂ) :
    (∑ I : IndepFinset G, (C.law.probability I : ℂ) *
      conditionalExpectationComplex C S f I) =
      ∑ I : IndepFinset G, (C.law.probability I : ℂ) * f I := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (IndepFinset G))
    (restriction S) (fun I => (C.law.probability I : ℂ) *
      conditionalExpectationComplex C S f I)]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (IndepFinset G))
    (restriction S) (fun I => (C.law.probability I : ℂ) * f I)]
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hne : (Finset.univ.filter
      (fun I : IndepFinset G => restriction S I = T)).Nonempty
  · obtain ⟨I₀, hI₀⟩ := hne
    have hI₀T : restriction S I₀ = T := by simpa using hI₀
    have hconst : ∀ I ∈ Finset.univ.filter
        (fun I : IndepFinset G => restriction S I = T),
        conditionalExpectationComplex C S f I =
          conditionalExpectationComplex C S f I₀ := by
      intro I hI
      apply conditionalExpectationComplex_eq_of_restriction_eq
      have hIT : restriction S I = T := by simpa using hI
      exact hIT.trans hI₀T.symm
    calc
      (∑ I ∈ Finset.univ with restriction S I = T,
          (C.law.probability I : ℂ) * conditionalExpectationComplex C S f I) =
          (∑ I ∈ Finset.univ with restriction S I = T,
            (C.law.probability I : ℂ)) * conditionalExpectationComplex C S f I₀ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro I hI
        rw [hconst I hI]
      _ = (restrictionFiberMass C S I₀ : ℂ) *
          conditionalExpectationComplex C S f I₀ := by
        congr 1
        unfold restrictionFiberMass restrictionFiber
        push_cast
        apply Finset.sum_congr
        · ext I
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hI₀T]
        · intro I hI
          rfl
      _ = ∑ I ∈ Finset.univ with restriction S I = T,
          (C.law.probability I : ℂ) * f I := by
        unfold conditionalExpectationComplex
        rw [mul_div_cancel₀ _]
        · unfold restrictionFiber
          apply Finset.sum_congr
          · ext I
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hI₀T]
          · intro I hI
            rfl
        · exact_mod_cast ne_of_gt (restrictionFiberMass_pos C S I₀)
  · have hempty : Finset.univ.filter
        (fun I : IndepFinset G => restriction S I = T) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

theorem conditionalExpectationComplex_restriction_mul
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (g : Finset V → ℂ) (f : IndepFinset G → ℂ) (I : IndepFinset G) :
    conditionalExpectationComplex C S
      (fun J => g (restriction S J) * f J) I =
      g (restriction S I) * conditionalExpectationComplex C S f I := by
  classical
  unfold conditionalExpectationComplex
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  change (C.law.probability J : ℂ) *
      (g (restriction S J) * f J) =
    g (restriction S I) * ((C.law.probability J : ℂ) * f J)
  rw [(mem_restrictionFiber.mp hJ)]
  ring

theorem lawExpectation_restriction_mul_conditionalExpectationComplex
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (g : Finset V → ℂ) (f : IndepFinset G → ℂ) :
    (∑ I : IndepFinset G, (C.law.probability I : ℂ) *
      (g (restriction S I) * conditionalExpectationComplex C S f I)) =
      ∑ I : IndepFinset G, (C.law.probability I : ℂ) *
        (g (restriction S I) * f I) := by
  calc
    _ = ∑ I : IndepFinset G, (C.law.probability I : ℂ) *
        conditionalExpectationComplex C S
          (fun J => g (restriction S J) * f J) I := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [conditionalExpectationComplex_restriction_mul C S g f I]
    _ = _ := lawExpectation_conditionalExpectationComplex C S _

theorem conditionalExpectationComplex_eq_allowedOutside
    (C : Forest.CanonicalFirstRecoveryState G)
    (D : Finset V) (I : IndepFinset G)
    (f : IndepFinset G → ℂ) :
    conditionalExpectationComplex C D f I =
      ∑ T : IndepFinset (AllowedOutsideGraph D I),
        (Forest.hardCoreLaw (AllowedOutsideGraph D I)
          C.activity C.activity_pos).probability T *
            f (glueAllowedOutside D I T) := by
  classical
  let H := Forest.hardCoreLaw (AllowedOutsideGraph D I)
    C.activity C.activity_pos
  let M := restrictionFiberMass C D I
  have hsum :
      (∑ J ∈ restrictionFiber D I,
          (C.law.probability J : ℂ) * f J) =
        ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          (C.law.probability J.1 : ℂ) * f J.1 := by
    apply Finset.sum_subtype
    intro J
    simp [restrictionFiber]
  have hnum :
      (∑ J ∈ restrictionFiber D I,
          (C.law.probability J : ℂ) * f J) =
        (M : ℂ) * ∑ T : IndepFinset (AllowedOutsideGraph D I),
          (H.probability T : ℂ) * f (glueAllowedOutside D I T) := by
    rw [hsum]
    calc
      (∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          (C.law.probability J.1 : ℂ) * f J.1) =
        ∑ J : {J : IndepFinset G // restriction D J = restriction D I},
          (M : ℂ) * ((H.probability (restrictionFiberAllowedEquiv D I J) : ℂ) *
            f J.1) := by
            apply Finset.sum_congr rfl
            intro J hJ
            rw [law_probability_allowedOutside_factor,
              ← restrictionFiberMass_eq_allowedOutsideFiberFactor]
            push_cast
            ring
      _ = (M : ℂ) * ∑ J : {J : IndepFinset G //
          restriction D J = restriction D I},
          (H.probability (restrictionFiberAllowedEquiv D I J) : ℂ) * f J.1 := by
            rw [Finset.mul_sum]
      _ = (M : ℂ) * ∑ T : IndepFinset (AllowedOutsideGraph D I),
          (H.probability T : ℂ) * f (glueAllowedOutside D I T) := by
            congr 1
            rw [← Equiv.sum_comp (restrictionFiberAllowedEquiv D I)
              (fun T : IndepFinset (AllowedOutsideGraph D I) =>
                (H.probability T : ℂ) * f (glueAllowedOutside D I T))]
            apply Finset.sum_congr rfl
            intro J hJ
            simp [restrictionFiberAllowedEquiv]
  unfold conditionalExpectationComplex
  rw [hnum]
  change (M : ℂ) * (∑ T : IndepFinset (AllowedOutsideGraph D I),
      (H.probability T : ℂ) * f (glueAllowedOutside D I T)) / (M : ℂ) = _
  exact mul_div_cancel_left₀ _ (by
    exact_mod_cast ne_of_gt (restrictionFiberMass_pos C D I))

theorem conditionalExpectationComplex_fiberInvariant_mul
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (h f : IndepFinset G → ℂ)
    (hh : ∀ I J, restriction S I = restriction S J → h I = h J)
    (I : IndepFinset G) :
    conditionalExpectationComplex C S (fun J => h J * f J) I =
      h I * conditionalExpectationComplex C S f I := by
  classical
  unfold conditionalExpectationComplex
  rw [← mul_div_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  change (C.law.probability J : ℂ) * (h J * f J) =
    h I * ((C.law.probability J : ℂ) * f J)
  rw [hh J I (mem_restrictionFiber.mp hJ)]
  ring

theorem lawExpectation_fiberInvariant_mul_conditionalExpectationComplex
    (C : Forest.CanonicalFirstRecoveryState G) (S : Finset V)
    (h f : IndepFinset G → ℂ)
    (hh : ∀ I J, restriction S I = restriction S J → h I = h J) :
    (∑ I : IndepFinset G, (C.law.probability I : ℂ) *
      (h I * conditionalExpectationComplex C S f I)) =
      ∑ I : IndepFinset G, (C.law.probability I : ℂ) * (h I * f I) := by
  calc
    _ = ∑ I : IndepFinset G, (C.law.probability I : ℂ) *
        conditionalExpectationComplex C S (fun J => h J * f J) I := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [conditionalExpectationComplex_fiberInvariant_mul C S h f hh I]
    _ = _ := lawExpectation_conditionalExpectationComplex C S _

end
end ActualMartingaleProjection
end Erdos993
