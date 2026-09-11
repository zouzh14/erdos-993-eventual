import Erdos993.Forest.AppendixDSpineCovariancePQV

/-!
# Appendix D: explicit inhomogeneous retained law and path kernels

This module packages the retained marginal of the one original global canonical
hard-core law as a finite law, together with the inhomogeneous hard-core mass
built source the effective activities obtained by integrating omitted descendant
branches.  It also exposes orientation-free cavity messages and the exact
binary transition/regression data along paths.  No retained graph or subtree
is assigned canonical or first-recovery data.
-/

open scoped BigOperators

namespace Erdos993
namespace ActualRootedVariance

noncomputable section
set_option maxHeartbeats 800000
universe u

noncomputable local instance finiteSubtypeAppendixDInhomogeneous
    {α : Type*} [Fintype α] (p : α → Prop) : Fintype {x // p x} :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable local instance classicalDecidableEqAppendixDInhomogeneous
    (α : Type*) : DecidableEq α := Classical.decEq α

namespace ComponentRooting

open Forest

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Independent configurations supported on a retained vertex set. -/
abbrev RetainedConfiguration (G : SimpleGraph V) (S : Finset V) :=
  {T : Finset V // T ⊆ S ∧ G.IsIndepSet (T : Set V)}

/-- Restriction of one global independent configuration to the retained set. -/
noncomputable def retainedRestriction (S : Finset V) (I : IndepFinset G) :
    RetainedConfiguration G S := by
  classical
  refine ⟨ActualMartingaleProjection.restriction S I, ?_, ?_⟩
  · exact Finset.inter_subset_right
  · apply I.property.mono
    intro x hx
    exact (Finset.mem_inter.mp hx).1

@[simp] theorem retainedRestriction_val (S : Finset V) (I : IndepFinset G) :
    (retainedRestriction (G := G) S I : Finset V) =
      ActualMartingaleProjection.restriction S I := rfl

/-- The inhomogeneous hard-core weight on the retained induced forest. -/
noncomputable def retainedInhomogeneousMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (T : RetainedConfiguration G S) : ℝ :=
  ∏ u ∈ (T : Finset V), R.effectiveActivity (G := G) C S u

/-- The finite inhomogeneous partition function. -/
noncomputable def retainedInhomogeneousPartition
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) : ℝ :=
  ∑ T : RetainedConfiguration G S, R.retainedInhomogeneousMass (G := G) C S T

theorem retainedInhomogeneousMass_pos
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (T : RetainedConfiguration G S) :
    0 < R.retainedInhomogeneousMass (G := G) C S T := by
  unfold retainedInhomogeneousMass
  exact Finset.prod_pos fun u hu => R.effectiveActivity_pos (G := G) C S u

theorem retainedInhomogeneousPartition_pos
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) :
    0 < R.retainedInhomogeneousPartition (G := G) C S := by
  classical
  let T0 : RetainedConfiguration G S := ⟨∅, by simp, by simp⟩
  have hnonneg : ∀ T : RetainedConfiguration G S,
      0 ≤ R.retainedInhomogeneousMass (G := G) C S T :=
    fun T => (R.retainedInhomogeneousMass_pos (G := G) C S T).le
  have hle : R.retainedInhomogeneousMass (G := G) C S T0 ≤
      ∑ T : RetainedConfiguration G S,
        R.retainedInhomogeneousMass (G := G) C S T :=
    Finset.single_le_sum (fun T _ => hnonneg T) (Finset.mem_univ T0)
  exact (R.retainedInhomogeneousMass_pos (G := G) C S T0).trans_le hle

/-- The normalized finite inhomogeneous hard-core law with site activities
`effectiveActivity C R S`. -/
noncomputable def retainedInhomogeneousLaw
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) : FiniteLatticeLaw (RetainedConfiguration G S) where
  stat T := (T : Finset V).card
  probability T := R.retainedInhomogeneousMass (G := G) C S T /
    R.retainedInhomogeneousPartition (G := G) C S
  probability_nonneg T := div_nonneg
    (R.retainedInhomogeneousMass_pos (G := G) C S T).le
    (R.retainedInhomogeneousPartition_pos (G := G) C S).le
  probability_sum := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (R.retainedInhomogeneousPartition_pos (G := G) C S))

@[simp] theorem retainedInhomogeneousLaw_probability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (T : RetainedConfiguration G S) :
    (R.retainedInhomogeneousLaw (G := G) C S).probability T =
      R.retainedInhomogeneousMass (G := G) C S T /
        R.retainedInhomogeneousPartition (G := G) C S := rfl

/-- The literal pushforward marginal of the original global canonical law. -/
noncomputable def originalRetainedMarginalLaw
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) : FiniteLatticeLaw (RetainedConfiguration G S) where
  stat T := (T : Finset V).card
  probability T := ∑ I : IndepFinset G,
    if retainedRestriction (G := G) S I = T then C.law.probability I else 0
  probability_nonneg T := Finset.sum_nonneg fun I _ => by
    split_ifs
    · exact C.law.probability_nonneg I
    · exact le_rfl
  probability_sum := by
    classical
    rw [Finset.sum_comm]
    calc
      (∑ I : IndepFinset G, ∑ T : RetainedConfiguration G S,
          if retainedRestriction (G := G) S I = T then C.law.probability I else 0) =
          ∑ I : IndepFinset G, C.law.probability I := by
            apply Finset.sum_congr rfl
            intro I hI
            simp
      _ = 1 := C.law.probability_sum

/-- Exact point-mass form of the original-law restriction pushforward. -/
theorem originalRetainedMarginalLaw_probability_eq_restrictionFiberMass
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (I : IndepFinset G) :
    (R.originalRetainedMarginalLaw (G := G) C S).probability
        (retainedRestriction (G := G) S I) =
      ActualMartingaleProjection.restrictionFiberMass C S I := by
  classical
  unfold originalRetainedMarginalLaw ActualMartingaleProjection.restrictionFiberMass
    ActualMartingaleProjection.restrictionFiber
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [retainedRestriction, Subtype.mk.injEq]

/-- D.55 point masses of the original retained marginal, after exact
integration of every omitted descendant branch. -/
theorem originalRetainedMarginalLaw_probability_eq_boundary_PQ
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    (I : IndepFinset G) :
    (R.originalRetainedMarginalLaw (G := G) C S).probability
        (retainedRestriction (G := G) S I) =
      C.activity ^ (ActualMartingaleProjection.restriction S I).card *
        (∏ w ∈ R.exposedBoundary (G := G) S,
          if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
            R.rootedP (G := G) C w else R.rootedQ (G := G) C w) /
        independenceEval G C.activity := by
  rw [R.originalRetainedMarginalLaw_probability_eq_restrictionFiberMass]
  exact R.restrictionFiberMass_eq_activity_pow_mul_prod_boundary_PQ
    (G := G) C hS I

/-- Boundary factors are a configuration-independent product of `P`'s times
exactly the omitted-child vacancy factors attached to occupied retained
vertices. -/
theorem boundaryPQ_eq_boundaryP_mul_omittedVacancy
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (S : Finset V) (I : IndepFinset G) :
    (∏ w ∈ R.exposedBoundary (G := G) S,
      if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
        R.rootedP (G := G) C w else R.rootedQ (G := G) C w) =
      (∏ w ∈ R.exposedBoundary (G := G) S,
        R.rootedP (G := G) C w) *
      ∏ u ∈ ActualMartingaleProjection.restriction S I,
        ∏ w ∈ R.omittedChildren (G := G) S u,
          R.vacancyProbability (G := G) C w := by
  classical
  let U := ActualMartingaleProjection.restriction S I
  let W := U.biUnion (fun u => R.omittedChildren (G := G) S u)
  have hdisj :
      (↑U : Set V).PairwiseDisjoint
        (fun u => R.omittedChildren (G := G) S u) := by
    intro u hu v hv huv
    change Disjoint (R.omittedChildren (G := G) S u)
      (R.omittedChildren (G := G) S v)
    rw [Finset.disjoint_left]
    intro w hwu hwv
    have huw : R.IsChild (G := G) u w ∧ w ∉ S := by
      simpa [omittedChildren] using hwu
    have hvw : R.IsChild (G := G) v w ∧ w ∉ S := by
      simpa [omittedChildren] using hwv
    exact huv (R.isChild_unique (G := G) C.isForest huw.1 hvw.1)
  have hWsub : W ⊆ R.exposedBoundary (G := G) S := by
    intro w hw
    rcases Finset.mem_biUnion.mp hw with ⟨u, huU, huw⟩
    have hu : u ∈ I.1 ∧ u ∈ S := by
      simpa [U, ActualMartingaleProjection.restriction] using huU
    have huw' : R.IsChild (G := G) u w ∧ w ∉ S := by
      simpa [omittedChildren] using huw
    exact (R.mem_exposedBoundary (G := G) S w).mpr
      ⟨huw'.2, Or.inr ⟨u, hu.2, huw'.1⟩⟩
  have hparent_one {w : V} (hw : w ∈ W) :
      ActualMartingaleProjection.parentOccupationIndicator R I w = 1 := by
    rcases Finset.mem_biUnion.mp hw with ⟨u, huU, huw⟩
    have hu : u ∈ I.1 ∧ u ∈ S := by
      simpa [U, ActualMartingaleProjection.restriction] using huU
    have huw' : R.IsChild (G := G) u w ∧ w ∉ S := by
      simpa [omittedChildren] using huw
    have hnroot : w ≠ R.rootOf (G := G) w := by
      intro hr
      exact (R.not_isChild_of_eq_root (G := G) hr) huw'.1
    rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent
          C R I hnroot,
      R.selectedParent_eq_of_isChild (G := G) C huw'.1 hnroot]
    simp [ActualMartingaleProjection.occupationIndicator, hu.1]
  have hparent_zero {w : V}
      (hwB : w ∈ R.exposedBoundary (G := G) S) (hwW : w ∉ W) :
      ActualMartingaleProjection.parentOccupationIndicator R I w = 0 := by
    rcases (R.mem_exposedBoundary (G := G) S w).mp hwB with
      ⟨hwout, hroot | ⟨p, hpS, hpw⟩⟩
    · exact ActualMartingaleProjection.parentOccupationIndicator_root R I hroot
    · have hpI : p ∉ I.1 := by
        intro hpI
        apply hwW
        apply Finset.mem_biUnion.mpr
        refine ⟨p, ?_, ?_⟩
        · simp [U, ActualMartingaleProjection.restriction, hpI, hpS]
        · simp [omittedChildren, hpw, hwout]
      have hnroot : w ≠ R.rootOf (G := G) w := by
        intro hr
        exact (R.not_isChild_of_eq_root (G := G) hr) hpw
      rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent
            C R I hnroot,
        R.selectedParent_eq_of_isChild (G := G) C hpw hnroot]
      simp [ActualMartingaleProjection.occupationIndicator, hpI]
  have hterm (w : V) (hwB : w ∈ R.exposedBoundary (G := G) S) :
      (if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
          R.rootedP (G := G) C w else R.rootedQ (G := G) C w) =
        R.rootedP (G := G) C w *
          (if w ∈ W then R.vacancyProbability (G := G) C w else 1) := by
    by_cases hwW : w ∈ W
    · have hpne :
          ActualMartingaleProjection.parentOccupationIndicator R I w ≠ 0 := by
        rw [hparent_one hwW]
        norm_num
      rw [if_neg hpne, if_pos hwW]
      unfold vacancyProbability
      field_simp [ne_of_gt (R.rootedP_pos (G := G) C w)]
    · rw [if_pos (hparent_zero hwB hwW), if_neg hwW, mul_one]
  have hfilter :
      (R.exposedBoundary (G := G) S).filter (fun w => w ∈ W) = W := by
    ext w
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hWsub h, h⟩⟩
  calc
    _ = ∏ w ∈ R.exposedBoundary (G := G) S,
          R.rootedP (G := G) C w *
            (if w ∈ W then R.vacancyProbability (G := G) C w else 1) := by
          apply Finset.prod_congr rfl
          exact hterm
    _ = (∏ w ∈ R.exposedBoundary (G := G) S,
          R.rootedP (G := G) C w) *
        ∏ w ∈ R.exposedBoundary (G := G) S,
          (if w ∈ W then R.vacancyProbability (G := G) C w else 1) := by
          rw [Finset.prod_mul_distrib]
    _ = (∏ w ∈ R.exposedBoundary (G := G) S,
          R.rootedP (G := G) C w) *
        ∏ w ∈ W, R.vacancyProbability (G := G) C w := by
          rw [← Finset.prod_filter, hfilter]
    _ = _ := by
          dsimp [W]
          rw [Finset.prod_biUnion hdisj]

/-- A retained configuration regarded as a global independent configuration
with every omitted vertex vacant. -/
def retainedAsGlobal (S : Finset V) (T : RetainedConfiguration G S) :
    IndepFinset G := ⟨(T : Finset V), T.property.2⟩

@[simp] theorem retainedRestriction_retainedAsGlobal
    (S : Finset V) (T : RetainedConfiguration G S) :
    retainedRestriction (G := G) S (retainedAsGlobal (G := G) S T) = T := by
  apply Subtype.ext
  change (T : Finset V) ∩ S = (T : Finset V)
  exact Finset.inter_eq_left.mpr T.property.1

/-- Exact normalized equality: the pushforward of the one original global law
is the finite inhomogeneous hard-core law with activities `effectiveActivity`.
This is D.55 in normalized-law form. -/
theorem originalRetainedMarginalLaw_probability_eq_retainedInhomogeneousLaw
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S)
    (T : RetainedConfiguration G S) :
    (R.originalRetainedMarginalLaw (G := G) C S).probability T =
      (R.retainedInhomogeneousLaw (G := G) C S).probability T := by
  classical
  let K : ℝ :=
    (∏ w ∈ R.exposedBoundary (G := G) S,
      R.rootedP (G := G) C w) / independenceEval G C.activity
  have hmass (U : RetainedConfiguration G S) :
      R.retainedInhomogeneousMass (G := G) C S U =
        C.activity ^ (U : Finset V).card *
          ∏ u ∈ (U : Finset V),
            ∏ w ∈ R.omittedChildren (G := G) S u,
              R.vacancyProbability (G := G) C w := by
    unfold retainedInhomogeneousMass effectiveActivity
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const]
  have hproportional (U : RetainedConfiguration G S) :
      (R.originalRetainedMarginalLaw (G := G) C S).probability U =
        K * R.retainedInhomogeneousMass (G := G) C S U := by
    let I : IndepFinset G := retainedAsGlobal (G := G) S U
    have hrestriction :
        ActualMartingaleProjection.restriction S I = (U : Finset V) := by
      change (U : Finset V) ∩ S = (U : Finset V)
      exact Finset.inter_eq_left.mpr U.property.1
    have hret : retainedRestriction (G := G) S I = U := by
      apply Subtype.ext
      exact hrestriction
    calc
      _ = (R.originalRetainedMarginalLaw (G := G) C S).probability
          (retainedRestriction (G := G) S I) := by rw [hret]
      _ = C.activity ^
            (ActualMartingaleProjection.restriction S I).card *
          (∏ w ∈ R.exposedBoundary (G := G) S,
            if ActualMartingaleProjection.parentOccupationIndicator R I w = 0 then
              R.rootedP (G := G) C w else R.rootedQ (G := G) C w) /
          independenceEval G C.activity :=
            R.originalRetainedMarginalLaw_probability_eq_boundary_PQ
              (G := G) C hS I
      _ = K * R.retainedInhomogeneousMass (G := G) C S U := by
        rw [R.boundaryPQ_eq_boundaryP_mul_omittedVacancy
              (G := G) C S I, hrestriction, hmass U]
        dsimp [K]
        ring
  have hnormalize :
      K * R.retainedInhomogeneousPartition (G := G) C S = 1 := by
    unfold retainedInhomogeneousPartition
    rw [Finset.mul_sum]
    calc
      (∑ U : RetainedConfiguration G S,
          K * R.retainedInhomogeneousMass (G := G) C S U) =
          ∑ U : RetainedConfiguration G S,
            (R.originalRetainedMarginalLaw (G := G) C S).probability U := by
              apply Finset.sum_congr rfl
              intro U hU
              exact (hproportional U).symm
      _ = 1 := (R.originalRetainedMarginalLaw (G := G) C S).probability_sum
  rw [retainedInhomogeneousLaw_probability, hproportional T]
  apply (eq_div_iff
    (ne_of_gt (R.retainedInhomogeneousPartition_pos (G := G) C S))).2
  calc
    (K * R.retainedInhomogeneousMass (G := G) C S T) *
        R.retainedInhomogeneousPartition (G := G) C S =
      R.retainedInhomogeneousMass (G := G) C S T *
        (K * R.retainedInhomogeneousPartition (G := G) C S) := by ring
    _ = R.retainedInhomogeneousMass (G := G) C S T := by rw [hnormalize, mul_one]

/-- Equality of the pushforward law and the normalized effective-activity law. -/
theorem originalRetainedMarginalLaw_eq_retainedInhomogeneousLaw
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {S : Finset V} (hS : ActualMartingaleProjection.AncestorClosed R S) :
    R.originalRetainedMarginalLaw (G := G) C S =
      R.retainedInhomogeneousLaw (G := G) C S := by
  let L₁ := R.originalRetainedMarginalLaw (G := G) C S
  let L₂ := R.retainedInhomogeneousLaw (G := G) C S
  have hstat : L₁.stat = L₂.stat := by
    rfl
  have hprob : L₁.probability = L₂.probability := by
    funext T
    exact R.originalRetainedMarginalLaw_probability_eq_retainedInhomogeneousLaw
      (G := G) C hS T
  cases hL₁ : L₁ with
  | mk stat₁ probability₁ hnonneg₁ hsum₁ =>
    cases hL₂ : L₂ with
    | mk stat₂ probability₂ hnonneg₂ hsum₂ =>
      rw [hL₁, hL₂] at hstat hprob
      change stat₁ = stat₂ at hstat
      change probability₁ = probability₂ at hprob
      subst stat₂
      subst probability₂
      change L₁ = L₂
      rw [hL₁, hL₂]

/-- A rooting used to read the cavity on the `source` side of the oriented edge
`source → toward`.  If the supplied rooting already has `toward` as parent it is
kept; otherwise the component is rerooted at `toward`. -/
noncomputable def directedCavityRooting (R : ComponentRooting G)
    (source toward : V) : ComponentRooting G := by
  classical
  exact if R.IsChild (G := G) toward source then R else R.rerootAt (G := G) toward

/-- Vacant and occupied cavity partition functions in either edge orientation. -/
noncomputable def directedCavityQ (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) : ℝ :=
  (R.directedCavityRooting (G := G) source toward).rootedQ (G := G) C source

noncomputable def directedCavityA (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) : ℝ :=
  (R.directedCavityRooting (G := G) source toward).rootedA (G := G) C source

noncomputable def directedCavityP (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) : ℝ :=
  (R.directedCavityRooting (G := G) source toward).rootedP (G := G) C source

/-- The directed cavity occupation odds and its logistic transition parameter. -/
noncomputable def directedCavityOdds (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) : ℝ :=
  R.directedCavityA (G := G) C source toward /
    R.directedCavityQ (G := G) C source toward

noncomputable def directedCavityTransition (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) : ℝ :=
  R.directedCavityA (G := G) C source toward /
    R.directedCavityP (G := G) C source toward

/-- Both cavity partition functions are positive, in either orientation. -/
theorem directedCavityQ_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) :
    0 < R.directedCavityQ (G := G) C source toward := by
  unfold directedCavityQ
  exact (R.directedCavityRooting (G := G) source toward).rootedQ_pos
    (G := G) C source

theorem directedCavityA_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) :
    0 < R.directedCavityA (G := G) C source toward := by
  unfold directedCavityA
  exact (R.directedCavityRooting (G := G) source toward).rootedA_pos
    (G := G) C source

theorem directedCavityP_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) :
    0 < R.directedCavityP (G := G) C source toward := by
  unfold directedCavityP
  exact (R.directedCavityRooting (G := G) source toward).rootedP_pos
    (G := G) C source

theorem directedCavityOdds_pos (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) :
    0 < R.directedCavityOdds (G := G) C source toward :=
  div_pos (R.directedCavityA_pos (G := G) C source toward)
    (R.directedCavityQ_pos (G := G) C source toward)

/-- Exact partition identity and logistic conversion of odds to transition. -/
theorem directedCavityP_eq_Q_add_A (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (source toward : V) :
    R.directedCavityP (G := G) C source toward =
      R.directedCavityQ (G := G) C source toward +
        R.directedCavityA (G := G) C source toward := by
  unfold directedCavityP directedCavityQ directedCavityA
  exact (R.directedCavityRooting (G := G) source toward).rootedP_eq_rootedQ_add_rootedA
    (G := G) C source

theorem directedCavityTransition_eq_odds_div_one_add
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (source toward : V) :
    R.directedCavityTransition (G := G) C source toward =
      R.directedCavityOdds (G := G) C source toward /
        (1 + R.directedCavityOdds (G := G) C source toward) := by
  unfold directedCavityTransition directedCavityOdds
  rw [R.directedCavityP_eq_Q_add_A (G := G) C source toward]
  field_simp [ne_of_gt (R.directedCavityQ_pos (G := G) C source toward),
    ne_of_gt (R.directedCavityA_pos (G := G) C source toward)]

/-- In the orientation already supplied by `R`, the directed transition is the
original-law child cavity probability. -/
@[simp] theorem directedCavityTransition_of_isChild
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) :
    R.directedCavityTransition (G := G) C u p =
      R.occupationProbability (G := G) C u := by
  simp [directedCavityTransition, directedCavityA, directedCavityP,
    directedCavityRooting, hpu, occupationProbability]

/-- Directed cavity odds are bounded by the unchanged global activity. -/
theorem directedCavityOdds_le_activity
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (source toward : V) :
    R.directedCavityOdds (G := G) C source toward ≤ C.activity := by
  let R' := R.directedCavityRooting (G := G) source toward
  have hprod : (∏ v ∈ R'.children (G := G) source,
      R'.vacancyProbability (G := G) C v) ≤ 1 := by
    apply Finset.prod_le_one
    · intro v hv
      exact (R'.vacancyProbability_pos (G := G) C v).le
    · intro v hv
      rw [R'.vacancyProbability_eq_one_sub_occupationProbability (G := G) C v]
      linarith [R'.occupationProbability_nonneg (G := G) C v]
  have hformula := R'.occupationOdds_eq_activity_mul_prod_children (G := G) C source
  have heq : R.directedCavityOdds (G := G) C source toward =
      R'.occupationProbability (G := G) C source /
        R'.vacancyProbability (G := G) C source := by
    unfold directedCavityOdds directedCavityA directedCavityQ
      occupationProbability vacancyProbability
    dsimp [R']
    rw [div_div_div_cancel_right₀ (ne_of_gt (R'.rootedP_pos (G := G) C source))]
  rw [heq, hformula]
  exact mul_le_of_le_one_right C.activity_pos.le hprod

/-- Under `activity < 27`, both orientations have odds below `27` and affine
transition slope below `27/28`. -/
theorem directedCavityOdds_lt_twentySeven
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (source toward : V) :
    R.directedCavityOdds (G := G) C source toward < 27 :=
  (R.directedCavityOdds_le_activity (G := G) C source toward).trans_lt hz

theorem directedCavityTransition_lt_twentySeven_div_twentyEight
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) (source toward : V) :
    R.directedCavityTransition (G := G) C source toward < (27 : ℝ) / 28 := by
  unfold directedCavityTransition directedCavityA directedCavityP
  exact occupationProbability_lt_twentySeven_div_twentyEight (G := G) C
    (R.directedCavityRooting (G := G) source toward) hz source

/-- Explicit simultaneous statement for the two orientations of one edge. -/
theorem directedCavity_both_orientations_contractive
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    (hz : C.activity < 27) {u v : V} (huv : G.Adj u v) :
    (0 < R.directedCavityOdds (G := G) C u v ∧
      R.directedCavityOdds (G := G) C u v < 27 ∧
      R.directedCavityTransition (G := G) C u v < (27 : ℝ) / 28) ∧
    (0 < R.directedCavityOdds (G := G) C v u ∧
      R.directedCavityOdds (G := G) C v u < 27 ∧
      R.directedCavityTransition (G := G) C v u < (27 : ℝ) / 28) := by
  exact ⟨⟨R.directedCavityOdds_pos (G := G) C u v,
    R.directedCavityOdds_lt_twentySeven (G := G) C hz u v,
    R.directedCavityTransition_lt_twentySeven_div_twentyEight (G := G) C hz u v⟩,
    ⟨R.directedCavityOdds_pos (G := G) C v u,
    R.directedCavityOdds_lt_twentySeven (G := G) C hz v u,
    R.directedCavityTransition_lt_twentySeven_div_twentyEight (G := G) C hz v u⟩⟩

/-- The two-state hard-core transition mass.  An occupied parent forces a
vacant child; a vacant parent gives Bernoulli parameter `t`. -/
def twoStateHardCoreKernel (t : ℝ) (parent child : Bool) : ℝ :=
  if parent then (if child then 0 else 1)
  else (if child then t else 1 - t)

@[simp] theorem sum_twoStateHardCoreKernel (t : ℝ) (parent : Bool) :
    ∑ child : Bool, twoStateHardCoreKernel t parent child = 1 := by
  cases parent <;> simp [twoStateHardCoreKernel]

/-- The exact affine conditional-mean row of the two-state kernel. -/
theorem sum_twoStateHardCoreKernel_mul_indicator (t : ℝ) (parent : Bool) :
    ∑ child : Bool, twoStateHardCoreKernel t parent child *
      (if child then (1 : ℝ) else 0) =
      t * (1 - if parent then (1 : ℝ) else 0) := by
  cases parent <;> simp [twoStateHardCoreKernel]

/-- Every rooted child edge of the original-law occupation process has exactly
the preceding inhomogeneous two-state affine transition, with its innovation
term separated. -/
theorem occupationIndicator_child_markov_recursion
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u) (I : IndepFinset G) :
    ActualMartingaleProjection.occupationIndicator I u =
      ActualMartingaleProjection.eta C R I u +
        R.directedCavityTransition (G := G) C u p *
          (1 - ActualMartingaleProjection.occupationIndicator I p) := by
  rw [R.directedCavityTransition_of_isChild (G := G) C hpu]
  have hu : u ≠ R.rootOf (G := G) u := by
    intro h
    exact R.not_isChild_of_eq_root (G := G) h hpu
  unfold ActualMartingaleProjection.eta
  rw [ActualMartingaleProjection.parentOccupationIndicator_eq_selectedParent C R I hu,
    R.selectedParent_eq_of_isChild (G := G) C hpu hu]
  ring

/-- An explicit finite path witnessing successive affine two-state regressions.
Unlike `CovariancePeeling` (a proposition), this data type retains the edge
sequence, so its numerical slope product is computationally available. -/
inductive InhomogeneousMarkovPath (R : ComponentRooting G) : V → V → ℕ → Type u
  | refl (x : V) : InhomogeneousMarkovPath R x x 0
  | right {x p u : V} {n : ℕ}
      (hpu : R.IsChild (G := G) p u)
      (hout : ¬ R.IsDescendant (G := G) u x)
      (h : InhomogeneousMarkovPath R x p n) :
      InhomogeneousMarkovPath R x u (n + 1)
  | left {p u y : V} {n : ℕ}
      (hpu : R.IsChild (G := G) p u)
      (hout : ¬ R.IsDescendant (G := G) u y)
      (h : InhomogeneousMarkovPath R p y n) :
      InhomogeneousMarkovPath R u y (n + 1)

/-- Forget the retained edge data and recover the proposition used by the
pre-existing covariance peeling proof. -/
def InhomogeneousMarkovPath.toCovariancePeeling
    (R : ComponentRooting G) :
    {x y : V} → {n : ℕ} → InhomogeneousMarkovPath R x y n →
      CovariancePeeling R x y n
  | _, _, _, .refl x => .refl x
  | _, _, _, .right hpu hout h => .right hpu hout (h.toCovariancePeeling R)
  | _, _, _, .left hpu hout h => .left hpu hout (h.toCovariancePeeling R)

/-- The terminal vertex at which an explicit Markov path closes. -/
def InhomogeneousMarkovPath.baseVertex
    (R : ComponentRooting G) :
    {x y : V} → {n : ℕ} → InhomogeneousMarkovPath R x y n → V
  | _, _, _, .refl x => x
  | _, _, _, .right _ _ h => h.baseVertex R
  | _, _, _, .left _ _ h => h.baseVertex R

/-- Finite conditional expectation is additive. -/
theorem conditionalExpectation_add_local
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (f g : IndepFinset G → ℝ) (I : IndepFinset G) :
    ActualMartingaleProjection.conditionalExpectation C S (fun J => f J + g J) I =
      ActualMartingaleProjection.conditionalExpectation C S f I +
        ActualMartingaleProjection.conditionalExpectation C S g I := by
  unfold ActualMartingaleProjection.conditionalExpectation
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, add_div]

/-- Constants pull out of the finite conditional expectation. -/
theorem conditionalExpectation_const_mul_local
    (C : CanonicalFirstRecoveryState G) (S : Finset V) (a : ℝ)
    (f : IndepFinset G → ℝ) (I : IndepFinset G) :
    ActualMartingaleProjection.conditionalExpectation C S (fun J => a * f J) I =
      a * ActualMartingaleProjection.conditionalExpectation C S f I := by
  unfold ActualMartingaleProjection.conditionalExpectation
  have hterm (J : IndepFinset G) :
      C.law.probability J * (a * f J) = a * (C.law.probability J * f J) := by
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  ring

/-- Subtraction is preserved by finite conditional expectation. -/
theorem conditionalExpectation_sub_local
    (C : CanonicalFirstRecoveryState G) (S : Finset V)
    (f g : IndepFinset G → ℝ) (I : IndepFinset G) :
    ActualMartingaleProjection.conditionalExpectation C S (fun J => f J - g J) I =
      ActualMartingaleProjection.conditionalExpectation C S f I -
        ActualMartingaleProjection.conditionalExpectation C S g I := by
  unfold ActualMartingaleProjection.conditionalExpectation
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, sub_div]

/-- An observed occupation indicator is fixed by conditional expectation. -/
theorem conditionalExpectation_occupationIndicator_of_mem
    (C : CanonicalFirstRecoveryState G) (S : Finset V) {p : V}
    (hp : p ∈ S) (I : IndepFinset G) :
    ActualMartingaleProjection.conditionalExpectation C S
        (fun J => ActualMartingaleProjection.occupationIndicator J p) I =
      ActualMartingaleProjection.occupationIndicator I p := by
  unfold ActualMartingaleProjection.conditionalExpectation
  have hsum :
      (∑ J ∈ ActualMartingaleProjection.restrictionFiber S I,
        C.law.probability J * ActualMartingaleProjection.occupationIndicator J p) =
      (∑ J ∈ ActualMartingaleProjection.restrictionFiber S I,
        C.law.probability J) *
          ActualMartingaleProjection.occupationIndicator I p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [ActualMartingaleProjection.occupationIndicator_eq_of_restriction_eq hp
      (ActualMartingaleProjection.mem_restrictionFiber.mp hJ)]
  rw [hsum]
  unfold ActualMartingaleProjection.restrictionFiberMass
  rw [mul_div_cancel_left₀]
  exact ne_of_gt (ActualMartingaleProjection.restrictionFiberMass_pos C S I)

/-- Exact D.58 one-step conditional transition.  Given any ancestor-closed
observed past containing the parent but not the child, the child is forced to
zero when the parent is occupied and otherwise is Bernoulli with the directed
cavity transition parameter. -/
theorem occupationIndicator_child_conditionalTransition
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {p u : V} (hpu : R.IsChild (G := G) p u)
    (S : Finset V) (hS : ActualMartingaleProjection.AncestorClosed R S)
    (hp : p ∈ S) (hu : u ∉ S) (I : IndepFinset G) :
    ActualMartingaleProjection.conditionalExpectation C S
        (fun J => ActualMartingaleProjection.occupationIndicator J u) I =
      R.directedCavityTransition (G := G) C u p *
        (1 - ActualMartingaleProjection.occupationIndicator I p) := by
  have hfun : (fun J : IndepFinset G =>
      ActualMartingaleProjection.occupationIndicator J u) =
      fun J => ActualMartingaleProjection.eta C R J u +
        R.directedCavityTransition (G := G) C u p *
          ((fun _ : IndepFinset G => (1 : ℝ)) J -
            ActualMartingaleProjection.occupationIndicator J p) := by
    funext J
    simpa using R.occupationIndicator_child_markov_recursion (G := G) C hpu J
  rw [hfun, conditionalExpectation_add_local,
    ActualMartingaleProjection.conditionalExpectation_eta_eq_zero_of_unobserved
      C R S hS u hu I,
    conditionalExpectation_const_mul_local,
    conditionalExpectation_sub_local,
    ActualMartingaleProjection.conditionalExpectation_const,
    conditionalExpectation_occupationIndicator_of_mem C S hp I]
  ring

/-- The exact affine slope product attached to an explicit Markov path. -/
noncomputable def InhomogeneousMarkovPath.affineSlopeProduct
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) :
    {x y : V} → {n : ℕ} → InhomogeneousMarkovPath R x y n → ℝ
  | _, _, _, .refl _ => 1
  | _, _, _, .right (p := p) (u := u) _ _ h =>
      (-R.directedCavityTransition (G := G) C u p) * h.affineSlopeProduct C R
  | _, _, _, .left (p := p) (u := u) _ _ h =>
      (-R.directedCavityTransition (G := G) C u p) * h.affineSlopeProduct C R

/-- Exact path covariance formula: covariance is the terminal diagonal
Bernoulli variance multiplied by the product of the affine Markov slopes. -/
theorem occupationCovariance_eq_affineSlopeProduct
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {x y : V} {n : ℕ} (h : InhomogeneousMarkovPath R x y n) :
    occupationCovariance C x y =
      h.affineSlopeProduct C R *
        occupationCovariance C (h.baseVertex R) (h.baseVertex R) := by
  induction h with
  | refl x => simp [InhomogeneousMarkovPath.affineSlopeProduct,
      InhomogeneousMarkovPath.baseVertex]
  | @right x p u n hpu hout h ih =>
      rw [R.occupationCovariance_child (G := G) C hpu hout, ih]
      simp only [InhomogeneousMarkovPath.affineSlopeProduct,
        InhomogeneousMarkovPath.baseVertex,
        R.directedCavityTransition_of_isChild (G := G) C hpu]
      ring
  | @left p u y n hpu hout h ih =>
      rw [occupationCovariance_comm C u y,
        R.occupationCovariance_child (G := G) C hpu hout,
        occupationCovariance_comm C y p, ih]
      simp only [InhomogeneousMarkovPath.affineSlopeProduct,
        InhomogeneousMarkovPath.baseVertex,
        R.directedCavityTransition_of_isChild (G := G) C hpu]
      ring

end ComponentRooting
end
end ActualRootedVariance
end Erdos993
