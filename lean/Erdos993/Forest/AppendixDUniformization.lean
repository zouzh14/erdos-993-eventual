import Erdos993.Forest.AppendixDRetainedMartingaleArray
open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
namespace Erdos993.Forest
open Erdos993.ActualRootedVariance
open CanonicalCompactnessWrapper
open CanonicalCompactnessWrapper.CanonicalSequence
noncomputable section
universe u v

private theorem hardCoreLaw_mean_iso' {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) (z : ℝ) (hz : 0 < z) :
    (hardCoreLaw G z hz).mean = (hardCoreLaw H z hz).mean := by
  unfold FiniteLatticeLaw.mean
  apply Fintype.sum_equiv (indepFinsetIsoEquiv e)
  intro s
  simp only [hardCoreLaw]
  rw [indepFinsetIsoEquiv_card]
  congr 2
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso e]

private theorem independenceCoefficients_iso' {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {G : SimpleGraph A} {H : SimpleGraph B} (e : G ≃g H) :
    independenceCoefficients G = independenceCoefficients H := by
  funext k
  unfold independenceCoefficients
  norm_cast
  rw [← coeff_independencePolynomial, ← coeff_independencePolynomial,
    independencePolynomial_iso e]

noncomputable def CanonicalFirstRecoveryState.comapEquiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    (e : A ≃ B) {G : SimpleGraph B} (C : CanonicalFirstRecoveryState G) :
    CanonicalFirstRecoveryState (G.comap e.toEmbedding) where
  isForest := (SimpleGraph.Iso.comap e G).isAcyclic_iff.mpr C.isForest
  index := C.index
  firstRecovery := by
    rw [independenceCoefficients_iso' (SimpleGraph.Iso.comap e G)]
    exact C.firstRecovery
  activity := C.activity
  activity_pos := C.activity_pos
  mean_eq_index := by
    rw [hardCoreLaw_mean_iso' (SimpleGraph.Iso.comap e G)]
    exact C.mean_eq_index

/- The universe-polymorphic variance transport is established below together
with the generic graph-isomorphism transport layer. -/

end
end Forest

namespace ActualRootedVariance.ComponentRooting
open Forest
noncomputable section
universe u v

noncomputable def pullbackIso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) : ComponentRooting H where
  root c := φ.symm (R.root (φ.connectedComponentEquiv c))
  root_mem c := by
    change φ.symm (R.root (φ.connectedComponentEquiv c)) ∈ c.supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff,
      SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ _).mp
      (R.root_mem (φ.connectedComponentEquiv c))

@[simp] theorem pullbackIso_rootOf
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).rootOf (G := H) u = φ.symm (R.rootOf (G := G) (φ u)) := by
  simp [rootOf, pullbackIso, SimpleGraph.Iso.connectedComponentEquiv]

private theorem graphIso_dist_eq
    {A : Type u} {B : Type v} {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (u v : A) : G.dist (φ u) (φ v) = H.dist u v := by
  by_cases hr : H.Reachable u v
  · have hrG : G.Reachable (φ u) (φ v) :=
      SimpleGraph.Iso.reachable_iff.mpr hr
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := hrG.exists_walk_length_eq_dist
    apply le_antisymm
    · calc
        G.dist (φ u) (φ v) ≤ (p.map φ.toHom).length :=
          SimpleGraph.dist_le _
        _ = p.length := by simp
        _ = H.dist u v := hp
    · calc
        H.dist u v ≤ (q.map φ.symm.toHom).length := by
          simpa using SimpleGraph.dist_le (q.map φ.symm.toHom)
        _ = q.length := by simp
        _ = G.dist (φ u) (φ v) := hq
  · have hrG : ¬ G.Reachable (φ u) (φ v) := by
      simpa [SimpleGraph.Iso.reachable_iff] using hr
    rw [H.dist_eq_zero_of_not_reachable hr,
      G.dist_eq_zero_of_not_reachable hrG]

@[simp] theorem pullbackIso_isChild_iff
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u v : A) :
    (R.pullbackIso φ).IsChild (G := H) u v ↔
      R.IsChild (G := G) (φ u) (φ v) := by
  simp only [IsChild, pullbackIso_rootOf]
  have hdist (x : B) (y : A) :
      H.dist (φ.symm x) y = G.dist x (φ y) := by
    rw [← graphIso_dist_eq φ (φ.symm x) y, φ.apply_symm_apply]
  simp only [φ.map_rel_iff, hdist]


@[simp] theorem pullbackIso_mem_descendants_iff
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u v : A) :
    v ∈ (R.pullbackIso φ).descendants (G := H) u ↔
      φ v ∈ R.descendants (G := G) (φ u) := by
  rw [mem_descendants, mem_descendants]
  constructor
  · intro h
    exact h.lift φ (fun a b hab => (pullbackIso_isChild_iff φ R a b).mp hab)
  · intro h
    have h' := h.lift φ.symm (fun a b hab =>
      (pullbackIso_isChild_iff φ R (φ.symm a) (φ.symm b)).mpr (by simpa using hab))
    simpa using h'

noncomputable def descendantsEquiv
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u : A) :
    {v // v ∈ (R.pullbackIso φ).descendants (G := H) u} ≃
      {v // v ∈ R.descendants (G := G) (φ u)} where
  toFun v := ⟨φ v, (pullbackIso_mem_descendants_iff φ R u v).mp v.property⟩
  invFun v := ⟨φ.symm v, by
    apply (pullbackIso_mem_descendants_iff φ R u (φ.symm v)).mpr
    simpa only [φ.apply_symm_apply] using v.property⟩
  left_inv v := by ext; simp
  right_inv v := by ext; simp

noncomputable def subtreeIso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).Subtree (G := H) u ≃g
      R.Subtree (G := G) (φ u) where
  toEquiv := descendantsEquiv φ R u
  map_rel_iff' := by
    intro x y
    change G.Adj (φ x) (φ y) ↔ H.Adj x y
    exact φ.map_rel_iff

@[simp] theorem subtreeIso_subtreeRoot
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}
    (φ : H ≃g G) (R : ComponentRooting G) (u : A) :
    subtreeIso φ R u ((R.pullbackIso φ).subtreeRoot (G := H) u) =
      R.subtreeRoot (G := G) (φ u) := by
  rfl

end
end ComponentRooting
end ActualRootedVariance
end Erdos993

namespace Erdos993.Forest
noncomputable section
universe u v

noncomputable def CanonicalFirstRecoveryState.pullbackIso
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G)
    (C : CanonicalFirstRecoveryState G) : CanonicalFirstRecoveryState H where
  isForest := φ.isAcyclic_iff.mpr C.isForest
  index := C.index
  firstRecovery := by
    rw [independenceCoefficients_iso' φ]
    exact C.firstRecovery
  activity := C.activity
  activity_pos := C.activity_pos
  mean_eq_index := by
    rw [hardCoreLaw_mean_iso' φ]
    exact C.mean_eq_index

end
end Forest
end Erdos993

namespace Erdos993
noncomputable section
universe u v

noncomputable local instance finiteSubtypeAux {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

private theorem independenceEval_iso_aux {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (z : ℝ) :
    independenceEval H z = independenceEval G z := by
  simp only [independenceEval, independencePolynomialReal]
  rw [independencePolynomial_iso φ]

private theorem hardCoreLaw_mean_iso_aux {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw H z hz).mean = (Forest.hardCoreLaw G z hz).mean := by
  unfold Forest.FiniteLatticeLaw.mean
  apply Fintype.sum_equiv (indepFinsetIsoEquiv φ)
  intro s
  simp only [Forest.hardCoreLaw]
  rw [indepFinsetIsoEquiv_card, independenceEval_iso_aux φ z]

private theorem hardCoreLaw_secondMoment_iso_aux
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw H z hz).secondMoment =
      (Forest.hardCoreLaw G z hz).secondMoment := by
  unfold Forest.FiniteLatticeLaw.secondMoment
  apply Fintype.sum_equiv (indepFinsetIsoEquiv φ)
  intro s
  simp only [Forest.hardCoreLaw]
  rw [indepFinsetIsoEquiv_card, independenceEval_iso_aux φ z]

private theorem hardCoreLaw_variance_iso_aux
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (z : ℝ) (hz : 0 < z) :
    (Forest.hardCoreLaw H z hz).variance =
      (Forest.hardCoreLaw G z hz).variance := by
  rw [Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    Forest.FiniteLatticeLaw.variance_eq_secondMoment_sub_sq_mean,
    hardCoreLaw_mean_iso_aux φ z hz, hardCoreLaw_secondMoment_iso_aux φ z hz]

noncomputable def deleteVertexIsoOf
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (u : A) :
    deleteVertex H u ≃g deleteVertex G (φ u) where
  toEquiv :=
    { toFun := fun x => ⟨φ x, fun h => x.property (φ.injective h)⟩
      invFun := fun y => ⟨φ.symm y, fun h => y.property (by
        calc
          (y : B) = φ (φ.symm y) := (φ.apply_symm_apply y).symm
          _ = φ u := congrArg φ h)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp }
  map_rel_iff' := by
    intro x y
    change G.Adj (φ x) (φ y) ↔ H.Adj x y
    exact φ.map_rel_iff

noncomputable def deleteClosedNeighborhoodIsoOf
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G) (u : A) :
    deleteClosedNeighborhood H u ≃g deleteClosedNeighborhood G (φ u) where
  toEquiv :=
    { toFun := fun x => ⟨φ x, by
        refine ⟨fun h => x.property.1 (φ.injective h), ?_⟩
        simpa only [φ.map_rel_iff] using x.property.2⟩
      invFun := fun y => ⟨φ.symm y, by
        refine ⟨fun h => y.property.1 (by
          calc
            (y : B) = φ (φ.symm y) := (φ.apply_symm_apply y).symm
            _ = φ u := congrArg φ h), ?_⟩
        intro ha
        exact y.property.2 (by simpa using (φ.map_rel_iff).mpr ha)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro y; ext; simp }
  map_rel_iff' := by
    intro x y
    change G.Adj (φ x) (φ y) ↔ H.Adj x y
    exact φ.map_rel_iff

namespace ActualRootedVariance.ComponentRooting
open Forest

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}

private theorem pullbackIso_rootedP_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).rootedP (G := H) (C.pullbackIso φ) u =
      R.rootedP (G := G) C (φ u) := by
  unfold rootedP
  exact independenceEval_iso_aux (subtreeIso φ R u) C.activity

private theorem pullbackIso_rootedQ_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).rootedQ (G := H) (C.pullbackIso φ) u =
      R.rootedQ (G := G) C (φ u) := by
  unfold rootedQ
  exact independenceEval_iso_aux (deleteVertexIsoOf (subtreeIso φ R u)
    ((R.pullbackIso φ).subtreeRoot (G := H) u)) C.activity

private theorem pullbackIso_rootedA_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).rootedA (G := H) (C.pullbackIso φ) u =
      R.rootedA (G := G) C (φ u) := by
  unfold rootedA
  congr 1
  exact independenceEval_iso_aux (deleteClosedNeighborhoodIsoOf (subtreeIso φ R u)
    ((R.pullbackIso φ).subtreeRoot (G := H) u)) C.activity

@[simp] theorem pullbackIso_occupationProbability_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).occupationProbability (G := H) (C.pullbackIso φ) u =
      R.occupationProbability (G := G) C (φ u) := by
  unfold occupationProbability
  rw [pullbackIso_rootedA_eq, pullbackIso_rootedP_eq]

@[simp] theorem pullbackIso_vacancyProbability_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).vacancyProbability (G := H) (C.pullbackIso φ) u =
      R.vacancyProbability (G := G) C (φ u) := by
  unfold vacancyProbability
  rw [pullbackIso_rootedQ_eq, pullbackIso_rootedP_eq]

@[simp] theorem pullbackIso_conditionalMeanDifference_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).conditionalMeanDifference (G := H) (C.pullbackIso φ) u =
      R.conditionalMeanDifference (G := G) C (φ u) := by
  unfold conditionalMeanDifference occupiedMean vacantMean
  simp only [CanonicalFirstRecoveryState.pullbackIso]
  have hv := hardCoreLaw_mean_iso_aux
    (deleteVertexIsoOf (subtreeIso φ R u)
      ((R.pullbackIso φ).subtreeRoot (G := H) u)) C.activity C.activity_pos
  have ho := hardCoreLaw_mean_iso_aux
    (deleteClosedNeighborhoodIsoOf (subtreeIso φ R u)
      ((R.pullbackIso φ).subtreeRoot (G := H) u)) C.activity C.activity_pos
  rw [hv, ho]
  rw [subtreeIso_subtreeRoot]

end ComponentRooting
end ActualRootedVariance
end
end Erdos993

namespace Erdos993
noncomputable section
universe u v
open Forest

namespace Forest.CanonicalFirstRecoveryState

@[simp] theorem pullbackIso_variance_eq
    {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B} (φ : H ≃g G)
    (C : CanonicalFirstRecoveryState G) :
    (C.pullbackIso φ).variance = C.variance := by
  unfold variance law pullbackIso
  exact hardCoreLaw_variance_iso_aux φ C.activity C.activity_pos

end Forest.CanonicalFirstRecoveryState

namespace ActualRootedVariance.ComponentRooting

noncomputable local instance finiteSubtypeParent {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

variable {A : Type u} {B : Type v} [Fintype A] [Fintype B]
    {H : SimpleGraph A} {G : SimpleGraph B}

private theorem pullbackIso_nonroot
    (φ : H ≃g G) (R : ComponentRooting G) {u : A}
    (hu : u ≠ (R.pullbackIso φ).rootOf (G := H) u) :
    φ u ≠ R.rootOf (G := G) (φ u) := by
  intro h
  apply hu
  rw [pullbackIso_rootOf]
  apply φ.injective
  simpa using h

private theorem pullbackIso_selectedParent_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) {u : A}
    (hu : u ≠ (R.pullbackIso φ).rootOf (G := H) u) :
    φ ((R.pullbackIso φ).selectedParent (G := H) u hu) =
      R.selectedParent (G := G) (φ u) (pullbackIso_nonroot φ R hu) := by
  symm
  apply R.selectedParent_eq_of_isChild (G := G) C
  · exact (pullbackIso_isChild_iff φ R _ _).mp
      ((R.pullbackIso φ).selectedParent_isChild (G := H) u hu)

@[simp] theorem pullbackIso_parentAbsentProbability_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).parentAbsentProbability (G := H) (C.pullbackIso φ) u =
      R.parentAbsentProbability (G := G) C (φ u) := by
  by_cases hu : u = (R.pullbackIso φ).rootOf (G := H) u
  · have hφu : φ u = R.rootOf (G := G) (φ u) := by
      have h := congrArg φ hu
      simpa [pullbackIso_rootOf] using h
    rw [parentAbsentProbability, dif_pos hu,
      parentAbsentProbability, dif_pos hφu]
  · have hφu := pullbackIso_nonroot φ R hu
    rw [(R.pullbackIso φ).parentAbsentProbability_eq_deleteVertex_ratio
      (G := H) (C.pullbackIso φ) hu,
      R.parentAbsentProbability_eq_deleteVertex_ratio (G := G) C hφu]
    simp only [CanonicalFirstRecoveryState.pullbackIso]
    rw [independenceEval_iso_aux
      (deleteVertexIsoOf φ ((R.pullbackIso φ).selectedParent (G := H) u hu)) C.activity,
      independenceEval_iso_aux φ C.activity,
      pullbackIso_selectedParent_eq φ C R hu]

@[simp] theorem pullbackIso_vertexVarianceContribution_eq
    (φ : H ≃g G) (C : CanonicalFirstRecoveryState G)
    (R : ComponentRooting G) (u : A) :
    (R.pullbackIso φ).vertexVarianceContribution (G := H) (C.pullbackIso φ) u =
      R.vertexVarianceContribution (G := G) C (φ u) := by
  unfold vertexVarianceContribution
  rw [pullbackIso_parentAbsentProbability_eq,
    pullbackIso_occupationProbability_eq,
    pullbackIso_vacancyProbability_eq,
    pullbackIso_conditionalMeanDifference_eq]

end ActualRootedVariance.ComponentRooting
end
end Erdos993

namespace Erdos993.Forest
open Erdos993.ActualRootedVariance
open CanonicalCompactnessWrapper
open CanonicalCompactnessWrapper.CanonicalSequence
open Filter
noncomputable section
universe u v

/-- Sequential uniformization first proved for `Fin`-indexed forests. -/
theorem appendixD_uniform_fin_D1 :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ {n : ℕ} {G : SimpleGraph (Fin n)}
        (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G),
        C.activity < 27 → T ≤ C.variance →
        ∃ v, κ * C.variance ≤ R.vertexVarianceContribution (G := G) C v := by
  by_contra h
  push Not at h
  have hcounter : ∀ j : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n))
        (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G),
      C.activity < 27 ∧
      ((j : ℝ) + 1) ≤ C.variance ∧
      ∀ v : Fin n, R.vertexVarianceContribution (G := G) C v <
        (1 / ((j : ℝ) + 1)) * C.variance := by
    intro j
    exact h (1 / ((j : ℝ) + 1)) (by positivity)
      ((j : ℝ) + 1) (by positivity)
  choose N G C R hz hV hsmall using hcounter
  let S : CanonicalSequence := {
    order := N
    graph := G
    state := C
    activity_lt := hz
    variance_pos := fun j => lt_of_lt_of_le (by positivity) (hV j)
    variance_tendsto := by
      apply Filter.tendsto_atTop_mono (fun j => hV j)
      refine Filter.tendsto_atTop_mono'
        (f₁ := fun j : ℕ => (j : ℝ))
        (f₂ := fun j : ℕ => (j : ℝ) + 1) atTop
        (Eventually.of_forall fun j : ℕ => ?_) ?_
      · norm_num
      · exact (tendsto_natCast_atTop_atTop :
          Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop)
  }
  have hmax (j : ℕ) :
      (R j).maxVertexVarianceContribution (G := G j) (C j) <
        (1 / ((j : ℝ) + 1)) * (C j).variance := by
    have hne : (Finset.univ : Finset (Fin (N j))).Nonempty := by
      by_contra hempty
      have hp := (R j).maxVertexVarianceContribution_pos (G := G j) (C j)
      rw [ComponentRooting.maxVertexVarianceContribution, dif_neg hempty] at hp
      exact (lt_irrefl 0) hp
    rw [ComponentRooting.maxVertexVarianceContribution, dif_pos hne,
      Finset.max'_lt_iff]
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨v, hv, rfl⟩
    exact hsmall j v
  have hratio : Tendsto (fun j =>
      (R j).maxVertexVarianceContribution (G := S.graph j) (S.state j) /
        S.V j) atTop (𝓝 0) := by
    refine squeeze_zero
      (f := fun j =>
        (R j).maxVertexVarianceContribution (G := S.graph j) (S.state j) /
          S.V j)
      (g := fun j : ℕ => 1 / ((j : ℝ) + 1)) ?_ ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    · intro j
      exact div_nonneg (le_of_lt ((R j).maxVertexVarianceContribution_pos
        (G := G j) (C j))) (le_of_lt (S.variance_pos j))
    · intro j
      change (R j).maxVertexVarianceContribution (G := G j) (C j) /
          (C j).variance ≤ 1 / ((j : ℝ) + 1)
      rw [div_le_iff₀ (S.variance_pos j)]
      exact le_of_lt (hmax j)
  exact (feller_failure_D8 S R) hratio

/-- Appendix D.1 for arbitrary finite vertex types, obtained by genuine graph
isomorphism transport to `Fin (Fintype.card V)`. -/
theorem appendixD_uniform_finite_D1 :
    ∃ κ : ℝ, 0 < κ ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
        (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G),
        C.activity < 27 → T ≤ C.variance →
        ∃ v, κ * C.variance ≤ R.vertexVarianceContribution (G := G) C v := by
  obtain ⟨κ, hκ, T, hT, hfin⟩ := appendixD_uniform_fin_D1
  refine ⟨κ, hκ, T, hT, ?_⟩
  intro V inst G C R hactivity hvariance
  let e : Fin (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
  let H : SimpleGraph (Fin (Fintype.card V)) := G.comap e.toEmbedding
  let φ : H ≃g G := SimpleGraph.Iso.comap e G
  let C' : CanonicalFirstRecoveryState H := C.pullbackIso φ
  let R' : ComponentRooting H := R.pullbackIso φ
  have hactivity' : C'.activity < 27 := by simpa [C', CanonicalFirstRecoveryState.pullbackIso]
  have hvariance' : T ≤ C'.variance := by
    simpa [C'] using hvariance
  obtain ⟨v, hv⟩ := hfin C' R' hactivity' hvariance'
  refine ⟨φ v, ?_⟩
  simpa [C', R'] using hv

end
end Erdos993.Forest

namespace Erdos993.Forest
open Erdos993.ActualRootedVariance
noncomputable section
universe u v

/-- Theorem D.1 packaged for the compiled family of genuine componentwise
rootings. -/
noncomputable def actualMacroscopicContributionInterface :
    MacroscopicContributionInterface actualRootedForestFamily.{u} := by
  let h := appendixD_uniform_finite_D1.{u}
  let κ : ℝ := Classical.choose h
  have hκ := Classical.choose_spec h
  let T : ℝ := Classical.choose hκ.2
  have hT := Classical.choose_spec hκ.2
  refine
    { kappa27 := κ
      varianceThreshold27 := T
      kappa27_pos := hκ.1
      varianceThreshold27_nonneg := hT.1
      conclusion := ?_ }
  intro V inst G C R hactivity hvariance
  obtain ⟨v, hv⟩ := hT.2 C R hactivity hvariance
  refine ⟨v, ?_⟩
  simpa [κ, actualRootedForestFamily,
    ComponentRooting.observables, RootedForestObservables.contribution,
    ComponentRooting.vertexVarianceContribution,
    ComponentRooting.vacancyProbability_eq_one_sub_occupationProbability] using hv

end
end Erdos993.Forest
