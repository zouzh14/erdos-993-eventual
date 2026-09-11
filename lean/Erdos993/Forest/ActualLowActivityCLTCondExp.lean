import Erdos993.Forest.ActualLowActivityCLT

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos993.Forest.ActualLowActivityCLT

open Erdos993.ActualRootedVariance
open Erdos993.ActualMartingaleProjection
open Erdos993.UniformFourthMoment
open Erdos993.Forest.MartingaleArrayCLT

universe u

noncomputable local instance arrayClassicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

variable (Vseq : ℕ → Type u) [∀ n, Fintype (Vseq n)]
variable (Gseq : (n : ℕ) → SimpleGraph (Vseq n))
variable (hGseq : ∀ n, (Gseq n).IsAcyclic)
variable (zseq : ℕ → ℝ) (hzseq : ∀ n, 0 < zseq n)
variable (Rseq : (n : ℕ) → ComponentRooting (Gseq n))

abbrev ActualSeedSpace (n : ℕ) := BernoulliAssignment (Vseq n)

noncomputable instance actualArraySeedMeasurableSpace (n : ℕ) :
    MeasurableSpace (ActualSeedSpace Vseq n) := ⊤

noncomputable def actualSeedMeasure (n : ℕ) : Measure (ActualSeedSpace Vseq n) :=
  (hardCoreBernoulliSeedLaw (Rseq n) (zseq n) (hzseq n)).toMeasure

noncomputable def prefixProjection (n k : ℕ) (ω : ActualSeedSpace Vseq n) :
    ActualSeedSpace Vseq n := fun v =>
  if ((parentFirstEquiv (Rseq n)).symm v).val < k then ω v else false

noncomputable def actualPrefixMeasurableSpace (n k : ℕ) :
    MeasurableSpace (ActualSeedSpace Vseq n) :=
  MeasurableSpace.comap (prefixProjection Vseq Gseq Rseq n k) ⊤

lemma actualPrefixMeasurableSpace_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    actualPrefixMeasurableSpace Vseq Gseq Rseq n i ≤
      actualPrefixMeasurableSpace Vseq Gseq Rseq n j := by
  intro s hs
  rcases hs with ⟨t, -, rfl⟩
  refine ⟨(prefixProjection Vseq Gseq Rseq n i) ⁻¹' t, Set.mem_univ _, ?_⟩
  ext ω
  have hproj : prefixProjection Vseq Gseq Rseq n i
      (prefixProjection Vseq Gseq Rseq n j ω) =
      prefixProjection Vseq Gseq Rseq n i ω := by
    funext v
    dsimp [prefixProjection]
    by_cases hi : ((parentFirstEquiv (Rseq n)).symm v).val < i
    · have hj : ((parentFirstEquiv (Rseq n)).symm v).val < j := lt_of_lt_of_le hi hij
      simp [hi, hj]
    · simp [hi]
  simp only [Set.mem_preimage]
  rw [hproj]

noncomputable def actualPrefixFiltration (n : ℕ) :
    Filtration ℕ (actualArraySeedMeasurableSpace Vseq n) where
  seq k := actualPrefixMeasurableSpace Vseq Gseq Rseq n k
  mono' _ _ h := actualPrefixMeasurableSpace_mono Vseq Gseq Rseq n h
  le' k := by
    intro s hs
    exact Set.mem_univ _

lemma samePrefix_iff_prefixProjection_eq
    (n : ℕ) (k : Fin (Fintype.card (Vseq n) + 1))
    (ω η : ActualSeedSpace Vseq n) :
    samePrefix (parentFirstEquiv (Rseq n)) k ω η ↔
      prefixProjection Vseq Gseq Rseq n k.val ω =
        prefixProjection Vseq Gseq Rseq n k.val η := by
  constructor
  · intro h
    funext v
    let i : Fin (Fintype.card (Vseq n)) := (parentFirstEquiv (Rseq n)).symm v
    have he : parentFirstEquiv (Rseq n) i = v := by simp [i]
    dsimp [prefixProjection]
    by_cases hi : i.val < k.val
    · rw [if_pos hi, if_pos hi]
      simpa [he] using h ⟨i, hi⟩
    · rw [if_neg hi, if_neg hi]
  · intro h i
    have hv := congrFun h (parentFirstEquiv (Rseq n) ⟨i, by omega⟩)
    dsimp [prefixProjection] at hv
    simpa using hv

section CondExpBridge

variable {V : Type u} [Fintype V]

noncomputable def oneRowPrefixProjection
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) : BernoulliAssignment V := fun v =>
  if (e.symm v).val < k.val then ω v else false

noncomputable def oneRowPrefixSpace
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) :
    MeasurableSpace (BernoulliAssignment V) :=
  MeasurableSpace.comap (oneRowPrefixProjection e k) ⊤

/-- The prefix comap spaces form the increasing filtration obtained by exposing
coordinates in the order `e`. -/
theorem oneRowPrefixSpace_mono
    (e : Fin (Fintype.card V) ≃ V)
    {k l : Fin (Fintype.card V + 1)} (hkl : k ≤ l) :
    oneRowPrefixSpace e k ≤ oneRowPrefixSpace e l := by
  have hmask : @Measurable (BernoulliAssignment V) (BernoulliAssignment V)
      ⊤ ⊤ (oneRowPrefixProjection e k) := by
    rw [measurable_iff_comap_le]
    exact le_top
  have hproj :
      @Measurable (BernoulliAssignment V) (BernoulliAssignment V)
        (oneRowPrefixSpace e l) ⊤ (oneRowPrefixProjection e l) := by
    rw [measurable_iff_comap_le]
    change oneRowPrefixSpace e l ≤ oneRowPrefixSpace e l
    exact le_rfl
  have hcomp := hmask.comp hproj
  rw [measurable_iff_comap_le] at hcomp
  have hprojcomp :
      oneRowPrefixProjection e k ∘ oneRowPrefixProjection e l =
        oneRowPrefixProjection e k := by
    funext ω v
    by_cases hv : (e.symm v).1 < k.1
    · simp [oneRowPrefixProjection, hv, lt_of_lt_of_le hv hkl]
    · simp [oneRowPrefixProjection, hv]
  simpa only [oneRowPrefixSpace, hprojcomp] using hcomp

lemma oneRow_samePrefix_iff_prefixProjection_eq
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1))
    (ω η : BernoulliAssignment V) :
    samePrefix e k ω η ↔
      oneRowPrefixProjection e k ω = oneRowPrefixProjection e k η := by
  constructor
  · intro h
    funext v
    let i : Fin (Fintype.card V) := e.symm v
    have he : e i = v := by simp [i]
    dsimp [oneRowPrefixProjection]
    by_cases hi : i.val < k.val
    · rw [if_pos hi, if_pos hi]
      simpa [he] using h ⟨i, hi⟩
    · rw [if_neg hi, if_neg hi]
  · intro h i
    have hv := congrFun h (e ⟨i, by omega⟩)
    dsimp [oneRowPrefixProjection] at hv
    simpa using hv

lemma finiteDoobMean_prefixProjection
    (p : BernoulliAssignment V → ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1))
    (ω : BernoulliAssignment V) :
    finiteDoobMean p f e k (oneRowPrefixProjection e k ω) =
      finiteDoobMean p f e k ω := by
  apply finiteDoobMean_eq_of_samePrefix
  intro i
  dsimp [oneRowPrefixProjection]
  simp [i.2]

lemma finiteDoobMean_stronglyMeasurable_prefix
    (p : BernoulliAssignment V → ℝ) (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) :
    @StronglyMeasurable (BernoulliAssignment V) ℝ inferInstance
      (oneRowPrefixSpace e k) (finiteDoobMean p f e k) := by
  letI : MeasurableSpace (BernoulliAssignment V) := ⊤
  letI : MeasurableSpace (BernoulliAssignment V) := oneRowPrefixSpace e k
  have htop : @StronglyMeasurable (BernoulliAssignment V) ℝ inferInstance ⊤
      (finiteDoobMean p f e k) :=
    measurable_from_top.stronglyMeasurable
  have hproj : @Measurable (BernoulliAssignment V) (BernoulliAssignment V)
      (oneRowPrefixSpace e k) ⊤ (oneRowPrefixProjection e k) := by
    rw [measurable_iff_comap_le]
    change oneRowPrefixSpace e k ≤ oneRowPrefixSpace e k
    exact le_rfl
  have hcomp := htop.comp_measurable hproj
  have heq : finiteDoobMean p f e k ∘ oneRowPrefixProjection e k =
      finiteDoobMean p f e k := by
    funext ω
    exact finiteDoobMean_prefixProjection p f e k ω
  rw [heq] at hcomp
  exact hcomp

lemma finiteDoobMean_integral_identity
    (p : BernoulliAssignment V → ℝ) (hp : ∀ ω, 0 ≤ p ω)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) :
    ∑ ω, p ω * finiteDoobMean p f e k ω = ∑ ω, p ω * f ω := by
  classical
  let q : BernoulliAssignment V → BernoulliAssignment V := oneRowPrefixProjection e k
  have hfiber (a : BernoulliAssignment V) :
      (∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with q ω = a,
          p ω * finiteDoobMean p f e k ω) =
        ∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with q ω = a,
          p ω * f ω := by
    let D : ℝ := ∑ ω, if q ω = a then p ω else 0
    let N : ℝ := ∑ ω, if q ω = a then p ω * f ω else 0
    by_cases hD : D = 0
    · have hzero : ∀ ω, q ω = a → p ω = 0 := by
        intro ω hq
        have hle : p ω ≤ D := by
          dsimp [D]
          calc
            p ω = if q ω = a then p ω else 0 := by simp [hq]
            _ ≤ ∑ η, if q η = a then p η else 0 := by
              refine Finset.single_le_sum
                (f := fun η => if q η = a then p η else 0) ?_
                (Finset.mem_univ ω)
              intro η hη
              by_cases hqa : q η = a <;> simp [hqa, hp η]
        rw [hD] at hle
        exact le_antisymm hle (hp ω)
      apply Finset.sum_congr rfl
      intro ω hω
      have hq := (Finset.mem_filter.mp hω).2
      rw [hzero ω hq]
      ring
    · have hmean : ∀ ω, q ω = a → finiteDoobMean p f e k ω = N / D := by
        intro ω hq
        have hweighted : prefixWeighted p f e k ω = N := by
          unfold prefixWeighted
          apply Finset.sum_congr rfl
          intro η hη
          rw [oneRow_samePrefix_iff_prefixProjection_eq]
          by_cases hqa : oneRowPrefixProjection e k η = a
          · have heq : oneRowPrefixProjection e k ω =
                oneRowPrefixProjection e k η := by
              simpa [q] using hq.trans hqa.symm
            simp [heq, hqa, N, q]
          · have hne : oneRowPrefixProjection e k ω ≠
                oneRowPrefixProjection e k η := by
              intro heq
              apply hqa
              simpa [q] using (hq.symm.trans heq).symm
            simp [hne, hqa, N, q]
        have hpref : prefixMass p e k ω = D := by
          unfold prefixMass
          apply Finset.sum_congr rfl
          intro η hη
          rw [oneRow_samePrefix_iff_prefixProjection_eq]
          by_cases hqa : oneRowPrefixProjection e k η = a
          · have heq : oneRowPrefixProjection e k ω =
                oneRowPrefixProjection e k η := by
              simpa [q] using hq.trans hqa.symm
            simp [heq, hqa, D, q]
          · have hne : oneRowPrefixProjection e k ω ≠
                oneRowPrefixProjection e k η := by
              intro heq
              apply hqa
              simpa [q] using (hq.symm.trans heq).symm
            simp [hne, hqa, D, q]
        rw [finiteDoobMean, dif_neg]
        · rw [hweighted, hpref]
        · rw [hpref]
          exact hD
      rw [Finset.sum_filter, Finset.sum_filter]
      calc
        (∑ ω, if q ω = a then p ω * finiteDoobMean p f e k ω else 0) =
            ∑ ω, if q ω = a then p ω * (N / D) else 0 := by
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hq : q ω = a
          · simp [hq, hmean ω hq]
          · simp [hq]
        _ = D * (N / D) := by
          dsimp [D]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro ω hω
          by_cases hq : q ω = a <;> simp [hq] <;> ring
        _ = N := by field_simp
        _ = ∑ ω, if q ω = a then p ω * f ω else 0 := rfl
  have hleft := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (BernoulliAssignment V)))
    (g := q) (f := fun ω => p ω * finiteDoobMean p f e k ω)
  have hright := Finset.sum_fiberwise
    (s := (Finset.univ : Finset (BernoulliAssignment V)))
    (g := q) (f := fun ω => p ω * f ω)
  calc
    (∑ ω, p ω * finiteDoobMean p f e k ω) =
        ∑ a, ∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with q ω = a,
          p ω * finiteDoobMean p f e k ω := hleft.symm
    _ = ∑ a, ∑ ω ∈ (Finset.univ : Finset (BernoulliAssignment V)) with q ω = a,
          p ω * f ω := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hfiber a
    _ = ∑ ω, p ω * f ω := hright

end CondExpBridge

end Erdos993.Forest.ActualLowActivityCLT

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos993.Forest.ActualLowActivityCLT

open Erdos993.UniformFourthMoment

universe u

noncomputable local instance condExpClassicalDecidableEq (α : Type*) : DecidableEq α :=
  Classical.decEq α

section GenericCondExp

variable {V : Type u} [Fintype V]
local instance topBernoulliMeasurableSpace : MeasurableSpace (BernoulliAssignment V) := ⊤

lemma finiteDoobMean_integral_toMeasure_identity
    (L : FiniteLatticeLaw (BernoulliAssignment V))
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) :
    ∫ ω, finiteDoobMean L.probability f e k ω ∂L.toMeasure =
      ∫ ω, f ω ∂L.toMeasure := by
  rw [L.integral_toMeasure_eq_sum, L.integral_toMeasure_eq_sum]
  exact finiteDoobMean_integral_identity L.probability L.probability_nonneg f e k

lemma finiteDoobMean_eq_condExp
    (L : FiniteLatticeLaw (BernoulliAssignment V))
    (hp : ∀ ω, 0 < L.probability ω)
    (f : BernoulliAssignment V → ℝ)
    (e : Fin (Fintype.card V) ≃ V) (k : Fin (Fintype.card V + 1)) :
    L.toMeasure[f | oneRowPrefixSpace e k] =ᵐ[L.toMeasure]
      finiteDoobMean L.probability f e k := by
  have hm : oneRowPrefixSpace e k ≤
      (topBernoulliMeasurableSpace : MeasurableSpace (BernoulliAssignment V)) := by
    exact le_top
  have hfint : Integrable f L.toMeasure := Integrable.of_finite
  have hgstrong : @StronglyMeasurable (BernoulliAssignment V) ℝ inferInstance
      (oneRowPrefixSpace e k) (finiteDoobMean L.probability f e k) :=
    finiteDoobMean_stronglyMeasurable_prefix L.probability f e k
  have hgint : Integrable (finiteDoobMean L.probability f e k) L.toMeasure :=
    Integrable.of_finite
  have hchar := ae_eq_condExp_of_forall_setIntegral_eq hm hfint
    (fun s hs hfin => hgint.integrableOn)
    (fun s hs hfin => by
      have hsrep : ∃ t : Set (BernoulliAssignment V),
          s = oneRowPrefixProjection e k ⁻¹' t := by
        rcases (MeasurableSpace.measurableSet_comap.mp hs) with ⟨t, ht, hts⟩
        exact ⟨t, hts.symm⟩
      rcases hsrep with ⟨t, rfl⟩
      let q := oneRowPrefixProjection e k
      let h : BernoulliAssignment V → ℝ :=
        (q ⁻¹' t).indicator (fun _ => (1 : ℝ))
      have hhprefix : ∀ ω η, samePrefix e k ω η → h η = h ω := by
        intro ω η hpre
        have hqeq := (oneRow_samePrefix_iff_prefixProjection_eq e k ω η).mp hpre
        dsimp [h, q]
        by_cases hmem : oneRowPrefixProjection e k ω ∈ t
        · have hmem' : oneRowPrefixProjection e k η ∈ t := by simpa [hqeq] using hmem
          simp [hmem, hmem']
        · have hmem' : oneRowPrefixProjection e k η ∉ t := by simpa [hqeq] using hmem
          simp [hmem, hmem']
      have hmeanMul : ∀ ω,
          finiteDoobMean L.probability (fun η => h η * f η) e k ω =
            h ω * finiteDoobMean L.probability f e k ω := by
        intro ω
        exact finiteDoobMean_measurable_mul L.probability hp h f e k ω
          (fun η hpre => hhprefix ω η hpre)
      have hs_top : @MeasurableSet (BernoulliAssignment V)
          (topBernoulliMeasurableSpace : MeasurableSpace (BernoulliAssignment V))
          (oneRowPrefixProjection e k ⁻¹' t) := hm _ hs
      rw [← integral_indicator hs_top]
      rw [← integral_indicator hs_top]
      have hglobal := finiteDoobMean_integral_toMeasure_identity L
        (fun η => h η * f η) e k
      calc
        (∫ x, (q ⁻¹' t).indicator (finiteDoobMean L.probability f e k) x ∂L.toMeasure) =
            ∫ x, finiteDoobMean L.probability (fun η => h η * f η) e k x
              ∂L.toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [hmeanMul x]
          dsimp [h]
          by_cases hx : x ∈ q ⁻¹' t <;> simp [hx]
        _ = ∫ x, h x * f x ∂L.toMeasure := hglobal
        _ = ∫ x, (q ⁻¹' t).indicator f x ∂L.toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with x
          dsimp [h]
          by_cases hx : x ∈ q ⁻¹' t <;> simp [hx])
    hgstrong.aestronglyMeasurable
  exact hchar.symm

end GenericCondExp

end Erdos993.Forest.ActualLowActivityCLT
