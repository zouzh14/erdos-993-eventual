import Erdos993.Forest.AddabilityAndHighActivityFinitePackage
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Finite probability at the mean

This module begins the C.50 adapter with a proved finite Bernoulli lower-tail bound.
The product measure below is literal and its coordinate independence and Hoeffding bound are
supplied by proved Mathlib declarations.  No concentration inequality is assumed.
-/

open MeasureTheory Measure unitInterval
open scoped ENNReal NNReal ProbabilityTheory unitInterval BigOperators

namespace Erdos993.Forest.ProbabilityAtMean

noncomputable section

noncomputable local instance finiteSubtype {α : Type*} [Fintype α] (p : α → Prop) :
    Fintype {x // p x} := Fintype.ofInjective Subtype.val Subtype.val_injective

variable {ι : Type*}

noncomputable def boolMeasure (p : I) : Measure Bool :=
  toNNReal p • Measure.dirac true + toNNReal (σ p) • Measure.dirac false

instance (p : I) : IsProbabilityMeasure (boolMeasure p) := by
  rw [boolMeasure]
  infer_instance

noncomputable def productMeasure {ι : Type*} (p : I) : Measure (ι → Bool) :=
  Measure.infinitePi (fun _ : ι => boolMeasure p)

instance {ι : Type*} (p : I) : IsProbabilityMeasure (productMeasure (ι := ι) p) := by
  rw [productMeasure]
  infer_instance

noncomputable def lowerCentered {ι : Type*} (p : I) (i : ι) (ω : ι → Bool) : ℝ :=
  (p : ℝ) - if ω i then 1 else 0

lemma lowerCentered_integral [Fintype ι] (p : I) (i : ι) :
    ∫ ω, lowerCentered p i ω ∂productMeasure p = 0 := by
  have hmap : Measure.map (fun ω : ι → Bool => ω i) (productMeasure p) = boolMeasure p := by
    rw [productMeasure, infinitePi_map_eval]
  have h_int := MeasureTheory.integral_map
    (μ := productMeasure p) (φ := fun ω : ι → Bool => ω i)
    (f := fun b : Bool => (p : ℝ) - if b then 1 else 0)
    (measurable_pi_apply i).aemeasurable (by fun_prop)
  rw [hmap] at h_int
  change (∫ ω, ((p : ℝ) - if ω i then 1 else 0) ∂productMeasure p) = 0
  rw [← h_int]
  simp [boolMeasure, integral_add_measure]
  change (p : ℝ) * ((p : ℝ) - 1) + (1 - (p : ℝ)) * (p : ℝ) = 0
  ring

lemma lowerCentered_subgaussian [Fintype ι] (p : I) (i : ι) :
    ProbabilityTheory.HasSubgaussianMGF (lowerCentered p i) (1 / 4 : ℝ≥0)
      (productMeasure p) := by
  have h : ProbabilityTheory.HasSubgaussianMGF (lowerCentered p i)
      ((‖(p : ℝ) - ((p : ℝ) - 1)‖₊ / 2) ^ 2) (productMeasure p) := by
    apply ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
        (X := lowerCentered p i) (a := (p : ℝ) - 1) (b := p)
    · change AEMeasurable (fun ω : ι → Bool =>
          (p : ℝ) - if ω i then 1 else 0) (productMeasure p)
      exact Measurable.aemeasurable (by fun_prop)
    · filter_upwards [] with ω
      simp only [lowerCentered]
      split <;> constructor <;> norm_num
    · exact lowerCentered_integral p i
  have heq : ((‖(p : ℝ) - ((p : ℝ) - 1)‖₊ / 2) ^ 2) = (1 / 4 : ℝ≥0) := by
    ext
    norm_num
  rwa [heq] at h

/-- Finite Bernoulli lower-tail inequality in the exact C.50 normalization before cancelling 4. -/
lemma finiteBernoulli_lowerTail [Fintype ι] (p : I) {d : ℝ} (hd : 0 ≤ d) :
    (productMeasure p).real {ω : ι → Bool |
      d ≤ ∑ i, lowerCentered p i ω} ≤
        Real.exp (-d ^ 2 / (2 * ((Fintype.card ι : ℝ) * (4 : ℝ)⁻¹))) := by
  have hi : ProbabilityTheory.iIndepFun (fun i : ι => lowerCentered p i) (productMeasure p) := by
    rw [productMeasure]
    exact ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ι => boolMeasure p)
      (X := fun i b => (p : ℝ) - if b then 1 else 0) (by fun_prop)
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    hi (s := Finset.univ) (c := fun _ => (1 / 4 : ℝ≥0))
      (fun i _ => lowerCentered_subgaussian p i) hd
  simpa [Finset.sum_const_zero, nsmul_eq_mul] using h

/-- The reusable nonempty finite Bernoulli bound `exp (-2*d^2/a)` needed by C.50. -/
lemma C50_finiteBernoulli_lowerTail [Fintype ι] [Nonempty ι] (p : I) {d : ℝ} (hd : 0 ≤ d) :
    (productMeasure p).real {ω : ι → Bool |
      d ≤ ∑ i, lowerCentered p i ω} ≤
        Real.exp (-2 * d ^ 2 / (Fintype.card ι : ℝ)) := by
  have h := finiteBernoulli_lowerTail (ι := ι) p hd
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have heq :
      -d ^ 2 / (2 * ((Fintype.card ι : ℝ) * (4 : ℝ)⁻¹)) =
        -2 * d ^ 2 / (Fintype.card ι : ℝ) := by
    field_simp
    ring
  rw [← heq]
  exact h

/-- Exact atomic mass of the literal finite Boolean product measure. -/
lemma productMeasure_singleton_real [Fintype ι] (p : I) (ω : ι → Bool) :
    (productMeasure p).real {ω} =
      ∏ i, if ω i then (p : ℝ) else 1 - (p : ℝ) := by
  change ((productMeasure p) {ω}).toReal = _
  rw [productMeasure, Measure.infinitePi_singleton, tprod_fintype]
  simp only [boolMeasure]
  rw [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases h : ω i <;>
    simp [ENNReal.smul_def, h, ENNReal.toReal_add, ENNReal.coe_toReal]

private lemma finset_prod_bool (s : Finset ι) (p q : ℝ) (ω : ι → Bool) :
    (∏ i ∈ s, if ω i then p else q) =
      p ^ (s.filter fun i => ω i = true).card *
        q ^ (s.filter fun i => ω i = false).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      cases h : ω a <;>
        simp [Finset.filter_insert, ha, h, ih, pow_succ] <;> ring

private lemma fintype_prod_bool [Fintype ι] (p : ℝ) (ω : ι → Bool) :
    (∏ i, if ω i then p else 1 - p) =
      p ^ (Finset.univ.filter fun i => ω i).card *
        (1 - p) ^ (Fintype.card ι - (Finset.univ.filter fun i => ω i).card) := by
  classical
  have hfalse :
      (Finset.univ.filter fun i : ι => ω i = false).card =
        Fintype.card ι - (Finset.univ.filter fun i : ι => ω i = true).card := by
    rw [← Finset.card_compl]
    congr 1
    ext i
    cases h : ω i <;> simp [h]
  rw [finset_prod_bool, hfalse]

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {P : FiniteBipartition G} {c : BipartitionSide}

noncomputable local instance colorEnvironmentFintype
    (P : FiniteBipartition G) (c : BipartitionSide) :
    Fintype (ColorEnvironment P c) :=
  Fintype.ofInjective (fun E : ColorEnvironment P c => E.occupied) (by
    intro E₁ E₂ h
    cases E₁ with
    | mk o₁ h₁ =>
      cases E₂ with
      | mk o₂ h₂ =>
        cases h
        rfl)

/-- A representative of the global configuration for an exact conditioned environment. -/
noncomputable def restrictionConditionedGlobalState
    (P : FiniteBipartition G) (c : BipartitionSide) (s : IndepFinset G) :
    (restrictionEnvironment (G := G) P c s).ConditionedGlobalState := by
  refine ⟨s, ?_⟩
  ext v
  simp [restrictionEnvironment]

/-- Restricting the extension of a fiber state recovers its environment. -/
lemma restrictionEnvironment_extension_eq'
    {P : FiniteBipartition G} (c : BipartitionSide)
    (E : ColorEnvironment P c) (t : E.FiberState) :
    restrictionEnvironment (G := G) P c (E.extension t) = E := by
  have hocc := E.extension_inter_side t
  cases E with
  | mk occ hsub =>
    simp only [restrictionEnvironment]
    congr

/-- A nondependent carrier for finite environment/fiber disintegration.  Its
second component is a raw Finset, while the subtype proof is recorded only in
this outer proposition.  This avoids any heterogeneous equality in finite sums. -/
noncomputable def ColorFiberData
    (P : FiniteBipartition G) (c : BipartitionSide) :=
  {q : ColorEnvironment P c × Finset V // q.2 ⊆ q.1.available}

noncomputable local instance colorFiberDataFintype
    (P : FiniteBipartition G) (c : BipartitionSide) : Fintype (ColorFiberData P c) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable def globalStateToFiberData
    (P : FiniteBipartition G) (c : BipartitionSide) (s : IndepFinset G) :
    ColorFiberData P c := by
  let E := restrictionEnvironment (G := G) P c s
  let hs := restrictionConditionedGlobalState (G := G) P c s
  let t := E.fiberStateOfConditionedGlobalState hs
  exact ⟨(E, t.1), t.2⟩

noncomputable def fiberDataToGlobal
    (P : FiniteBipartition G) (c : BipartitionSide) (q : ColorFiberData P c) :
    IndepFinset G :=
  q.1.1.extension ⟨q.1.2, q.2⟩

noncomputable def globalStateEquivFiberData
    (P : FiniteBipartition G) (c : BipartitionSide) :
    IndepFinset G ≃ ColorFiberData P c where
  toFun := globalStateToFiberData P c
  invFun := fiberDataToGlobal P c
  left_inv s := by
    let E := restrictionEnvironment (G := G) P c s
    let hs := restrictionConditionedGlobalState (G := G) P c s
    let t := E.fiberStateOfConditionedGlobalState hs
    have h := E.fiberStateEquivConditionedGlobalState.right_inv hs
    apply Subtype.ext
    dsimp [globalStateToFiberData, fiberDataToGlobal]
    have hu :
        (⟨(E.fiberStateOfConditionedGlobalState hs).1,
          (E.fiberStateOfConditionedGlobalState hs).2⟩ : E.FiberState) =
          E.fiberStateOfConditionedGlobalState hs := Subtype.ext rfl
    rw [hu]
    change (E.extension (E.fiberStateOfConditionedGlobalState hs)).val = s.val
    exact congrArg (fun x : E.ConditionedGlobalState => x.1.val) h
  right_inv q := by
    rcases q with ⟨⟨E, t⟩, ht⟩
    let t' : E.FiberState := ⟨t, ht⟩
    let R := restrictionEnvironment (G := G) P c (E.extension t')
    have hrest : R = E := by
      exact restrictionEnvironment_extension_eq' (G := G) c E t'
    have hraw :
        (R.fiberStateOfConditionedGlobalState
          (restrictionConditionedGlobalState (G := G) P c (E.extension t'))).1 = t := by
      ext v
      change v ∈ (E.extension t').val ∩ P.other c ↔ v ∈ t
      constructor
      · intro hv
        rcases Finset.mem_inter.mp hv with ⟨hvext, hvother⟩
        rcases Finset.mem_union.mp hvext with hvE | hvt
        · exact False.elim ((Finset.disjoint_left.mp
            (P.disjoint_side_other c)) (E.subset_side hvE) hvother)
        · exact hvt
      · intro hvt
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hvt,
          (E.mem_available v).mp (t'.2 hvt) |>.1⟩
    apply Subtype.ext
    dsimp [globalStateToFiberData, fiberDataToGlobal]
    exact Prod.ext hrest hraw

/-- The global finite sum can be grouped by the exact environment/fiber data. -/
lemma sum_global_eq_sum_fiberData
    (P : FiniteBipartition G) (c : BipartitionSide)
    (f : IndepFinset G → ℝ) :
    (∑ s : IndepFinset G, f s) =
      ∑ q : ColorFiberData P c, f (fiberDataToGlobal P c q) := by
  let e := globalStateEquivFiberData (G := G) P c
  refine Fintype.sum_equiv e (fun s => f s)
    (fun q => f (fiberDataToGlobal P c q)) ?_
  intro s
  exact congrArg f (e.left_inv s).symm

/-- Group the global finite sum by a genuine sigma type carrying an exact
environment and its finite fiber.  The raw finite-set carrier avoids
heterogeneous equality in later Bayes sums. -/
noncomputable def fiberDataEquivFiberSigma
    (P : FiniteBipartition G) (c : BipartitionSide) :
    ColorFiberData P c ≃ Σ E : ColorEnvironment P c, E.FiberState where
  toFun q := ⟨q.1.1, ⟨q.1.2, q.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    apply Sigma.ext rfl
    exact heq_of_eq (Subtype.ext rfl)

lemma sum_global_eq_sum_fiberSigma
    (P : FiniteBipartition G) (c : BipartitionSide)
    (f : IndepFinset G → ℝ) :
    (∑ s : IndepFinset G, f s) =
      ∑ E : ColorEnvironment P c, ∑ t : E.FiberState,
        f (fiberDataToGlobal P c ⟨(E, t.1), t.2⟩) := by
  let e := fiberDataEquivFiberSigma (G := G) P c
  calc
    (∑ s : IndepFinset G, f s) =
        ∑ q : ColorFiberData P c, f (fiberDataToGlobal P c q) :=
      sum_global_eq_sum_fiberData (G := G) P c f
    _ = ∑ r : (Σ E : ColorEnvironment P c, E.FiberState),
          f (fiberDataToGlobal P c (e.symm r)) := by
      simpa using (Fintype.sum_equiv e
        (fun q => f (fiberDataToGlobal P c q))
        (fun r => f (fiberDataToGlobal P c (e.symm r))) (by
          intro q
          exact congrArg (fun r => f (fiberDataToGlobal P c r)) (e.left_inv q)))
    _ = ∑ E : ColorEnvironment P c, ∑ t : E.FiberState,
        f (fiberDataToGlobal P c ⟨(E, t.1), t.2⟩) := by
      rw [Fintype.sum_sigma]
      rfl

/-- A pointwise residual is the centered deviation of the total count from
its exact conditional mean on the opposite color fiber. -/
lemma sideResidual_opposite_eq_rank_sub_conditionalMean
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    sideResidual (G := G) P c.opposite z s =
      (s.val.card : ℝ) -
        actualConditionalMean G P c z hz
          (restrictionEnvironment (G := G) P c s) := by
  rw [C41_actual_conditionalMean G P c z hz]
  rw [available_card_restrictionEnvironment (G := G) P c s]
  have hocc_c :
      (∑ v ∈ P.side c, occupiedIndicator (G := G) s v) =
        ((s.val ∩ P.side c).card : ℝ) := by
    simp [occupiedIndicator, Finset.inter_comm]
  have hocc_o :
      (∑ v ∈ P.other c, occupiedIndicator (G := G) s v) =
        ((s.val ∩ P.other c).card : ℝ) := by
    simp [occupiedIndicator, Finset.inter_comm]
  have hcard :
      (s.val ∩ P.side c).card + (s.val ∩ P.other c).card = s.val.card := by
    have hdis : Disjoint (s.val ∩ P.side c) (s.val ∩ P.other c) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      exact (Finset.disjoint_left.mp (P.disjoint_side_other c))
        (Finset.mem_inter.mp hv1).2 (Finset.mem_inter.mp hv2).2
    calc
      (s.val ∩ P.side c).card + (s.val ∩ P.other c).card =
          ((s.val ∩ P.side c) ∪ (s.val ∩ P.other c)).card :=
        (Finset.card_union_of_disjoint hdis).symm
      _ = (s.val ∩ (P.side c ∪ P.other c)).card := by
        rw [Finset.inter_union_distrib_left]
      _ = s.val.card := by rw [P.union_side_other]; simp
  have hoccE :
      (restrictionEnvironment (G := G) P c s).occupied.val.card =
        (s.val ∩ P.side c).card := by
    rfl
  unfold sideResidual vertexResidual
  rw [← P.other_eq_side_opposite c]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hcardR :
      ((s.val ∩ P.side c).card : ℝ) +
          ((s.val ∩ P.other c).card : ℝ) = (s.val.card : ℝ) := by
    exact_mod_cast hcard
  rw [hocc_o, hoccE]
  nlinarith [hcardR]

/-- Encode an inherited C.40 fiber subset by its Boolean membership coordinates. -/
def fiberStateToBool (E : ColorEnvironment P c) (t : E.FiberState) :
    (↥E.available → Bool) := fun i => decide (i.1 ∈ t.1)

/-- Decode Boolean coordinates on the finite available subtype to an inherited fiber state. -/
def boolToFiberState (E : ColorEnvironment P c) (ω : ↥E.available → Bool) :
    E.FiberState := by
  classical
  refine ⟨(Finset.univ.filter fun i : ↥E.available => ω i).map
    ⟨Subtype.val, Subtype.val_injective⟩, ?_⟩
  intro v hv
  rcases Finset.mem_map.mp hv with ⟨i, hi, rfl⟩
  exact i.2

/-- The exact finite coordinate equivalence behind the C.40 Bernoulli fiber. -/
def fiberStateEquivBool (E : ColorEnvironment P c) :
    E.FiberState ≃ (↥E.available → Bool) where
  toFun := fiberStateToBool E
  invFun := boolToFiberState E
  left_inv t := by
    apply Subtype.ext
    ext v
    constructor
    · intro hv
      change v ∈ ((Finset.univ.filter fun i : ↥E.available =>
        fiberStateToBool E t i).map ⟨Subtype.val, Subtype.val_injective⟩) at hv
      rcases Finset.mem_map.mp hv with ⟨i, hi, hiv⟩
      have hit : i.1 ∈ t.1 := by
        have := (Finset.mem_filter.mp hi).2
        simpa [fiberStateToBool] using this
      simpa [← hiv] using hit
    · intro hv
      change v ∈ ((Finset.univ.filter fun i : ↥E.available =>
        fiberStateToBool E t i).map ⟨Subtype.val, Subtype.val_injective⟩)
      apply Finset.mem_map.mpr
      refine ⟨⟨v, t.2 hv⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [fiberStateToBool, hv]⟩
  right_inv ω := by
    funext i
    cases h : ω i <;> simp [fiberStateToBool, boolToFiberState, h]

/-- A Boolean coordinate atom has exactly the inherited C.40 Bernoulli-subset weight. -/
lemma productMeasure_singleton_eq_fiberWeight
    (E : ColorEnvironment P c) (p : I) (ω : ↥E.available → Bool) :
    (productMeasure p).real {ω} =
      BernoulliSubset.weight E.available (boolToFiberState E ω).1 (p : ℝ) := by
  rw [productMeasure_singleton_real, BernoulliSubset.weight]
  have hcard : (boolToFiberState E ω).1.card =
      (Finset.univ.filter fun i : ↥E.available => ω i = true).card := by
    simp [boolToFiberState]
  rw [hcard]
  rw [← show Fintype.card ↥E.available = E.available.card by
    exact Fintype.card_coe _]
  exact fintype_prod_bool (ι := ↥E.available) (p : ℝ) ω

/-- C.40 rewritten on the explicit Boolean-coordinate model; this remains the literal
normalized global hard-core conditional probability, not an abstract replacement law. -/
theorem C40_actual_conditional_probability_bool
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c)
    (ω : ↥E.available → Bool) :
    actualConditionalProbability G P c z hz E (boolToFiberState E ω) =
      BernoulliSubset.weight E.available (boolToFiberState E ω).1 (hardCoreTheta z) := by
  exact C40_actual_conditional_probability G P c z hz E (boolToFiberState E ω)

/-- The unchanged hard-core Bernoulli parameter, bundled in the unit interval. -/
noncomputable def hardCoreThetaUnit (z : ℝ) (hz : 0 < z) : I :=
  ⟨hardCoreTheta z, by
    constructor
    · exact div_nonneg hz.le (by linarith)
    · apply (div_le_one (by linarith)).2
      linarith⟩

@[simp] lemma coe_hardCoreThetaUnit (z : ℝ) (hz : 0 < z) :
    ((hardCoreThetaUnit z hz : I) : ℝ) = hardCoreTheta z := rfl

/-- The centered Boolean-coordinate sum is exactly `theta*a_C-|t|`. -/
lemma sum_lowerCentered_eq_fiber (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (ω : ↥E.available → Bool) :
    (∑ i, lowerCentered (hardCoreThetaUnit z hz) i ω) =
      hardCoreTheta z * (E.available.card : ℝ) -
        ((boolToFiberState E ω).1.card : ℝ) := by
  have hcard : (boolToFiberState E ω).1.card =
      (Finset.univ.filter fun i : ↥E.available => ω i = true).card := by
    simp [boolToFiberState]
  rw [hcard]
  simp [lowerCentered, hardCoreThetaUnit, Finset.sum_sub_distrib]
  ring

/-- Literal inherited conditional-fiber mass of the centered lower-tail event. -/
noncomputable def actualConditionalLowerTailMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (d : ℝ) : ℝ :=
  ∑ t : E.FiberState,
    if d ≤ hardCoreTheta z * (E.available.card : ℝ) - (t.1.card : ℝ) then
      actualConditionalProbability G P c z hz E t else 0

/-- Exact transport: the inherited C.40 finite global conditional fiber is the literal
Boolean product-measure lower-tail event. -/
theorem actualConditionalLowerTailMass_eq_productMeasure
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) (d : ℝ) :
    actualConditionalLowerTailMass (G := G) z hz E d =
      (productMeasure (ι := ↥E.available) (hardCoreThetaUnit z hz)).real
        {ω : ↥E.available → Bool |
          d ≤ ∑ i, lowerCentered (hardCoreThetaUnit z hz) i ω} := by
  classical
  let S : Finset (↥E.available → Bool) := Finset.univ.filter fun ω =>
    d ≤ ∑ i, lowerCentered (hardCoreThetaUnit z hz) i ω
  have hmeasure :
      (∑ ω ∈ S, (productMeasure (ι := ↥E.available)
          (hardCoreThetaUnit z hz)).real {ω}) =
        (productMeasure (ι := ↥E.available) (hardCoreThetaUnit z hz)).real
          {ω : ↥E.available → Bool |
            d ≤ ∑ i, lowerCentered (hardCoreThetaUnit z hz) i ω} := by
    calc
      _ = (productMeasure (ι := ↥E.available)
          (hardCoreThetaUnit z hz)).real (S : Set _) := by
        exact MeasureTheory.sum_measureReal_singleton S
      _ = _ := by
        congr 1
        ext ω
        simp [S]
  unfold actualConditionalLowerTailMass
  calc
    (∑ t : E.FiberState, if d ≤ hardCoreTheta z * (E.available.card : ℝ) -
        (t.1.card : ℝ) then actualConditionalProbability G P c z hz E t else 0) =
      ∑ ω : (↥E.available → Bool),
        if d ≤ hardCoreTheta z * (E.available.card : ℝ) -
            ((boolToFiberState E ω).1.card : ℝ) then
          actualConditionalProbability G P c z hz E (boolToFiberState E ω) else 0 := by
      symm
      exact (fiberStateEquivBool E).symm.sum_comp
        (fun t : E.FiberState => if d ≤ hardCoreTheta z * (E.available.card : ℝ) -
          (t.1.card : ℝ) then actualConditionalProbability G P c z hz E t else 0)
    _ = ∑ ω : (↥E.available → Bool),
        if d ≤ ∑ i, lowerCentered (hardCoreThetaUnit z hz) i ω then
          (productMeasure (hardCoreThetaUnit z hz)).real {ω} else 0 := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [sum_lowerCentered_eq_fiber]
      congr 1
      rw [C40_actual_conditional_probability_bool]
      symm
      exact productMeasure_singleton_eq_fiberWeight E (hardCoreThetaUnit z hz) ω
    _ = ∑ ω ∈ S, (productMeasure (hardCoreThetaUnit z hz)).real {ω} := by
      rw [← Finset.sum_filter]
    _ = _ := hmeasure

/-- **Actual-fiber C.50.** On a nonempty C.40 fiber, the literal conditional
lower-tail mass satisfies the exact Hoeffding exponent. -/
theorem C50_actualConditionalLowerTailMass_of_nonempty
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c)
    {d : ℝ} (hd : 0 ≤ d) (hE : E.available.Nonempty) :
    actualConditionalLowerTailMass (G := G) z hz E d ≤
      Real.exp (-2 * d ^ 2 / (E.available.card : ℝ)) := by
  let v : V := hE.choose
  have hv : v ∈ E.available := hE.choose_spec
  let iv : ↥E.available := ⟨v, hv⟩
  letI : Nonempty ↥E.available := ⟨iv⟩
  rw [actualConditionalLowerTailMass_eq_productMeasure]
  have h := C50_finiteBernoulli_lowerTail
    (ι := ↥E.available) (hardCoreThetaUnit z hz) hd
  rw [show Fintype.card ↥E.available = E.available.card by
    exact Fintype.card_coe _] at h
  exact h

/-- Literal conditional probability of the global rank event `X=s` inside one C.40 fiber. -/
noncomputable def actualConditionalRankMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (s : ℕ) : ℝ :=
  ∑ t : E.FiberState,
    if (E.extension t).val.card = s then
      actualConditionalProbability G P c z hz E t else 0

lemma actualConditionalProbability_nonneg
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) (t : E.FiberState) :
    0 ≤ actualConditionalProbability G P c z hz E t := by
  unfold actualConditionalProbability
  rw [actualFiberWeight_eq]
  exact div_nonneg (mul_nonneg
      (div_pos (pow_pos hz _) (independenceEval_pos G hz)).le
      (pow_pos hz _).le)
    (actualFiberMass_pos G P c z hz E).le

/-- A fiber rank event whose conditional mean is at least `d` above `s` is
contained in the transported centered lower-tail event. -/
theorem actualConditionalRankMass_le_lowerTail
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c)
    (s : ℕ) {d : ℝ}
    (hmean : d < actualConditionalMean G P c z hz E - (s : ℝ)) :
    actualConditionalRankMass (G := G) z hz E s ≤
      actualConditionalLowerTailMass (G := G) z hz E d := by
  unfold actualConditionalRankMass actualConditionalLowerTailMass
  apply Finset.sum_le_sum
  intro t ht
  by_cases hrank : (E.extension t).val.card = s
  · have hcard : ((E.extension t).val.card : ℝ) = (s : ℝ) := by
      exact_mod_cast hrank
    have hext : ((E.extension t).val.card : ℝ) =
        (E.occupied.val.card : ℝ) + (t.1.card : ℝ) := by
      rw [E.extension_card]
      norm_num
    have hm := C41_actual_conditionalMean G P c z hz E
    have htail : d ≤ hardCoreTheta z * (E.available.card : ℝ) - (t.1.card : ℝ) := by
      rw [hm] at hmean
      linarith
    simp [hrank, htail]
  · have hp := actualConditionalProbability_nonneg
      (G := G) (P := P) (c := c) z hz E t
    rw [if_neg hrank]
    split <;> simp [hp]

lemma actualConditionalRankMass_le_one
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) (s : ℕ) :
    actualConditionalRankMass (G := G) z hz E s ≤ 1 := by
  unfold actualConditionalRankMass
  calc
    (∑ t : E.FiberState,
      if (E.extension t).val.card = s then
        actualConditionalProbability G P c z hz E t else 0) ≤
      ∑ t : E.FiberState, actualConditionalProbability G P c z hz E t := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases h : (E.extension t).val.card = s
        · simp [h]
        · simp [h, actualConditionalProbability_nonneg
            (G := G) (P := P) (c := c) z hz E t]
    _ = 1 := C40_actual_conditional_probability_sum G P c z hz E

/-- If the available fiber is empty, a rank event cannot lie above its
conditional mean by a nonnegative amount. -/
lemma actualConditionalRankMass_eq_zero_of_empty
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c) (s : ℕ)
    {d : ℝ} (hd : 0 ≤ d)
    (hmean : d < actualConditionalMean G P c z hz E - (s : ℝ))
    (hE : ¬ E.available.Nonempty) :
    actualConditionalRankMass (G := G) z hz E s = 0 := by
  have hcard0 : E.available.card = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact hE (Finset.card_pos.mp hpos)
  unfold actualConditionalRankMass
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hrank : (E.extension t).val.card = s
  · have hcard : ((E.extension t).val.card : ℝ) = (s : ℝ) := by
      exact_mod_cast hrank
    have hext : ((E.extension t).val.card : ℝ) =
        (E.occupied.val.card : ℝ) + (t.1.card : ℝ) := by
      rw [E.extension_card]
      norm_num
    have hm := C41_actual_conditionalMean G P c z hz E
    rw [hm, hcard0] at hmean
    have hmean' : d < (E.occupied.val.card : ℝ) - (s : ℝ) := by
      simpa using hmean
    have hst : (s : ℝ) = (E.occupied.val.card : ℝ) + (t.1.card : ℝ) := by
      linarith [hcard, hext]
    have hcontra : False := by
      nlinarith [hmean', hst,
        (Nat.cast_nonneg t.1.card : (0 : ℝ) ≤ (t.1.card : ℝ))]
    exact hcontra.elim
  · simp [hrank]

/-- C.50 for a rank event, with the empty-fiber branch made explicit. -/
theorem C50_actualConditionalRankMass
    (z : ℝ) (hz : 0 < z) (E : ColorEnvironment P c)
    (s : ℕ) {d : ℝ} (hd : 0 ≤ d)
    (hmean : d < actualConditionalMean G P c z hz E - (s : ℝ)) :
    actualConditionalRankMass (G := G) z hz E s ≤
      Real.exp (-2 * d ^ 2 / (E.available.card : ℝ)) := by
  by_cases hE : E.available.Nonempty
  · exact (actualConditionalRankMass_le_lowerTail
      (G := G) (P := P) (c := c) z hz E s hmean).trans
      (C50_actualConditionalLowerTailMass_of_nonempty
        (G := G) (P := P) (c := c) z hz E hd hE)
  · have hcard : E.available.card = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hpos
      exact hE (Finset.card_pos.mp hpos)
    have hone := actualConditionalRankMass_le_one
      (G := G) (P := P) (c := c) z hz E s
    simpa [hcard] using hone

/-- A useful arithmetic form of the C.50 exponent comparison. -/
lemma probabilityAtMean_exponent_le
    {s a : ℕ} {Cstar : ℝ} (hC : 0 < Cstar)
    (hs : 0 < s) (ha : 0 < a)
    (haC : (a : ℝ) < Cstar * (s : ℝ)) :
    -2 * ((s : ℝ) / 224) ^ 2 / (a : ℝ) ≤
      -(s : ℝ) / (25088 * Cstar) := by
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hfrac : 1 / Cstar < (s : ℝ) / (a : ℝ) := by
    apply (div_lt_div_iff₀ hC haR).2
    nlinarith [haC]
  have hscaled : (s : ℝ) / Cstar <
      (s : ℝ) ^ 2 / (a : ℝ) := by
    calc
      (s : ℝ) / Cstar = (s : ℝ) * (1 / Cstar) := by ring
      _ < (s : ℝ) * ((s : ℝ) / (a : ℝ)) :=
        mul_lt_mul_of_pos_left hfrac hsR
      _ = (s : ℝ) ^ 2 / (a : ℝ) := by ring
  exact le_of_lt (calc
    -2 * ((s : ℝ) / 224) ^ 2 / (a : ℝ) =
        -((s : ℝ) ^ 2 / (a : ℝ)) / 25088 := by
          field_simp
          ring
    _ < -(s : ℝ) / Cstar / 25088 := by
      have hneg := neg_lt_neg hscaled
      have hneg' : -((s : ℝ) ^ 2 / (a : ℝ)) < -(s : ℝ) / Cstar := by
        convert hneg using 1 <;> ring
      exact (div_lt_div_iff_of_pos_right
        (by norm_num : (0 : ℝ) < 25088)).2 hneg'
    _ = -(s : ℝ) / (25088 * Cstar) := by ring)

/-- The actual-fiber probability-at-the-mean estimate at the manuscript
constant, after the finite C.39 order bound is supplied. -/
theorem C50_actualConditionalRankMass_probabilityAtMean
    (C : CanonicalFirstRecoveryState G)
    (hs : 0 < C.index)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27)
    (E : ColorEnvironment P c)
    (hmean : (C.index : ℝ) / 224 <
      actualConditionalMean G P c C.activity C.activity_pos E -
        (C.index : ℝ)) :
    actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index ≤
      Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
  have hC39 := C39_order_and_variance_lt (G := G) C hzlow hz27
  by_cases hE : E.available.Nonempty
  · have hd : 0 ≤ (C.index : ℝ) / 224 := by positivity
    have htail := C50_actualConditionalRankMass
      (G := G) (P := P) (c := c) C.activity C.activity_pos E C.index hd hmean
    have ha : 0 < E.available.card := Finset.card_pos.mpr hE
    have haC : (E.available.card : ℝ) <
        (3304 / 3 : ℝ) * (C.index : ℝ) := by
      have hsub : E.available.card ≤ Fintype.card V :=
        Finset.card_le_card (Finset.subset_univ E.available)
      have hN : (Fintype.card V : ℝ) <
          (3304 / 3 : ℝ) * (C.index : ℝ) := by
        simpa [CanonicalFirstRecoveryState.order] using hC39.1
      exact lt_of_le_of_lt (by exact_mod_cast hsub) hN
    have hexp := probabilityAtMean_exponent_le
      (s := C.index) (a := E.available.card) (Cstar := (3304 / 3 : ℝ))
      (by norm_num) hs ha haC
    have hmon := Real.exp_le_exp.mpr hexp
    exact htail.trans hmon
  · have hzeroRank := actualConditionalRankMass_eq_zero_of_empty
      (G := G) (P := P) (c := c) C.activity C.activity_pos E C.index
      (by positivity) hmean hE
    rw [hzeroRank]
    positivity

/-- The joint finite hard-core mass of the high-addability rank event in the
C.37 threshold decomposition. -/
noncomputable def C44_highRankMass
    (C : CanonicalFirstRecoveryState G) : ℝ :=
  ∑ s : IndepFinset G,
    if s.val.card = C.index ∧
        (5 : ℝ) * (C.index : ℝ) / 6 ≤ actualAddableCount (G := G) s then
      C.law.probability s else 0

/-- The high-addability part of the rank fiber has the quantitative mass
needed for the two-color pigeonhole step. -/
theorem C44_highRankMass_gt
    (C : CanonicalFirstRecoveryState G)
    (hs : 0 < C.index)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27) :
    C.law.rankMass C.index / (6 * (3304 / 3 : ℝ)) <
      C44_highRankMass C := by
  classical
  let L : ℝ := C.law.rankMass C.index
  let H : ℝ := C44_highRankMass C
  have hL : 0 < L := by
    dsimp [L]
    exact hardCoreLaw_rankMass_pos_of_coefficient_pos G C.activity
      C.activity_pos C.index C.center_coeff_pos
  have hS : 0 < (C.index : ℝ) := by exact_mod_cast hs
  have hC39 := C39_order_and_variance_lt (G := G) C hzlow hz27
  have hN : (C.order : ℝ) < (3304 / 3 : ℝ) * (C.index : ℝ) := hC39.1
  have hA_le : ∀ s : IndepFinset G,
      actualAddableCount (G := G) s ≤ (C.order : ℝ) := by
    intro s
    have horder : C.order = Fintype.card V := rfl
    rw [horder]
    change (∑ v : V, addableIndicator (G := G) s v) ≤
      (Fintype.card V : ℝ)
    calc
      (∑ v : V, addableIndicator (G := G) s v) ≤
          ∑ v : V, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        unfold addableIndicator
        split <;> norm_num
      _ = (Fintype.card V : ℝ) := by simp
  have hnumLower :
      ((C.index + 1 : ℕ) : ℝ) * L <
        ∑ s : IndepFinset G,
          if s.val.card = C.index then
            C.law.probability s * actualAddableCount (G := G) s else 0 := by
    have hcond := C37_conditionalExpectedAddable_gt (G := G) C
    have hdiv := (lt_div_iff₀ hL).mp hcond
    simpa [L, hardCoreConditionalExpectedAddable] using hdiv
  have hnumUpper :
      (∑ s : IndepFinset G,
          if s.val.card = C.index then
            C.law.probability s * actualAddableCount (G := G) s else 0) ≤
        (5 : ℝ) * (C.index : ℝ) / 6 * L +
          (C.order : ℝ) * H := by
    have hterm :
        (∑ s : IndepFinset G,
          if s.val.card = C.index then
            C.law.probability s * actualAddableCount (G := G) s else 0) ≤
          ∑ s : IndepFinset G,
            (((5 : ℝ) * (C.index : ℝ) / 6) *
              (if s.val.card = C.index then C.law.probability s else 0) +
            (C.order : ℝ) *
              (if s.val.card = C.index ∧
                  (5 : ℝ) * (C.index : ℝ) / 6 ≤
                    actualAddableCount (G := G) s then C.law.probability s else 0)) := by
      apply Finset.sum_le_sum
      intro s hs'
      by_cases hr : s.val.card = C.index
      · have hp : 0 ≤ C.law.probability s :=
          hardCoreLaw_probability_nonneg G C.activity C.activity_pos s
        by_cases hh : (5 : ℝ) * (C.index : ℝ) / 6 ≤
            actualAddableCount (G := G) s
        · have hbound := mul_le_mul_of_nonneg_left (hA_le s) hp
          have hnonneg : 0 ≤
              ((5 : ℝ) * (C.index : ℝ) / 6) * C.law.probability s := by
            positivity
          rw [if_pos hr, if_pos hr, if_pos (And.intro hr hh)]
          calc
            C.law.probability s * actualAddableCount (G := G) s ≤
                C.law.probability s * (C.order : ℝ) := hbound
            _ ≤ ((5 : ℝ) * (C.index : ℝ) / 6) * C.law.probability s +
                (C.order : ℝ) * C.law.probability s := by
              nlinarith [hnonneg]
        · have halt : actualAddableCount (G := G) s <
              (5 : ℝ) * (C.index : ℝ) / 6 := lt_of_not_ge hh
          have hbound := mul_le_mul_of_nonneg_left (halt.le) hp
          rw [if_pos hr, if_pos hr, if_neg (by
            intro h
            exact hh h.2)]
          simpa [mul_comm] using hbound
      · rw [if_neg hr, if_neg hr, if_neg (by
          intro h
          exact hr h.1)]
        norm_num
    have hLsum :
        (∑ s : IndepFinset G,
          if s.val.card = C.index then C.law.probability s else 0) = L := by
      change (∑ s : IndepFinset G,
          if C.law.stat s = C.index then C.law.probability s else 0) =
        C.law.rankMass C.index
      exact (C.law.rankMass_eq_sum_probability C.index).symm
    have hHsum :
        (∑ s : IndepFinset G,
          if s.val.card = C.index ∧
              (5 : ℝ) * (C.index : ℝ) / 6 ≤
                actualAddableCount (G := G) s then C.law.probability s else 0) = H := by
      rfl
    calc
      _ ≤ _ := hterm
      _ = ((5 : ℝ) * (C.index : ℝ) / 6) *
            (∑ s : IndepFinset G,
              if s.val.card = C.index then C.law.probability s else 0) +
          (C.order : ℝ) *
            (∑ s : IndepFinset G,
              if s.val.card = C.index ∧
                  (5 : ℝ) * (C.index : ℝ) / 6 ≤
                    actualAddableCount (G := G) s then C.law.probability s else 0) := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      _ = (5 : ℝ) * (C.index : ℝ) / 6 * L + (C.order : ℝ) * H := by
        rw [hLsum, hHsum]
  have hsucc : ((C.index + 1 : ℕ) : ℝ) = (C.index : ℝ) + 1 := by norm_num
  rw [hsucc] at hnumLower
  have hNH :
      ((C.index : ℝ) / 6) * L < (C.order : ℝ) * H := by
    nlinarith [hnumLower, hnumUpper, hL]
  have hHnonneg : 0 ≤ H := by
    dsimp [H, C44_highRankMass]
    apply Finset.sum_nonneg
    intro s hs'
    by_cases h : s.val.card = C.index ∧
        (5 : ℝ) * (C.index : ℝ) / 6 ≤ actualAddableCount (G := G) s
    · rw [if_pos h]
      exact hardCoreLaw_probability_nonneg G C.activity C.activity_pos s
    · rw [if_neg h]
  have hscale :
      (C.index : ℝ) * (L / 6) <
        (C.index : ℝ) * ((3304 / 3 : ℝ) * H) := by
    calc
      (C.index : ℝ) * (L / 6) = ((C.index : ℝ) / 6) * L := by ring
      _ < (C.order : ℝ) * H := hNH
      _ ≤ (3304 / 3 : ℝ) * (C.index : ℝ) * H := by
        exact mul_le_mul_of_nonneg_right hN.le hHnonneg
      _ = (C.index : ℝ) * ((3304 / 3 : ℝ) * H) := by ring
  have hcancel : L / 6 < (3304 / 3 : ℝ) * H := by
    nlinarith [hscale, hS]
  change L / (6 * (3304 / 3 : ℝ)) < H
  apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 6 * (3304 / 3))).2
  nlinarith [hcancel]

/-- The joint finite hard-core mass of the rank event and the fixed-color
large-deviation event used in C.44. -/
noncomputable def C44_fixedColorMass
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) : ℝ :=
  ∑ s : IndepFinset G,
    if s.val.card = C.index ∧
        sideResidual (G := G) P c.opposite C.activity s <
          -(C.index : ℝ) / 224 then
      C.law.probability s else 0

/-- Literal finite disintegration of the C.44 fixed-color mass into the exact
C.40 environment fibers. -/
theorem C44_fixedColorMass_eq_fibers
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) :
    C44_fixedColorMass C P c =
      ∑ E : ColorEnvironment P c,
        if (C.index : ℝ) / 224 <
            actualConditionalMean G P c C.activity C.activity_pos E -
              (C.index : ℝ) then
          actualFiberMass G P c C.activity C.activity_pos E *
            actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index
        else 0 := by
  classical
  unfold C44_fixedColorMass
  rw [sum_global_eq_sum_fiberSigma (G := G) P c]
  apply Finset.sum_congr rfl
  intro E hE
  have hfactor (t : E.FiberState) :
      C.law.probability (E.extension t) =
        actualFiberMass G P c C.activity C.activity_pos E *
          actualConditionalProbability G P c C.activity C.activity_pos E t := by
    change actualFiberWeight G P c C.activity C.activity_pos E t = _
    unfold actualConditionalProbability
    have hne : actualFiberMass G P c C.activity C.activity_pos E ≠ 0 :=
      (actualFiberMass_pos G P c C.activity C.activity_pos E).ne'
    rw [← mul_div_assoc]
    exact (eq_div_iff hne).2 (by ring)
  by_cases hm : (C.index : ℝ) / 224 <
      actualConditionalMean G P c C.activity C.activity_pos E -
        (C.index : ℝ)
  · rw [if_pos hm]
    have hevent (t : E.FiberState) :
        ((E.extension t).val.card = C.index ∧
          sideResidual (G := G) P c.opposite C.activity (E.extension t) <
            -(C.index : ℝ) / 224) ↔
          (E.extension t).val.card = C.index := by
      rw [sideResidual_opposite_eq_rank_sub_conditionalMean
        (G := G) P c C.activity C.activity_pos (E.extension t)]
      rw [restrictionEnvironment_extension_eq' (G := G) c E t]
      constructor
      · intro h
        exact h.1
      · intro h
        have hcardR : ((E.extension t).val.card : ℝ) = (C.index : ℝ) := by
          exact_mod_cast h
        exact ⟨h, by linarith [hm, hcardR]⟩
    calc
      (∑ t : E.FiberState,
          if (E.extension t).val.card = C.index ∧
              sideResidual (G := G) P c.opposite C.activity
                (E.extension t) < -(C.index : ℝ) / 224 then
            C.law.probability (E.extension t) else 0) =
          ∑ t : E.FiberState,
            if (E.extension t).val.card = C.index then
              C.law.probability (E.extension t) else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [hevent t]
      _ = ∑ t : E.FiberState,
          if (E.extension t).val.card = C.index then
            actualFiberMass G P c C.activity C.activity_pos E *
              actualConditionalProbability G P c C.activity C.activity_pos E t else 0 := by
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hr : (E.extension t).val.card = C.index
        · rw [if_pos hr, if_pos hr, hfactor t]
        · rw [if_neg hr, if_neg hr]
      _ = actualFiberMass G P c C.activity C.activity_pos E *
          actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index := by
        unfold actualConditionalRankMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        by_cases hr : (E.extension t).val.card = C.index
        · simp [hr]
        · simp [hr]
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro t ht
    have hnot : ¬ ((E.extension t).val.card = C.index ∧
        sideResidual (G := G) P c.opposite C.activity (E.extension t) <
          -(C.index : ℝ) / 224) := by
      intro h
      rw [sideResidual_opposite_eq_rank_sub_conditionalMean
        (G := G) P c C.activity C.activity_pos (E.extension t)] at h
      rw [restrictionEnvironment_extension_eq' (G := G) c E t] at h
      have hcardR : ((E.extension t).val.card : ℝ) = (C.index : ℝ) := by
        exact_mod_cast h.1
      linarith [hm, h.2, hcardR]
    change (if (E.extension t).val.card = C.index ∧
        sideResidual (G := G) P c.opposite C.activity (E.extension t) <
          -(C.index : ℝ) / 224 then C.law.probability (E.extension t) else 0) = 0
    simp [hnot]
/-- The fixed-color mass is bounded by the finite C.50 exponent whenever the
canonical order/activity hypotheses are available. -/
theorem C44_fixedColorMass_le
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (c : BipartitionSide) (hs : 0 < C.index)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27) :
    C44_fixedColorMass C P c ≤
      Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
  classical
  rw [C44_fixedColorMass_eq_fibers]
  have htotal :
      (∑ E : ColorEnvironment P c,
        actualFiberMass G P c C.activity C.activity_pos E) = 1 := by
    calc
      (∑ E : ColorEnvironment P c,
          actualFiberMass G P c C.activity C.activity_pos E) =
          ∑ E : ColorEnvironment P c, ∑ t : E.FiberState,
            C.law.probability (E.extension t) := by
        apply Finset.sum_congr rfl
        intro E hE
        unfold actualFiberMass actualFiberWeight
        rfl
      _ = ∑ s : IndepFinset G, C.law.probability s := by
        symm
        simpa using (sum_global_eq_sum_fiberSigma (G := G) P c
          (fun s : IndepFinset G => C.law.probability s))
      _ = 1 := C.law.probability_sum
  let q : ℝ := Real.exp (-C.index / (25088 * (3304 / 3 : ℝ)))
  have hq : 0 ≤ q := by positivity
  calc
    (∑ E : ColorEnvironment P c,
        if (C.index : ℝ) / 224 <
            actualConditionalMean G P c C.activity C.activity_pos E -
              (C.index : ℝ) then
          actualFiberMass G P c C.activity C.activity_pos E *
            actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index
        else 0) ≤
      ∑ E : ColorEnvironment P c,
        actualFiberMass G P c C.activity C.activity_pos E * q := by
      apply Finset.sum_le_sum
      intro E hE
      by_cases hm : (C.index : ℝ) / 224 <
          actualConditionalMean G P c C.activity C.activity_pos E -
            (C.index : ℝ)
      · rw [if_pos hm]
        have htail := C50_actualConditionalRankMass_probabilityAtMean
          (G := G) (P := P) (c := c) C hs hzlow hz27 E hm
        exact mul_le_mul_of_nonneg_left htail
          (actualFiberMass_pos G P c C.activity C.activity_pos E).le
      · rw [if_neg hm]
        exact mul_nonneg
          (actualFiberMass_pos G P c C.activity C.activity_pos E).le hq
    _ = q := by
      rw [← Finset.sum_mul, htotal]
      simp [q]

/-- The high-addability rank event is covered by the union of the two
fixed-color lower-tail events.  This is the finite C.42/C.43 pigeonhole
step, with all sums taken in the actual hard-core law. -/
theorem C44_highRankMass_le_fixedColorMass_sum
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (hs : 0 < C.index) (hzlow : (3 : ℝ) / 2 < C.activity) :
    C44_highRankMass C ≤
      C44_fixedColorMass C P .left + C44_fixedColorMass C P .right := by
  classical
  have hS : 0 < (C.index : ℝ) := by exact_mod_cast hs
  have hcover : ∀ s : IndepFinset G,
      (s.val.card = C.index ∧
          (5 : ℝ) * (C.index : ℝ) / 6 ≤ actualAddableCount (G := G) s) →
      (s.val.card = C.index ∧
          sideResidual (G := G) P .left C.activity s <
            -(C.index : ℝ) / 224) ∨
        (s.val.card = C.index ∧
          sideResidual (G := G) P .right C.activity s <
            -(C.index : ℝ) / 224) := by
    intro s hhigh
    have hprod :
        (3 : ℝ) / 2 * (C.index : ℝ) < C.activity * (C.index : ℝ) := by
      exact mul_lt_mul_of_pos_right hzlow hS
    have hAprod :
        C.activity * ((5 : ℝ) * (C.index : ℝ) / 6) ≤
          C.activity * actualAddableCount (G := G) s := by
      exact mul_le_mul_of_nonneg_left hhigh.2 C.activity_pos.le
    have hbase :
        (C.index : ℝ) - C.activity * ((5 : ℝ) * (C.index : ℝ) / 6) <
          (-(C.index : ℝ) / 10) * (1 + C.activity) := by
      nlinarith [hprod]
    have hnum :
        (C.index : ℝ) - C.activity * actualAddableCount (G := G) s ≤
          (C.index : ℝ) - C.activity * ((5 : ℝ) * (C.index : ℝ) / 6) := by
      nlinarith [hAprod]
    have hsumneg :
        sideResidual (G := G) P .left C.activity s +
            sideResidual (G := G) P .right C.activity s <
          -(C.index : ℝ) / 10 := by
      calc
        sideResidual (G := G) P .left C.activity s +
              sideResidual (G := G) P .right C.activity s =
            ((s.val.card : ℝ) - C.activity * actualAddableCount (G := G) s) /
              (1 + C.activity) := by
                simpa using C42_sideResidual_add (G := G) P C.activity
                  C.activity_pos s
        _ = ((C.index : ℝ) - C.activity * actualAddableCount (G := G) s) /
              (1 + C.activity) := by
                have hcard : (s.val.card : ℝ) = (C.index : ℝ) := by
                  exact_mod_cast hhigh.1
                rw [hcard]
        _ < (-(C.index : ℝ) / 10) := by
          apply (div_lt_iff₀ (by linarith [C.activity_pos])).2
          exact lt_of_le_of_lt hnum hbase
    by_cases hl : sideResidual (G := G) P .left C.activity s <
        -(C.index : ℝ) / 224
    · exact Or.inl ⟨hhigh.1, hl⟩
    · by_cases hr : sideResidual (G := G) P .right C.activity s <
          -(C.index : ℝ) / 224
      · exact Or.inr ⟨hhigh.1, hr⟩
      · exfalso
        have hll : -(C.index : ℝ) / 224 ≤
            sideResidual (G := G) P .left C.activity s := le_of_not_gt hl
        have hlr : -(C.index : ℝ) / 224 ≤
            sideResidual (G := G) P .right C.activity s := le_of_not_gt hr
        nlinarith [hsumneg, hS]
  unfold C44_highRankMass C44_fixedColorMass
  rw [← Finset.sum_add_distrib]
  simp only [BipartitionSide.opposite_left, BipartitionSide.opposite_right]
  apply Finset.sum_le_sum
  intro s hs'
  by_cases hhigh : s.val.card = C.index ∧
      (5 : ℝ) * (C.index : ℝ) / 6 ≤ actualAddableCount (G := G) s
  · obtain hleft | hright := hcover s hhigh
    · rw [if_pos hhigh]
      have hp : 0 ≤ C.law.probability s :=
        hardCoreLaw_probability_nonneg G C.activity C.activity_pos s
      by_cases hright' : s.val.card = C.index ∧
          sideResidual (G := G) P .right C.activity s <
            -(C.index : ℝ) / 224
      · rw [if_pos hright', if_pos hleft]
        nlinarith
      · rw [if_neg hright', if_pos hleft]
        nlinarith
    · rw [if_pos hhigh]
      have hp : 0 ≤ C.law.probability s :=
        hardCoreLaw_probability_nonneg G C.activity C.activity_pos s
      by_cases hleft' : s.val.card = C.index ∧
          sideResidual (G := G) P .left C.activity s <
            -(C.index : ℝ) / 224
      · rw [if_pos hright, if_pos hleft']
        nlinarith
      · rw [if_pos hright, if_neg hleft']
        nlinarith
  · rw [if_neg hhigh]
    have hp : 0 ≤ C.law.probability s :=
      hardCoreLaw_probability_nonneg G C.activity C.activity_pos s
    by_cases hright : s.val.card = C.index ∧
        sideResidual (G := G) P .right C.activity s <
          -(C.index : ℝ) / 224
    · rw [if_pos hright]
      by_cases hleft : s.val.card = C.index ∧
          sideResidual (G := G) P .left C.activity s <
            -(C.index : ℝ) / 224
      · rw [if_pos hleft]
        nlinarith
      · rw [if_neg hleft]
        nlinarith
    · rw [if_neg hright]
      by_cases hleft : s.val.card = C.index ∧
          sideResidual (G := G) P .left C.activity s <
            -(C.index : ℝ) / 224
      · rw [if_pos hleft]
        nlinarith
      · rw [if_neg hleft]
        norm_num

/-- **Finite C.44.**  For a genuine finite bipartition, the probability of
being at the first-recovery rank is bounded by the explicit C.44 exponential.
The lower activity floor and the separate activity cap are both exposed as
finite hypotheses. -/
theorem C44_probability_at_mean_finite
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (hs : 0 < C.index)
    (hzlow : (3 : ℝ) / 2 < C.activity) (hz27 : C.activity < 27) :
    C.law.rankMass C.index ≤
      12 * (3304 / 3 : ℝ) *
        Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
  classical
  let K : ℝ := 3304 / 3
  let L : ℝ := C.law.rankMass C.index
  have hhigh := C44_highRankMass_gt (G := G) C hs hzlow hz27
  have hcover := C44_highRankMass_le_fixedColorMass_sum
    (G := G) C P hs hzlow
  have hsumgt :
      L / (6 * K) <
        C44_fixedColorMass C P .left + C44_fixedColorMass C P .right := by
    dsimp [L, K] at hhigh ⊢
    exact lt_of_lt_of_le hhigh hcover
  have hpigeonhole :
      (L / (12 * K) < C44_fixedColorMass C P .left) ∨
        (L / (12 * K) < C44_fixedColorMass C P .right) := by
    by_cases hl : L / (12 * K) < C44_fixedColorMass C P .left
    · exact Or.inl hl
    · right
      have hll : C44_fixedColorMass C P .left ≤ L / (12 * K) := le_of_not_gt hl
      nlinarith [hsumgt]
  have hq : L / (12 * K) <
      Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
    cases hpigeonhole with
    | inl hl =>
        exact hl.trans_le (C44_fixedColorMass_le
          (G := G) C P .left hs hzlow hz27)
    | inr hr =>
        exact hr.trans_le (C44_fixedColorMass_le
          (G := G) C P .right hs hzlow hz27)
  have hstrict : L <
      (12 * K) * Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
    have hden : 0 < 12 * K := by norm_num [K]
    have hstrict' := (div_lt_iff₀ hden).mp (by simpa [K] using hq)
    simpa [mul_comm, mul_left_comm, mul_assoc] using hstrict'
  change L ≤ 12 * (3304 / 3 : ℝ) *
      Real.exp (-C.index / (25088 * (3304 / 3 : ℝ)))
  exact le_of_lt (by simpa [K, mul_assoc] using hstrict)
/-- An explicit variance threshold at which the canonical activity is above
`3/2`.  This package does not hide the activity cap in the floor. -/
def EventualActivityFloor (V_h : ℝ) : Prop :=
  ∀ C : CanonicalFirstRecoveryState G,
    V_h ≤ C.variance → (3 : ℝ) / 2 < C.activity

/-- The explicit variance-threshold package for the full finite C.44 bound.
The cap `activity < 27` remains a separate hypothesis. -/
theorem eventual_C44_probability_at_mean_finite
    (V_h : ℝ) (hfloor : EventualActivityFloor (G := G) V_h)
    (C : CanonicalFirstRecoveryState G) (P : FiniteBipartition G)
    (hs : 0 < C.index)
    (hvariance : V_h ≤ C.variance)
    (hz27 : C.activity < 27) :
    C.law.rankMass C.index ≤
      12 * (3304 / 3 : ℝ) *
        Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
  exact C44_probability_at_mean_finite C P hs (hfloor C hvariance) hz27

theorem eventual_C50_actualConditionalRankMass_probabilityAtMean
    (V_h : ℝ) (hfloor : EventualActivityFloor (G := G) V_h)
    (C : CanonicalFirstRecoveryState G)
    (hs : 0 < C.index)
    (hvariance : V_h ≤ C.variance)
    (hz27 : C.activity < 27)
    (E : ColorEnvironment P c)
    (hmean : (C.index : ℝ) / 224 <
      actualConditionalMean G P c C.activity C.activity_pos E -
        (C.index : ℝ)) :
    actualConditionalRankMass (G := G) C.activity C.activity_pos E C.index ≤
      Real.exp (-C.index / (25088 * (3304 / 3 : ℝ))) := by
  exact C50_actualConditionalRankMass_probabilityAtMean
    C hs (hfloor C hvariance) hz27 E hmean

