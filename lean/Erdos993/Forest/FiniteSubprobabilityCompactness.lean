import Erdos993.Forest.CanonicalLaw
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Finite subprobability compactness for Appendix D

This file supplies two measure-theoretic adapters used by Appendix D.  The
configuration law is the literal global hard-core law of the supplied
`CanonicalFirstRecoveryState`; no new canonical state is constructed.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace Erdos993

noncomputable section

universe u

open Forest

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- The finite configuration space is equipped with its discrete measurable
space. -/
instance indepFinsetMeasurableSpace : MeasurableSpace (IndepFinset G) := ⊤

instance indepFinsetMeasurableSingletonClass :
    MeasurableSingletonClass (IndepFinset G) := ⟨fun _ => trivial⟩

/-- The PMF of the literal global canonical law on independent sets. -/
def actualConfigurationPMF (C : CanonicalFirstRecoveryState G) :
    PMF (IndepFinset G) := by
  refine PMF.ofFintype (fun I => ENNReal.ofReal (C.law.probability I)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun I _ => C.law.probability_nonneg I)]
  rw [C.law.probability_sum]
  norm_num

@[simp] theorem actualConfigurationPMF_apply_toReal
    (C : CanonicalFirstRecoveryState G) (I : IndepFinset G) :
    (actualConfigurationPMF C I).toReal = C.law.probability I := by
  simp only [actualConfigurationPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (C.law.probability_nonneg I)

/-- The probability measure of the literal global canonical configuration. -/
def actualConfigurationLaw (C : CanonicalFirstRecoveryState G) :
    ProbabilityMeasure (IndepFinset G) :=
  ⟨(actualConfigurationPMF C).toMeasure,
    PMF.toMeasure.isProbabilityMeasure (actualConfigurationPMF C)⟩

/-- Evaluation of the literal global configuration law on a finite event. -/
theorem actualConfigurationLaw_apply_finset
    (C : CanonicalFirstRecoveryState G) (s : Finset (IndepFinset G)) :
    ((actualConfigurationLaw C : Measure (IndepFinset G)) s).toReal =
      ∑ I ∈ s, C.law.probability I := by
  change ((actualConfigurationPMF C).toMeasure s).toReal = _
  rw [PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum
    (fun I hI => (actualConfigurationPMF C).apply_ne_top I)]
  apply Finset.sum_congr rfl
  intro I hI
  exact actualConfigurationPMF_apply_toReal C I

/-- A Dirac mass bundled as a finite measure. -/
def finiteDirac {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (x : X) : FiniteMeasure X :=
  ⟨Measure.dirac x, by infer_instance⟩

@[simp] theorem finiteDirac_mass {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (x : X) :
    (finiteDirac x).mass = 1 := by
  simp [FiniteMeasure.mass, finiteDirac]

@[simp] theorem finiteMeasure_mass_smul {X : Type*} [MeasurableSpace X]
    (c : ℝ≥0) (μ : FiniteMeasure X) :
    (c • μ).mass = c * μ.mass := by
  simp [FiniteMeasure.mass]

@[simp] theorem finiteMeasure_mass_add {X : Type*} [MeasurableSpace X]
    (μ ν : FiniteMeasure X) :
    (μ + ν).mass = μ.mass + ν.mass := by
  exact congrFun (FiniteMeasure.coeFn_add μ ν) Set.univ

@[simp] theorem finiteMeasure_mass_sum {X ι : Type*} [MeasurableSpace X]
    (s : Finset ι) (μ : ι → FiniteMeasure X) :
    (∑ i ∈ s, μ i).mass = ∑ i ∈ s, (μ i).mass := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Sequential compactness for positive finite subprobabilities on a compact
metrizable space.  The proof extracts `(mass, normalize)` in the compact
probability-measure space and reconstructs the finite limit. -/
theorem exists_subseq_finiteMeasure_compact_normalize_D35
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] [T2Space X] [PseudoMetricSpace X]
    [SecondCountableTopology X] [CompactSpace X] [Nonempty X]
    (μ : ℕ → FiniteMeasure X) (p : ℝ≥0)
    (hlower : ∀ n, p ≤ (μ n).mass)
    (hupper : ∀ n, (μ n).mass ≤ 1) :
    ∃ q : ℝ≥0, ∃ π : ProbabilityMeasure X, ∃ φ : ℕ → ℕ,
      p ≤ q ∧ q ≤ 1 ∧ StrictMono φ ∧
      Tendsto (μ ∘ φ) atTop (𝓝 (q • π.toFiniteMeasure)) := by
  let s : Set (ℝ≥0 × ProbabilityMeasure X) :=
    Set.Icc p 1 ×ˢ (Set.univ : Set (ProbabilityMeasure X))
  have hs : IsCompact s := isCompact_Icc.prod isCompact_univ
  have hx : ∀ n, ((μ n).mass, (μ n).normalize) ∈ s := by
    intro n
    exact ⟨⟨hlower n, hupper n⟩, Set.mem_univ _⟩
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hs.tendsto_subseq hx
  refine ⟨a.1, a.2, φ, ha.1.1, ha.1.2, hφ, ?_⟩
  have hmass : Tendsto (fun n => (μ (φ n)).mass) atTop (𝓝 a.1) := by
    have h := continuous_fst.continuousAt.tendsto.comp hlim
    simpa [Function.comp_def] using h
  have hprob : Tendsto (fun n => (μ (φ n)).normalize) atTop (𝓝 a.2) := by
    have h := continuous_snd.continuousAt.tendsto.comp hlim
    simpa [Function.comp_def] using h
  have hfinite : Tendsto (fun n => (μ (φ n)).normalize.toFiniteMeasure)
      atTop (𝓝 a.2.toFiniteMeasure) := by
    exact
      (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds atTop).1 hprob
  have hsmul := hmass.smul hfinite
  apply hsmul.congr'
  exact Eventually.of_forall fun n => by
    exact (FiniteMeasure.self_eq_mass_smul_normalize (μ (φ n))).symm

end

end Erdos993
