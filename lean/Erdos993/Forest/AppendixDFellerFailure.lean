import Erdos993.Forest.AppendixDMacroscopicContribution
import Erdos993.Forest.AppendixDSpineCovariancePQV
import Erdos993.Forest.CanonicalActivityFloor

/-!
# Appendix D: Feller-failure continuation

This module begins the post-D.7 part of Appendix D.  It records the exact
Fourier/Turán contradiction endpoint needed after the martingale CLT in D.8.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos993
namespace Forest

noncomputable section

open CanonicalCompactnessWrapper
open CanonicalCompactnessWrapper.CanonicalSequence
open Erdos993.MeasureFourierInversion
open Erdos993.Forest.MartingaleArrayCLT

namespace CanonicalCompactnessWrapper.CanonicalSequence

/-- D.73--D.79 endpoint: an actual canonical first-recovery sequence cannot
converge weakly to the standard Gaussian.  Thus, once D.68--D.72 and the
generic martingale CLT produce this weak limit, the D.8 contradiction is
formal and does not need a local CLT assumption. -/
theorem not_tendsto_standardGaussian_D73_D79
    (S : CanonicalSequence) (γ : ProbabilityMeasure ℝ)
    (hγ : (γ : Measure ℝ) = gaussianReal 0 1) :
    ¬ Tendsto S.standardizedLaw atTop (𝓝 γ) := by
  intro hweak
  have hchar : ∀ u : ℝ,
      Tendsto (fun n => S.characteristic n u) atTop (𝓝 (charFun γ u)) := by
    intro u
    have h := (ProbabilityMeasure.tendsto_iff_tendsto_charFun).1 hweak u
    simpa [characteristic] using h
  have hA :=
    Erdos993.Forest.AppendixA.CanonicalSequence.fullDomainEnvelope_of_appendixA4
      S γ id strictMono_id hchar
  have hweakId : Tendsto (S.standardizedLaw ∘ id) atTop (𝓝 γ) := by
    simpa using hweak
  have hcurv := fourier_turan_curvature_limit_of_fullDomainEnvelope S γ id
    (Erdos993.Forest.AppendixA.appendixA4Envelope 27) strictMono_id hweakId hA
  have hpos := standardGaussian_inverse_curvature_pos γ hγ hA
  have hevent : ∀ᶠ n in atTop,
      0 < (S.V n) ^ 2 *
        ((S.centeredMass n 0) ^ 2 -
          S.centeredMass n (-1) * S.centeredMass n 1) := by
    simpa using hcurv.eventually (Ioi_mem_nhds hpos)
  obtain ⟨n, hn⟩ := hevent.exists
  have hreverse := S.centered_mass_strict_reverse_turan n
  have hVpos := S.variance_pos n
  nlinarith [sq_pos_of_pos hVpos]

/-- D.68, one-row quantitative form.  Under the original global canonical
law, the normalized retained predictable quadratic variation is concentrated
around its exact normalized mean.  The bound is precisely D.7 divided by
`epsilon² V²`; no replacement canonical state is introduced. -/
theorem predictableQuadraticVariation_deviation_measure_le_D68
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G)
    (R : ActualRootedVariance.ComponentRooting G)
    (hz : C.activity < 27) {S : Finset V}
    (hS : ActualMartingaleProjection.AncestorClosed R S)
    (m : ℝ)
    (hm : ∀ u ∈ S,
      R.vertexVarianceContribution (G := G) C u ≤ m)
    (hm0 : 0 ≤ m) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    C.law.toMeasure
        {I | epsilon ≤
          |R.predictableQuadraticVariation (G := G) C S I / C.variance -
            (∑ u ∈ S, R.vertexVarianceContribution (G := G) C u) /
              C.variance|} ≤
      ENNReal.ofReal
        (10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m /
          (epsilon ^ 2 * C.variance)) := by
  classical
  let μ := C.law.toMeasure
  let Q : IndepFinset G → ℝ :=
    R.predictableQuadraticVariation (G := G) C S
  let GS : ℝ :=
    ∑ u ∈ S, R.vertexVarianceContribution (G := G) C u
  let A : ℝ :=
    10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m * C.variance
  have hV : 0 < C.variance :=
    ActualRootedVariance.ComponentRooting.canonicalFirstRecovery_variance_pos C
  have hmeanQ : ActualMartingaleProjection.lawExpectation C Q = GS := by
    exact R.lawExpectation_predictableQuadraticVariation_eq (G := G) C S
  have hsum :
      (∑ I : IndepFinset G, C.law.probability I *
        |Q I / C.variance - GS / C.variance| ^ 2) =
      ActualMartingaleProjection.lawVariance C Q / C.variance ^ 2 := by
    have hvar : ActualMartingaleProjection.lawVariance C Q =
        ∑ I : IndepFinset G, C.law.probability I * (Q I - GS) ^ 2 := by
      unfold ActualMartingaleProjection.lawVariance
      rw [hmeanQ]
      rfl
    rw [hvar]
    calc
      (∑ I : IndepFinset G, C.law.probability I *
          |Q I / C.variance - GS / C.variance| ^ 2) =
          ∑ I : IndepFinset G,
            (C.law.probability I * (Q I - GS) ^ 2) / C.variance ^ 2 := by
        apply Finset.sum_congr rfl
        intro I hI
        rw [sq_abs]
        field_simp [hV.ne']
      _ = (∑ I : IndepFinset G,
            C.law.probability I * (Q I - GS) ^ 2) / C.variance ^ 2 := by
        rw [Finset.sum_div]
  have hIntegral :
      (∫ I, |Q I / C.variance - GS / C.variance| ^ 2 ∂μ) ≤
        A / C.variance ^ 2 := by
    dsimp only [μ]
    rw [Erdos993.Forest.FiniteLatticeLaw.integral_toMeasure_eq_sum]
    rw [hsum]
    exact div_le_div_of_nonneg_right
      (R.lawVariance_predictableQuadraticVariation_le_variance
        (G := G) C hz hS m hm hm0)
      (sq_nonneg C.variance)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := μ)
    (f := fun I => |Q I / C.variance - GS / C.variance| ^ 2)
    (Filter.Eventually.of_forall (fun I => sq_nonneg
      |Q I / C.variance - GS / C.variance|))
    (Integrable.of_finite) (epsilon ^ 2)
  have hsqEvent :
      {I | epsilon ^ 2 ≤
        |Q I / C.variance - GS / C.variance| ^ 2} =
      {I | epsilon ≤
        |Q I / C.variance - GS / C.variance|} := by
    ext I
    simp only [Set.mem_setOf_eq]
    exact sq_le_sq₀ hepsilon.le
      (abs_nonneg (Q I / C.variance - GS / C.variance))
  rw [hsqEvent] at hmarkov
  have hreal0 :
      μ.real {I | epsilon ≤
        |Q I / C.variance - GS / C.variance|} ≤
        (A / C.variance ^ 2) / epsilon ^ 2 := by
    apply (le_div_iff₀' (sq_pos_of_pos hepsilon)).2
    exact hmarkov.trans hIntegral
  have hrewrite :
      (A / C.variance ^ 2) / epsilon ^ 2 =
        10976 * ((R.rootedLeaves (G := G) S).card : ℝ) ^ 2 * m /
          (epsilon ^ 2 * C.variance) := by
    dsimp [A]
    field_simp [hV.ne', hepsilon.ne']
  rw [hrewrite] at hreal0
  change μ {I | epsilon ≤ |Q I / C.variance - GS / C.variance|} ≤ _
  calc
    μ {I | epsilon ≤ |Q I / C.variance - GS / C.variance|} =
        ENNReal.ofReal
          (μ.real {I | epsilon ≤
            |Q I / C.variance - GS / C.variance|}) := by
      exact (ENNReal.ofReal_toReal
        (measure_ne_top μ {I | epsilon ≤
          |Q I / C.variance - GS / C.variance|})).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal0

/-- Sequential D.68.  Once retained ancestor-closed sets have asymptotically
full variance mass and satisfy the finite-leaf Feller ratio supplied by D.66--D.67,
D.7 implies convergence in probability of their normalized predictable
quadratic variations to one, under the varying original global laws. -/
theorem predictableQuadraticVariation_tendstoInProbability_D68
    (S : CanonicalSequence)
    (rooting : ∀ n,
      ActualRootedVariance.ComponentRooting (S.graph n))
    (retained : ∀ n, Finset (Fin (S.order n)))
    (hretained : ∀ n,
      ActualMartingaleProjection.AncestorClosed (rooting n) (retained n))
    (m : ℕ → ℝ)
    (hm : ∀ n u, u ∈ retained n →
      (rooting n).vertexVarianceContribution
        (G := S.graph n) (S.state n) u ≤ m n)
    (hm0 : ∀ n, 0 ≤ m n)
    (hmean : Tendsto (fun n =>
      (∑ u ∈ retained n,
        (rooting n).vertexVarianceContribution
          (G := S.graph n) (S.state n) u) / S.V n) atTop (𝓝 1))
    (hfeller : Tendsto (fun n =>
      (((rooting n).rootedLeaves (G := S.graph n) (retained n)).card : ℝ) ^ 2 *
        m n / S.V n) atTop (𝓝 0)) :
    TendstoInProbabilityVarying
      (fun n => IndepFinset (S.graph n))
      (fun n => (S.state n).law.toMeasure)
      (fun n I =>
        (rooting n).predictableQuadraticVariation
          (G := S.graph n) (S.state n) (retained n) I / S.V n)
      atTop 1 := by
  intro epsilon hepsilon
  have hehalf : 0 < epsilon / 2 := half_pos hepsilon
  let center : ℕ → ℝ := fun n =>
    (∑ u ∈ retained n,
      (rooting n).vertexVarianceContribution
        (G := S.graph n) (S.state n) u) / S.V n
  let boundReal : ℕ → ℝ := fun n =>
    10976 *
        (((rooting n).rootedLeaves (G := S.graph n) (retained n)).card : ℝ) ^ 2 *
        m n /
      ((epsilon / 2) ^ 2 * S.V n)
  have hcenter : ∀ᶠ n in atTop, |center n - 1| < epsilon / 2 := by
    have hnhds := hmean.eventually (Metric.ball_mem_nhds (x := (1 : ℝ)) hehalf)
    filter_upwards [hnhds] with n hn
    simpa [center, Real.dist_eq] using hn
  have hboundReal : Tendsto boundReal atTop (𝓝 0) := by
    have hc : Tendsto (fun _n : ℕ => 10976 / (epsilon / 2) ^ 2) atTop
        (𝓝 (10976 / (epsilon / 2) ^ 2)) := tendsto_const_nhds
    have hmul := hc.mul hfeller
    have hmul0 : Tendsto
        (fun x => 10976 / (epsilon / 2) ^ 2 *
          ((((rooting x).rootedLeaves (G := S.graph x) (retained x)).card : ℝ) ^ 2 *
            m x / S.V x)) atTop (𝓝 0) := by
      simpa using hmul
    apply hmul0.congr'
    filter_upwards with n
    dsimp [boundReal]
    have hV := S.variance_pos n
    field_simp [hV.ne', hehalf.ne']
  have hbound : Tendsto (fun n => ENNReal.ofReal (boundReal n)) atTop
      (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hboundReal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal)) atTop (𝓝 0))
    hbound
  · exact Filter.Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [hcenter] with n hn
    let q : IndepFinset (S.graph n) → ℝ := fun I =>
      (rooting n).predictableQuadraticVariation
        (G := S.graph n) (S.state n) (retained n) I / S.V n
    have hsubset :
        {I | epsilon ≤ |q I - 1|} ⊆
          {I | epsilon / 2 ≤ |q I - center n|} := by
      intro I hI
      change epsilon ≤ |q I - 1| at hI
      have htri : |q I - 1| ≤ |q I - center n| + |center n - 1| := by
        calc
          |q I - 1| = |(q I - center n) + (center n - 1)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      change epsilon / 2 ≤ |q I - center n|
      linarith
    calc
      (S.state n).law.toMeasure {I | epsilon ≤ |q I - 1|} ≤
          (S.state n).law.toMeasure
            {I | epsilon / 2 ≤ |q I - center n|} := measure_mono hsubset
      _ ≤ ENNReal.ofReal (boundReal n) := by
        simpa [q, center, boundReal, CanonicalSequence.V] using
          predictableQuadraticVariation_deviation_measure_le_D68
            (S.state n) (rooting n) (S.activity_lt n)
            (hretained n) (m n) (hm n) (hm0 n) hehalf

/-- D.66 accounting identity: retained mass plus omitted mass is exactly the
full canonical variance.  Both terms are evaluated under the original state. -/
theorem retained_sum_add_omitted_eq_variance_D66
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : CanonicalFirstRecoveryState G)
    (R : ActualRootedVariance.ComponentRooting G) (D : Finset V) :
    (∑ u ∈ D, R.vertexVarianceContribution (G := G) C u) +
      R.omittedVarianceContribution (G := G) C D = C.variance := by
  classical
  rw [ActualRootedVariance.ComponentRooting.omittedVarianceContribution]
  calc
    (∑ u ∈ D, R.vertexVarianceContribution (G := G) C u) +
        ∑ u ∈ ActualRootedVariance.ComponentRooting.outsideSet D,
          R.vertexVarianceContribution (G := G) C u =
        ∑ u : V, R.vertexVarianceContribution (G := G) C u := by
      simpa [ActualRootedVariance.ComponentRooting.outsideSet] using
        Finset.sum_add_sum_compl D
          (fun u => R.vertexVarianceContribution (G := G) C u)
    _ = C.variance :=
      R.sum_vertexVarianceContribution_eq_variance (G := G) C

/-- Error scale used in the D.66--D.67 diagonal selection. -/
def fellerErrorScale (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

lemma fellerErrorScale_pos (j : ℕ) : 0 < fellerErrorScale j := by
  unfold fellerErrorScale
  positivity

lemma fellerErrorScale_tendsto_zero :
    Tendsto fellerErrorScale atTop (𝓝 0) := by
  unfold fellerErrorScale
  simpa only [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private noncomputable def diagonalIndexD8
    (P : ℕ → ℕ → Prop)
    (hP : ∀ j N, ∃ n, N < n ∧ P j n) : ℕ → ℕ :=
  fun j => Nat.rec (Classical.choose (hP 0 0))
    (fun k prev => Classical.choose (hP (k + 1) prev)) j

private theorem diagonalIndexD8_spec
    (P : ℕ → ℕ → Prop)
    (hP : ∀ j N, ∃ n, N < n ∧ P j n) :
    StrictMono (diagonalIndexD8 P hP) ∧
      ∀ j, P j (diagonalIndexD8 P hP j) := by
  let φ := diagonalIndexD8 P hP
  have hsucc : ∀ j, φ j < φ (j + 1) := by
    intro j
    exact (Classical.choose_spec (hP (j + 1) (φ j))).1
  refine ⟨strictMono_nat_of_lt_succ hsucc, ?_⟩
  intro j
  cases j with
  | zero => exact (Classical.choose_spec (hP 0 0)).2
  | succ j => exact (Classical.choose_spec (hP (j + 1) (φ j))).2

/-- The concrete diagonal output of D.66--D.67 under the negation of a
macroscopic vertex contribution.  It stores only indices and thresholds; each
retained set is definitionally `retainedVarianceSet` for the original global
state at the selected index. -/
structure RetainedFellerSubsequence
    (S : CanonicalSequence)
    (rooting : ∀ n,
      ActualRootedVariance.ComponentRooting (S.graph n)) where
  subseq : ℕ → ℕ
  strictMono_subseq : StrictMono subseq
  alpha : ℕ → ℝ
  alpha_pos : ∀ j, 0 < alpha j
  alpha_le_one : ∀ j, alpha j ≤ 1
  omitted_le : ∀ j,
    (rooting (subseq j)).omittedVarianceContribution
      (G := S.graph (subseq j)) (S.state (subseq j))
      ((rooting (subseq j)).retainedVarianceSet
        (G := S.graph (subseq j)) (S.state (subseq j)) (alpha j)) ≤
      fellerErrorScale j * S.V (subseq j)
  leaf_feller_le : ∀ j,
    (((rooting (subseq j)).rootedLeaves
      (G := S.graph (subseq j))
      ((rooting (subseq j)).retainedVarianceSet
        (G := S.graph (subseq j)) (S.state (subseq j)) (alpha j))).card : ℝ) ^ 2 *
      (rooting (subseq j)).maxVertexVarianceContribution
        (G := S.graph (subseq j)) (S.state (subseq j)) /
      S.V (subseq j) ≤ fellerErrorScale j

/-- D.66--D.67 diagonal selection.  The only contradiction hypothesis is the
literal Feller condition `max_u g_n(u) / V_n → 0`. -/
theorem exists_retainedFellerSubsequence_D66_D67
    (S : CanonicalSequence)
    (rooting : ∀ n,
      ActualRootedVariance.ComponentRooting (S.graph n))
    (hFeller : Tendsto (fun n =>
      (rooting n).maxVertexVarianceContribution
        (G := S.graph n) (S.state n) / S.V n) atTop (𝓝 0)) :
    Nonempty (RetainedFellerSubsequence S rooting) := by
  classical
  have happrox : ∀ j, ∃ alpha : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ᶠ n in atTop,
        (rooting n).omittedVarianceContribution (G := S.graph n)
          (S.state n)
          ((rooting n).retainedVarianceSet (G := S.graph n)
            (S.state n) alpha) ≤ fellerErrorScale j * S.V n := by
    intro j
    exact ActualRootedVariance.ComponentRooting.finiteBranchApproximation_D5
      S rooting (fellerErrorScale j) (fellerErrorScale_pos j)
  let alpha : ℕ → ℝ := fun j => Classical.choose (happrox j)
  have halpha : ∀ j, 0 < alpha j ∧ alpha j ≤ 1 ∧
      ∀ᶠ n in atTop,
        (rooting n).omittedVarianceContribution (G := S.graph n)
          (S.state n)
          ((rooting n).retainedVarianceSet (G := S.graph n)
            (S.state n) (alpha j)) ≤ fellerErrorScale j * S.V n :=
    fun j => Classical.choose_spec (happrox j)
  let P : ℕ → ℕ → Prop := fun j n =>
    (rooting n).omittedVarianceContribution (G := S.graph n)
        (S.state n)
        ((rooting n).retainedVarianceSet (G := S.graph n)
          (S.state n) (alpha j)) ≤ fellerErrorScale j * S.V n ∧
    (1 / alpha j) ^ 2 *
        ((rooting n).maxVertexVarianceContribution
          (G := S.graph n) (S.state n) / S.V n) < fellerErrorScale j
  have hP : ∀ j N, ∃ n, N < n ∧ P j n := by
    intro j N
    have hscaled : Tendsto (fun n =>
        (1 / alpha j) ^ 2 *
          ((rooting n).maxVertexVarianceContribution
            (G := S.graph n) (S.state n) / S.V n)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hFeller)
    have hsmall : ∀ᶠ n in atTop,
        (1 / alpha j) ^ 2 *
          ((rooting n).maxVertexVarianceContribution
            (G := S.graph n) (S.state n) / S.V n) <
          fellerErrorScale j :=
      hscaled.eventually (Iio_mem_nhds (fellerErrorScale_pos j))
    have hboth : ∀ᶠ n in atTop, P j n := (halpha j).2.2.and hsmall
    have hlater : ∀ᶠ n in atTop, N < n := eventually_gt_atTop N
    obtain ⟨n, hnN, hnP⟩ := (hlater.and hboth).exists
    exact ⟨n, hnN, hnP⟩
  let phi := diagonalIndexD8 P hP
  have hphispec := diagonalIndexD8_spec P hP
  refine ⟨{
    subseq := phi
    strictMono_subseq := hphispec.1
    alpha := alpha
    alpha_pos := fun j => (halpha j).1
    alpha_le_one := fun j => (halpha j).2.1
    omitted_le := fun j => (hphispec.2 j).1
    leaf_feller_le := ?_ }⟩
  intro j
  let n := phi j
  let D := (rooting n).retainedVarianceSet
    (G := S.graph n) (S.state n) (alpha j)
  let L : ℝ := (((rooting n).rootedLeaves (G := S.graph n) D).card : ℝ)
  let M : ℝ := (rooting n).maxVertexVarianceContribution
    (G := S.graph n) (S.state n)
  have hL : L ≤ 1 / alpha j := by
    exact (rooting n).rootedLeaves_card_le_one_div_alpha
      (G := S.graph n) (S.state n) (alpha j) (halpha j).1
  have hL0 : 0 ≤ L := by positivity
  have haInv0 : 0 ≤ 1 / alpha j :=
    (one_div_pos.mpr (halpha j).1).le
  have hLsq : L ^ 2 ≤ (1 / alpha j) ^ 2 := by nlinarith
  have hratio0 : 0 ≤ M / S.V n := by
    exact div_nonneg
      ((rooting n).maxVertexVarianceContribution_pos
        (G := S.graph n) (S.state n)).le
      (S.variance_pos n).le
  change L ^ 2 * M / S.V n ≤ fellerErrorScale j
  calc
    L ^ 2 * M / S.V n = L ^ 2 * (M / S.V n) := by ring
    _ ≤ (1 / alpha j) ^ 2 * (M / S.V n) :=
      mul_le_mul_of_nonneg_right hLsq hratio0
    _ ≤ fellerErrorScale j := (hphispec.2 j).2.le

/-- D.68 specialized to the concrete D.66--D.67 diagonal.  This is the
predictable-variation input for the retained martingale array, still on the
original global canonical configuration spaces and laws. -/
theorem RetainedFellerSubsequence.predictableQuadraticVariation_D68
    {S : CanonicalSequence}
    {rooting : ∀ n,
      ActualRootedVariance.ComponentRooting (S.graph n)}
    (A : RetainedFellerSubsequence S rooting) :
    TendstoInProbabilityVarying
      (fun j => IndepFinset (S.graph (A.subseq j)))
      (fun j => (S.state (A.subseq j)).law.toMeasure)
      (fun j I =>
        (rooting (A.subseq j)).predictableQuadraticVariation
          (G := S.graph (A.subseq j)) (S.state (A.subseq j))
          ((rooting (A.subseq j)).retainedVarianceSet
            (G := S.graph (A.subseq j)) (S.state (A.subseq j)) (A.alpha j)) I /
          S.V (A.subseq j))
      atTop 1 := by
  classical
  let T : CanonicalSequence := S.subsequence A.subseq A.strictMono_subseq
  let RT : ∀ j,
      ActualRootedVariance.ComponentRooting (T.graph j) :=
    fun j => rooting (A.subseq j)
  let D : ∀ j, Finset (Fin (T.order j)) := fun j =>
    (RT j).retainedVarianceSet (G := T.graph j) (T.state j) (A.alpha j)
  let m : ℕ → ℝ := fun j =>
    (RT j).maxVertexVarianceContribution (G := T.graph j) (T.state j)
  let O : ℕ → ℝ := fun j =>
    (RT j).omittedVarianceContribution (G := T.graph j) (T.state j) (D j) /
      T.V j
  have hO0 : ∀ j, 0 ≤ O j := by
    intro j
    apply div_nonneg
    · unfold ActualRootedVariance.ComponentRooting.omittedVarianceContribution
      exact Finset.sum_nonneg fun u _ =>
        (RT j).vertexVarianceContribution_nonneg (G := T.graph j) (T.state j) u
    · exact (T.variance_pos j).le
  have hOle : ∀ j, O j ≤ fellerErrorScale j := by
    intro j
    apply (div_le_iff₀ (T.variance_pos j)).2
    simpa [T, RT, D, CanonicalSequence.V] using A.omitted_le j
  have hO : Tendsto O atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _j : ℕ => (0 : ℝ)) atTop (𝓝 0))
      fellerErrorScale_tendsto_zero
      (Filter.Eventually.of_forall hO0)
      (Filter.Eventually.of_forall hOle)
  have hmean : Tendsto (fun j =>
      (∑ u ∈ D j,
        (RT j).vertexVarianceContribution
          (G := T.graph j) (T.state j) u) / T.V j) atTop (𝓝 1) := by
    have hsub : Tendsto (fun j => 1 - O j) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hO
    simpa only [sub_zero] using hsub.congr' (Filter.Eventually.of_forall (fun j => by
      have hid := retained_sum_add_omitted_eq_variance_D66
        (T.state j) (RT j) (D j)
      have hV := T.variance_pos j
      dsimp only [O, CanonicalSequence.V]
      field_simp [hV.ne']
      linarith))
  have hfiniteLeaf : Tendsto (fun j =>
      (((RT j).rootedLeaves (G := T.graph j) (D j)).card : ℝ) ^ 2 *
        m j / T.V j) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _j : ℕ => (0 : ℝ)) atTop (𝓝 0))
      fellerErrorScale_tendsto_zero
    · exact Filter.Eventually.of_forall (fun j => by
        exact div_nonneg
          (mul_nonneg (sq_nonneg _)
            ((RT j).maxVertexVarianceContribution_pos
              (G := T.graph j) (T.state j)).le)
          (T.variance_pos j).le)
    · exact Filter.Eventually.of_forall (fun j => by
        simpa [T, RT, D, m, CanonicalSequence.V] using A.leaf_feller_le j)
  have hmain := predictableQuadraticVariation_tendstoInProbability_D68
    T RT D
    (fun j => (RT j).retainedVarianceSet_ancestorClosed
      (G := T.graph j) (T.state j) (A.alpha j))
    m
    (fun j u hu => (RT j).vertexVarianceContribution_le_max
      (G := T.graph j) (T.state j) u)
    (fun j => ((RT j).maxVertexVarianceContribution_pos
      (G := T.graph j) (T.state j)).le)
    hmean hfiniteLeaf
  simpa [T, RT, D, m, CanonicalSequence.V] using hmain

end CanonicalCompactnessWrapper.CanonicalSequence

end
end Forest
end Erdos993
