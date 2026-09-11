import Erdos993.Forest.FullDomainFourierEnvelope
import Erdos993.Forest.CanonicalCompactnessWrapper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Appendix A.4 full-domain canonical envelope

This module applies the explicit forest estimate `hardCoreLaw_characteristicModulus_le_exp_A4`
to an actual `CanonicalSequence`.  It constructs the explicit majorant

`exp (-appendixA4Constant Z * boundedScaleH (recursiveAlpha Z) (u ^ 2))`,

proves its required weighted integrability, and packages the zero-extended canonical
characteristic functions and their subsequential limit into `FullDomainEnvelope`.
No envelope hypothesis is assumed.
-/

open Filter MeasureTheory Complex Real Set
open scoped BigOperators ENNReal NNReal Topology

namespace Erdos993.Forest.AppendixA
noncomputable section

open CanonicalCompactnessWrapper
open FourierTuranCurvature

lemma FiniteLatticeLaw.centeredCharacteristic_eq_sum_rankMass_bounded
    {β : Type*} [Fintype β] (L : FiniteLatticeLaw β) (N : ℕ)
    (hstat : ∀ a, L.stat a ≤ N) (θ : ℝ) :
    L.centeredCharacteristic θ =
      ∑ k ∈ Finset.range (N + 1),
        (L.rankMass k : ℂ) * FiniteLatticeLaw.phase θ ((k : ℝ) - L.mean) := by
  unfold FiniteLatticeLaw.centeredCharacteristic FiniteLatticeLaw.rankMass
  push_cast
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp [eq_comm, Finset.mem_range, hstat a]


lemma CanonicalSequence.characteristic_eq_centeredCharacteristic
    (S : CanonicalSequence) (n : ℕ) (u : ℝ) :
    S.characteristic n u =
      (S.state n).law.centeredCharacteristic
        (u / Real.sqrt (S.V n)) := by
  rw [S.characteristic_eq_finite_sum]
  rw [FiniteLatticeLaw.centeredCharacteristic_eq_sum_rankMass_bounded
    (N := S.order n) (hstat := fun a =>
      (by
        have hh := hardCoreLaw_stat_le_order (S.graph n)
          (S.state n).activity (S.state n).activity_pos a
        simpa [CanonicalFirstRecoveryState.law] using hh))]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  unfold CanonicalSequence.standardizedRank FiniteLatticeLaw.phase
  rw [(S.state n).law_mean]
  congr 1
  push_cast
  ring


open Asymptotics

noncomputable def appendixA4Envelope (Z : ℝ) (u : ℝ) : ℝ :=
  Real.exp (-appendixA4Constant Z *
    boundedScaleH (recursiveAlpha Z) (u ^ 2))

lemma appendixA4Envelope_continuous {Z : ℝ} (hZ : 0 < Z) :
    Continuous (appendixA4Envelope Z) := by
  have hp : Continuous (fun u : ℝ => (u ^ 2) ^ recursiveAlpha Z) :=
    (continuous_id.pow 2).rpow_const (fun _ => Or.inr (recursiveAlpha_pos hZ).le)
  have hH : Continuous (fun u : ℝ =>
      boundedScaleH (recursiveAlpha Z) (u ^ 2)) :=
    (continuous_id.pow 2).min hp
  have hc : Continuous (fun _ : ℝ => appendixA4Constant Z) := continuous_const
  exact (hc.neg.mul hH).rexp

lemma appendixA4Envelope_weight_integrable {Z : ℝ} (hZ : 0 < Z) :
    Integrable (fun u : ℝ => weight u *
      appendixA4Envelope Z u) := by
  let c := appendixA4Constant Z
  let α := recursiveAlpha Z
  let p := 2 * α
  let f : ℝ → ℝ := fun u => weight u *
    appendixA4Envelope Z u
  have hc : 0 < c := by simpa [c] using appendixA4Constant_pos hZ
  have hα : 0 < α := by simpa [α] using recursiveAlpha_pos hZ
  have hα1 : α < 1 := by simpa [α] using recursiveAlpha_lt_one hZ
  have hp : 0 < p := by dsimp [p]; positivity
  have ht : Tendsto (fun x : ℝ => x ^ p) atTop atTop := tendsto_rpow_atTop hp
  have ho := (isLittleO_exp_neg_mul_rpow_atTop hc (-4 / p)).comp_tendsto ht
  have hev0 := ho.bound (show (0 : ℝ) < 1 by norm_num)
  have hev : ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧
      f x ≤ 2 * x ^ (-2 : ℝ) := by
    filter_upwards [hev0, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hxpos : 0 < x := zero_lt_one.trans_le hx1
    have hxp0 : 0 ≤ x ^ p := Real.rpow_nonneg hxpos.le p
    have hexp : Real.exp (-c * x ^ p) ≤ (x ^ p) ^ (-4 / p) := by
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_of_nonneg hxp0, abs_of_nonneg (Real.rpow_nonneg hxp0 _)] using hx
    have hnested : (x ^ p) ^ (-4 / p) = x ^ (-4 : ℝ) := by
      rw [← Real.rpow_mul hxpos.le]
      congr 1
      field_simp [hp.ne']
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    have hpowle : (x ^ 2) ^ α ≤ x ^ 2 :=
      Real.rpow_le_self_of_one_le hx2 hα1.le
    have hpoweq : (x ^ 2) ^ α = x ^ p := by
      rw [← Real.rpow_two x, ← Real.rpow_mul hxpos.le]
    have hH : boundedScaleH α (x ^ 2) = x ^ p := by
      unfold boundedScaleH
      rw [min_eq_right hpowle, hpoweq]
    have hw : weight x ≤ 2 * x ^ 2 := by
      unfold weight
      nlinarith
    constructor
    · exact hx1
    · calc
        f x = weight x * Real.exp (-c * x ^ p) := by
          simp [f, appendixA4Envelope, c, α, hH]
        _ ≤ (2 * x ^ 2) * Real.exp (-c * x ^ p) :=
          mul_le_mul_of_nonneg_right hw (Real.exp_pos _).le
        _ ≤ (2 * x ^ 2) * x ^ (-4 : ℝ) :=
          mul_le_mul_of_nonneg_left (hexp.trans_eq hnested)
            (mul_nonneg (by norm_num) (sq_nonneg x))
        _ = 2 * x ^ (-2 : ℝ) := by
          rw [← Real.rpow_two x]
          rw [mul_assoc, ← Real.rpow_add hxpos]
          norm_num
  rcases (eventually_atTop.1 hev) with ⟨M, hM⟩
  let M0 := max 1 M
  have hM0 : 0 < M0 := zero_lt_one.trans_le (le_max_left _ _)
  have htailPoint : ∀ x ∈ Set.Ioi M0, ‖f x‖ ≤ ‖2 * x ^ (-2 : ℝ)‖ := by
    intro x hx
    have hh := hM x (le_trans (le_max_right _ _) hx.le)
    have hfx0 : 0 ≤ f x := by
      exact mul_nonneg (weight_nonneg x) (Real.exp_pos _).le
    have hg0 : 0 ≤ 2 * x ^ (-2 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg (le_trans hM0.le hx.le) _)
    change |f x| ≤ |2 * x ^ (-2 : ℝ)|
    rw [abs_of_nonneg hfx0, abs_of_nonneg hg0]
    exact hh.2
  have htailDom : IntegrableOn (fun x : ℝ => 2 * x ^ (-2 : ℝ)) (Set.Ioi M0) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hM0).const_mul 2
  have hfmeas : AEStronglyMeasurable f := by
    have hA := appendixA4Envelope_continuous hZ
    exact ((continuous_const.add (continuous_id.pow 2)).mul hA).aestronglyMeasurable
  have htail : IntegrableOn f (Set.Ioi M0) := by
    apply htailDom.mono' hfmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hr := (hM x (le_trans (le_max_right _ _) hx.le)).2
    have hfx0 : 0 ≤ f x :=
      mul_nonneg (weight_nonneg x) (Real.exp_pos _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hfx0]
    exact hr
  have hcompact : IntegrableOn f (Set.Icc 0 M0) := by
    apply ContinuousOn.integrableOn_Icc
    exact ((continuous_const.add (continuous_id.pow 2)).mul
      (appendixA4Envelope_continuous hZ)).continuousOn
  have hpos : IntegrableOn f (Set.Ici 0) := by
    have hu := hcompact.union htail
    convert hu using 1
    ext x
    simp [hM0.le]
  have hneg : IntegrableOn f (Set.Iic 0) := by
    have hn : IntegrableOn (fun x => f (-x)) (Set.Iic 0) := by
      simpa using hpos.comp_neg
    apply hn.congr_fun
    · intro x hx
      simp [f, appendixA4Envelope, weight, boundedScaleH]
    · exact measurableSet_Iic
  have hall := hneg.union hpos
  simpa [f] using hall

lemma CanonicalSequence.norm_characteristic_eq_characteristicModulus
    (S : CanonicalSequence) (n : ℕ) (u : ℝ) :
    ‖S.characteristic n u‖ =
      (S.state n).law.characteristicModulus
        (u / Real.sqrt (S.V n)) := by
  rw [CanonicalSequence.characteristic_eq_centeredCharacteristic S]
  rfl

lemma CanonicalSequence.norm_characteristic_le_appendixA4Envelope
    (S : CanonicalSequence) (n : ℕ) (u : ℝ) (hu : u ∈ S.domain n) :
    ‖S.characteristic n u‖ ≤ appendixA4Envelope 27 u := by
  have hs : 0 < Real.sqrt (S.V n) := Real.sqrt_pos.2 (S.variance_pos n)
  have habs : |u| ≤ Real.pi * Real.sqrt (S.V n) := by
    rw [abs_le]
    simpa [CanonicalSequence.domain, neg_mul] using hu
  have hθ : |u / Real.sqrt (S.V n)| ≤ Real.pi := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).2 habs
  have hz27 : (S.state n).activity ≤ (27 : ℝ) := (S.activity_lt n).le
  have hA4 := hardCoreLaw_characteristicModulus_le_exp_A4
    (S.graph n) (S.state n).isForest 27 (S.state n).activity
    (u / Real.sqrt (S.V n)) (by norm_num) (S.state n).activity_pos hz27 hθ
  have hscale : (S.state n).law.variance *
      (u / Real.sqrt (S.V n)) ^ 2 = u ^ 2 := by
    change S.V n * (u / Real.sqrt (S.V n)) ^ 2 = u ^ 2
    field_simp [hs.ne']
    have hsquare : Real.sqrt (S.V n) ^ 2 = S.V n :=
      Real.sq_sqrt (S.variance_pos n).le
    rw [hsquare]
    ring
  change (S.state n).law.characteristicModulus (u / Real.sqrt (S.V n)) ≤
    Real.exp (-appendixA4Constant 27 * boundedScaleH (recursiveAlpha 27)
      ((S.state n).law.variance * (u / Real.sqrt (S.V n)) ^ 2)) at hA4
  rw [hscale] at hA4
  rw [CanonicalSequence.norm_characteristic_eq_characteristicModulus]
  simpa [appendixA4Envelope] using hA4

lemma CanonicalSequence.norm_zeroExtendedCharacteristic_le_appendixA4Envelope
    (S : CanonicalSequence) (n : ℕ) (u : ℝ) :
    ‖S.zeroExtendedCharacteristic n u‖ ≤ appendixA4Envelope 27 u := by
  by_cases hu : u ∈ S.domain n
  · rw [CanonicalSequence.zeroExtendedCharacteristic, Set.indicator_of_mem hu]
    exact CanonicalSequence.norm_characteristic_le_appendixA4Envelope S n u hu
  · rw [CanonicalSequence.zeroExtendedCharacteristic, Set.indicator_of_notMem hu, norm_zero]
    exact (Real.exp_pos _).le

lemma CanonicalSequence.zeroExtendedCharacteristic_aestronglyMeasurable
    (S : CanonicalSequence) (n : ℕ) :
    AEStronglyMeasurable (S.zeroExtendedCharacteristic n) := by
  have hc : Continuous (S.characteristic n) := by
    unfold CanonicalSequence.characteristic
    fun_prop
  have hm : Measurable (S.zeroExtendedCharacteristic n) := by
    unfold CanonicalSequence.zeroExtendedCharacteristic CanonicalSequence.domain
    exact hc.measurable.indicator measurableSet_Icc
  exact hm.aestronglyMeasurable

lemma CanonicalSequence.fullDomainEnvelope_of_appendixA4
    (S : CanonicalSequence) (ν : ProbabilityMeasure ℝ) (subseq : ℕ → ℕ)
    (hsubseq : StrictMono subseq)
    (hchar : ∀ u : ℝ, Tendsto (fun m => S.characteristic (subseq m) u) atTop
      (𝓝 (charFun ν u))) :
    CanonicalSequence.FullDomainEnvelope
      (fun m => S.zeroExtendedCharacteristic (subseq m)) (charFun ν)
      (appendixA4Envelope 27) := by
  let A := appendixA4Envelope 27
  have hpsimeas : ∀ m,
      AEStronglyMeasurable (S.zeroExtendedCharacteristic (subseq m)) :=
    fun m => CanonicalSequence.zeroExtendedCharacteristic_aestronglyMeasurable S (subseq m)
  have hphicont : Continuous (charFun (ν : Measure ℝ)) := by fun_prop
  have hphimeas : AEStronglyMeasurable (charFun (ν : Measure ℝ)) :=
    hphicont.aestronglyMeasurable
  have hwmeas : AEStronglyMeasurable weight := by
    have : Continuous weight := by unfold weight; fun_prop
    exact this.aestronglyMeasurable
  have hzeroTend : ∀ u : ℝ,
      Tendsto (fun m => S.zeroExtendedCharacteristic (subseq m) u) atTop
        (𝓝 (charFun ν u)) :=
    CanonicalSequence.zeroExtendedCharacteristic_tendsto S hsubseq hchar
  have hphiNorm : ∀ u, ‖charFun ν u‖ ≤ A u := by
    intro u
    have ht := (continuous_norm.tendsto (charFun ν u)).comp (hzeroTend u)
    exact le_of_tendsto ht (Filter.Eventually.of_forall fun m =>
      CanonicalSequence.norm_zeroExtendedCharacteristic_le_appendixA4Envelope
        S (subseq m) u)
  refine
    { A_nonneg := fun u => (Real.exp_pos _).le
      A_weight_integrable := appendixA4Envelope_weight_integrable (by norm_num)
      psi_measurable := ?_
      phi_measurable := ?_
      difference_measurable := ?_
      psi_bound := ?_
      phi_bound := ?_ }
  · intro m
    unfold weightedNorm
    exact hwmeas.mul (hpsimeas m).norm
  · unfold weightedNorm
    exact hwmeas.mul hphimeas.norm
  · intro m
    unfold weightedDifference
    exact hwmeas.mul ((hpsimeas m).sub hphimeas).norm
  · intro m u
    unfold weightedNorm
    exact mul_le_mul_of_nonneg_left
      (CanonicalSequence.norm_zeroExtendedCharacteristic_le_appendixA4Envelope
        S (subseq m) u) (weight_nonneg u)
  · intro u
    unfold weightedNorm
    exact mul_le_mul_of_nonneg_left (hphiNorm u) (weight_nonneg u)

theorem CanonicalSequence.exists_subseq_fullDomainEnvelope_A4
    (S : CanonicalSequence) :
    ∃ ν : ProbabilityMeasure ℝ, ∃ subseq : ℕ → ℕ,
      StrictMono subseq ∧
      Tendsto (S.standardizedLaw ∘ subseq) atTop (𝓝 ν) ∧
      (∀ u : ℝ, Tendsto (fun m => S.characteristic (subseq m) u) atTop
        (𝓝 (charFun ν u))) ∧
      CanonicalSequence.FullDomainEnvelope
        (fun m => S.zeroExtendedCharacteristic (subseq m)) (charFun ν)
        (appendixA4Envelope 27) := by
  obtain ⟨ν, subseq, hsubseq, hlaw, hchar⟩ := S.exists_subseq_charFun_tendsto
  exact ⟨ν, subseq, hsubseq, hlaw, hchar,
    CanonicalSequence.fullDomainEnvelope_of_appendixA4 S ν subseq hsubseq hchar⟩
