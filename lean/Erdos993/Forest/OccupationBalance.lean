import Erdos993.Forest.LargeDisplacementContribution
import Erdos993.Forest.Interfaces

open scoped BigOperators Topology
open Filter Set

namespace Erdos993
namespace ActualRootedVariance

noncomputable section

universe u

namespace ComponentRooting

open Forest

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V}

/-- Explicit exponent used in the uniform C.3 contradiction. -/
noncomputable def balanceExponent (c : ℝ) : ℝ := 28 + 12096 / c

/-- Explicit upper cap for C.18's parameter in the occupation-balance proof. -/
noncomputable def balanceChiCap (c : ℝ) : ℝ :=
  27 * Real.exp (-balanceExponent c)

/-- Explicit occupation lower bound for Theorem C.3. -/
noncomputable def occupationRho (c : ℝ) : ℝ :=
  c * balanceChiCap c / 3136

/-- Explicit nonnegative variance threshold for Theorem C.3. -/
noncomputable def occupationBalanceVarianceThreshold (c : ℝ) : ℝ := 4 / c

/-- The explicit C.18 parameter cap is positive. -/
theorem balanceChiCap_pos {c : ℝ} (_hc : 0 < c) :
    0 < balanceChiCap c := by
  unfold balanceChiCap
  exact mul_pos (by norm_num) (Real.exp_pos _)

/-- The explicit C.18 parameter cap is strictly below one. -/
theorem balanceChiCap_lt_one {c : ℝ} (hc : 0 < c) :
    balanceChiCap c < 1 := by
  let M := balanceExponent c
  have hM : 28 < M := by
    dsimp [M, balanceExponent]
    exact lt_add_of_pos_right 28 (div_pos (by norm_num) hc)
  have hexp : 27 < Real.exp M := by
    calc
      (27 : ℝ) < M + 1 := by linarith
      _ ≤ Real.exp M := Real.add_one_le_exp M
  dsimp [balanceChiCap]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_lt_one (Real.exp_pos M)).2 hexp

/-- The explicit occupation lower bound is positive for every `c > 0`. -/
theorem occupationRho_pos {c : ℝ} (hc : 0 < c) :
    0 < occupationRho c := by
  unfold occupationRho
  exact div_pos (mul_pos hc (balanceChiCap_pos hc)) (by norm_num)

/-- The explicit variance threshold is nonnegative for every `c > 0`. -/
theorem occupationBalanceVarianceThreshold_nonneg {c : ℝ} (hc : 0 < c) :
    0 ≤ occupationBalanceVarianceThreshold c := by
  unfold occupationBalanceVarianceThreshold
  exact (div_pos (by norm_num) hc).le

/-- Exact simplification of the logarithm occurring at the explicit C.18 cap. -/
theorem log_twentySeven_div_balanceChiCap {c : ℝ} (_hc : 0 < c) :
    Real.log (27 / balanceChiCap c) = balanceExponent c := by
  have hratio : 27 / balanceChiCap c = Real.exp (balanceExponent c) := by
    unfold balanceChiCap
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  rw [hratio, Real.log_exp]

/-- Quantitative scalar contradiction chosen for the explicit C.3 constants. -/
theorem balanceChiCap_suppression {c : ℝ} (hc : 0 < c) :
    112 * balanceChiCap c * Real.log (27 / balanceChiCap c) < c := by
  let M := balanceExponent c
  have hM28 : 28 < M := by
    dsimp [M, balanceExponent]
    exact lt_add_of_pos_right 28 (div_pos (by norm_num) hc)
  have hM0 : 0 < M := lt_trans (by norm_num) hM28
  have hcM : 12096 < c * M := by
    dsimp [M, balanceExponent]
    field_simp [hc.ne']
    nlinarith
  let x := M / 2
  have hx0 : 0 < x := div_pos hM0 (by norm_num)
  have hxexp : x < Real.exp x := by
    exact lt_trans (lt_add_of_pos_right x (by norm_num))
      (Real.add_one_lt_exp hx0.ne')
  have hsquare : x ^ 2 < Real.exp x ^ 2 := by
    nlinarith [Real.exp_pos x]
  have hexpquad : M ^ 2 / 4 < Real.exp M := by
    rw [show M = x + x by dsimp [x]; ring, Real.exp_add]
    dsimp only [x] at hsquare ⊢
    nlinarith
  have hpoly : 3024 * M < c * (M ^ 2 / 4) := by
    have hpositive : 0 < (c * M - 12096) * M :=
      mul_pos (sub_pos.mpr hcM) hM0
    nlinarith
  have hmul : 3024 * M < c * Real.exp M :=
    hpoly.trans (mul_lt_mul_of_pos_left hexpquad hc)
  rw [log_twentySeven_div_balanceChiCap hc]
  unfold balanceChiCap
  rw [Real.exp_neg]
  rw [show 112 * (27 * (Real.exp M)⁻¹) * M =
      (3024 * M) / Real.exp M by field_simp [Real.exp_ne_zero]; ring]
  exact (div_lt_iff₀ (Real.exp_pos M)).2 hmul

/-- The actual observables contribution is exactly the W1.1 vertex contribution. -/
theorem observables_contribution_eq_vertexVarianceContribution
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    (ComponentRooting.observables G C R).contribution v =
      R.vertexVarianceContribution (G := G) C v := by
  change R.parentAbsentProbability (G := G) C v *
      R.occupationProbability (G := G) C v *
      (1 - R.occupationProbability (G := G) C v) *
      R.conditionalMeanDifference (G := G) C v ^ 2 =
    R.parentAbsentProbability (G := G) C v *
      R.occupationProbability (G := G) C v *
      R.vacancyProbability (G := G) C v *
      R.conditionalMeanDifference (G := G) C v ^ 2
  rw [vacancyProbability_eq_one_sub_occupationProbability]

/-- Every actual contribution is nonnegative. -/
theorem vertexVarianceContribution_nonneg_actual
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    0 ≤ R.vertexVarianceContribution (G := G) C v := by
  rw [← observables_contribution_eq_vertexVarianceContribution]
  exact Forest.RootedForestObservables.contribution_nonneg
    (ComponentRooting.observables G C R) v

/-- The actual contribution is at most one quarter of the squared displacement. -/
theorem vertexVarianceContribution_le_quarter_delta_sq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    R.vertexVarianceContribution (G := G) C v ≤
      (1 / 4 : ℝ) * R.conditionalMeanDifference (G := G) C v ^ 2 := by
  unfold vertexVarianceContribution
  have ha := R.parentAbsentProbability_le_one (G := G) C v
  have hp := R.occupationProbability_nonneg (G := G) C v
  have hq := R.vacancyProbability_eq_one_sub_occupationProbability (G := G) C v
  have hprod :
      R.occupationProbability (G := G) C v *
        R.vacancyProbability (G := G) C v ≤ (1 / 4 : ℝ) := by
    rw [hq]
    nlinarith [sq_nonneg (2 * R.occupationProbability (G := G) C v - 1)]
  have hd : 0 ≤ R.conditionalMeanDifference (G := G) C v ^ 2 := sq_nonneg _
  calc
      R.parentAbsentProbability (G := G) C v *
          R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v *
          R.conditionalMeanDifference (G := G) C v ^ 2 =
        (R.parentAbsentProbability (G := G) C v *
          (R.occupationProbability (G := G) C v *
            R.vacancyProbability (G := G) C v)) *
          R.conditionalMeanDifference (G := G) C v ^ 2 := by ring
      _ ≤ (R.occupationProbability (G := G) C v *
          R.vacancyProbability (G := G) C v) *
          R.conditionalMeanDifference (G := G) C v ^ 2 := by
        have hpq : 0 ≤ R.occupationProbability (G := G) C v *
            R.vacancyProbability (G := G) C v :=
          mul_nonneg hp (R.vacancyProbability_pos (G := G) C v).le
        have hbase : R.parentAbsentProbability (G := G) C v *
            (R.occupationProbability (G := G) C v *
              R.vacancyProbability (G := G) C v) ≤
            R.occupationProbability (G := G) C v *
              R.vacancyProbability (G := G) C v := by
          simpa using mul_le_mul_of_nonneg_right ha hpq
        exact mul_le_mul_of_nonneg_right hbase hd
      _ ≤ (1 / 4 : ℝ) *
          R.conditionalMeanDifference (G := G) C v ^ 2 :=
        mul_le_mul_of_nonneg_right hprod hd

/-- The actual contribution is bounded by `p_u * Δ_u²`. -/
theorem vertexVarianceContribution_le_occupation_mul_delta_sq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V) :
    R.vertexVarianceContribution (G := G) C v ≤
      R.occupationProbability (G := G) C v *
        R.conditionalMeanDifference (G := G) C v ^ 2 := by
  unfold vertexVarianceContribution
  let a := R.parentAbsentProbability (G := G) C v
  let p := R.occupationProbability (G := G) C v
  let q := R.vacancyProbability (G := G) C v
  let d := R.conditionalMeanDifference (G := G) C v
  have ha0 : 0 ≤ a := R.parentAbsentProbability_nonneg (G := G) C v
  have ha1 : a ≤ 1 := R.parentAbsentProbability_le_one (G := G) C v
  have hp0 : 0 ≤ p := R.occupationProbability_nonneg (G := G) C v
  have hq0 : 0 ≤ q := (R.vacancyProbability_pos (G := G) C v).le
  have hq1 : q ≤ 1 := by
    have hpq := R.occupationProbability_add_vacancyProbability (G := G) C v
    change p + q = 1 at hpq
    linarith
  have hap : a * p ≤ p := by
    simpa using mul_le_of_le_one_left hp0 ha1
  have hap0 : 0 ≤ a * p := mul_nonneg ha0 hp0
  have hapq : a * p * q ≤ p :=
    (mul_le_of_le_one_right hap0 hq1).trans hap
  exact mul_le_mul_of_nonneg_right hapq (sq_nonneg d)

/-- A macroscopic actual contribution forces the lower displacement inequality
in Theorem C.3. -/
theorem four_mul_c_variance_le_delta_sq
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    4 * c * C.variance ≤
      R.conditionalMeanDifference (G := G) C v ^ 2 := by
  have hquarter := R.vertexVarianceContribution_le_quarter_delta_sq
    (G := G) C v
  nlinarith

/-- Above the explicit threshold, half the absolute displacement is at least two. -/
theorem two_le_half_abs_conditionalMeanDifference
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c)
    (hV : occupationBalanceVarianceThreshold c ≤ C.variance)
    (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    2 ≤ |R.conditionalMeanDifference (G := G) C v| / 2 := by
  let d := R.conditionalMeanDifference (G := G) C v
  have hdelta := R.four_mul_c_variance_le_delta_sq (G := G) C v hmac
  have hcv : 4 ≤ c * C.variance := by
    unfold occupationBalanceVarianceThreshold at hV
    have hfour : 4 ≤ C.variance * c := (div_le_iff₀ hc).mp hV
    nlinarith
  have hsq : 16 ≤ d ^ 2 := by
    change 4 * c * C.variance ≤ d ^ 2 at hdelta
    nlinarith
  have habs : 4 ≤ |d| := by
    nlinarith [sq_abs d, abs_nonneg d]
  exact by nlinarith

/-- A counted vertex contributes its full actual `g(u)` to the global `G(b)`. -/
theorem vertexVarianceContribution_le_G_of_counted
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G)
    {b : ℝ} (v : V)
    (hv : b < |R.conditionalMeanDifference (G := G) C v|) :
    R.vertexVarianceContribution (G := G) C v ≤ ComponentRooting.G C R b := by
  classical
  unfold ComponentRooting.G
  have hsingle :
      (if b < |R.conditionalMeanDifference (G := G) C v| then
        R.vertexVarianceContribution (G := G) C v else 0) ≤
      ∑ u, if b < |R.conditionalMeanDifference (G := G) C u| then
        R.vertexVarianceContribution (G := G) C u else 0 := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun u => if b < |R.conditionalMeanDifference (G := G) C u| then
        R.vertexVarianceContribution (G := G) C u else 0)
      (fun u _ => by
        change 0 ≤ (if b < |R.conditionalMeanDifference (G := G) C u| then
          R.vertexVarianceContribution (G := G) C u else 0)
        split_ifs
        · exact R.vertexVarianceContribution_nonneg (G := G) C u
        · norm_num)
      (Finset.mem_univ v)
  simpa [hv] using hsingle

/-- If `g(u) ≥ cV`, then C.18's parameter at `b=|Δ_u|/2` is controlled by
`3136 p_u / c`. -/
theorem chi_half_abs_le_occupation
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c)
    (hb : 0 < |R.conditionalMeanDifference (G := G) C v| / 2)
    (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    chi C (|R.conditionalMeanDifference (G := G) C v| / 2) ≤
      3136 * R.occupationProbability (G := G) C v / c := by
  let p := R.occupationProbability (G := G) C v
  let d := R.conditionalMeanDifference (G := G) C v
  have hcpd : c * C.variance ≤ p * d ^ 2 :=
    hmac.trans (R.vertexVarianceContribution_le_occupation_mul_delta_sq
      (G := G) C v)
  have hVpd : C.variance ≤ p * d ^ 2 / c := by
    apply (le_div_iff₀ hc).2
    simpa [mul_comm] using hcpd
  unfold chi
  apply (div_le_iff₀ (sq_pos_of_pos hb)).2
  calc
    784 * C.variance ≤ 784 * (p * d ^ 2 / c) :=
      mul_le_mul_of_nonneg_left hVpd (by norm_num)
    _ = (3136 * p / c) * (|d| / 2) ^ 2 := by
      rw [div_pow, sq_abs]
      ring

/-- The explicit uniform occupation lower bound, obtained by applying the global
C.18 theorem to `b = |Δ_u|/2`.  No local first-recovery state is introduced. -/
theorem occupationRho_le_occupationProbability
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c) (hz : C.activity < 27)
    (hV : occupationBalanceVarianceThreshold c ≤ C.variance)
    (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    occupationRho c ≤ R.occupationProbability (G := G) C v := by
  by_contra hnot
  have hp_lt : R.occupationProbability (G := G) C v < occupationRho c :=
    lt_of_not_ge hnot
  let d := R.conditionalMeanDifference (G := G) C v
  let b := |d| / 2
  have hb2 : 2 ≤ b := by
    dsimp [b, d]
    exact R.two_le_half_abs_conditionalMeanDifference (G := G) C v hc hV hmac
  have hb : 1 < b := lt_of_lt_of_le (by norm_num) hb2
  have hchiBound : chi C b ≤
      3136 * R.occupationProbability (G := G) C v / c := by
    dsimp [b, d]
    exact R.chi_half_abs_le_occupation (G := G) C v hc
      (lt_of_lt_of_le (by norm_num) hb2) hmac
  have hscaled_lt :
      3136 * R.occupationProbability (G := G) C v / c < balanceChiCap c := by
    calc
      3136 * R.occupationProbability (G := G) C v / c <
          3136 * occupationRho c / c := by
        exact div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left hp_lt (by norm_num)) hc
      _ = balanceChiCap c := by
        unfold occupationRho
        field_simp [hc.ne']
  have hchiCap : chi C b < balanceChiCap c := hchiBound.trans_lt hscaled_lt
  have hchiOne : chi C b < 1 := hchiCap.trans (balanceChiCap_lt_one hc)
  have hVpos : 0 < C.variance := canonicalFirstRecovery_variance_pos C
  have hchiPos : 0 < chi C b := by
    unfold chi
    exact div_pos (mul_pos (by norm_num) hVpos) (sq_pos_of_pos (lt_trans (by norm_num) hb))
  have hmono :
      chi C b * Real.log (27 / chi C b) ≤
        balanceChiCap c * Real.log (27 / balanceChiCap c) :=
    mul_log_twentySeven_div_mono hchiPos hchiCap.le (balanceChiCap_lt_one hc)
  have hlogPos : 0 < Real.log (27 / chi C b) := Real.log_pos <| by
    apply (lt_div_iff₀ hchiPos).2
    nlinarith
  have hfnonneg :
      0 ≤ chi C b * Real.log (27 / chi C b) :=
    mul_nonneg hchiPos.le hlogPos.le
  have hratio0 : 0 ≤ b / (b - 1) := by
    exact div_nonneg (le_trans (by norm_num) hb2) (by linarith)
  have hratio2 : b / (b - 1) ≤ 2 := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  have hratioSq : (b / (b - 1)) ^ 2 ≤ 4 := by
    have hprod : 0 ≤ (2 - b / (b - 1)) * (2 + b / (b - 1)) :=
      mul_nonneg (sub_nonneg.mpr hratio2) (add_nonneg (by norm_num) hratio0)
    nlinarith
  have hC18 := R.C18 (G := G) C b hz hb hchiOne
  have hC18small : ComponentRooting.G C R b / C.variance < c := by
    calc
      ComponentRooting.G C R b / C.variance ≤
          (b / (b - 1)) ^ 2 * 28 *
            (chi C b * Real.log (27 / chi C b)) := by
        simpa only [mul_assoc] using hC18
      _ ≤ 112 * (chi C b * Real.log (27 / chi C b)) := by
        have hcoef : (b / (b - 1)) ^ 2 * 28 ≤ 112 := by
          nlinarith
        exact mul_le_mul_of_nonneg_right hcoef hfnonneg
      _ ≤ 112 * (balanceChiCap c *
          Real.log (27 / balanceChiCap c)) :=
        mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ = 112 * balanceChiCap c *
          Real.log (27 / balanceChiCap c) := by ring
      _ < c := balanceChiCap_suppression hc
  have hcounted : b < |d| := by
    dsimp [b] at hb2 ⊢
    nlinarith
  have hgG : R.vertexVarianceContribution (G := G) C v ≤
      ComponentRooting.G C R b := by
    dsimp [b, d]
    exact R.vertexVarianceContribution_le_G_of_counted (G := G) C v hcounted
  have hc_le_Gdiv : c ≤ ComponentRooting.G C R b / C.variance := by
    apply (le_div_iff₀ hVpos).2
    exact hmac.trans hgG
  exact (not_lt_of_ge hc_le_Gdiv) hC18small

/-- The actual coefficient `a_u p_u q_u` is at least `ρ(c)/784` once the
occupation lower bound holds. -/
theorem occupationRho_div_784_le_coefficient
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c) (hz : C.activity < 27)
    (hoccupation : occupationRho c ≤
      R.occupationProbability (G := G) C v) :
    occupationRho c / 784 ≤
      R.parentAbsentProbability (G := G) C v *
        R.occupationProbability (G := G) C v *
        R.vacancyProbability (G := G) C v := by
  let rho := occupationRho c
  let a := R.parentAbsentProbability (G := G) C v
  let p := R.occupationProbability (G := G) C v
  let q := R.vacancyProbability (G := G) C v
  have hrho : 0 < rho := occupationRho_pos hc
  have ha : (1 / 28 : ℝ) < a :=
    R.one_div_twentyEight_lt_parentAbsentProbability (G := G) C hz v
  have hq : (1 / 28 : ℝ) < q :=
    R.one_div_twentyEight_lt_vacancyProbability (G := G) C hz v
  have hp : 0 < p := lt_of_lt_of_le hrho hoccupation
  have hrhop : rho / 28 ≤ (1 / 28 : ℝ) * p := by
    dsimp [rho, p] at hoccupation ⊢
    nlinarith
  have hap : rho / 28 < a * p :=
    hrhop.trans_lt (mul_lt_mul_of_pos_right ha hp)
  have hleft : rho / 784 < (rho / 28) * q := by
    have hrho28 : 0 < rho / 28 := div_pos hrho (by norm_num)
    have hleft0 := mul_lt_mul_of_pos_left hq hrho28
    calc
      rho / 784 = (rho / 28) * (1 / 28 : ℝ) := by ring
      _ < (rho / 28) * q := hleft0
  have hright : (rho / 28) * q < a * p * q :=
    mul_lt_mul_of_pos_right hap (lt_trans (by norm_num) hq)
  exact (hleft.trans hright).le

/-- The upper displacement inequality in Theorem C.3 for actual rooted forests. -/
theorem conditionalMeanDifference_sq_le_784_div_rho_mul_variance
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c) (hz : C.activity < 27)
    (hV : occupationBalanceVarianceThreshold c ≤ C.variance)
    (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    R.conditionalMeanDifference (G := G) C v ^ 2 ≤
      (784 / occupationRho c) * C.variance := by
  let rho := occupationRho c
  let a := R.parentAbsentProbability (G := G) C v
  let p := R.occupationProbability (G := G) C v
  let q := R.vacancyProbability (G := G) C v
  let d := R.conditionalMeanDifference (G := G) C v
  have hrho : 0 < rho := occupationRho_pos hc
  have hoccupation : rho ≤ p := by
    dsimp [rho, p]
    exact R.occupationRho_le_occupationProbability (G := G) C v hc hz hV hmac
  have hcoefficient : rho / 784 ≤ a * p * q := by
    dsimp [rho, a, p, q] at hoccupation ⊢
    exact R.occupationRho_div_784_le_coefficient (G := G) C v hc hz hoccupation
  have hsmall : (rho / 784) * d ^ 2 ≤ C.variance := by
    calc
      (rho / 784) * d ^ 2 ≤ (a * p * q) * d ^ 2 :=
        mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg d)
      _ = R.vertexVarianceContribution (G := G) C v := by
        unfold vertexVarianceContribution
        rfl
      _ ≤ C.variance := R.vertexVarianceContribution_le_variance (G := G) C v
  have hquot : d ^ 2 ≤ C.variance / (rho / 784) := by
    apply (le_div_iff₀ (div_pos hrho (by norm_num))).2
    simpa [mul_comm] using hsmall
  change d ^ 2 ≤ (784 / rho) * C.variance
  calc
    d ^ 2 ≤ C.variance / (rho / 784) := hquot
    _ = (784 / rho) * C.variance := by
      field_simp [hrho.ne']

/-- Exact actual-rooted occupation-balance theorem with all three requested
bounds and explicit constants. -/
theorem occupationBalance_actual
    (C : CanonicalFirstRecoveryState G) (R : ComponentRooting G) (v : V)
    {c : ℝ} (hc : 0 < c) (hz : C.activity < 27)
    (hV : occupationBalanceVarianceThreshold c ≤ C.variance)
    (hmac : c * C.variance ≤
      R.vertexVarianceContribution (G := G) C v) :
    occupationRho c ≤ R.occupationProbability (G := G) C v ∧
      4 * c * C.variance ≤
        R.conditionalMeanDifference (G := G) C v ^ 2 ∧
      R.conditionalMeanDifference (G := G) C v ^ 2 ≤
        (784 / occupationRho c) * C.variance := by
  exact ⟨R.occupationRho_le_occupationProbability (G := G) C v hc hz hV hmac,
    R.four_mul_c_variance_le_delta_sq (G := G) C v hmac,
    R.conditionalMeanDifference_sq_le_784_div_rho_mul_variance
      (G := G) C v hc hz hV hmac⟩

end ComponentRooting

/-- The actual W3.1 interface. Its realization is an actual component rooting,
and its sole analytic input is the already global actual-rooted C.18 theorem. -/
noncomputable def actualOccupationBalanceInterface :
    Forest.OccupationBalanceInterface (actualRootedForestFamily : Forest.RootedForestFamily) where
  rho := ComponentRooting.occupationRho
  varianceThreshold := ComponentRooting.occupationBalanceVarianceThreshold
  rho_pos := by
    intro c hc
    exact ComponentRooting.occupationRho_pos hc
  varianceThreshold_nonneg := by
    intro c hc
    exact ComponentRooting.occupationBalanceVarianceThreshold_nonneg hc
  conclusion := by
    intro V inst G C R u c hc hz hV hmac
    have hmac' : c * C.variance ≤
        R.vertexVarianceContribution (G := G) C u := by
      rw [← ComponentRooting.observables_contribution_eq_vertexVarianceContribution]
      exact hmac
    change ComponentRooting.occupationRho c ≤
        R.occupationProbability (G := G) C u ∧
      4 * c * C.variance ≤
        R.conditionalMeanDifference (G := G) C u ^ 2 ∧
      R.conditionalMeanDifference (G := G) C u ^ 2 ≤
        (784 / ComponentRooting.occupationRho c) * C.variance
    exact R.occupationBalance_actual (G := G) C u hc hz hV hmac'

end
end ActualRootedVariance
end Erdos993
