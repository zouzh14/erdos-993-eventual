import Erdos993.Forest.Interfaces

/-!
# Actual sublinear displacement on finite rooted trees

This file proves the raw rooted-tree estimate from Lemma 5.1 using a local,
self-contained forest/tree representation.  Sibling order carries no
mathematical information.  No rooted-variance construction is imported.
-/

namespace Erdos993
namespace Forest

noncomputable section

open scoped BigOperators

mutual
/-- A self-contained finite rooted tree. -/
inductive LocalRootedTree where
  | node (children : LocalRootedForest) : LocalRootedTree

/-- A finite ordered list of rooted trees (the children of a node). -/
inductive LocalRootedForest where
  | nil : LocalRootedForest
  | cons (head : LocalRootedTree) (tail : LocalRootedForest) : LocalRootedForest
end

namespace LocalRootedTree

/-- Convert the local forest spine to an ordinary list. -/
def forestToList : LocalRootedForest → List LocalRootedTree
  | .nil => []
  | .cons t ts => t :: forestToList ts

mutual
/-- Number of vertices in a local tree. -/
def order : LocalRootedTree → ℕ
  | .node children => 1 + forestOrder children

/-- Number of vertices in a local forest. -/
def forestOrder : LocalRootedForest → ℕ
  | .nil => 0
  | .cons t ts => order t + forestOrder ts
end

/-- List version of forest order. -/
theorem forestOrder_eq_sum : ∀ f : LocalRootedForest,
    forestOrder f = ((forestToList f).map order).sum
  | .nil => by rfl
  | .cons t ts => by simp [forestOrder, forestToList, forestOrder_eq_sum ts]

mutual
/-- Hard-core subtree ratio `R_x`. -/
def message (z : ℝ) : LocalRootedTree → ℝ
  | .node children => z * vacancyProduct z children

/-- Product of child vacancy probabilities. -/
def vacancyProduct (z : ℝ) : LocalRootedForest → ℝ
  | .nil => 1
  | .cons t ts => (1 - message z t / (1 + message z t)) * vacancyProduct z ts
end

/-- Conditional occupation probability `p_x = R_x/(1+R_x)`. -/
def occupation (z : ℝ) (t : LocalRootedTree) : ℝ :=
  message z t / (1 + message z t)

mutual
/-- Conditional-mean displacement. -/
def displacement (z : ℝ) : LocalRootedTree → ℝ
  | .node children => 1 - displacementSum z children

/-- Sum of child terms `p_y Delta_y`. -/
def displacementSum (z : ℝ) : LocalRootedForest → ℝ
  | .nil => 0
  | .cons t ts => occupation z t * displacement z t + displacementSum z ts
end

mutual
/-- `(depth, path product)` for every descendant. -/
def weightedPaths (z : ℝ) : LocalRootedTree → List (ℕ × ℝ)
  | .node children => (0, 1) :: forestWeightedPaths z children

/-- Weighted paths in every child subtree, shifted across the child edge. -/
def forestWeightedPaths (z : ℝ) : LocalRootedForest → List (ℕ × ℝ)
  | .nil => []
  | .cons t ts =>
      (weightedPaths z t).map (fun dw =>
        (dw.1 + 1, occupation z t * dw.2)) ++ forestWeightedPaths z ts
end

/-- Requested `Delta_x = 1 - sum_child p_y Delta_y` recursion. -/
theorem displacement_recursion (z : ℝ) (children : LocalRootedForest) :
    displacement z (.node children) = 1 - displacementSum z children := by
  rfl

/-- Vacancy is the reciprocal of `1+R`. -/
theorem one_sub_occupation {z : ℝ} (t : LocalRootedTree)
    (h : 1 + message z t ≠ 0) :
    1 - occupation z t = 1 / (1 + message z t) := by
  unfold occupation
  field_simp
  ring

mutual
/-- Positivity and strict unit upper bound for occupation probabilities. -/
theorem message_pos_occupation_bounds {z : ℝ} (hz : 0 < z) :
    ∀ t : LocalRootedTree,
      0 < message z t ∧ 0 < occupation z t ∧ occupation z t < 1
  | .node children => by
      have hv := vacancyProduct_pos hz children
      have hm : 0 < message z (.node children) := mul_pos hz hv
      have hd : 0 < 1 + message z (.node children) := by linarith
      refine ⟨hm, div_pos hm hd, ?_⟩
      exact (div_lt_one hd).mpr (by linarith)

/-- The child-vacancy product is positive. -/
theorem vacancyProduct_pos {z : ℝ} (hz : 0 < z) :
    ∀ f : LocalRootedForest, 0 < vacancyProduct z f
  | .nil => by simp [vacancyProduct]
  | .cons t ts => by
      have ht := (message_pos_occupation_bounds hz t).2.2
      have hts := vacancyProduct_pos hz ts
      simp only [vacancyProduct]
      change 0 < (1 - occupation z t) * vacancyProduct z ts
      exact mul_pos (sub_pos.mpr ht) hts
end

mutual
/-- Every message is at most the common activity. -/
theorem message_le_activity {z : ℝ} (hz : 0 < z) :
    ∀ t : LocalRootedTree, message z t ≤ z
  | .node children => by
      have hp := vacancyProduct_le_one hz children
      have hv := (vacancyProduct_pos hz children).le
      simp only [message]
      nlinarith

/-- Every child-vacancy product is at most one. -/
theorem vacancyProduct_le_one {z : ℝ} (hz : 0 < z) :
    ∀ f : LocalRootedForest, vacancyProduct z f ≤ 1
  | .nil => by simp [vacancyProduct]
  | .cons t ts => by
      have ht := message_pos_occupation_bounds hz t
      have hts := vacancyProduct_le_one hz ts
      have hts0 := (vacancyProduct_pos hz ts).le
      simp only [vacancyProduct]
      change (1 - occupation z t) * vacancyProduct z ts ≤ 1
      have hvac1 : 1 - occupation z t ≤ 1 := by linarith [ht.2.1]
      exact (mul_le_mul_of_nonneg_right hvac1 hts0).trans (by simpa using hts)
end

/-- Requested uniform message/occupation upper bound `p_x ≤ Z/(1+Z)`. -/
theorem occupation_le_ceiling {z Z : ℝ} (hz : 0 < z) (hzZ : z ≤ Z)
    (t : LocalRootedTree) : occupation z t ≤ Z / (1 + Z) := by
  have hmpos := (message_pos_occupation_bounds hz t).1
  have hmZ : message z t ≤ Z := (message_le_activity hz t).trans hzZ
  have hZ : 0 < Z := lt_of_lt_of_le hz hzZ
  unfold occupation
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

mutual
/-- Weighted paths enumerate exactly the vertices of a tree. -/
theorem weightedPaths_length : ∀ (z : ℝ) (t : LocalRootedTree),
    (weightedPaths z t).length = order t
  | z, .node children => by
      simp only [weightedPaths, order, List.length_cons]
      rw [forestWeightedPaths_length z children]
      omega

/-- Forest version of exact path enumeration. -/
theorem forestWeightedPaths_length : ∀ (z : ℝ) (f : LocalRootedForest),
    (forestWeightedPaths z f).length = forestOrder f
  | _, .nil => by rfl
  | z, .cons t ts => by
      simp [forestWeightedPaths, forestOrder, weightedPaths_length z t,
        forestWeightedPaths_length z ts]
end

/-- Signed alternating sum over all weighted paths. -/
def alternatingPathSum (z : ℝ) (t : LocalRootedTree) : ℝ :=
  ((weightedPaths z t).map (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).sum

/-- Forest signed sum, used to prove the exact expansion. -/
def forestAlternatingPathSum (z : ℝ) (f : LocalRootedForest) : ℝ :=
  ((forestWeightedPaths z f).map (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).sum

mutual
/-- Exact signed alternating path-product expansion. -/
theorem displacement_eq_alternatingPathSum : ∀ (z : ℝ) (t : LocalRootedTree),
    displacement z t = alternatingPathSum z t
  | z, .node children => by
      simp only [displacement, alternatingPathSum, weightedPaths, List.map_cons,
        List.sum_cons, pow_zero, one_mul]
      have hforest := forestAlternatingPathSum_eq z children
      unfold forestAlternatingPathSum at hforest
      rw [hforest]
      ring

/-- Forest auxiliary for the exact alternating expansion. -/
theorem forestAlternatingPathSum_eq : ∀ (z : ℝ) (f : LocalRootedForest),
    forestAlternatingPathSum z f = -displacementSum z f
  | _, .nil => by simp [forestAlternatingPathSum, forestWeightedPaths, displacementSum]
  | z, .cons t ts => by
      simp only [forestAlternatingPathSum, forestWeightedPaths, List.map_append,
        List.sum_append, displacementSum]
      have htail := forestAlternatingPathSum_eq z ts
      unfold forestAlternatingPathSum at htail
      rw [htail]
      have hmap :
          (((weightedPaths z t).map (fun dw =>
              (dw.1 + 1, occupation z t * dw.2))).map
            (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).sum =
          -occupation z t * alternatingPathSum z t := by
        rw [List.map_map]
        change
          ((weightedPaths z t).map (fun dw =>
            (-1 : ℝ) ^ (dw.1 + 1) * (occupation z t * dw.2))).sum =
          -occupation z t * alternatingPathSum z t
        rw [show ((weightedPaths z t).map (fun dw =>
            (-1 : ℝ) ^ (dw.1 + 1) * (occupation z t * dw.2))).sum =
            ((weightedPaths z t).map (fun dw =>
              (-occupation z t) * ((-1 : ℝ) ^ dw.1 * dw.2))).sum by
          apply congrArg List.sum
          apply List.map_congr_left
          intro dw hdw
          ring]
        rw [List.sum_map_mul_left]
        change (-occupation z t) *
          ((weightedPaths z t).map (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).sum =
          -occupation z t * alternatingPathSum z t
        rfl
      rw [hmap, ← displacement_eq_alternatingPathSum z t]
      ring
end

mutual
/-- Every path weight is positive and at most `bar^depth` when all
occupation probabilities are at most `bar`. -/
theorem weightedPath_bounds {z bar : ℝ} (hbar0 : 0 ≤ bar)
    (hocc : ∀ t : LocalRootedTree, 0 < occupation z t ∧ occupation z t ≤ bar) :
    ∀ (t : LocalRootedTree) (d : ℕ) (w : ℝ),
      (d, w) ∈ weightedPaths z t → 0 < w ∧ w ≤ bar ^ d
  | .node children, d, w, h => by
      simp only [weightedPaths, List.mem_cons] at h
      rcases h with hroot | hforest
      · simp only [Prod.mk.injEq] at hroot
        rcases hroot with ⟨rfl, rfl⟩
        simp
      · exact forestWeightedPath_bounds hbar0 hocc children d w hforest

/-- Forest auxiliary for path-weight bounds. -/
theorem forestWeightedPath_bounds {z bar : ℝ} (hbar0 : 0 ≤ bar)
    (hocc : ∀ t : LocalRootedTree, 0 < occupation z t ∧ occupation z t ≤ bar) :
    ∀ (f : LocalRootedForest) (d : ℕ) (w : ℝ),
      (d, w) ∈ forestWeightedPaths z f → 0 < w ∧ w ≤ bar ^ d
  | .nil, _, _, h => by simp [forestWeightedPaths] at h
  | .cons t ts, d, w, h => by
      simp only [forestWeightedPaths, List.mem_append, List.mem_map] at h
      rcases h with ⟨dw, hdw, hEq⟩ | htail
      · rcases dw with ⟨d', w'⟩
        simp only [Prod.mk.injEq] at hEq
        rcases hEq with ⟨rfl, rfl⟩
        have hw := weightedPath_bounds hbar0 hocc t d' w' hdw
        have hp := hocc t
        refine ⟨mul_pos hp.1 hw.1, ?_⟩
        rw [pow_succ']
        exact mul_le_mul hp.2 hw.2 hw.1.le (hp.1.le.trans hp.2)
      · exact forestWeightedPath_bounds hbar0 hocc ts d w htail
end

private theorem abs_list_sum_le_sum_abs : ∀ l : List ℝ,
    |l.sum| ≤ (l.map abs).sum
  | [] => by simp
  | x :: xs => by
      simp only [List.sum_cons, List.map_cons]
      exact (abs_add_le x xs.sum).trans
        (add_le_add_right (abs_list_sum_le_sum_abs xs) |x|)

/-- Equation (5.6): absolute displacement is at most total path weight. -/
theorem abs_displacement_le_weightSum {z : ℝ} (hz : 0 < z)
    (t : LocalRootedTree) :
    |displacement z t| ≤ ((weightedPaths z t).map Prod.snd).sum := by
  rw [displacement_eq_alternatingPathSum]
  unfold alternatingPathSum
  calc
    |((weightedPaths z t).map (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).sum| ≤
        (((weightedPaths z t).map (fun dw => (-1 : ℝ) ^ dw.1 * dw.2)).map abs).sum :=
      abs_list_sum_le_sum_abs _
    _ = ((weightedPaths z t).map Prod.snd).sum := by
      rw [List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro dw hdw
      have hw := weightedPath_bounds (show (0 : ℝ) ≤ 1 by norm_num)
        (fun s => ⟨(message_pos_occupation_bounds hz s).2.1,
          (message_pos_occupation_bounds hz s).2.2.le⟩) t dw.1 dw.2 hdw
      simp [abs_mul, abs_pow, hw.1.le]

/-! ## Logarithmic message identity and branching budget -/

private theorem list_prod_pos {l : List ℝ} (h : ∀ x ∈ l, 0 < x) :
    0 < l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.prod_cons]
      exact mul_pos (h a (by simp)) (ih (by
        intro x hx
        exact h x (by simp [hx])))

private theorem sum_neg_map (l : List ℝ) :
    (l.map (fun x => -x)).sum = -l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, add_comm]

/-- The logarithm of the vacancy product is the sum of the logarithms of its
factors.  This is the finite-product part of (5.7). -/
theorem log_vacancyProduct {z : ℝ} (hz : 0 < z) :
    ∀ f : LocalRootedForest,
      Real.log (vacancyProduct z f) =
        ((forestToList f).map (fun t => Real.log (1 - occupation z t))).sum
  | .nil => by simp [vacancyProduct, forestToList]
  | .cons t ts => by
      have hm : 0 < message z t := (message_pos_occupation_bounds hz t).1
      have ht : 0 < 1 - occupation z t := by
        rw [one_sub_occupation t (by nlinarith)]
        exact one_div_pos.mpr (by nlinarith)
      have hts : 0 < vacancyProduct z ts := vacancyProduct_pos hz ts
      rw [vacancyProduct, forestToList, List.map_cons, List.sum_cons]
      change Real.log ((1 - occupation z t) * vacancyProduct z ts) = _
      rw [Real.log_mul ht.ne' hts.ne', log_vacancyProduct hz ts]

/-- Equation (5.3) after applying logarithms. -/
theorem logarithmic_message_identity {z : ℝ} (hz : 0 < z)
    (children : LocalRootedForest) :
    Real.log (message z (.node children)) = Real.log z +
      ((forestToList children).map
        (fun t => Real.log (1 - occupation z t))).sum := by
  have hv : 0 < vacancyProduct z children := vacancyProduct_pos hz children
  rw [message, Real.log_mul hz.ne' hv.ne', log_vacancyProduct hz children]

/-- The exact logarithmic child-budget identity used in (5.7). -/
theorem logarithmic_child_budget {z : ℝ} (hz : 0 < z)
    (children : LocalRootedForest) :
    ((forestToList children).map
      (fun t => -Real.log (1 - occupation z t))).sum =
      Real.log (z / message z (.node children)) := by
  have hm : 0 < message z (.node children) :=
    (message_pos_occupation_bounds hz _).1
  rw [Real.log_div hz.ne' hm.ne', logarithmic_message_identity hz]
  calc
    ((forestToList children).map
      (fun t => -Real.log (1 - occupation z t))).sum =
        -((forestToList children).map
          (fun t => Real.log (1 - occupation z t))).sum := by
      simpa only [List.map_map, Function.comp_apply] using
        sum_neg_map ((forestToList children).map
          (fun t => Real.log (1 - occupation z t)))
    _ = Real.log z - (Real.log z +
        ((forestToList children).map
          (fun t => Real.log (1 - occupation z t))).sum) := by ring

/-- Occupation is bounded above by its positive message. -/
theorem occupation_le_message {z : ℝ} (hz : 0 < z)
    (t : LocalRootedTree) : occupation z t ≤ message z t := by
  have hm := (message_pos_occupation_bounds hz t).1
  unfold occupation
  have hd : 0 < 1 + message z t := by positivity
  apply (div_le_iff₀ hd).2
  nlinarith

private theorem tau_mul_filter_length_le_sum (l : List ℝ) (tau : ℝ)
    (h0 : ∀ x ∈ l, 0 ≤ x) :
    tau * ((l.filter (fun x => tau ≤ x)).length : ℝ) ≤ l.sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      have ih' := ih (fun y hy => h0 y (by simp [hy]))
      by_cases hx : tau ≤ x
      · rw [List.filter_cons_of_pos (by simpa using hx)]
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith
      · rw [List.filter_cons_of_neg (by simpa using hx)]
        simp only [List.sum_cons]
        have hx0 := h0 x (by simp)
        nlinarith

private theorem occupation_le_neg_log_vacancy {z : ℝ} (hz : 0 < z)
    (t : LocalRootedTree) :
    occupation z t ≤ -Real.log (1 - occupation z t) := by
  have hp := (message_pos_occupation_bounds hz t).2
  have hq : 0 < 1 - occupation z t := sub_pos.mpr hp.2
  have hlog := Real.log_le_sub_one_of_pos hq
  linarith

/-- A parent whose occupation is at least `sigma` has uniformly bounded total
child occupation.  This is a coarse, division-only consequence of (5.7). -/
theorem child_occupation_sum_le {z Z sigma : ℝ} (hz : 0 < z)
    (hzZ : z ≤ Z) (hsigma : 0 < sigma) (children : LocalRootedForest)
    (hparent : sigma ≤ occupation z (.node children)) :
    ((forestToList children).map (occupation z)).sum ≤ Z / sigma := by
  have hnonneg : ∀ t ∈ forestToList children, 0 ≤ occupation z t := by
    intro t ht
    exact (message_pos_occupation_bounds hz t).2.1.le
  have hloglower :
      ((forestToList children).map (occupation z)).sum ≤
        ((forestToList children).map
          (fun t => -Real.log (1 - occupation z t))).sum :=
    List.sum_le_sum (fun t ht => occupation_le_neg_log_vacancy hz t)
  have hmpos : 0 < message z (.node children) :=
    (message_pos_occupation_bounds hz _).1
  have hmsigma : sigma ≤ message z (.node children) :=
    hparent.trans (occupation_le_message hz _)
  have hratio : z / message z (.node children) ≤ Z / sigma := by
    have hZ0 : 0 ≤ Z := hz.le.trans hzZ
    exact div_le_div₀ hZ0 hzZ hsigma hmsigma
  have hratio_pos : 0 < z / message z (.node children) := div_pos hz hmpos
  have hlogratio : Real.log (z / message z (.node children)) ≤ Z / sigma :=
    (Real.log_le_sub_one_of_pos hratio_pos).trans (by linarith)
  rw [logarithmic_child_budget hz] at hloglower
  exact hloglower.trans hlogratio

/-- A numerical large-child bound.  Unlike the eventual displacement theorem,
this helper follows directly from the logarithmic identity. -/
theorem exists_large_child_bound (Z sigma tau : ℝ)
    (_hZ : 0 < Z) (hsigma : 0 < sigma) (htau : 0 < tau) :
    ∃ M : ℕ, ∀ (z : ℝ) (children : LocalRootedForest),
      0 < z → z ≤ Z → sigma ≤ occupation z (.node children) →
      ((forestToList children).filter
        (fun t => tau ≤ occupation z t)).length ≤ M := by
  obtain ⟨M, hM⟩ := exists_nat_ge (Z / sigma / tau)
  refine ⟨M, ?_⟩
  intro z children hz hzZ hparent
  have hcountsum := tau_mul_filter_length_le_sum
    ((forestToList children).map (occupation z)) tau (by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact (message_pos_occupation_bounds hz t).2.1.le)
  have hsum := child_occupation_sum_le hz hzZ hsigma children hparent
  have hreal :
      (((forestToList children).filter
        (fun t => tau ≤ occupation z t)).length : ℝ) ≤ Z / sigma / tau := by
    have hmapfilter :
        (((forestToList children).map (occupation z)).filter
          (fun p => tau ≤ p)).length =
        ((forestToList children).filter
          (fun t => tau ≤ occupation z t)).length := by
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
        List.countP_map]
      rfl
    rw [hmapfilter] at hcountsum
    exact (le_div_iff₀ htau).2 (by simpa [mul_comm] using hcountsum.trans hsum)
  exact_mod_cast hreal.trans hM

/-! ## Finite weighted-path counting -/

/-- Children selected by a predicate. -/
def childCount (P : LocalRootedTree → Prop) [DecidablePred P]
    (f : LocalRootedForest) : ℕ :=
  ((forestToList f).filter P).length

/-- A deliberately coarse geometric bound `1 + M + ... + M^D`. -/
def geometricBound (M : ℕ) : ℕ → ℕ
  | 0 => 1
  | D + 1 => 1 + M * geometricBound M D

mutual
/-- Number of predicate-good descendants through depth `D`, including the
current root. -/
def goodTreeCount (P : LocalRootedTree → Prop) [DecidablePred P] :
    ℕ → LocalRootedTree → ℕ
  | 0, _ => 1
  | D + 1, .node f => 1 + goodForestCount P D f

/-- Forest auxiliary for `goodTreeCount`. -/
def goodForestCount (P : LocalRootedTree → Prop) [DecidablePred P] :
    ℕ → LocalRootedForest → ℕ
  | _, .nil => 0
  | D, .cons t ts =>
      (if P t then goodTreeCount P D t else 0) + goodForestCount P D ts
end

mutual
/-- Predicate-good bounded-depth trees obey the geometric branching bound. -/
theorem goodTreeCount_le_geometricBound (P : LocalRootedTree → Prop)
    [DecidablePred P] (M : ℕ)
    (hchild : ∀ f, P (.node f) → childCount P f ≤ M) :
    ∀ D t, P t → goodTreeCount P D t ≤ geometricBound M D
  | 0, t, ht => by simp [goodTreeCount, geometricBound]
  | D + 1, .node f, ht => by
      simp only [goodTreeCount, geometricBound]
      have hf := goodForestCount_le_count_mul P M hchild D f
      calc
        1 + goodForestCount P D f ≤
            1 + childCount P f * geometricBound M D :=
          Nat.add_le_add_left hf 1
        _ ≤ 1 + M * geometricBound M D := by
          gcongr
          exact hchild f ht

/-- Forest auxiliary for the geometric branching bound. -/
theorem goodForestCount_le_count_mul (P : LocalRootedTree → Prop)
    [DecidablePred P] (M : ℕ)
    (hchild : ∀ f, P (.node f) → childCount P f ≤ M) :
    ∀ D f,
      goodForestCount P D f ≤ childCount P f * geometricBound M D
  | D, .nil => by simp [goodForestCount, childCount, forestToList]
  | D, .cons t ts => by
      simp only [goodForestCount]
      have htail := goodForestCount_le_count_mul P M hchild D ts
      by_cases ht : P t
      · simp only [if_pos ht]
        have hhead := goodTreeCount_le_geometricBound P M hchild D t ht
        have hc : childCount P (.cons t ts) = 1 + childCount P ts := by
          simp [childCount, forestToList, ht, Nat.add_comm]
        rw [hc, Nat.add_mul, one_mul]
        exact Nat.add_le_add hhead htail
      · simp only [if_neg ht, zero_add]
        have hc : childCount P (.cons t ts) = childCount P ts := by
          simp [childCount, forestToList, ht]
        rw [hc]
        exact htail
end

mutual
/-- Number of paths whose weight, after multiplication by an incoming weight
`a`, is at least `tau`. -/
def scaledLargeTreeCount (z tau a : ℝ) : LocalRootedTree → ℕ
  | .node f => (if tau ≤ a then 1 else 0) + scaledLargeForestCount z tau a f

/-- Forest auxiliary for `scaledLargeTreeCount`. -/
def scaledLargeForestCount (z tau a : ℝ) : LocalRootedForest → ℕ
  | .nil => 0
  | .cons t ts =>
      scaledLargeTreeCount z tau (a * occupation z t) t +
        scaledLargeForestCount z tau a ts
end

private theorem filter_mapped_weight_length (l : List (ℕ × ℝ))
    (tau a p : ℝ) :
    ((l.map (fun dw => (dw.1 + 1, p * dw.2))).filter
      (fun dw => tau ≤ a * dw.2)).length =
    (l.filter (fun dw => tau ≤ (a * p) * dw.2)).length := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    List.countP_map]
  apply congrArg (fun q => List.countP q l)
  funext dw
  simp only [Function.comp_apply, mul_assoc]

mutual
/-- The recursive count is exactly the filter count on `weightedPaths`. -/
theorem scaledLargeTreeCount_eq_filter : ∀ (z tau a : ℝ)
    (t : LocalRootedTree),
    scaledLargeTreeCount z tau a t =
      ((weightedPaths z t).filter (fun dw => tau ≤ a * dw.2)).length
  | z, tau, a, .node f => by
      simp only [scaledLargeTreeCount, weightedPaths, List.filter_cons]
      rw [scaledLargeForestCount_eq_filter z tau a f]
      by_cases h : tau ≤ a
      · simp [h, Nat.add_comm]
      · simp [h]

/-- Forest version of the exact filter-count identity. -/
theorem scaledLargeForestCount_eq_filter : ∀ (z tau a : ℝ)
    (f : LocalRootedForest),
    scaledLargeForestCount z tau a f =
      ((forestWeightedPaths z f).filter
        (fun dw => tau ≤ a * dw.2)).length
  | z, tau, a, .nil => by
      simp [scaledLargeForestCount, forestWeightedPaths]
  | z, tau, a, .cons t ts => by
      rw [scaledLargeForestCount, forestWeightedPaths, List.filter_append,
        List.length_append, scaledLargeTreeCount_eq_filter,
        scaledLargeForestCount_eq_filter]
      rw [filter_mapped_weight_length]
end

mutual
/-- If the incoming weight is already below `tau`, all later scaled path
weights are below `tau` because every occupation probability is at most one. -/
theorem scaledLargeTreeCount_eq_zero_of_lt {z tau : ℝ}
    (hocc : ∀ t : LocalRootedTree, 0 ≤ occupation z t ∧ occupation z t ≤ 1) :
    ∀ (a : ℝ) (t : LocalRootedTree), 0 ≤ a → a < tau →
      scaledLargeTreeCount z tau a t = 0
  | a, .node f, ha0, hat => by
      rw [scaledLargeTreeCount]
      simp only [if_neg (not_le.mpr hat), zero_add]
      exact scaledLargeForestCount_eq_zero_of_lt hocc a f ha0 hat

/-- Forest auxiliary for the below-threshold zero lemma. -/
theorem scaledLargeForestCount_eq_zero_of_lt {z tau : ℝ}
    (hocc : ∀ t : LocalRootedTree, 0 ≤ occupation z t ∧ occupation z t ≤ 1) :
    ∀ (a : ℝ) (f : LocalRootedForest), 0 ≤ a → a < tau →
      scaledLargeForestCount z tau a f = 0
  | a, .nil, ha0, hat => by simp [scaledLargeForestCount]
  | a, .cons t ts, ha0, hat => by
      rw [scaledLargeForestCount,
        scaledLargeTreeCount_eq_zero_of_lt hocc (a * occupation z t) t
          (mul_nonneg ha0 (hocc t).1)
          (lt_of_le_of_lt (mul_le_of_le_one_right ha0 (hocc t).2) hat),
        scaledLargeForestCount_eq_zero_of_lt hocc a ts ha0 hat]
end

mutual
/-- If `a * bar^(D+1) < tau`, all scaled-large paths occur among the
`tau`-occupied descendants through depth `D`. -/
theorem scaledLargeTreeCount_le_goodTreeCount {z tau bar : ℝ}
    (hbar0 : 0 ≤ bar) (hbar1 : bar ≤ 1)
    (hocc : ∀ t : LocalRootedTree,
      0 ≤ occupation z t ∧ occupation z t ≤ bar) :
    ∀ (D : ℕ) (a : ℝ) (t : LocalRootedTree),
      0 ≤ a → a ≤ 1 → a * bar ^ D < tau →
      scaledLargeTreeCount z tau a t ≤
        (if tau ≤ a then
          goodTreeCount (fun s => tau ≤ occupation z s) D t else 0)
  | 0, a, .node f, ha0, ha1, hpower => by
      by_cases hta : tau ≤ a
      · have hat : a < tau := by simpa using hpower
        exact (not_lt_of_ge hta hat).elim
      · rw [scaledLargeTreeCount_eq_zero_of_lt
            (fun s => ⟨(hocc s).1, (hocc s).2.trans hbar1⟩)
            a (.node f) ha0 (lt_of_not_ge hta)]
        simp [hta]
  | D + 1, a, .node f, ha0, ha1, hpower => by
      by_cases hta : tau ≤ a
      · rw [scaledLargeTreeCount, if_pos hta, goodTreeCount, if_pos hta]
        simp only [Nat.add_le_add_iff_left]
        exact scaledLargeForestCount_le_goodForestCount hbar0 hbar1 hocc
          D a f ha0 ha1 hpower
      · rw [scaledLargeTreeCount_eq_zero_of_lt
            (fun s => ⟨(hocc s).1, (hocc s).2.trans hbar1⟩)
            a (.node f) ha0 (lt_of_not_ge hta)]
        simp [hta]

/-- Forest auxiliary for the bounded-depth count comparison. -/
theorem scaledLargeForestCount_le_goodForestCount {z tau bar : ℝ}
    (hbar0 : 0 ≤ bar) (hbar1 : bar ≤ 1)
    (hocc : ∀ t : LocalRootedTree,
      0 ≤ occupation z t ∧ occupation z t ≤ bar) :
    ∀ (D : ℕ) (a : ℝ) (f : LocalRootedForest),
      0 ≤ a → a ≤ 1 → a * bar ^ (D + 1) < tau →
      scaledLargeForestCount z tau a f ≤
        goodForestCount (fun s => tau ≤ occupation z s) D f
  | D, a, .nil, ha0, ha1, hpower => by
      simp [scaledLargeForestCount, goodForestCount]
  | D, a, .cons t ts, ha0, ha1, hpower => by
      rw [scaledLargeForestCount, goodForestCount]
      have hp := hocc t
      have htail := scaledLargeForestCount_le_goodForestCount
        hbar0 hbar1 hocc D a ts ha0 ha1 hpower
      by_cases hpt : tau ≤ occupation z t
      · rw [if_pos hpt]
        have hap0 : 0 ≤ a * occupation z t := mul_nonneg ha0 hp.1
        have hap1 : a * occupation z t ≤ 1 :=
          (mul_le_of_le_one_right ha0 (hp.2.trans hbar1)).trans ha1
        have happower :
            (a * occupation z t) * bar ^ D < tau := by
          calc
            (a * occupation z t) * bar ^ D ≤
                (a * bar) * bar ^ D :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hp.2 ha0)
                (pow_nonneg hbar0 _)
            _ = a * bar ^ (D + 1) := by
              rw [pow_succ]
              ring
            _ < tau := hpower
        by_cases hapat : tau ≤ a * occupation z t
        · exact Nat.add_le_add
            (by
              simpa [hapat] using
                scaledLargeTreeCount_le_goodTreeCount hbar0 hbar1 hocc
                  D (a * occupation z t) t hap0 hap1 happower)
            htail
        · rw [scaledLargeTreeCount_eq_zero_of_lt
            (fun s => ⟨(hocc s).1, (hocc s).2.trans hbar1⟩)
            (a * occupation z t) t hap0 (lt_of_not_ge hapat), zero_add]
          exact htail.trans (Nat.le_add_left _ _)
      · rw [if_neg hpt, zero_add]
        have hchildlt : a * occupation z t < tau :=
          lt_of_le_of_lt (mul_le_of_le_one_left hp.1 ha1) (lt_of_not_ge hpt)
        rw [scaledLargeTreeCount_eq_zero_of_lt
          (fun s => ⟨(hocc s).1, (hocc s).2.trans hbar1⟩)
          (a * occupation z t) t (mul_nonneg ha0 hp.1) hchildlt,
          zero_add]
        exact htail
end

/-- Uniform threshold/count bound for all root-to-descendant path weights. -/
theorem large_path_count_uniform {Z rho tau : ℝ}
    (hZ : 0 < Z) (hrho : 0 < rho) (htau : 0 < tau) :
    ∃ K : ℕ, ∀ (z : ℝ) (t : LocalRootedTree),
      0 < z → z ≤ Z → rho ≤ occupation z t →
      ((weightedPaths z t).filter (fun dw => tau ≤ dw.2)).length ≤ K := by
  let bar : ℝ := Z / (1 + Z)
  have hbar0 : 0 ≤ bar := (div_nonneg hZ.le (by positivity))
  have hbar1 : bar < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one htau hbar1
  obtain ⟨Mroot, hMroot⟩ :=
    exists_large_child_bound Z rho tau hZ hrho htau
  obtain ⟨Mchild, hMchild⟩ :=
    exists_large_child_bound Z tau tau hZ htau htau
  refine ⟨1 + Mroot * geometricBound Mchild D, ?_⟩
  intro z t hz hzZ hroot
  let P : LocalRootedTree → Prop := fun s => tau ≤ occupation z s
  have hocc : ∀ s : LocalRootedTree,
      0 ≤ occupation z s ∧ occupation z s ≤ bar := by
    intro s
    constructor
    · exact (message_pos_occupation_bounds hz s).2.1.le
    · exact occupation_le_ceiling hz hzZ s
  have hchild : ∀ f, P (.node f) → childCount P f ≤ Mchild := by
    intro f hf
    exact hMchild z f hz hzZ hf
  have hpower : (1 : ℝ) * bar ^ (D + 1) < tau := by
    have hbarpow0 : 0 ≤ bar ^ D := pow_nonneg hbar0 _
    calc
      (1 : ℝ) * bar ^ (D + 1) = bar ^ D * bar := by
        rw [pow_succ]
        ring
      _ ≤ bar ^ D * 1 := mul_le_mul_of_nonneg_left hbar1.le hbarpow0
      _ < tau := by simpa using hD
  rcases t with ⟨f⟩
  have hfilter := scaledLargeTreeCount_eq_filter z tau 1 (.node f)
  have hfilter' :
      scaledLargeTreeCount z tau 1 (.node f) =
        ((weightedPaths z (.node f)).filter (fun dw => tau ≤ dw.2)).length := by
    simpa using hfilter
  by_cases htau1 : tau ≤ 1
  · rw [scaledLargeTreeCount, if_pos htau1] at hfilter'
    rw [← hfilter']
    have hforest := scaledLargeForestCount_le_goodForestCount
      hbar0 hbar1.le hocc D 1 f (by norm_num) (by norm_num) hpower
    have hgood := goodForestCount_le_count_mul P Mchild hchild D f
    have hrootchild : childCount P f ≤ Mroot := hMroot z f hz hzZ hroot
    exact Nat.add_le_add_left
      (hforest.trans (hgood.trans (Nat.mul_le_mul_right _ hrootchild))) 1
  · have hzero := scaledLargeTreeCount_eq_zero_of_lt
      (fun s => ⟨(hocc s).1, (hocc s).2.trans hbar1.le⟩)
      1 (.node f) (by norm_num) (lt_of_not_ge htau1)
    rw [hzero] at hfilter'
    rw [← hfilter']
    omega

/-- Exact depth bound: any path with weight at least `tau` has depth at most
some `D` depending only on `Z` and `tau`. -/
theorem exists_large_path_depth_bound {Z tau : ℝ}
    (hZ : 0 < Z) (htau : 0 < tau) :
    ∃ D : ℕ, ∀ (z : ℝ) (t : LocalRootedTree) (dw : ℕ × ℝ),
      0 < z → z ≤ Z → dw ∈ weightedPaths z t → tau ≤ dw.2 → dw.1 ≤ D := by
  let bar : ℝ := Z / (1 + Z)
  have hbar0 : 0 ≤ bar := div_nonneg hZ.le (by positivity)
  have hbar1 : bar < 1 := by
    apply (div_lt_one (by positivity)).2
    linarith
  obtain ⟨D, hD⟩ := exists_pow_lt_of_lt_one htau hbar1
  refine ⟨D, ?_⟩
  intro z t dw hz hzZ hdw hlarge
  have hweight := weightedPath_bounds hbar0
    (fun s => ⟨(message_pos_occupation_bounds hz s).2.1,
      occupation_le_ceiling hz hzZ s⟩) t dw.1 dw.2 hdw
  by_contra hnot
  have hsucc : D + 1 ≤ dw.1 := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hsucc
  have hpowle : bar ^ dw.1 ≤ bar ^ (D + 1) := by
    rw [hk, pow_add]
    have hk1 : bar ^ k ≤ 1 := pow_le_one₀ hbar0 hbar1.le
    exact mul_le_of_le_one_right (pow_nonneg hbar0 _) hk1
  have hpowstep : bar ^ (D + 1) ≤ bar ^ D := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hbar0 _) hbar1.le
  linarith
theorem weightedPaths_weight_nonneg {z : ℝ} (hz : 0 < z)
    (t : LocalRootedTree) (dw : ℕ × ℝ) (hdw : dw ∈ weightedPaths z t) :
    0 ≤ dw.2 := by
  exact (weightedPath_bounds (show (0 : ℝ) ≤ 1 by norm_num)
    (fun s => ⟨(message_pos_occupation_bounds hz s).2.1,
      (message_pos_occupation_bounds hz s).2.2.le⟩)
    t dw.1 dw.2 hdw).1.le

/-- Splitting path weights at `tau` bounds the absolute weighted sum by a
large-path count plus `tau` times the number of vertices. -/
theorem path_weight_sum_le_count_add {z tau : ℝ} (hz : 0 < z)
    (htau : 0 ≤ tau) (t : LocalRootedTree) :
    ((weightedPaths z t).map (fun dw => dw.2)).sum ≤
      (((weightedPaths z t).filter (fun dw => tau ≤ dw.2)).length : ℝ) +
        tau * order t := by
  let l := weightedPaths z t
  have hle_each : ∀ dw ∈ l,
      dw.2 ≤ (if tau ≤ dw.2 then 1 else tau) := by
    intro dw hdw
    have hw0 := weightedPaths_weight_nonneg hz t dw hdw
    have hw1 := (weightedPath_bounds (show (0 : ℝ) ≤ 1 by norm_num)
      (fun s => ⟨(message_pos_occupation_bounds hz s).2.1,
        (message_pos_occupation_bounds hz s).2.2.le⟩)
      t dw.1 dw.2 hdw).2
    by_cases h : tau ≤ dw.2
    · have hwone : dw.2 ≤ 1 := by simpa using hw1
      simp [h, hwone]
    · simp [h, le_of_not_ge h]
  calc
    (l.map (fun dw => dw.2)).sum ≤
        (l.map (fun dw => if tau ≤ dw.2 then 1 else tau)).sum :=
      List.sum_le_sum (by simpa using hle_each)
    _ ≤ (((l.filter (fun dw => tau ≤ dw.2)).length : ℕ) : ℝ) +
          tau * (l.length : ℝ) := by
      induction l with
      | nil => simp
      | cons dw l ih =>
          by_cases h : tau ≤ dw.2
          · have hfilter :
                ((dw :: l).filter (fun q => tau ≤ q.2)).length =
                  1 + (l.filter (fun q => tau ≤ q.2)).length := by
              simp [h, Nat.add_comm]
            rw [hfilter]
            simp only [List.map_cons, if_pos h, List.sum_cons,
              List.length_cons, Nat.cast_add, Nat.cast_one]
            nlinarith
          · have hfilter :
                ((dw :: l).filter (fun q => tau ≤ q.2)).length =
                  (l.filter (fun q => tau ≤ q.2)).length := by
              simp [h]
            rw [hfilter]
            simp only [List.map_cons, if_neg h, List.sum_cons,
              List.length_cons, Nat.cast_add, Nat.cast_one]
            nlinarith
    _ = (((weightedPaths z t).filter (fun dw => tau ≤ dw.2)).length : ℝ) +
          tau * order t := by
      simp only [l]
      rw [weightedPaths_length]

/-- Uniform epsilon-plus-constant displacement theorem. The constant is
uniform over all finite rooted trees and all `0 < z ≤ Z`. -/
theorem exists_uniform_displacement_bound {Z rho eta : ℝ}
    (hZ : 0 < Z) (hrho : 0 < rho) (heta : 0 < eta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (z : ℝ) (t : LocalRootedTree),
      0 < z → z ≤ Z → rho ≤ occupation z t →
      |displacement z t| ≤ eta * order t + K := by
  obtain ⟨K, hK⟩ := large_path_count_uniform hZ hrho heta
  refine ⟨K, Nat.cast_nonneg _, ?_⟩
  intro z t hz hzZ hroot
  have habs : |displacement z t| ≤
      ((weightedPaths z t).map (fun dw => dw.2)).sum :=
    abs_displacement_le_weightSum hz t
  calc
    |displacement z t| ≤
        ((weightedPaths z t).map (fun dw => dw.2)).sum := habs
    _ ≤ (((weightedPaths z t).filter (fun dw => eta ≤ dw.2)).length : ℝ) +
          eta * order t := path_weight_sum_le_count_add hz heta.le t
    _ ≤ K + eta * order t := by
      gcongr
      exact_mod_cast hK z t hz hzZ hroot
    _ = eta * order t + K := by ring

universe u

/-- Fieldwise-equality-only adapter data for a later instantiation of
`SublinearConditionalMeanInterface`. No instance is created in this unit. -/
structure SublinearConditionalMeanFieldwiseAdapterSpec
    (F : RootedForestFamily.{u}) where
  localTree :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G),
      F.Realization C → V → LocalRootedTree
  occupationProbability_eq :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
      (F.observables C r).occupationProbability v =
        occupation C.activity (localTree C r v)
  conditionalMeanDifference_eq :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
      (F.observables C r).conditionalMeanDifference v =
        displacement C.activity (localTree C r v)
  subtreeOrder_eq :
    ∀ {V : Type u} [Fintype V] {G : SimpleGraph V}
      (C : CanonicalFirstRecoveryState G) (r : F.Realization C) (v : V),
      (F.observables C r).subtreeOrder v = order (localTree C r v)

end LocalRootedTree

end
end Forest
end Erdos993
