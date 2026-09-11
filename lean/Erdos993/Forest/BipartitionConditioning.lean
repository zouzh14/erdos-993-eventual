import Erdos993.Forest.CanonicalLaw
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Actual bipartition conditioning for the finite hard-core law

This file proves Appendix C (C.40)--(C.43) directly from the finite hard-core
weights in `Forest.Specification`.  A conditional fiber contains only an exact
color-class occupation environment and free vertices on the opposite color;
it contains no canonical or first-recovery data.
-/

namespace Erdos993
namespace Forest

noncomputable section
open scoped BigOperators

universe u

/-! ## Finite Bernoulli subset sums -/

namespace BernoulliSubset

variable {α : Type u} [DecidableEq α]

/-- Product Bernoulli weight of a subset `t ⊆ s`. -/
def weight (s t : Finset α) (p : ℝ) : ℝ :=
  p ^ t.card * (1 - p) ^ (s.card - t.card)

private theorem weight_not_insert (s t : Finset α) (a : α) (p : ℝ)
    (ha : a ∉ s) (ht : t ⊆ s) :
    weight (insert a s) t p = (1 - p) * weight s t p := by
  have hat : a ∉ t := fun h => ha (ht h)
  have hcard : t.card ≤ s.card := Finset.card_le_card ht
  have hsub : s.card + 1 - t.card = (s.card - t.card) + 1 := by omega
  simp only [weight, Finset.card_insert_of_notMem ha]
  rw [hsub, pow_succ]
  ring

private theorem weight_insert (s t : Finset α) (a : α) (p : ℝ)
    (ha : a ∉ s) (ht : t ⊆ s) :
    weight (insert a s) (insert a t) p = p * weight s t p := by
  have hat : a ∉ t := fun h => ha (ht h)
  have hcard : t.card ≤ s.card := Finset.card_le_card ht
  have hsub : s.card + 1 - (t.card + 1) = s.card - t.card := by omega
  simp only [weight, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem hat]
  rw [hsub, pow_succ]
  ring

/-- Splitting the weighted powerset sum according to whether a new point occurs. -/
theorem sum_insert (s : Finset α) (a : α) (p : ℝ) (f : Finset α → ℝ)
    (ha : a ∉ s) :
    ∑ t ∈ (insert a s).powerset, weight (insert a s) t p * f t =
      (1 - p) * (∑ t ∈ s.powerset, weight s t p * f t) +
        p * (∑ t ∈ s.powerset, weight s t p * f (insert a t)) := by
  rw [Finset.sum_powerset_insert ha]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [weight_not_insert s t a p ha (Finset.mem_powerset.mp ht)]
    ring
  · apply Finset.sum_congr rfl
    intro t ht
    rw [weight_insert s t a p ha (Finset.mem_powerset.mp ht)]
    ring

/-- Product Bernoulli weights are normalized, by an explicit finite powerset sum. -/
theorem sum_weight (s : Finset α) (p : ℝ) :
    ∑ t ∈ s.powerset, weight s t p = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert a s ha ih =>
      calc
        (∑ t ∈ (insert a s).powerset, weight (insert a s) t p) =
            (1 - p) * (∑ t ∈ s.powerset, weight s t p) +
              p * (∑ t ∈ s.powerset, weight s t p) := by
                simpa only [mul_one] using sum_insert s a p (fun _ => 1) ha
        _ = 1 := by rw [ih]; ring

/-- First moment of the cardinality under the finite product Bernoulli law. -/
theorem sum_weight_card (s : Finset α) (p : ℝ) :
    ∑ t ∈ s.powerset, weight s t p * (t.card : ℝ) = p * (s.card : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert a s ha ih =>
      rw [sum_insert s a p (fun t => (t.card : ℝ)) ha]
      have hins : ∀ t ∈ s.powerset,
          ((insert a t).card : ℝ) = (t.card : ℝ) + 1 := by
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [Finset.card_insert_of_notMem hat]
        norm_num
      calc
        (1 - p) * (∑ t ∈ s.powerset, weight s t p * (t.card : ℝ)) +
            p * (∑ t ∈ s.powerset,
              weight s t p * ((insert a t).card : ℝ)) =
          (1 - p) * (p * (s.card : ℝ)) +
            p * (p * (s.card : ℝ) + 1) := by
              rw [ih]
              congr 2
              calc
                (∑ t ∈ s.powerset,
                    weight s t p * ((insert a t).card : ℝ)) =
                  ∑ t ∈ s.powerset, (weight s t p * (t.card : ℝ) +
                    weight s t p) := by
                      apply Finset.sum_congr rfl
                      intro t ht
                      rw [hins t ht]
                      ring
                _ = p * (s.card : ℝ) + 1 := by
                      rw [Finset.sum_add_distrib, ih, sum_weight]
        _ = p * ((insert a s).card : ℝ) := by
          rw [Finset.card_insert_of_notMem ha]
          push_cast
          ring

/-- Second raw moment of the cardinality under the product Bernoulli law. -/
theorem sum_weight_card_sq (s : Finset α) (p : ℝ) :
    ∑ t ∈ s.powerset, weight s t p * (t.card : ℝ) ^ 2 =
      p * (1 - p) * (s.card : ℝ) + (p * (s.card : ℝ)) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | @insert a s ha ih =>
      rw [sum_insert s a p (fun t => (t.card : ℝ) ^ 2) ha]
      have hins : ∀ t ∈ s.powerset,
          ((insert a t).card : ℝ) = (t.card : ℝ) + 1 := by
        intro t ht
        have hat : a ∉ t := fun h => ha ((Finset.mem_powerset.mp ht) h)
        rw [Finset.card_insert_of_notMem hat]
        norm_num
      have hshift :
          (∑ t ∈ s.powerset,
              weight s t p * ((insert a t).card : ℝ) ^ 2) =
            (p * (1 - p) * (s.card : ℝ) + (p * (s.card : ℝ)) ^ 2) +
              2 * (p * (s.card : ℝ)) + 1 := by
        calc
          _ = ∑ t ∈ s.powerset,
              (weight s t p * (t.card : ℝ) ^ 2 +
                2 * (weight s t p * (t.card : ℝ)) + weight s t p) := by
                  apply Finset.sum_congr rfl
                  intro t ht
                  rw [hins t ht]
                  ring
          _ = _ := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ih,
              ← Finset.mul_sum, sum_weight_card, sum_weight]
      rw [ih, hshift, Finset.card_insert_of_notMem ha]
      push_cast
      ring

/-- Centered second moment, obtained from the two preceding finite sums. -/
theorem sum_weight_variance (s : Finset α) (p : ℝ) :
    ∑ t ∈ s.powerset,
        weight s t p * ((t.card : ℝ) - p * (s.card : ℝ)) ^ 2 =
      p * (1 - p) * (s.card : ℝ) := by
  calc
    _ = ∑ t ∈ s.powerset,
        (weight s t p * (t.card : ℝ) ^ 2 -
          2 * (p * (s.card : ℝ)) * (weight s t p * (t.card : ℝ)) +
          (p * (s.card : ℝ)) ^ 2 * weight s t p) := by
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = (∑ t ∈ s.powerset, weight s t p * (t.card : ℝ) ^ 2) -
        2 * (p * (s.card : ℝ)) *
          (∑ t ∈ s.powerset, weight s t p * (t.card : ℝ)) +
        (p * (s.card : ℝ)) ^ 2 *
          (∑ t ∈ s.powerset, weight s t p) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ = _ := by
      rw [sum_weight_card_sq, sum_weight_card, sum_weight]
      ring

/-- The rank-`k` Bernoulli mass is the binomial coefficient times one product weight. -/
theorem sum_weight_card_eq (s : Finset α) (p : ℝ) (k : ℕ) :
    ∑ t ∈ s.powerset with t.card = k, weight s t p =
      (s.card.choose k : ℝ) * p ^ k * (1 - p) ^ (s.card - k) := by
  classical
  calc
    _ = ∑ t ∈ s.powersetCard k, weight s t p := by
      apply Finset.sum_congr
      · ext t
        simp [Finset.mem_powersetCard]
      · intro t ht
        rfl
    _ = ∑ _t ∈ s.powersetCard k,
        (p ^ k * (1 - p) ^ (s.card - k)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [weight, (Finset.mem_powersetCard.mp ht).2]
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
      push_cast
      ring

end BernoulliSubset

/-! ## A genuine finite bipartition and exact color environments -/

/-- The two named sides used in Appendix C. -/
inductive BipartitionSide
  | left
  | right
  deriving DecidableEq

open BipartitionSide

namespace BipartitionSide

/-- The opposite named side. -/
def opposite : BipartitionSide → BipartitionSide
  | .left => .right
  | .right => .left

@[simp] theorem opposite_left : opposite .left = .right := rfl
@[simp] theorem opposite_right : opposite .right = .left := rfl
@[simp] theorem opposite_opposite (c : BipartitionSide) : opposite (opposite c) = c := by
  cases c <;> rfl

end BipartitionSide

/-- A genuine bipartition of all vertices.  `IsBipartiteWith` says every edge
crosses the two disjoint classes; `cover` also assigns isolated vertices. -/
structure FiniteBipartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  left : Finset V
  right : Finset V
  crosses : G.IsBipartiteWith (left : Set V) (right : Set V)
  cover : left ∪ right = Finset.univ

namespace FiniteBipartition

variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Selected color class. -/
def side (P : FiniteBipartition G) : BipartitionSide → Finset V
  | .left => P.left
  | .right => P.right

/-- Opposite color class. -/
def other (P : FiniteBipartition G) : BipartitionSide → Finset V
  | .left => P.right
  | .right => P.left

@[simp] theorem side_left (P : FiniteBipartition G) :
    P.side .left = P.left := rfl
@[simp] theorem side_right (P : FiniteBipartition G) :
    P.side .right = P.right := rfl
@[simp] theorem other_left (P : FiniteBipartition G) :
    P.other .left = P.right := rfl
@[simp] theorem other_right (P : FiniteBipartition G) :
    P.other .right = P.left := rfl
@[simp] theorem other_eq_side_opposite (P : FiniteBipartition G)
    (c : BipartitionSide) :
    P.other c = P.side (BipartitionSide.opposite c) := by
  cases c <;> rfl

/-- The two selected sides are disjoint. -/
theorem disjoint_side_other (P : FiniteBipartition G) (c : BipartitionSide) :
    Disjoint (P.side c) (P.other c) := by
  rw [Finset.disjoint_left]
  intro v hv ho
  cases c with
  | left => exact (Set.disjoint_left.mp P.crosses.disjoint) hv ho
  | right => exact (Set.disjoint_left.mp P.crosses.disjoint) ho hv

/-- The selected and opposite sides cover every vertex. -/
theorem union_side_other (P : FiniteBipartition G) (c : BipartitionSide) :
    P.side c ∪ P.other c = Finset.univ := by
  cases c with
  | left => exact P.cover
  | right => simpa [Finset.union_comm] using P.cover

/-- No edge has both endpoints in one color class. -/
theorem not_adj_of_mem_side (P : FiniteBipartition G) (c : BipartitionSide)
    {v w : V} (hv : v ∈ P.side c) (hw : w ∈ P.side c) : ¬G.Adj v w := by
  intro hadj
  rcases P.crosses.mem_of_adj hadj with h | h
  · cases c with
    | left => exact (Set.disjoint_left.mp P.crosses.disjoint) hw h.2
    | right => exact (Set.disjoint_left.mp P.crosses.disjoint) h.1 hv
  · cases c with
    | left => exact (Set.disjoint_left.mp P.crosses.disjoint) hv h.1
    | right => exact (Set.disjoint_left.mp P.crosses.disjoint) h.2 hw

/-- No edge has both endpoints in the opposite color class. -/
theorem not_adj_of_mem_other (P : FiniteBipartition G) (c : BipartitionSide)
    {v w : V} (hv : v ∈ P.other c) (hw : w ∈ P.other c) : ¬G.Adj v w := by
  cases c with
  | left => exact P.not_adj_of_mem_side .right hv hw
  | right => exact P.not_adj_of_mem_side .left hv hw

/-- A neighbor of an opposite-side vertex lies in the selected side. -/
theorem mem_side_of_adj_mem_other (P : FiniteBipartition G)
    (c : BipartitionSide) {v u : V} (hv : v ∈ P.other c)
    (hvu : G.Adj v u) : u ∈ P.side c := by
  have hu : u ∈ (Finset.univ : Finset V) := Finset.mem_univ u
  rw [← P.union_side_other c] at hu
  rcases Finset.mem_union.mp hu with huside | huother
  · exact huside
  · exact False.elim ((P.not_adj_of_mem_other c hv huother) hvu)

end FiniteBipartition

/-! ## Exact conditional fibers of the actual hard-core law -/

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- An exact color-class occupation environment.  Deliberately, this carries
only an independent set contained in the conditioned color; there is no root,
recovery time, or first-recovery flag. -/
structure ColorEnvironment (P : FiniteBipartition G) (c : BipartitionSide) where
  occupied : IndepFinset G
  subset_side : occupied.val ⊆ P.side c

namespace ColorEnvironment

variable {P : FiniteBipartition G} {c : BipartitionSide}

/-- Vertices on the unconditioned color having no neighbor in the exact
conditioned occupation. -/
def available (E : ColorEnvironment P c) : Finset V :=
  (P.other c).filter fun v => ∀ u ∈ E.occupied.val, ¬G.Adj v u

@[simp] theorem mem_available (E : ColorEnvironment P c) (v : V) :
    v ∈ E.available ↔
      v ∈ P.other c ∧ ∀ u ∈ E.occupied.val, ¬G.Adj v u := by
  simp [available]

/-- A fiber state is exactly a subset of available opposite-color vertices. -/
abbrev FiberState (E : ColorEnvironment P c) :=
  {t : Finset V // t ⊆ E.available}

instance (E : ColorEnvironment P c) : Fintype E.FiberState :=
  Fintype.ofFinite E.FiberState

/-- The actual global independent set represented by a conditional fiber state. -/
def extension (E : ColorEnvironment P c) (t : E.FiberState) : IndepFinset G where
  val := E.occupied.val ∪ t.1
  property := by
    rw [SimpleGraph.isIndepSet_iff]
    intro v hv w hw hvw
    simp only [Finset.mem_coe, Finset.mem_union] at hv hw
    rcases hv with hvE | hvt
    · rcases hw with hwE | hwt
      · exact ((SimpleGraph.isIndepSet_iff G).mp E.occupied.property) hvE hwE hvw
      · have haw := (E.mem_available w).mp (t.2 hwt)
        intro hadj
        exact haw.2 v hvE ((G.adj_comm v w).mp hadj)
    · rcases hw with hwE | hwt
      · have hav := (E.mem_available v).mp (t.2 hvt)
        exact hav.2 w hwE
      · exact P.not_adj_of_mem_other c
          ((E.mem_available v).mp (t.2 hvt)).1
          ((E.mem_available w).mp (t.2 hwt)).1

/-- The fixed and free parts of an extension are disjoint. -/
theorem disjoint_occupied_fiber (E : ColorEnvironment P c) (t : E.FiberState) :
    Disjoint E.occupied.val t.1 := by
  apply Finset.disjoint_left.mpr
  intro v hvE hvt
  have hs := E.subset_side hvE
  have ho := (E.mem_available v).mp (t.2 hvt) |>.1
  exact (Finset.disjoint_left.mp (P.disjoint_side_other c)) hs ho

/-- Occupation size in a fiber is fixed size plus free-subset size. -/
theorem extension_card (E : ColorEnvironment P c) (t : E.FiberState) :
    (E.extension t).val.card = E.occupied.val.card + t.1.card := by
  exact Finset.card_union_of_disjoint (E.disjoint_occupied_fiber t)

/-- Restriction of an extension to the conditioned color is exactly the
conditioning environment. -/
theorem extension_inter_side (E : ColorEnvironment P c) (t : E.FiberState) :
    (E.extension t).val ∩ P.side c = E.occupied.val := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvext, hvside⟩
    rcases Finset.mem_union.mp hvext with hvE | hvt
    · exact hvE
    · have hvother := (E.mem_available v).mp (t.2 hvt) |>.1
      exact False.elim ((Finset.disjoint_left.mp (P.disjoint_side_other c)) hvside hvother)
  · intro hvE
    exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hvE, E.subset_side hvE⟩

/-- The global independent configurations in the exact conditioning event. -/
abbrev ConditionedGlobalState (E : ColorEnvironment P c) :=
  {s : IndepFinset G // s.val ∩ P.side c = E.occupied.val}

/-- Recover the free opposite-side subset from any global configuration in the
exact conditioning event. -/
def fiberStateOfConditionedGlobalState (E : ColorEnvironment P c)
    (s : E.ConditionedGlobalState) : E.FiberState :=
  ⟨s.1.val ∩ P.other c, by
    intro v hv
    rcases Finset.mem_inter.mp hv with ⟨hvs, hvother⟩
    rw [E.mem_available]
    refine ⟨hvother, ?_⟩
    intro u huE
    have huside : u ∈ P.side c := E.subset_side huE
    have hus : u ∈ s.1.val := by
      have huinter : u ∈ s.1.val ∩ P.side c := by
        rw [s.2]
        exact huE
      exact (Finset.mem_inter.mp huinter).1
    have hvu : v ≠ u := by
      intro h
      subst u
      exact (Finset.disjoint_left.mp (P.disjoint_side_other c)) huside hvother
    exact ((SimpleGraph.isIndepSet_iff G).mp s.1.property) hvs hus hvu⟩

/-- Exact finite disintegration: free fiber states are in bijection with *all*
global independent configurations whose restriction to the conditioned side
is `E.occupied`. -/
def fiberStateEquivConditionedGlobalState (E : ColorEnvironment P c) :
    E.FiberState ≃ E.ConditionedGlobalState where
  toFun t := ⟨E.extension t, E.extension_inter_side t⟩
  invFun := E.fiberStateOfConditionedGlobalState
  left_inv t := by
    apply Subtype.ext
    ext v
    constructor
    · intro hv
      rcases Finset.mem_inter.mp hv with ⟨hvext, hvother⟩
      rcases Finset.mem_union.mp hvext with hvE | hvt
      · exact False.elim
          ((Finset.disjoint_left.mp (P.disjoint_side_other c))
            (E.subset_side hvE) hvother)
      · exact hvt
    · intro hvt
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_union_right _ hvt, (E.mem_available v).mp (t.2 hvt) |>.1⟩
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    ext v
    change v ∈ E.occupied.val ∪ (s.1.val ∩ P.other c) ↔ v ∈ s.1.val
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with hvE | hvother
      · have hvinter : v ∈ s.1.val ∩ P.side c := by
          rw [s.2]
          exact hvE
        exact (Finset.mem_inter.mp hvinter).1
      · exact (Finset.mem_inter.mp hvother).1
    · intro hvs
      have hvuniv : v ∈ (Finset.univ : Finset V) := Finset.mem_univ v
      rw [← P.union_side_other c] at hvuniv
      rcases Finset.mem_union.mp hvuniv with hvside | hvother
      · apply Finset.mem_union_left
        have hvinter : v ∈ s.1.val ∩ P.side c :=
          Finset.mem_inter.mpr ⟨hvs, hvside⟩
        rw [s.2] at hvinter
        exact hvinter
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvs, hvother⟩)

end ColorEnvironment

/-- The unchanged Gibbs activity parameter from the global law. -/
def hardCoreTheta (z : ℝ) : ℝ := z / (1 + z)

@[simp] theorem one_sub_hardCoreTheta {z : ℝ} (hz : 0 < z) :
    1 - hardCoreTheta z = 1 / (1 + z) := by
  unfold hardCoreTheta
  field_simp
  ring

variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (P : FiniteBipartition G)
variable (c : BipartitionSide)

/-- Global hard-core probability of the actual extension, before conditioning. -/
def actualFiberWeight (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (t : E.FiberState) : ℝ :=
  (hardCoreLaw G z hz).probability (E.extension t)

/-- Sum of original global probabilities across one exact conditional fiber. -/
def actualFiberMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) : ℝ :=
  ∑ t : E.FiberState, actualFiberWeight G P c z hz E t

/-- Original hard-core mass of the literal global conditioning event. -/
def actualConditioningEventMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) : ℝ :=
  ∑ s : E.ConditionedGlobalState, (hardCoreLaw G z hz).probability s.1

/-- The fiber normalizer is exactly the original finite hard-core mass of the
full global conditioning event, via the checked fiber/event equivalence. -/
theorem actualFiberMass_eq_conditioningEventMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualFiberMass G P c z hz E =
      actualConditioningEventMass G P c z hz E := by
  unfold actualFiberMass actualFiberWeight actualConditioningEventMass
  change (∑ t : E.FiberState,
      (hardCoreLaw G z hz).probability
        ((E.fiberStateEquivConditionedGlobalState t).1)) =
    ∑ s : E.ConditionedGlobalState, (hardCoreLaw G z hz).probability s.1
  exact E.fiberStateEquivConditionedGlobalState.sum_comp
    (fun s : E.ConditionedGlobalState => (hardCoreLaw G z hz).probability s.1)

/-- The probability of the conditioning event, written as a finite sum over
all global independent configurations satisfying its predicate. -/
def actualConditioningEventProbability (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) : ℝ :=
  ∑ s ∈ (Finset.univ.filter fun s : IndepFinset G =>
      s.val ∩ P.side c = E.occupied.val),
    (hardCoreLaw G z hz).probability s

/-- The event-subtype mass is the indicator/filter form of the same original-law
event probability. -/
theorem actualConditioningEventMass_eq_probability (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualConditioningEventMass G P c z hz E =
      actualConditioningEventProbability G P c z hz E := by
  unfold actualConditioningEventMass actualConditioningEventProbability
  symm
  exact Finset.sum_subtype
    (Finset.univ.filter fun s : IndepFinset G =>
      s.val ∩ P.side c = E.occupied.val)
    (by intro s; simp)
    (fun s : IndepFinset G => (hardCoreLaw G z hz).probability s)

/-- The fiber denominator is literally the finite original-law probability of
its global conditioning event. -/
theorem actualFiberMass_eq_conditioningEventProbability (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualFiberMass G P c z hz E =
      actualConditioningEventProbability G P c z hz E := by
  rw [actualFiberMass_eq_conditioningEventMass,
    actualConditioningEventMass_eq_probability]

/-- Conditional probability obtained by normalizing the original global
hard-core probabilities on the exact fiber. -/
def actualConditionalProbability (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (t : E.FiberState) : ℝ :=
  actualFiberWeight G P c z hz E t / actualFiberMass G P c z hz E

/-- Elementary finite binomial theorem in powerset form. -/
theorem sum_powerset_pow_card (s : Finset V) (z : ℝ) :
    ∑ t ∈ s.powerset, z ^ t.card = (1 + z) ^ s.card := by
  classical
  calc
    (∑ t ∈ s.powerset, z ^ t.card) =
        ∑ t ∈ s.powerset,
          (∏ _i ∈ t, z) * ∏ _i ∈ s \ t, (1 : ℝ) := by simp
    _ = ∏ _i ∈ s, (z + 1) := by
      symm
      exact Finset.prod_add (fun _ : V => z) (fun _ => 1) s
    _ = (1 + z) ^ s.card := by
      simp [add_comm]

/-- Convert a sum over the fiber subtype to its literal powerset sum. -/
theorem ColorEnvironment.sum_fiber (E : ColorEnvironment P c)
    (f : Finset V → ℝ) :
    ∑ t : E.FiberState, f t.1 = ∑ t ∈ E.available.powerset, f t := by
  symm
  exact Finset.sum_subtype E.available.powerset (by
    intro t
    exact Finset.mem_powerset) f

/-- Every extension retains the original global activity `z`; its probability
is the fixed-environment factor times `z` to the number of free vertices. -/
theorem actualFiberWeight_eq (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (t : E.FiberState) :
    actualFiberWeight G P c z hz E t =
      (z ^ E.occupied.val.card / independenceEval G z) * z ^ t.1.card := by
  simp only [actualFiberWeight, hardCoreLaw, E.extension_card, pow_add]
  ring

/-- The original global mass of an exact fiber has the expected product form. -/
theorem actualFiberMass_eq (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualFiberMass G P c z hz E =
      (z ^ E.occupied.val.card / independenceEval G z) *
        (1 + z) ^ E.available.card := by
  unfold actualFiberMass
  simp_rw [actualFiberWeight_eq G P c z hz E]
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ t : E.FiberState, z ^ t.1.card) =
        ∑ t ∈ E.available.powerset, z ^ t.card :=
      ColorEnvironment.sum_fiber (G := G) (P := P) (c := c) E
        (fun t : Finset V => z ^ t.card)
    _ = (1 + z) ^ E.available.card := sum_powerset_pow_card E.available z

/-- The normalizing mass of every exact fiber is strictly positive. -/
theorem actualFiberMass_pos (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    0 < actualFiberMass G P c z hz E := by
  rw [actualFiberMass_eq]
  exact mul_pos
    (div_pos (pow_pos hz _) (independenceEval_pos G hz))
    (pow_pos (by linarith) _)

/-- Algebraic conversion from unchanged-activity powers to Bernoulli subset
weights at `theta = z/(1+z)`. -/
theorem hardCore_ratio_eq_bernoulliWeight (z : ℝ) (hz : 0 < z)
    (s t : Finset V) (ht : t ⊆ s) :
    z ^ t.card / (1 + z) ^ s.card =
      BernoulliSubset.weight s t (hardCoreTheta z) := by
  have hcard : t.card ≤ s.card := Finset.card_le_card ht
  have hden : 1 + z ≠ 0 := ne_of_gt (by linarith)
  rw [BernoulliSubset.weight, one_sub_hardCoreTheta hz]
  rw [hardCoreTheta]
  rw [div_pow, div_pow]
  field_simp
  simp [← pow_add, Nat.add_sub_of_le hcard]

/-- **C.40, pointwise form.**  Normalizing the *actual global hard-core
probabilities* on an exact color fiber gives the product Bernoulli law on the
available opposite-color vertices, at the unchanged activity `z`. -/
theorem C40_actual_conditional_probability (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (t : E.FiberState) :
    actualConditionalProbability G P c z hz E t =
      BernoulliSubset.weight E.available t.1 (hardCoreTheta z) := by
  rw [actualConditionalProbability, actualFiberWeight_eq, actualFiberMass_eq]
  have hfixed : z ^ E.occupied.val.card / independenceEval G z ≠ 0 :=
    (div_pos (pow_pos hz _) (independenceEval_pos G hz)).ne'
  rw [mul_div_mul_left _ _ hfixed]
  exact hardCore_ratio_eq_bernoulliWeight z hz E.available t.1 t.2

/-- The actual conditional probabilities are normalized. -/
theorem C40_actual_conditional_probability_sum (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    ∑ t : E.FiberState, actualConditionalProbability G P c z hz E t = 1 := by
  simp_rw [C40_actual_conditional_probability G P c z hz E]
  calc
    (∑ t : E.FiberState,
        BernoulliSubset.weight E.available t.1 (hardCoreTheta z)) =
        ∑ t ∈ E.available.powerset,
          BernoulliSubset.weight E.available t (hardCoreTheta z) :=
      ColorEnvironment.sum_fiber (G := G) (P := P) (c := c) E
        (fun t : Finset V => BernoulliSubset.weight E.available t (hardCoreTheta z))
    _ = 1 := BernoulliSubset.sum_weight E.available (hardCoreTheta z)

/-- Conditional mass of a free occupation count. -/
def actualConditionalFreeRankMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (k : ℕ) : ℝ :=
  ∑ t : E.FiberState,
    if t.1.card = k then actualConditionalProbability G P c z hz E t else 0

/-- **C.40, binomial rank form.**  Given one color class exactly, the number
of occupied available vertices on the opposite color is binomial. -/
theorem C40_actual_conditional_freeRankMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (k : ℕ) :
    actualConditionalFreeRankMass G P c z hz E k =
      Nat.choose E.available.card k * hardCoreTheta z ^ k *
        (1 - hardCoreTheta z) ^ (E.available.card - k) := by
  unfold actualConditionalFreeRankMass
  simp_rw [C40_actual_conditional_probability G P c z hz E]
  calc
    (∑ t : E.FiberState,
        if t.1.card = k then
          BernoulliSubset.weight E.available t.1 (hardCoreTheta z) else 0) =
        ∑ t ∈ E.available.powerset,
          if t.card = k then
            BernoulliSubset.weight E.available t (hardCoreTheta z) else 0 :=
      ColorEnvironment.sum_fiber (G := G) (P := P) (c := c) E
        (fun t : Finset V => if t.card = k then
          BernoulliSubset.weight E.available t (hardCoreTheta z) else 0)
    _ = ∑ t ∈ E.available.powerset.filter (fun t => t.card = k),
          BernoulliSubset.weight E.available t (hardCoreTheta z) := by
      rw [← Finset.sum_filter]
    _ = Nat.choose E.available.card k * hardCoreTheta z ^ k *
        (1 - hardCoreTheta z) ^ (E.available.card - k) :=
      BernoulliSubset.sum_weight_card_eq E.available (hardCoreTheta z) k

/-- Conditional mass that the *total* occupation is the fixed conditioned
count plus `k` free occupations. -/
def actualConditionalTotalRankMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (k : ℕ) : ℝ :=
  ∑ t : E.FiberState,
    if (E.extension t).val.card = E.occupied.val.card + k then
      actualConditionalProbability G P c z hz E t else 0

/-- **C.40, shifted total-count form.**  In the exact conditional fiber,
`X = K_C + Bin(a_C, theta)` in literal rank-mass form. -/
theorem C40_actual_conditional_totalRankMass (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) (k : ℕ) :
    actualConditionalTotalRankMass G P c z hz E k =
      Nat.choose E.available.card k * hardCoreTheta z ^ k *
        (1 - hardCoreTheta z) ^ (E.available.card - k) := by
  unfold actualConditionalTotalRankMass
  simp_rw [E.extension_card, Nat.add_left_cancel_iff]
  change actualConditionalFreeRankMass G P c z hz E k = _
  exact C40_actual_conditional_freeRankMass G P c z hz E k

/-- Conditional mean of the total occupation number in the exact fiber. -/
def actualConditionalMean (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) : ℝ :=
  ∑ t : E.FiberState, actualConditionalProbability G P c z hz E t *
    ((E.extension t).val.card : ℝ)

/-- **C.41, mean identity.** `M_C = K_C + theta * a_C`. -/
theorem C41_actual_conditionalMean (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualConditionalMean G P c z hz E =
      (E.occupied.val.card : ℝ) + hardCoreTheta z * (E.available.card : ℝ) := by
  unfold actualConditionalMean
  simp_rw [C40_actual_conditional_probability G P c z hz E,
    E.extension_card, Nat.cast_add]
  calc
    (∑ t : E.FiberState,
        BernoulliSubset.weight E.available t.1 (hardCoreTheta z) *
          ((E.occupied.val.card : ℝ) + (t.1.card : ℝ))) =
      ∑ t ∈ E.available.powerset,
        BernoulliSubset.weight E.available t (hardCoreTheta z) *
          ((E.occupied.val.card : ℝ) + (t.card : ℝ)) :=
      ColorEnvironment.sum_fiber (G := G) (P := P) (c := c) E
        (fun t : Finset V =>
          BernoulliSubset.weight E.available t (hardCoreTheta z) *
            ((E.occupied.val.card : ℝ) + (t.card : ℝ)))
    _ = (E.occupied.val.card : ℝ) *
          (∑ t ∈ E.available.powerset,
            BernoulliSubset.weight E.available t (hardCoreTheta z)) +
        ∑ t ∈ E.available.powerset,
          BernoulliSubset.weight E.available t (hardCoreTheta z) * (t.card : ℝ) := by
      simp_rw [mul_add, mul_comm
        (BernoulliSubset.weight E.available _ (hardCoreTheta z))
        (E.occupied.val.card : ℝ)]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (E.occupied.val.card : ℝ) +
        hardCoreTheta z * (E.available.card : ℝ) := by
      rw [BernoulliSubset.sum_weight, BernoulliSubset.sum_weight_card, mul_one]

/-- Conditional variance of total occupation in the exact fiber. -/
def actualConditionalVariance (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) : ℝ :=
  ∑ t : E.FiberState, actualConditionalProbability G P c z hz E t *
    (((E.extension t).val.card : ℝ) - actualConditionalMean G P c z hz E) ^ 2

/-- **C.41, variance identity.** `W_C = theta * (1-theta) * a_C`. -/
theorem C41_actual_conditionalVariance (z : ℝ) (hz : 0 < z)
    (E : ColorEnvironment P c) :
    actualConditionalVariance G P c z hz E =
      hardCoreTheta z * (1 - hardCoreTheta z) * (E.available.card : ℝ) := by
  unfold actualConditionalVariance
  rw [C41_actual_conditionalMean G P c z hz E]
  simp_rw [C40_actual_conditional_probability G P c z hz E,
    E.extension_card, Nat.cast_add]
  have hpoint (t : E.FiberState) :
      ((E.occupied.val.card : ℝ) + (t.1.card : ℝ) -
        ((E.occupied.val.card : ℝ) +
          hardCoreTheta z * (E.available.card : ℝ))) ^ 2 =
      ((t.1.card : ℝ) - hardCoreTheta z * (E.available.card : ℝ)) ^ 2 := by ring
  simp_rw [hpoint]
  calc
    (∑ t : E.FiberState,
      BernoulliSubset.weight E.available t.1 (hardCoreTheta z) *
        ((t.1.card : ℝ) - hardCoreTheta z * (E.available.card : ℝ)) ^ 2) =
      ∑ t ∈ E.available.powerset,
        BernoulliSubset.weight E.available t (hardCoreTheta z) *
          ((t.card : ℝ) - hardCoreTheta z * (E.available.card : ℝ)) ^ 2 :=
      ColorEnvironment.sum_fiber (G := G) (P := P) (c := c) E
        (fun t : Finset V =>
          BernoulliSubset.weight E.available t (hardCoreTheta z) *
            ((t.card : ℝ) - hardCoreTheta z * (E.available.card : ℝ)) ^ 2)
    _ = hardCoreTheta z * (1 - hardCoreTheta z) * (E.available.card : ℝ) :=
      BernoulliSubset.sum_weight_variance E.available (hardCoreTheta z)

/-! ## C.42 residual variables on actual independent sets -/

/-- Actual occupation indicator `xi_v`. -/
def occupiedIndicator (s : IndepFinset G) (v : V) : ℝ :=
  if v ∈ s.val then 1 else 0

/-- Actual hard-core addability indicator `A_v`: the vertex is absent and can
be inserted without violating independence. -/
def addableIndicator (s : IndepFinset G) (v : V) : ℝ :=
  if v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u then 1 else 0

/-- `B_v = xi_v + A_v`. -/
def insertableOrOccupiedIndicator (s : IndepFinset G) (v : V) : ℝ :=
  occupiedIndicator (G := G) s v + addableIndicator (G := G) s v

/-- `h_v = xi_v - theta B_v`. -/
def vertexResidual (z : ℝ) (s : IndepFinset G) (v : V) : ℝ :=
  occupiedIndicator (G := G) s v - hardCoreTheta z * insertableOrOccupiedIndicator (G := G) s v

/-- Total number of currently addable vertices. -/
def actualAddableCount (s : IndepFinset G) : ℝ :=
  ∑ v : V, addableIndicator (G := G) s v

/-- Side residual `epsilon_C`. -/
def sideResidual (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (s : IndepFinset G) : ℝ :=
  ∑ v ∈ P.side c, vertexResidual (G := G) z s v

/-- Occupation indicators sum to the actual occupation cardinality. -/
theorem sum_occupiedIndicator (s : IndepFinset G) :
    ∑ v : V, occupiedIndicator (G := G) s v = (s.val.card : ℝ) := by
  classical
  simp [occupiedIndicator]

/-- `B` sums pointwise as `X+A`. -/
theorem sum_insertableOrOccupiedIndicator (s : IndepFinset G) :
    ∑ v : V, insertableOrOccupiedIndicator (G := G) s v =
      (s.val.card : ℝ) + actualAddableCount (G := G) s := by
  simp only [insertableOrOccupiedIndicator, actualAddableCount,
    Finset.sum_add_distrib, sum_occupiedIndicator (G := G)]

/-- **C.42.** Pointwise two-color residual identity
`epsilon_L + epsilon_R = (X-zA)/(1+z)`. -/
theorem C42_sideResidual_add (P : FiniteBipartition G)
    (z : ℝ) (hz : 0 < z) (s : IndepFinset G) :
    sideResidual (G := G) P .left z s + sideResidual (G := G) P .right z s =
      ((s.val.card : ℝ) - z * actualAddableCount (G := G) s) / (1 + z) := by
  have hparts :
      sideResidual (G := G) P .left z s + sideResidual (G := G) P .right z s =
        ∑ v : V, vertexResidual (G := G) z s v := by
    simp only [sideResidual]
    change (∑ v ∈ P.side .left, vertexResidual (G := G) z s v) +
      (∑ v ∈ P.other .left, vertexResidual (G := G) z s v) = _
    have hcover : P.side .left ∪ P.other .left = Finset.univ := by
      exact P.cover
    rw [← Finset.sum_union (P.disjoint_side_other .left), hcover]
  rw [hparts]
  have hsum :
      (∑ v : V, vertexResidual (G := G) z s v) =
        (s.val.card : ℝ) - hardCoreTheta z *
          ((s.val.card : ℝ) + actualAddableCount (G := G) s) := by
    simp_rw [vertexResidual]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      sum_occupiedIndicator (G := G),
      sum_insertableOrOccupiedIndicator (G := G)]
  rw [hsum]
  unfold hardCoreTheta
  field_simp
  ring

/-- The exact color environment obtained by restricting an actual global
configuration.  No recovery/localization data is retained. -/
def restrictionEnvironment (P : FiniteBipartition G) (c : BipartitionSide)
    (s : IndepFinset G) : ColorEnvironment P c where
  occupied := {
    val := s.val ∩ P.side c
    property := by
      rw [SimpleGraph.isIndepSet_iff]
      intro v hv w hw hvw
      exact ((SimpleGraph.isIndepSet_iff G).mp s.property)
        (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hw).1 hvw }
  subset_side := fun _ hv => (Finset.mem_inter.mp hv).2

/-- Availability computed from the restriction is equivalent to having no
occupied neighbor in the entire actual configuration. -/
theorem mem_available_restrictionEnvironment
    (P : FiniteBipartition G) (c : BipartitionSide)
    (s : IndepFinset G) (v : V) :
    v ∈ (restrictionEnvironment (G := G) P c s).available ↔
      v ∈ P.other c ∧ ∀ u ∈ s.val, ¬G.Adj v u := by
  rw [ColorEnvironment.mem_available]
  constructor
  · rintro ⟨hvother, hfree⟩
    refine ⟨hvother, ?_⟩
    intro u hu hadj
    have huside : u ∈ P.side c := P.mem_side_of_adj_mem_other c hvother hadj
    exact hfree u (Finset.mem_inter.mpr ⟨hu, huside⟩) hadj
  · rintro ⟨hvother, hfree⟩
    refine ⟨hvother, ?_⟩
    intro u hu
    exact hfree u (Finset.mem_inter.mp hu).1

/-- If `v` is occupied in an independent set, all its neighbors are absent. -/
theorem neighbor_free_of_mem (s : IndepFinset G) {v : V} (hv : v ∈ s.val) :
    ∀ u ∈ s.val, ¬G.Adj v u := by
  intro u hu hadj
  by_cases hvu : v = u
  · subst u
    exact @Std.Irrefl.irrefl V G.Adj G.loopless v hadj
  · exact ((SimpleGraph.isIndepSet_iff G).mp s.property) hv hu hvu hadj

/-- The actual variable `B_v=xi_v+A_v` is exactly the indicator that every
neighbor of `v` is absent. -/
theorem insertableOrOccupiedIndicator_eq_neighborFree
    (s : IndepFinset G) (v : V) :
    insertableOrOccupiedIndicator (G := G) s v =
      if (∀ u ∈ s.val, ¬G.Adj v u) then 1 else 0 := by
  by_cases hv : v ∈ s.val
  · have hfree := neighbor_free_of_mem (G := G) s hv
    rw [if_pos hfree]
    simp [insertableOrOccupiedIndicator, occupiedIndicator, addableIndicator, hv]
  · by_cases hfree : ∀ u ∈ s.val, ¬G.Adj v u
    · rw [if_pos hfree]
      unfold insertableOrOccupiedIndicator occupiedIndicator addableIndicator
      rw [if_neg hv, if_pos ⟨hv, hfree⟩]
      norm_num
    · rw [if_neg hfree]
      unfold insertableOrOccupiedIndicator occupiedIndicator addableIndicator
      rw [if_neg hv, if_neg]
      · norm_num
      · intro h
        exact hfree h.2

/-- The number of available opposite-side vertices in the actual restriction
is the sum of the actual `B_v` indicators on that side. -/
theorem available_card_restrictionEnvironment
    (P : FiniteBipartition G) (c : BipartitionSide) (s : IndepFinset G) :
    ((restrictionEnvironment (G := G) P c s).available.card : ℝ) =
      ∑ v ∈ P.other c, insertableOrOccupiedIndicator (G := G) s v := by
  classical
  calc
    ((restrictionEnvironment (G := G) P c s).available.card : ℝ) =
        ∑ v ∈ P.other c,
          if v ∈ (restrictionEnvironment (G := G) P c s).available
          then 1 else 0 := by
      rw [← Finset.sum_filter]
      have hfilter :
          (P.other c).filter
              (fun v => v ∈ (restrictionEnvironment (G := G) P c s).available) =
            (restrictionEnvironment (G := G) P c s).available := by
        ext v
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.2
        · intro hav
          exact ⟨(ColorEnvironment.mem_available _ _).mp hav |>.1, hav⟩
      rw [hfilter]
      simp
    _ = ∑ v ∈ P.other c,
        insertableOrOccupiedIndicator (G := G) s v := by
      apply Finset.sum_congr rfl
      intro v hvother
      simp only [mem_available_restrictionEnvironment (G := G) P c s,
        hvother, true_and,
        insertableOrOccupiedIndicator_eq_neighborFree (G := G)]

/-! ## C.43: the actual single-site toggle -/

/-- Independent configurations in which `v` is absent but addable. -/
abbrev AddableAt (G : SimpleGraph V) (v : V) :=
  {s : IndepFinset G // v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u}

/-- Independent configurations in which `v` is occupied. -/
abbrev OccupiedAt (G : SimpleGraph V) (v : V) :=
  {s : IndepFinset G // v ∈ s.val}

/-- Insert an addable vertex. -/
def insertAddable (v : V) (s : AddableAt G v) : IndepFinset G where
  val := insert v s.1.val
  property := by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with hav | ha
    · subst a
      rcases hb with hbv | hb
      · subst b
        exact False.elim (hab rfl)
      · exact s.2.2 b hb
    · rcases hb with hbv | hb
      · subst b
        intro hadj
        exact s.2.2 a ha ((G.adj_comm a v).mp hadj)
      · exact ((SimpleGraph.isIndepSet_iff G).mp s.1.property) ha hb hab

/-- Erase an occupied vertex. -/
def eraseOccupied (v : V) (s : OccupiedAt G v) : IndepFinset G where
  val := s.1.val.erase v
  property := by
    rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    exact ((SimpleGraph.isIndepSet_iff G).mp s.1.property)
      (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab

/-- The literal insertion/erasure toggle between addable and occupied states. -/
def addableOccupiedEquiv (v : V) : AddableAt G v ≃ OccupiedAt G v where
  toFun s := ⟨insertAddable (G := G) v s, Finset.mem_insert_self v _⟩
  invFun s := ⟨eraseOccupied (G := G) v s, by
    constructor
    · simp [eraseOccupied]
    · intro u hu
      have hu' : u ∈ s.1.val := Finset.mem_of_mem_erase hu
      intro hadj
      by_cases hvu : v = u
      · subst u
        exact @Std.Irrefl.irrefl V G.Adj G.loopless v hadj
      · exact ((SimpleGraph.isIndepSet_iff G).mp s.1.property)
          s.2 hu' hvu hadj⟩
  left_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    simp [insertAddable, eraseOccupied, s.2.1]
  right_inv s := by
    apply Subtype.ext
    apply Subtype.ext
    simp [insertAddable, eraseOccupied, s.2]

/-- Actual global occupation probability at one vertex, written as a finite
sum of the project's hard-core point probabilities. -/
def singleSiteOccupationProbability (z : ℝ) (hz : 0 < z) (v : V) : ℝ :=
  ∑ s : OccupiedAt G v, (hardCoreLaw G z hz).probability s.1

/-- Actual global probability that an absent vertex is addable. -/
def singleSiteAddableProbability (z : ℝ) (hz : 0 < z) (v : V) : ℝ :=
  ∑ s : AddableAt G v, (hardCoreLaw G z hz).probability s.1

/-- Actual probability that every neighbor is absent (`B_v=1`). -/
def singleSiteNeighborFreeProbability (z : ℝ) (hz : 0 < z) (v : V) : ℝ :=
  singleSiteOccupationProbability (G := G) z hz v +
    singleSiteAddableProbability (G := G) z hz v

/-- Global expectation of the actual occupation indicator equals its literal
occupied-state subtype sum. -/
theorem sum_probability_mul_occupiedIndicator
    (z : ℝ) (hz : 0 < z) (v : V) :
    (∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
      occupiedIndicator (G := G) s v) =
      singleSiteOccupationProbability (G := G) z hz v := by
  classical
  unfold occupiedIndicator singleSiteOccupationProbability
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter fun s : IndepFinset G => v ∈ s.val)
    (by intro s; simp) (fun s => (hardCoreLaw G z hz).probability s)

/-- Global expectation of the actual addability indicator equals its literal
absent-addable subtype sum. -/
theorem sum_probability_mul_addableIndicator
    (z : ℝ) (hz : 0 < z) (v : V) :
    (∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
      addableIndicator (G := G) s v) =
      singleSiteAddableProbability (G := G) z hz v := by
  classical
  unfold addableIndicator singleSiteAddableProbability
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (Finset.univ.filter fun s : IndepFinset G =>
      v ∉ s.val ∧ ∀ u ∈ s.val, ¬G.Adj v u)
    (by intro s; simp) (fun s => (hardCoreLaw G z hz).probability s)

/-- Global expectation of `B_v` is the actual probability that all neighbors
of `v` are absent. -/
theorem sum_probability_mul_insertableOrOccupiedIndicator
    (z : ℝ) (hz : 0 < z) (v : V) :
    (∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
      insertableOrOccupiedIndicator (G := G) s v) =
      singleSiteNeighborFreeProbability (G := G) z hz v := by
  simp only [insertableOrOccupiedIndicator, singleSiteNeighborFreeProbability,
    mul_add, Finset.sum_add_distrib]
  rw [sum_probability_mul_occupiedIndicator (G := G) z hz v,
    sum_probability_mul_addableIndicator (G := G) z hz v]

/-- Insertion adds exactly one vertex. -/
theorem insertAddable_card (v : V) (s : AddableAt G v) :
    (insertAddable (G := G) v s).val.card = s.1.val.card + 1 := by
  simp [insertAddable, s.2.1]

/-- Raw toggle identity at unchanged activity: occupied mass is `z` times
absent-addable mass. -/
theorem singleSiteOccupationProbability_eq_z_mul_addable
    (z : ℝ) (hz : 0 < z) (v : V) :
    singleSiteOccupationProbability (G := G) z hz v =
      z * singleSiteAddableProbability (G := G) z hz v := by
  classical
  unfold singleSiteOccupationProbability singleSiteAddableProbability
  rw [← (addableOccupiedEquiv (G := G) v).sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [hardCoreLaw]
  change z ^ (insertAddable (G := G) v s).val.card / independenceEval G z =
    z * (z ^ s.1.val.card / independenceEval G z)
  rw [insertAddable_card, pow_succ]
  ring

/-- Manuscript single-site toggle in normalized form:
`Pr(xi_v=1)=theta Pr(B_v=1)`. -/
theorem singleSiteOccupationProbability_eq_theta_mul_neighborFree
    (z : ℝ) (hz : 0 < z) (v : V) :
    singleSiteOccupationProbability (G := G) z hz v =
      hardCoreTheta z * singleSiteNeighborFreeProbability (G := G) z hz v := by
  rw [singleSiteNeighborFreeProbability,
    singleSiteOccupationProbability_eq_z_mul_addable (G := G) z hz v]
  unfold hardCoreTheta
  field_simp
  ring

/-- Actual expected occupation on a specified color. -/
def sideOccupationExpectation (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) : ℝ :=
  ∑ v ∈ P.side c, singleSiteOccupationProbability (G := G) z hz v

/-- The conditional variance for a global configuration, obtained by applying
the actual C.41 conditional variance to its exact color restriction. -/
def conditionalVarianceGivenRestriction (P : FiniteBipartition G)
    (c : BipartitionSide) (z : ℝ) (hz : 0 < z) (s : IndepFinset G) : ℝ :=
  actualConditionalVariance (G := G) P c z hz
    (restrictionEnvironment (G := G) P c s)

/-- The hard-core expectation of the actual conditional variance after
revealing color `c`.  This is a literal finite expectation under
`hardCoreLaw G z hz`, not a pre-simplified proxy. -/
def expectedConditionalVariance (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) : ℝ :=
  ∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
    conditionalVarianceGivenRestriction (G := G) P c z hz s

/-- Expanding the actual conditional variance and exchanging the two finite
sums gives its neighbor-free-indicator form. -/
theorem expectedConditionalVariance_eq_neighborFree_sum
    (P : FiniteBipartition G) (c : BipartitionSide)
    (z : ℝ) (hz : 0 < z) :
    expectedConditionalVariance (G := G) P c z hz =
      hardCoreTheta z * (1 - hardCoreTheta z) *
        ∑ v ∈ P.other c,
          singleSiteNeighborFreeProbability (G := G) z hz v := by
  unfold expectedConditionalVariance conditionalVarianceGivenRestriction
  simp_rw [C41_actual_conditionalVariance (G := G) P c z hz]
  simp_rw [available_card_restrictionEnvironment (G := G) P c]
  calc
    (∑ s : IndepFinset G, (hardCoreLaw G z hz).probability s *
        (hardCoreTheta z * (1 - hardCoreTheta z) *
          ∑ v ∈ P.other c,
            insertableOrOccupiedIndicator (G := G) s v)) =
        hardCoreTheta z * (1 - hardCoreTheta z) *
          ∑ s : IndepFinset G, ∑ v ∈ P.other c,
            (hardCoreLaw G z hz).probability s *
              insertableOrOccupiedIndicator (G := G) s v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v hv
      ring
    _ = hardCoreTheta z * (1 - hardCoreTheta z) *
          ∑ v ∈ P.other c, ∑ s : IndepFinset G,
            (hardCoreLaw G z hz).probability s *
              insertableOrOccupiedIndicator (G := G) s v := by
      congr 1
      rw [Finset.sum_comm]
    _ = hardCoreTheta z * (1 - hardCoreTheta z) *
          ∑ v ∈ P.other c,
            singleSiteNeighborFreeProbability (G := G) z hz v := by
      apply congrArg (fun x : ℝ => hardCoreTheta z * (1 - hardCoreTheta z) * x)
      apply Finset.sum_congr rfl
      intro v hv
      exact sum_probability_mul_insertableOrOccupiedIndicator (G := G) z hz v

/-- **C.43.** `E W_L = (1-theta)s_R`, with the color-symmetric statement
obtained by arbitrary `c`. -/
theorem C43_expectedConditionalVariance (P : FiniteBipartition G)
    (c : BipartitionSide) (z : ℝ) (hz : 0 < z) :
    expectedConditionalVariance (G := G) P c z hz =
      (1 - hardCoreTheta z) *
        sideOccupationExpectation (G := G) P (BipartitionSide.opposite c) z hz := by
  rw [expectedConditionalVariance_eq_neighborFree_sum (G := G) P c z hz]
  unfold sideOccupationExpectation
  rw [← FiniteBipartition.other_eq_side_opposite]
  simp_rw [singleSiteOccupationProbability_eq_theta_mul_neighborFree
    (G := G) z hz]
  rw [← Finset.mul_sum]
  ring

/-- **C.43, left-to-right form.** `E W_L = (1-theta) s_R`. -/
theorem C43_expectedConditionalVariance_left (P : FiniteBipartition G)
    (z : ℝ) (hz : 0 < z) :
    expectedConditionalVariance (G := G) P .left z hz =
      (1 - hardCoreTheta z) *
        sideOccupationExpectation (G := G) P .right z hz := by
  simpa using C43_expectedConditionalVariance (G := G) P .left z hz

/-- **C.43, right-to-left form.** `E W_R = (1-theta) s_L`. -/
theorem C43_expectedConditionalVariance_right (P : FiniteBipartition G)
    (z : ℝ) (hz : 0 < z) :
    expectedConditionalVariance (G := G) P .right z hz =
      (1 - hardCoreTheta z) *
        sideOccupationExpectation (G := G) P .left z hz := by
  simpa using C43_expectedConditionalVariance (G := G) P .right z hz

end
end Forest
end Erdos993
