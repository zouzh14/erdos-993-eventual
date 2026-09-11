import Erdos993.Forest.Specification

/-!
# Graph-level first-recovery consequences

This module packages the abstract first-recovery results from
`Forest.Specification` for independence-polynomial coefficient sequences.  It
does not introduce a second notion of recovery or a second canonical state.
-/

namespace Erdos993
namespace Forest

noncomputable section

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

/-- At a graph first recovery, downward closure makes the central independence
coefficient strictly positive. -/
theorem IsFirstRecovery.independence_center_pos {s : ℕ}
    (h : IsFirstRecovery (independenceCoefficients G) s) :
    0 < independenceCoefficients G s := by
  have hrise := h.isRecovery.2
  have hcenter_nonneg : 0 ≤ independenceCoefficients G s := Nat.cast_nonneg _
  have hsucc_real : 0 < independenceCoefficients G (s + 1) :=
    lt_of_le_of_lt hcenter_nonneg hrise
  have hsucc_nat : 0 < independenceCoeff G (s + 1) := by
    change (0 : ℝ) < (independenceCoeff G (s + 1) : ℝ) at hsucc_real
    exact_mod_cast hsucc_real
  have hcenter_nat := independenceCoeff_pos_of_succ_pos G s hsucc_nat
  change (0 : ℝ) < (independenceCoeff G s : ℝ)
  exact_mod_cast hcenter_nat

/-- The abstract negative-minor theorem specialized to graph independence
coefficients. -/
theorem IsFirstRecovery.independence_centralTuranMinor_neg {s : ℕ}
    (h : IsFirstRecovery (independenceCoefficients G) s) :
    centralTuranMinor (independenceCoefficients G) s < 0 :=
  centralTuranMinor_neg_of_firstRecovery h h.independence_center_pos

/-- Positive tilting converts graph first recovery into strict reverse Turan
at the same three ranks. -/
theorem IsFirstRecovery.independence_tilted_strict_reverse_turan {s : ℕ}
    (h : IsFirstRecovery (independenceCoefficients G) s)
    {z Z : ℝ} (hz : 0 < z) (hZ : Z ≠ 0) :
    tiltedMass (independenceCoefficients G) z Z s *
        tiltedMass (independenceCoefficients G) z Z s <
      tiltedMass (independenceCoefficients G) z Z (s - 1) *
        tiltedMass (independenceCoefficients G) z Z (s + 1) := by
  rw [tilted_strict_reverse_turan_iff]
  · exact sub_neg.mp h.independence_centralTuranMinor_neg
  · exact h.index_pos
  · exact hz
  · exact hZ

/-- In the orientation of `tilted_strict_turan_iff`, first recovery rules out
the usual strict Turan inequality. -/
theorem IsFirstRecovery.independence_not_tilted_strict_turan {s : ℕ}
    (h : IsFirstRecovery (independenceCoefficients G) s)
    {z Z : ℝ} (hz : 0 < z) (hZ : Z ≠ 0) :
    ¬(tiltedMass (independenceCoefficients G) z Z (s - 1) *
        tiltedMass (independenceCoefficients G) z Z (s + 1) <
      tiltedMass (independenceCoefficients G) z Z s *
        tiltedMass (independenceCoefficients G) z Z s) := by
  rw [tilted_strict_turan_iff _ _ _ _ h.index_pos hz hZ]
  exact not_lt_of_ge (le_of_lt (sub_neg.mp h.independence_centralTuranMinor_neg))

/-- A nonunimodal graph coefficient sequence has a least recovery carrying
all adjacent inequalities from (1.1). -/
theorem exists_graph_firstRecovery_witness
    (hG : ¬WeaklyUnimodal (independenceCoefficients G)) :
    ∃ s, IsFirstRecovery (independenceCoefficients G) s ∧
      independenceCoefficients G s ≤ independenceCoefficients G (s - 1) ∧
      independenceCoefficients G s < independenceCoefficients G (s + 1) ∧
      centralTuranMinor (independenceCoefficients G) s < 0 := by
  obtain ⟨s, hs⟩ := (exists_firstRecovery_iff (independenceCoefficients G)).2 hG
  exact ⟨s, hs, hs.prev_ge, hs.isRecovery.2,
    hs.independence_centralTuranMinor_neg⟩

/-- Graph-level nonunimodality produces a least recovery whose positive tilt
has a strict reverse Turan inequality. -/
theorem exists_graph_firstRecovery_tilted_reverse_turan
    (hG : ¬WeaklyUnimodal (independenceCoefficients G))
    {z Z : ℝ} (hz : 0 < z) (hZ : Z ≠ 0) :
    ∃ s, IsFirstRecovery (independenceCoefficients G) s ∧
      tiltedMass (independenceCoefficients G) z Z s *
          tiltedMass (independenceCoefficients G) z Z s <
        tiltedMass (independenceCoefficients G) z Z (s - 1) *
          tiltedMass (independenceCoefficients G) z Z (s + 1) := by
  obtain ⟨s, hs⟩ := (exists_firstRecovery_iff (independenceCoefficients G)).2 hG
  exact ⟨s, hs, hs.independence_tilted_strict_reverse_turan hz hZ⟩

end
end Forest
end Erdos993
