import Mathlib

/-!
# Tilted coefficient sequences and Turán inequalities

The normalized tilt below is intentionally stated for arbitrary real coefficient
sequences.  The first theorem is the denominator-free cross-multiplied identity;
the second shows that positive tilting neither creates nor destroys the strict
Turán inequality.
-/

namespace Erdos993

/-- The `z`-tilt of a coefficient sequence, normalized by `Z`. -/
noncomputable def tiltedMass (a : ℕ → ℝ) (z Z : ℝ) (k : ℕ) : ℝ := a k * z ^ k / Z

/-- Adjacent products under a tilt have the same common scaling factor.
No positivity or nonvanishing assumption is needed. -/
theorem tilted_cross_multiplication (a : ℕ → ℝ) (z Z : ℝ) (s : ℕ) (hs : 1 ≤ s) :
    tiltedMass a z Z (s - 1) * tiltedMass a z Z (s + 1) * (a s * a s) =
      tiltedMass a z Z s * tiltedMass a z Z s * (a (s - 1) * a (s + 1)) := by
  have he : (s - 1) + (s + 1) = s + s := by omega
  have hp : z ^ (s - 1) * z ^ (s + 1) = z ^ s * z ^ s := by
    rw [← pow_add, he, pow_add]
  simp only [tiltedMass, div_eq_mul_inv]
  calc
    _ = (a (s - 1) * a (s + 1) * (a s * a s) * (Z⁻¹ * Z⁻¹)) *
          (z ^ (s - 1) * z ^ (s + 1)) := by ring
    _ = (a (s - 1) * a (s + 1) * (a s * a s) * (Z⁻¹ * Z⁻¹)) *
          (z ^ s * z ^ s) := by rw [hp]
    _ = _ := by ring

/-- For a positive tilt and nonzero normalizer, strict Turán inequalities are
exactly equivalent before and after tilting.  No saddle-point condition occurs. -/
theorem tilted_strict_turan_iff (a : ℕ → ℝ) (z Z : ℝ) (s : ℕ) (hs : 1 ≤ s)
    (hz : 0 < z) (hZ : Z ≠ 0) :
    tiltedMass a z Z (s - 1) * tiltedMass a z Z (s + 1) <
        tiltedMass a z Z s * tiltedMass a z Z s ↔
      a (s - 1) * a (s + 1) < a s * a s := by
  have he : (s - 1) + (s + 1) = s + s := by omega
  have hp : z ^ (s - 1) * z ^ (s + 1) = z ^ s * z ^ s := by
    rw [← pow_add, he, pow_add]
  let c : ℝ := z ^ (s + s) / (Z * Z)
  have hc : 0 < c := div_pos (pow_pos hz _) (mul_self_pos.mpr hZ)
  have hneigh :
      tiltedMass a z Z (s - 1) * tiltedMass a z Z (s + 1) =
        c * (a (s - 1) * a (s + 1)) := by
    simp only [tiltedMass, c, div_eq_mul_inv]
    calc
      _ = (a (s - 1) * a (s + 1) * (Z⁻¹ * Z⁻¹)) *
            (z ^ (s - 1) * z ^ (s + 1)) := by ring
      _ = (a (s - 1) * a (s + 1) * (Z⁻¹ * Z⁻¹)) *
            (z ^ s * z ^ s) := by rw [hp]
      _ = _ := by rw [← pow_add]; ring
  have hcenter :
      tiltedMass a z Z s * tiltedMass a z Z s = c * (a s * a s) := by
    simp only [tiltedMass, c, div_eq_mul_inv]
    rw [pow_add]
    ring
  rw [hneigh, hcenter]
  constructor <;> intro h <;> nlinarith

end Erdos993
