import Erdos993.Forest.NarrowSubtreeLoss

/-!
# The concrete maximal-modulus Q/R path data for Appendix A.9

This module records the actual finite choices made by the root deletion
recursion.  A `qStep` selects a child component of `Tᵤ-u`; an `rStep` selects
a grandchild component of `Tᵤ-N[u]` and records the intervening child so that
the resulting vertex list is an honest downward path.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance
open ActualRootedVariance.ComponentRooting

universe u

variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA9Data (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- Roots of the components of `Tᵤ-N[u]`: the grandchildren of `u`. -/
noncomputable def grandchildrenAt
    (R : ComponentRooting G) (u : V) : Finset V :=
  (R.children (G := G) u).biUnion (fun c => R.children (G := G) c)

/-- A finite trace of genuine maximal-modulus deletion choices.  The inequality
stored by each constructor says precisely that its chosen deletion forest is
one of the two forests having maximal characteristic modulus. -/
inductive MaximalModulusTrace
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) : V → Type u
  | stop (u : V) : MaximalModulusTrace R z hz θ u
  | qStep {u v : V}
      (huv : R.IsChild (G := G) u v)
      (hmax : occupiedCharacteristicModulusAt R z hz θ u ≤
        vacantCharacteristicModulusAt R z hz θ u)
      (tail : MaximalModulusTrace R z hz θ v) :
      MaximalModulusTrace R z hz θ u
  | rStep {u c v : V}
      (huc : R.IsChild (G := G) u c)
      (hcv : R.IsChild (G := G) c v)
      (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
        occupiedCharacteristicModulusAt R z hz θ u)
      (tail : MaximalModulusTrace R z hz θ v) :
      MaximalModulusTrace R z hz θ u

namespace MaximalModulusTrace

/-- The filled vertex path.  An R-choice contributes both child edges. -/
def vertices {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → List V
  | .stop u => [u]
  | .qStep _ _ tail => u :: tail.vertices
  | .rStep (c := c) _ _ _ tail => u :: c :: tail.vertices

@[simp] theorem vertices_stop
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) (u : V) :
    (MaximalModulusTrace.stop (R := R) (z := z) (hz := hz) (θ := θ) u).vertices = [u] := rfl

/-- The root of the final selected descendant subtree. -/
def terminalRoot {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → V
  | .stop u => u
  | .qStep _ _ tail => tail.terminalRoot
  | .rStep _ _ _ tail => tail.terminalRoot

/-- Number of actual Q/R choices. -/
def choiceCount {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → ℕ
  | .stop _ => 0
  | .qStep _ _ tail => tail.choiceCount + 1
  | .rStep _ _ _ tail => tail.choiceCount + 1

/-- All discarded Q-components at a Q-step. -/
noncomputable def qDiscardedRoots (R : ComponentRooting G) (u v : V) : Finset V :=
  (R.children (G := G) u).erase v

/-- All discarded R-components at an R-step through `u-c-v`. -/
noncomputable def rDiscardedRoots (R : ComponentRooting G) (u c v : V) : Finset V :=
  (R.children (G := G) c).erase v ∪
    ((R.children (G := G) u).erase c).biUnion
      (fun d => R.children (G := G) d)

/-- The concrete finite family of all discarded component roots. -/
noncomputable def discardedRoots
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    MaximalModulusTrace R z hz θ u → Finset V
  | .stop _ => ∅
  | .qStep (u := u) (v := v) _ _ tail =>
      qDiscardedRoots R u v ∪ tail.discardedRoots
  | .rStep (u := u) (c := c) (v := v) _ _ _ tail =>
      rDiscardedRoots R u c v ∪ tail.discardedRoots

/-- The filled list starts at the trace index. -/
theorem vertices_eq_cons_tail
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.vertices = u :: τ.vertices.tail := by
  cases τ <;> rfl

/-- Filled paths are genuine child chains. -/
theorem vertices_isChain
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.vertices.IsChain (R.IsChild (G := G)) := by
  induction τ with
  | stop u => simp [vertices]
  | @qStep u v huv hmax tail ih =>
      rw [tail.vertices_eq_cons_tail] at ih
      change (u :: tail.vertices).IsChain (R.IsChild (G := G))
      rw [tail.vertices_eq_cons_tail]
      exact List.IsChain.cons_cons huv ih
  | @rStep u c v huc hcv hmax tail ih =>
      rw [tail.vertices_eq_cons_tail] at ih
      change (u :: c :: tail.vertices).IsChain (R.IsChild (G := G))
      rw [tail.vertices_eq_cons_tail]
      exact List.IsChain.cons_cons huc (List.IsChain.cons_cons hcv ih)

@[simp] theorem vertices_head
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) :
    τ.vertices.head? = some u := by cases τ <;> rfl

/-- A nontrivial trace produces the actual filled `DownwardPath`. -/
def toDownwardPath
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V} :
    (τ : MaximalModulusTrace R z hz θ u) → τ.choiceCount ≠ 0 → DownwardPath R
  | .stop _, h => False.elim (h rfl)
  | .qStep (u := u) (v := v) huv hmax tail, _ =>
      ⟨u, v, tail.vertices.tail, by
        have hc := (MaximalModulusTrace.qStep huv hmax tail).vertices_isChain
        change (u :: tail.vertices).IsChain (R.IsChild (G := G)) at hc
        rw [tail.vertices_eq_cons_tail] at hc
        exact hc⟩
  | .rStep (u := u) (c := c) huc hcv hmax tail, _ =>
      ⟨u, c, tail.vertices, by
        have hc := (MaximalModulusTrace.rStep huc hcv hmax tail).vertices_isChain
        change (u :: c :: tail.vertices).IsChain (R.IsChild (G := G)) at hc
        exact hc⟩

@[simp] theorem toDownwardPath_vertices
    {R : ComponentRooting G} {z : ℝ} {hz : 0 < z} {θ : ℝ} {u : V}
    (τ : MaximalModulusTrace R z hz θ u) (hτ : τ.choiceCount ≠ 0) :
    (τ.toDownwardPath hτ).vertices = τ.vertices := by
  cases τ with
  | stop u => exact False.elim (hτ rfl)
  | qStep huv hmax tail =>
      simp only [toDownwardPath, DownwardPath.vertices, vertices]
      rw [tail.vertices_eq_cons_tail]
      rfl
  | rStep huc hcv hmax tail => rfl

/-- Canonical finite construction, truncated after the supplied number of
choices.  Whenever the selected maximal deletion forest has a component, an
actual component is chosen; otherwise the trace terminates. -/
noncomputable def canonical
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ) :
    (fuel : ℕ) → (u : V) → MaximalModulusTrace R z hz θ u
  | 0, u => .stop u
  | fuel + 1, u =>
      if hQ : occupiedCharacteristicModulusAt R z hz θ u ≤
          vacantCharacteristicModulusAt R z hz θ u then
        if hne : (R.children (G := G) u).Nonempty then
          let v := hne.choose
          .qStep ((R.mem_children (G := G) u v).mp hne.choose_spec)
            hQ (canonical R z hz θ fuel v)
        else .stop u
      else
        if hne : (grandchildrenAt R u).Nonempty then
          let v := hne.choose
          have hv := hne.choose_spec
          have hex := Finset.mem_biUnion.mp hv
          let c := hex.choose
          .rStep ((R.mem_children (G := G) u c).mp hex.choose_spec.1)
            ((R.mem_children (G := G) c v).mp hex.choose_spec.2)
            (le_of_not_ge hQ) (canonical R z hz θ fuel v)
        else .stop u

/-- The canonical construction exists for every finite rooted tree and every
descendant subtree root, at every requested finite truncation length. -/
theorem exists_canonical
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ : ℝ)
    (fuel : ℕ) (u : V) :
    ∃ τ : MaximalModulusTrace R z hz θ u,
      τ = canonical R z hz θ fuel u :=
  ⟨canonical R z hz θ fuel u, rfl⟩

end MaximalModulusTrace
end
end AppendixA
end Forest
end Erdos993
