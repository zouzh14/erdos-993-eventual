import Erdos993.Forest.MaximalModulusPathLemma

/-!
# Concrete recursive continuation after Appendix A.9

This file defines the actual stopping/continuation construction used in Lemma
A.10.  The global starting scale `X`, cutoff fraction `σ`, and bounded-scale
cutoff `X0` remain fixed during the recursion.  Every recursive call moves to
an actual child or grandchild and is justified by strict `subtreeOrder` descent.
-/

namespace Erdos993
namespace Forest
namespace AppendixA

noncomputable section

open scoped BigOperators
open ActualRootedVariance UniformFourthMoment
open ActualRootedVariance.ComponentRooting

universe u
variable {V : Type u} [Fintype V] {G : SimpleGraph V}

noncomputable local instance classicalDecidableEqA10Data (α : Type*) : DecidableEq α :=
  Classical.decEq α

/-- A current subtree is retained when it has reached bounded scale or is an
actual high-scale narrow subtree. -/
def IsA10Retained
    (R : ComponentRooting G) (Z z : ℝ) (hz : 0 < z) (θ X0 : ℝ) (u : V) : Prop :=
  descendantScaleAt R z hz θ u ≤ X0 ∨ IsHighScaleNarrow R Z z hz θ u

/-- Components of a finite deletion forest whose scale exceeds the fixed
fraction `σ X` of the original global scale. -/
noncomputable def heavyRootsIn
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ)
    (s : Finset V) : Finset V :=
  s.filter (fun v => σ * X < descendantScaleAt R z hz θ v)

/-- Heavy components of the root-vacant (`Q`) deletion forest. -/
noncomputable def qHeavyRoots
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ) (u : V) :
    Finset V :=
  heavyRootsIn R z hz θ σ X (R.children (G := G) u)

/-- Heavy components of the closed-root (`R`) deletion forest. -/
noncomputable def rHeavyRoots
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ) (u : V) :
    Finset V :=
  heavyRootsIn R z hz θ σ X (grandchildrenAt R u)

@[simp] theorem mem_heavyRootsIn
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ)
    (s : Finset V) (v : V) :
    v ∈ heavyRootsIn R z hz θ σ X s ↔
      v ∈ s ∧ σ * X < descendantScaleAt R z hz θ v := by
  simp [heavyRootsIn]

@[simp] theorem mem_qHeavyRoots
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ)
    (u v : V) :
    v ∈ qHeavyRoots R z hz θ σ X u ↔
      R.IsChild (G := G) u v ∧ σ * X < descendantScaleAt R z hz θ v := by
  simp [qHeavyRoots, heavyRootsIn]

@[simp] theorem mem_rHeavyRoots
    (R : ComponentRooting G) (z : ℝ) (hz : 0 < z) (θ σ X : ℝ)
    (u v : V) :
    v ∈ rHeavyRoots R z hz θ σ X u ↔
      v ∈ grandchildrenAt R u ∧ σ * X < descendantScaleAt R z hz θ v := by
  simp [rHeavyRoots, heavyRootsIn]

/-- The actual A.10 continuation data.  `qStep` and `rStep` occur exactly when
the chosen maximal-modulus deletion forest has one heavy component.  The two
`split` constructors record the complementary stopping case. -/
inductive RecursiveDecomposition
    (R : ComponentRooting G) (Z z : ℝ) (hz : 0 < z)
    (θ X σ X0 : ℝ) : V → Type u
  | retained (u : V)
      (hretain : IsA10Retained R Z z hz θ X0 u) :
      RecursiveDecomposition R Z z hz θ X σ X0 u
  | splitQ (u : V)
      (hretain : ¬ IsA10Retained R Z z hz θ X0 u)
      (hmax : occupiedCharacteristicModulusAt R z hz θ u ≤
        vacantCharacteristicModulusAt R z hz θ u)
      (hsplit : ¬ ∃ v : V, qHeavyRoots R z hz θ σ X u = {v}) :
      RecursiveDecomposition R Z z hz θ X σ X0 u
  | splitR (u : V)
      (hretain : ¬ IsA10Retained R Z z hz θ X0 u)
      (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
        occupiedCharacteristicModulusAt R z hz θ u)
      (hsplit : ¬ ∃ v : V, rHeavyRoots R z hz θ σ X u = {v}) :
      RecursiveDecomposition R Z z hz θ X σ X0 u
  | qStep {u v : V}
      (hretain : ¬ IsA10Retained R Z z hz θ X0 u)
      (hmax : occupiedCharacteristicModulusAt R z hz θ u ≤
        vacantCharacteristicModulusAt R z hz θ u)
      (hone : qHeavyRoots R z hz θ σ X u = {v})
      (huv : R.IsChild (G := G) u v)
      (tail : RecursiveDecomposition R Z z hz θ X σ X0 v) :
      RecursiveDecomposition R Z z hz θ X σ X0 u
  | rStep {u c v : V}
      (hretain : ¬ IsA10Retained R Z z hz θ X0 u)
      (hmax : vacantCharacteristicModulusAt R z hz θ u ≤
        occupiedCharacteristicModulusAt R z hz θ u)
      (hone : rHeavyRoots R z hz θ σ X u = {v})
      (huc : R.IsChild (G := G) u c)
      (hcv : R.IsChild (G := G) c v)
      (tail : RecursiveDecomposition R Z z hz θ X σ X0 v) :
      RecursiveDecomposition R Z z hz θ X σ X0 u

/-- Canonical A.10 construction.  It tests retention first, uses exactly the
A.9 maximal-modulus tie rule, and continues precisely through a unique heavy
component. -/
noncomputable def recursiveDecomposition
    (R : ComponentRooting G) (Z z : ℝ) (hz : 0 < z)
    (θ X σ X0 : ℝ) (u : V) :
    RecursiveDecomposition R Z z hz θ X σ X0 u := by
  classical
  by_cases hretain : IsA10Retained R Z z hz θ X0 u
  · exact .retained u hretain
  · by_cases hQ : occupiedCharacteristicModulusAt R z hz θ u ≤
        vacantCharacteristicModulusAt R z hz θ u
    · by_cases hone : ∃ v : V, qHeavyRoots R z hz θ σ X u = {v}
      · let v := Classical.choose hone
        have hvset : qHeavyRoots R z hz θ σ X u = {v} :=
          Classical.choose_spec hone
        have hvheavy : v ∈ qHeavyRoots R z hz θ σ X u := by
          rw [hvset]
          simp
        have huv : R.IsChild (G := G) u v :=
          (mem_qHeavyRoots R z hz θ σ X u v).mp hvheavy |>.1
        exact .qStep hretain hQ hvset huv
          (recursiveDecomposition R Z z hz θ X σ X0 v)
      · exact .splitQ u hretain hQ hone
    · have hR : vacantCharacteristicModulusAt R z hz θ u ≤
          occupiedCharacteristicModulusAt R z hz θ u := le_of_not_ge hQ
      by_cases hone : ∃ v : V, rHeavyRoots R z hz θ σ X u = {v}
      · let v := Classical.choose hone
        have hvset : rHeavyRoots R z hz θ σ X u = {v} :=
          Classical.choose_spec hone
        have hvheavy : v ∈ rHeavyRoots R z hz θ σ X u := by
          rw [hvset]
          simp
        have hvg : v ∈ grandchildrenAt R u :=
          (mem_rHeavyRoots R z hz θ σ X u v).mp hvheavy |>.1
        let hex := Finset.mem_biUnion.mp hvg
        let c := Classical.choose hex
        have hucmem : c ∈ R.children (G := G) u :=
          (Classical.choose_spec hex).1
        have hcvmem : v ∈ R.children (G := G) c :=
          (Classical.choose_spec hex).2
        exact .rStep hretain hR hvset
          ((R.mem_children (G := G) u c).mp hucmem)
          ((R.mem_children (G := G) c v).mp hcvmem)
          (recursiveDecomposition R Z z hz θ X σ X0 v)
      · exact .splitR u hretain hR hone
termination_by R.subtreeOrder (G := G) u
decreasing_by
  · exact R.subtreeOrder_child_lt (G := G) huv
  · exact (R.subtreeOrder_child_lt (G := G)
      ((R.mem_children (G := G) c v).mp hcvmem)).trans
      (R.subtreeOrder_child_lt (G := G)
        ((R.mem_children (G := G) u c).mp hucmem))

namespace RecursiveDecomposition

/-- Forgetting the A.10 stop reason gives the genuine concrete A.9 trace. -/
def toTrace
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V} :
    RecursiveDecomposition R Z z hz θ X σ X0 u →
      MaximalModulusTrace R z hz θ u
  | .retained u _ => .stop u
  | .splitQ u _ _ _ => .stop u
  | .splitR u _ _ _ => .stop u
  | .qStep _ hmax _ huv tail => .qStep huv hmax tail.toTrace
  | .rStep _ hmax _ huc hcv tail => .rStep huc hcv hmax tail.toTrace

/-- The actual recursive family `C(T)`: all components discarded along the
unique-heavy continuation, followed either by the retained terminal subtree or
by every component of the final deletion forest. -/
noncomputable def family
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V} :
    RecursiveDecomposition R Z z hz θ X σ X0 u → Finset V
  | .retained u _ => {u}
  | .splitQ u _ _ _ => R.children (G := G) u
  | .splitR u _ _ _ => grandchildrenAt R u
  | .qStep (u := u) (v := v) _ _ _ _ tail =>
      MaximalModulusTrace.qDiscardedRoots R u v ∪ tail.family
  | .rStep (u := u) (c := c) (v := v) _ _ _ _ _ tail =>
      MaximalModulusTrace.rDiscardedRoots R u c v ∪ tail.family

/-- The terminal selected subtree root. -/
def terminalRoot
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) : V :=
  D.toTrace.terminalRoot

/-- The concrete A.9 charge generated by this run. -/
noncomputable def K
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) : ℝ :=
  D.toTrace.K

/-- The recursion terminates because the constructed object is finite; this
public equation records that every actual recursive continuation took a
strictly smaller descendant-cardinality measure. -/
theorem step_subtreeOrder_lt
    {R : ComponentRooting G} {Z z : ℝ} {hz : 0 < z}
    {θ X σ X0 : ℝ} {u : V}
    (D : RecursiveDecomposition R Z z hz θ X σ X0 u) :
    match D with
    | .qStep (v := v) _ _ _ huv _ =>
        R.subtreeOrder (G := G) v < R.subtreeOrder (G := G) u
    | .rStep (c := c) (v := v) _ _ _ huc hcv _ =>
        R.subtreeOrder (G := G) v < R.subtreeOrder (G := G) u
    | _ => True := by
  cases D with
  | retained => trivial
  | splitQ => trivial
  | splitR => trivial
  | qStep hretain hmax hone huv tail =>
      exact R.subtreeOrder_child_lt (G := G) huv
  | rStep hretain hmax hone huc hcv tail =>
      exact (R.subtreeOrder_child_lt (G := G) hcv).trans
        (R.subtreeOrder_child_lt (G := G) huc)

end RecursiveDecomposition

end
end AppendixA
end Forest
end Erdos993
