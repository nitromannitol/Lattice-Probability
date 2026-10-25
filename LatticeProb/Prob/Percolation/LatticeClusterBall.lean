import LatticeProb.Prob.Percolation.LatticeBondGraph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Int.Interval

/-!
# Finite Euclidean balls in open lattice components

The lattice is embedded coordinatewise into Mathlib's Euclidean space. Intersecting an
open Euclidean ball with an actual open component gives a finite set of component vertices.
Finiteness follows from integer coordinate bounds, with arbitrary ambient centers and real radii.
-/

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ}

/-- The coordinatewise integer inclusion into Euclidean space, with its Euclidean metric. -/
def latticeEuclideanEmbedding : Vertex d ↪ EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun i => (x i : ℝ))
  inj' := by
    intro x y h
    funext i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin d) => v i) h
    change (x i : ℝ) = (y i : ℝ) at hi
    exact_mod_cast hi

/-- An ambient open Euclidean ball contains only finitely many lattice vertices. -/
theorem finite_latticeEuclideanBall (z : Vertex d) (r : ℝ) :
    {x : Vertex d | dist (latticeEuclideanEmbedding x)
      (latticeEuclideanEmbedding z) < r}.Finite := by
  have hbox := Set.Finite.pi' (fun i : Fin d =>
    Set.finite_Icc (z i - ⌈r⌉) (z i + ⌈r⌉))
  apply hbox.subset
  intro x hx i
  have hi := PiLp.norm_apply_le
    (latticeEuclideanEmbedding x - latticeEuclideanEmbedding z) i
  change |(x i : ℝ) - (z i : ℝ)| ≤
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding z‖ at hi
  have hb : |(x i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉ : ℝ) :=
    (hi.trans_lt (show ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding z‖ < r from hx)).le.trans (Int.le_ceil r)
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor
  · exact_mod_cast (by linarith : (z i : ℝ) - (⌈r⌉ : ℝ) ≤ (x i : ℝ))
  · exact_mod_cast (by linarith : (x i : ℝ) ≤ (z i : ℝ) + (⌈r⌉ : ℝ))

/-- The finite component-vertex carrier of an open Euclidean ball. -/
theorem finite_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    {x : C | dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding z) < r}.Finite :=
  (finite_latticeEuclideanBall z r).preimage Subtype.val_injective.injOn

/-- The literal intersection of a component with an open Euclidean ball, on its vertex subtype. -/
def componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) : Finset C :=
  (finite_componentEuclideanBall C z r).toFinset

/-- Membership is exactly strict Euclidean distance less than the given radius. -/
theorem mem_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) (x : C) :
    x ∈ componentEuclideanBall C z r ↔
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding z) < r :=
  Set.Finite.mem_toFinset _

/-- Ambient membership displays both literal component inclusion and Euclidean distance. -/
theorem mem_image_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z x : Vertex d) (r : ℝ) :
    x ∈ (componentEuclideanBall C z r).image Subtype.val ↔
      x ∈ C.supp ∧ dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding z) < r := by
  classical
  simp only [Finset.mem_image, mem_componentEuclideanBall]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hr⟩
    exact ⟨⟨x, hx⟩, hr, rfl⟩

/-- Balls of nonpositive radius are empty, including radius zero. -/
theorem componentEuclideanBall_eq_empty {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) {r : ℝ} (hr : r ≤ 0) : componentEuclideanBall C z r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact (not_lt_of_ge (hr.trans dist_nonneg))
    ((mem_componentEuclideanBall C z r x).mp hx)

/-- Increasing the radius increases the component ball. -/
theorem componentEuclideanBall_mono {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) {r s : ℝ} (hrs : r ≤ s) :
    componentEuclideanBall C z r ⊆ componentEuclideanBall C z s := by
  intro x hx
  exact (mem_componentEuclideanBall C z s x).mpr
    (((mem_componentEuclideanBall C z r x).mp hx).trans_le hrs)

/-- A center in the component belongs to every ball of positive radius. -/
theorem center_mem_componentEuclideanBall {ω : Configuration d} (C : OpenComponent ω)
    (z : C) {r : ℝ} (hr : 0 < r) : z ∈ componentEuclideanBall C z.val r := by
  rw [mem_componentEuclideanBall, dist_self]
  exact hr

/-- Nonemptiness means that an actual component vertex lies at strict Euclidean distance. -/
theorem componentEuclideanBall_nonempty_iff {ω : Configuration d} (C : OpenComponent ω)
    (z : Vertex d) (r : ℝ) :
    (componentEuclideanBall C z r).Nonempty ↔
      ∃ x : Vertex d, x ∈ C.supp ∧
        dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding z) < r := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x.val, x.property, (mem_componentEuclideanBall C z r x).mp hx⟩
  · rintro ⟨x, hx, hr⟩
    exact ⟨⟨x, hx⟩, (mem_componentEuclideanBall C z r ⟨x, hx⟩).mpr hr⟩

/-- With a center in the component, nonemptiness is equivalent to positive radius. -/
theorem componentEuclideanBall_center_nonempty_iff {ω : Configuration d}
    (C : OpenComponent ω) (z : C) (r : ℝ) :
    (componentEuclideanBall C z.val r).Nonempty ↔ 0 < r := by
  constructor
  · rintro ⟨x, hx⟩
    exact dist_nonneg.trans_lt ((mem_componentEuclideanBall C z.val r x).mp hx)
  · intro hr
    exact ⟨z, center_mem_componentEuclideanBall C z hr⟩

/-- In the all-closed configuration each component contains just its given vertex. -/
theorem allClosed_component_vertex_eq (z : Vertex d)
    (x : (openGraph (allClosed d)).connectedComponentMk z) : x.val = z := by
  have h := ((openGraph (allClosed d)).connectedComponentMk z).reachable_of_mem_supp
    x.property (show z ∈ ((openGraph (allClosed d)).connectedComponentMk z).supp from rfl)
  simpa only [openGraph_allClosed, SimpleGraph.reachable_bot] using h

/-- A positive ball in an all-closed component is literally the singleton center. -/
theorem allClosed_componentEuclideanBall (z : Vertex d) {r : ℝ} (hr : 0 < r) :
    componentEuclideanBall ((openGraph (allClosed d)).connectedComponentMk z) z r =
      {⟨z, rfl⟩} := by
  classical
  ext x
  have hx : x = ⟨z, rfl⟩ := Subtype.ext (allClosed_component_vertex_eq z x)
  subst x
  simp only [Finset.mem_singleton, mem_componentEuclideanBall, dist_self, hr]

/-- Its actual cardinality is one, independently of the ambient dimension or positive radius. -/
theorem card_allClosed_componentEuclideanBall (z : Vertex d) {r : ℝ} (hr : 0 < r) :
    (componentEuclideanBall ((openGraph (allClosed d)).connectedComponentMk z) z r).card = 1 := by
  rw [allClosed_componentEuclideanBall z hr, Finset.card_singleton]

end

end LatticeProb.Percolation
