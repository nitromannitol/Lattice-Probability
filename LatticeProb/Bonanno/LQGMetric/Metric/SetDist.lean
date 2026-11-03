/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.SetDist at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distance between sets and geodesics between sets

* `setEDist A B` is GM's `𝔡(A, B) := inf_{x ∈ A, y ∈ B} 𝔡(x, y)` (`uniqueness-final.tex`
  l. 257–260 of arXiv:1905.00383), in `[0, ∞]` (`∞` if `A` or `B` is empty), built from mathlib's
  `Metric.infEDist`. Basic properties: comparison with point distances, symmetry,
  monotonicity, singletons, closures, attainment for compact sets.
* `IsGeodesicCurveBetween P a b A B`: a geodesic from `A` to `B` in CONF's sense
  (`confluence-final.tex` l. 499 of arXiv:1905.00381: "a geodesic from `A` to `B`, i.e. a path
  of length `D(A, B)` between these sets"); such a curve is a geodesic between its endpoints and
  its endpoints realize `D(A, B)`.

These are elementary facts (no published proof needed beyond the definitions); own elementary
proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- GM's distance between sets, `𝔡(A, B) = inf_{x ∈ A, y ∈ B} 𝔡(x, y)`. -/
noncomputable def setEDist (A B : Set X) : ℝ≥0∞ :=
  ⨅ x ∈ A, infEDist x B

theorem setEDist_eq_iInf (A B : Set X) : setEDist A B = ⨅ x ∈ A, ⨅ y ∈ B, edist x y :=
  rfl

theorem le_setEDist {A B : Set X} {d : ℝ≥0∞} :
    d ≤ setEDist A B ↔ ∀ x ∈ A, ∀ y ∈ B, d ≤ edist x y := by
  simp only [setEDist, le_iInf_iff, le_infEDist]

theorem setEDist_le_edist {A B : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ B) :
    setEDist A B ≤ edist x y :=
  (iInf₂_le x hx).trans (infEDist_le_edist_of_mem hy)

theorem setEDist_le_infEDist {A B : Set X} {x : X} (hx : x ∈ A) : setEDist A B ≤ infEDist x B :=
  iInf₂_le x hx

theorem setEDist_comm (A B : Set X) : setEDist A B = setEDist B A := by
  refine le_antisymm ?_ ?_ <;> rw [le_setEDist] <;> intro x hx y hy
  · rw [edist_comm]; exact setEDist_le_edist hy hx
  · rw [edist_comm]; exact setEDist_le_edist hy hx

theorem setEDist_anti {A A' B B' : Set X} (hA : A ⊆ A') (hB : B ⊆ B') :
    setEDist A' B' ≤ setEDist A B :=
  le_setEDist.2 fun _ hx _ hy => setEDist_le_edist (hA hx) (hB hy)

@[simp] theorem setEDist_singleton_left (x : X) (B : Set X) : setEDist {x} B = infEDist x B := by
  simp [setEDist]

@[simp] theorem setEDist_singleton (x y : X) : setEDist {x} {y} = edist x y := by
  simp

@[simp] theorem setEDist_empty_left (B : Set X) : setEDist (∅ : Set X) B = ∞ := by
  simp [setEDist]

@[simp] theorem setEDist_empty_right (A : Set X) : setEDist A (∅ : Set X) = ∞ := by
  rw [setEDist_comm, setEDist_empty_left]

theorem setEDist_closure (A B : Set X) : setEDist (closure A) (closure B) = setEDist A B := by
  refine le_antisymm (setEDist_anti subset_closure subset_closure) (le_setEDist.2 ?_)
  intro x hx y hy
  have h1 : setEDist A B ≤ infEDist x B := by
    have hc : IsClosed {z | setEDist A B ≤ infEDist z B} :=
      isClosed_le continuous_const continuous_infEDist
    exact closure_minimal (fun z hz => setEDist_le_infEDist hz) hc hx
  refine h1.trans ?_
  rw [← infEDist_closure]
  exact infEDist_le_edist_of_mem hy

/-- For nonempty compact sets the infimum is attained. -/
theorem IsCompact.exists_setEDist_eq_edist {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hA' : A.Nonempty) (hB' : B.Nonempty) : ∃ x ∈ A, ∃ y ∈ B, setEDist A B = edist x y := by
  obtain ⟨x, hx, hmin⟩ := hA.exists_isMinOn hA' (continuous_infEDist (s := B)).continuousOn
  obtain ⟨y, hy, hxy⟩ := hB.exists_infEDist_eq_edist hB' x
  refine ⟨x, hx, y, hy, le_antisymm (setEDist_le_edist hx hy) ?_⟩
  rw [← hxy]
  exact le_iInf₂ fun z hz => hmin hz

/-- A **geodesic from `A` to `B`** (CONF l. 499): a curve `P : [a, b] → X` from a point of `A` to
a point of `B` whose length is `𝔡(A, B)`. -/
def IsGeodesicCurveBetween (P : ℝ → X) (a b : ℝ) (A B : Set X) : Prop :=
  a ≤ b ∧ ContinuousOn P (Icc a b) ∧ P a ∈ A ∧ P b ∈ B ∧ curveLength P a b = setEDist A B

/-- A geodesic from `A` to `B` is a geodesic between its endpoints, which realize `𝔡(A, B)`. -/
theorem IsGeodesicCurveBetween.isGeodesicCurve {P : ℝ → X} {a b : ℝ} {A B : Set X}
    (hP : IsGeodesicCurveBetween P a b A B) :
    IsGeodesicCurve P a b ∧ edist (P a) (P b) = setEDist A B := by
  obtain ⟨hab, hc, ha, hb, hL⟩ := hP
  have h1 := edist_le_curveLength P hab
  have h2 := setEDist_le_edist ha hb
  have h3 : edist (P a) (P b) = setEDist A B := le_antisymm (h1.trans hL.le) h2
  exact ⟨⟨hab, hc, hL.trans h3.symm⟩, h3⟩

end LQGMetric.MetricGeometry
