/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/SetDist.lean.
-/
import LatticeProb.Topology.Length.Geodesic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Distance between sets and geodesics between sets

* `setEDist A B` is the infimum of `edist x y` over `x ∈ A` and `y ∈ B`, a value in `[0, ∞]`
  (`∞` if `A` or `B` is empty). It is built from `Metric.infEDist`. The file proves comparison
  with point distances, symmetry, monotonicity, singletons, closures, and attainment of the
  infimum for nonempty compact sets.
* `IsGeodesicCurveBetween P a b A B` says that `P : [a, b] → X` is continuous on `[a, b]`, starts
  in `A`, ends in `B`, and has length `setEDist A B` on `[a, b]`. Such a curve is a geodesic
  between its endpoints, and its endpoints realize `setEDist A B`
  (`IsGeodesicCurveBetween.isGeodesicCurve`).
-/

open Set Filter Topology Metric
open scoped ENNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- The distance between two sets: the infimum of `edist x y` over `x ∈ A` and `y ∈ B`. -/
noncomputable def setEDist (A B : Set X) : ℝ≥0∞ :=
  ⨅ x ∈ A, infEDist x B

/-- The distance between two sets is the infimum of `edist x y` over pairs of points. -/
theorem setEDist_eq_iInf (A B : Set X) : setEDist A B = ⨅ x ∈ A, ⨅ y ∈ B, edist x y :=
  rfl

/-- A lower bound on `setEDist A B` is a lower bound on every `edist x y` with `x ∈ A`, `y ∈ B`. -/
theorem le_setEDist {A B : Set X} {d : ℝ≥0∞} :
    d ≤ setEDist A B ↔ ∀ x ∈ A, ∀ y ∈ B, d ≤ edist x y := by
  simp only [setEDist, le_iInf_iff, le_infEDist]

/-- The distance between two sets is at most the distance between any two of their points. -/
theorem setEDist_le_edist {A B : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ B) :
    setEDist A B ≤ edist x y :=
  (iInf₂_le x hx).trans (infEDist_le_edist_of_mem hy)

/-- The distance between two sets is at most the distance from a point of the first set. -/
theorem setEDist_le_infEDist {A B : Set X} {x : X} (hx : x ∈ A) : setEDist A B ≤ infEDist x B :=
  iInf₂_le x hx

/-- The distance between two sets is symmetric. -/
theorem setEDist_comm (A B : Set X) : setEDist A B = setEDist B A := by
  refine le_antisymm ?_ ?_ <;> rw [le_setEDist] <;> intro x hx y hy
  · rw [edist_comm]; exact setEDist_le_edist hy hx
  · rw [edist_comm]; exact setEDist_le_edist hy hx

/-- The distance between two sets decreases when the sets are enlarged. -/
theorem setEDist_anti {A A' B B' : Set X} (hA : A ⊆ A') (hB : B ⊆ B') :
    setEDist A' B' ≤ setEDist A B :=
  le_setEDist.2 fun _ hx _ hy => setEDist_le_edist (hA hx) (hB hy)

/-- The distance from a singleton to a set is the point-to-set distance. -/
@[simp] theorem setEDist_singleton_left (x : X) (B : Set X) : setEDist {x} B = infEDist x B := by
  simp [setEDist]

/-- The distance between two singletons is the distance between their points. -/
@[simp] theorem setEDist_singleton (x y : X) : setEDist {x} {y} = edist x y := by
  simp

/-- The distance from the empty set to any set is `∞`. -/
@[simp] theorem setEDist_empty_left (B : Set X) : setEDist (∅ : Set X) B = ∞ := by
  simp [setEDist]

/-- The distance from any set to the empty set is `∞`. -/
@[simp] theorem setEDist_empty_right (A : Set X) : setEDist A (∅ : Set X) = ∞ := by
  rw [setEDist_comm, setEDist_empty_left]

/-- Taking closures does not change the distance between two sets. -/
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

/-- For nonempty compact sets the infimum defining `setEDist` is attained. -/
theorem IsCompact.exists_setEDist_eq_edist {A B : Set X} (hA : IsCompact A) (hB : IsCompact B)
    (hA' : A.Nonempty) (hB' : B.Nonempty) : ∃ x ∈ A, ∃ y ∈ B, setEDist A B = edist x y := by
  obtain ⟨x, hx, hmin⟩ := hA.exists_isMinOn hA' (continuous_infEDist (s := B)).continuousOn
  obtain ⟨y, hy, hxy⟩ := hB.exists_infEDist_eq_edist hB' x
  refine ⟨x, hx, y, hy, le_antisymm (setEDist_le_edist hx hy) ?_⟩
  rw [← hxy]
  exact le_iInf₂ fun z hz => hmin hz

/-- A **geodesic from `A` to `B`**: a curve `P : [a, b] → X` from a point of `A` to a point of `B`
whose length on `[a, b]` is `setEDist A B`. -/
def IsGeodesicCurveBetween (P : ℝ → X) (a b : ℝ) (A B : Set X) : Prop :=
  a ≤ b ∧ ContinuousOn P (Icc a b) ∧ P a ∈ A ∧ P b ∈ B ∧ curveLength P a b = setEDist A B

/-- A geodesic from `A` to `B` is a geodesic between its endpoints, which realize `setEDist A B`. -/
theorem IsGeodesicCurveBetween.isGeodesicCurve {P : ℝ → X} {a b : ℝ} {A B : Set X}
    (hP : IsGeodesicCurveBetween P a b A B) :
    IsGeodesicCurve P a b ∧ edist (P a) (P b) = setEDist A B := by
  obtain ⟨hab, hc, ha, hb, hL⟩ := hP
  have h1 := edist_le_curveLength P hab
  have h2 := setEDist_le_edist ha hb
  have h3 : edist (P a) (P b) = setEDist A B := le_antisymm (h1.trans hL.le) h2
  exact ⟨⟨hab, hc, hL.trans h3.symm⟩, h3⟩

/-! ### Nonvacuity examples -/

namespace SetDistExample

/-- The compact nonempty sets `[0, 1]` and `[2, 3]` in `ℝ` satisfy the hypotheses of
`IsCompact.exists_setEDist_eq_edist`, so the infimum between them is attained at some pair. -/
example : ∃ x ∈ Icc (0 : ℝ) 1, ∃ y ∈ Icc (2 : ℝ) 3,
    setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) = edist x y :=
  IsCompact.exists_setEDist_eq_edist isCompact_Icc isCompact_Icc ⟨0, by norm_num⟩ ⟨2, by norm_num⟩

/-- For the points `1 ∈ [0, 1]` and `2 ∈ [2, 3]`, the hypotheses of `setEDist_le_edist` hold. -/
example : setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) ≤ edist (1 : ℝ) 2 :=
  setEDist_le_edist (by norm_num) (by norm_num)

/-- For the point `0 ∈ [0, 1]` and the set `{2}`, the hypothesis of `setEDist_le_infEDist` holds. -/
example : setEDist (Icc (0 : ℝ) 1) {(2 : ℝ)} ≤ infEDist (0 : ℝ) {2} :=
  setEDist_le_infEDist (by norm_num)

/-- The sets `{0} ⊆ [0, 1]` and `{2} ⊆ [2, 3]` satisfy the hypotheses of `setEDist_anti`. -/
example : setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) ≤ setEDist {(0 : ℝ)} {(2 : ℝ)} :=
  setEDist_anti (singleton_subset_iff.2 (by norm_num)) (singleton_subset_iff.2 (by norm_num))

/-- The segment `t ↦ t` on `[1, 2] ⊆ ℝ` is a geodesic from `[0, 1]` to `[2, 3]`, two disjoint
compact intervals. Its length is `1 = setEDist [0, 1] [2, 3]`, which is also the distance between
its endpoints, so `IsGeodesicCurveBetween` and its consequence `IsGeodesicCurve` both hold. -/
example : IsGeodesicCurveBetween (fun t : ℝ => t) 1 2 (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) ∧
    IsGeodesicCurve (fun t : ℝ => t) 1 2 ∧
    edist (1 : ℝ) 2 = setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) := by
  have hd : setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) = 1 := by
    refine le_antisymm ?_ ?_
    · calc setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) ≤ edist (1 : ℝ) 2 :=
            setEDist_le_edist (by norm_num) (by norm_num)
        _ = 1 := by rw [edist_dist, Real.dist_eq]; norm_num
    · refine le_setEDist.2 fun x hx y hy => ?_
      have h : (1 : ℝ) ≤ |x - y| := by
        rw [abs_sub_comm]
        exact (by linarith [hx.2, hy.1] : (1 : ℝ) ≤ y - x).trans (le_abs_self _)
      rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal h
  have hP : IsGeodesicCurveBetween (fun t : ℝ => t) 1 2 (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3) := by
    refine ⟨by norm_num, continuousOn_id, by norm_num, by norm_num, ?_⟩
    change eVariationOn id (Icc (1 : ℝ) 2) = setEDist (Icc (0 : ℝ) 1) (Icc (2 : ℝ) 3)
    rw [eVariationOn_id_Icc, hd]
    norm_num
  exact ⟨hP, hP.isGeodesicCurve.1, hP.isGeodesicCurve.2⟩

end SetDistExample

end LatticeProb.MetricGeometry
