/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PaidDuality.PolygonFull at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.PaidDuality.PolygonTrace




 



set_option autoImplicit false

namespace SupercriticalLQGUniqueness.Exponent.PaidDuality

open Set
open scoped Convex ENNReal

 
def polygonFullEdges {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) : Finset (Σ _ : ι, ℕ) :=
  s.sigma (fun i => Finset.range (n i + 1))

 
def polygonFullTrace {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ) : Set ℂ :=
  ⋃ e ∈ polygonFullEdges s n,
    [v e.1 e.2 -[ℝ] v e.1 (min (e.2 + 1) (n e.1))]

 
def polygonPathsTrace {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ) : Set ℂ :=
  ⋃ i ∈ s, Exponent.PolygonCofinality.polygonPath (v i) (n i) '' Set.Icc (0 : ℝ) 1

theorem segCost_self (ξ : ℝ) (f : ℂ → ℝ) (a : ℂ) :
    LQGMetric.LFPP.segCost ξ f a a = 0 := by
  have hpath : LQGMetric.LFPP.segPath a a = (fun _ => a) := by
    funext t
    simp [LQGMetric.LFPP.segPath]
  rw [LQGMetric.LFPP.segCost, hpath]
  exact LQGMetric.DDDF.lfppLen_const (ξ := ξ) (f := f) a

theorem polygonFullTrace_eq_pathsTrace {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ) :
    polygonFullTrace s v n = polygonPathsTrace s v n := by
  classical
  ext z
  change z ∈ (⋃ e ∈ polygonFullEdges s n,
      [v e.1 e.2 -[ℝ] v e.1 (min (e.2 + 1) (n e.1))]) ↔
    z ∈ (⋃ i ∈ s, Exponent.PolygonCofinality.polygonPath (v i) (n i) '' Set.Icc (0 : ℝ) 1)
  constructor
  · intro hz
    obtain ⟨⟨i, j⟩, he, hzseg⟩ := Set.mem_iUnion₂.mp hz
    simp only [polygonFullEdges, Finset.mem_sigma, Finset.mem_range] at he
    obtain ⟨hi, hj⟩ := he
    have hjle : j ≤ n i := by
      omega
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    by_cases hjn : j = n i
    · subst j
      have hz' : z = v i (n i) := by
        simpa [min_eq_right (by omega : n i ≤ n i + 1), segment_same] using hzseg
      subst z
      exact ⟨1, by norm_num, polygonPath_end (v i) (n i)⟩
    · rw [polygonPath_trace]
      right
      have hjlt : j < n i := Nat.lt_of_le_of_ne hjle hjn
      refine Set.mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjlt, ?_⟩
      simpa [min_eq_left (by omega : j + 1 ≤ n i)] using hzseg
  · intro hz
    obtain ⟨i, hi, hzpath⟩ := Set.mem_iUnion₂.mp hz
    rw [polygonPath_trace] at hzpath
    rcases hzpath with hz0 | hzed
    · have hz' : z = v i 0 := by simpa using hz0
      subst z
      refine Set.mem_iUnion₂.mpr ⟨⟨i, 0⟩, ?_, ?_⟩
      · simp only [polygonFullEdges, Finset.mem_sigma, Finset.mem_range]
        exact ⟨hi, Nat.zero_lt_succ _⟩
      · exact left_mem_segment ℝ _ _
    · obtain ⟨j, hj, hzseg⟩ := Set.mem_iUnion₂.mp hzed
      have hjlt : j < n i := Finset.mem_range.mp hj
      refine Set.mem_iUnion₂.mpr ⟨⟨i, j⟩, ?_, ?_⟩
      · simp only [polygonFullEdges, Finset.mem_sigma, Finset.mem_range]
        exact ⟨hi, by omega⟩
      · simpa [min_eq_left (by omega : j + 1 ≤ n i)] using hzseg

 
theorem polygonFull_cost_eq_paths_cost {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (ξ : ℝ) (f : ℂ → ℝ) :
    (∑ e ∈ polygonFullEdges s n,
      LQGMetric.LFPP.segCost ξ f (v e.1 e.2)
        (v e.1 (min (e.2 + 1) (n e.1)))) =
      ∑ i ∈ s, LQGMetric.lfppLen ξ f
        (Exponent.PolygonCofinality.polygonPath (v i) (n i)) := by
  classical
  rw [polygonFullEdges, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_range_succ]
  have hlast : min (n i + 1) (n i) = n i := min_eq_right (Nat.le_succ _)
  rw [hlast, segCost_self, add_zero]
  have hcore : ∑ j ∈ Finset.range (n i),
      LQGMetric.LFPP.segCost ξ f (v i j)
        (v i (min (j + 1) (n i))) =
      ∑ j ∈ Finset.range (n i),
      LQGMetric.LFPP.segCost ξ f (v i j) (v i (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [min_eq_left (by have := Finset.mem_range.mp hj; omega : j + 1 ≤ n i)]
  rw [hcore]
  have hvertices : ∀ j ≤ n i, v i j ∈ (Set.univ : Set ℂ) := by simp
  exact (Exponent.PolygonCofinality.polygonPath_data (ξ := ξ) (f := f) (S := Set.univ)
    (convex_univ : Convex ℝ (Set.univ : Set ℂ))
    (v i) (n i) hvertices).2.2.symm

 
theorem paid_central_rect_of_polygon_paths {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (hadmitted : LQGMetric.Disconnects
      (polygonPathsTrace s v n) innerSquare outerOpenSquareᶜ)
    (k : Fin 4) (ξ : ℝ) (f : ℂ → ℝ) :
    ∃ P : ℝ → ℂ,
      LQGMetric.DDDF.AdmPath (centralRect k).toSet
        (centralRect k).side₁ (centralRect k).side₂ P ∧
      LQGMetric.lfppLen ξ f P ≤
        ∑ i ∈ s, LQGMetric.lfppLen ξ f
          (Exponent.PolygonCofinality.polygonPath (v i) (n i)) := by
  let E := polygonFullEdges s n
  let a : (Σ _ : ι, ℕ) → ℂ := fun e => v e.1 e.2
  let b : (Σ _ : ι, ℕ) → ℂ :=
    fun e => v e.1 (min (e.2 + 1) (n e.1))
  have hsep : LQGMetric.Disconnects
      (⋃ e ∈ E, [a e -[ℝ] b e]) innerSquare outerOpenSquareᶜ := by
    change LQGMetric.Disconnects (polygonFullTrace s v n)
      innerSquare outerOpenSquareᶜ
    rw [polygonFullTrace_eq_pathsTrace]
    exact hadmitted
  obtain ⟨P, hP, hcost⟩ :=
    paid_central_rect_of_annular_segment_family E a b hsep k ξ f
  refine ⟨P, hP, ?_⟩
  exact hcost.trans (polygonFull_cost_eq_paths_cost s v n ξ f).le

end SupercriticalLQGUniqueness.Exponent.PaidDuality

