import LatticeProb.Prob.FiniteTailMax
import LatticeProb.Prob.Percolation.LatticeRadialScale

/-!
# Radial scales for neighboring pole thresholds

The finite maximum includes the ambient pole and all of its positive coordinate neighbors.
A moment-controlled field and the neighboring thresholds yield a uniform radial scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb
open scoped ENNReal

namespace LatticeProb.Percolation

/-- The threshold at a pole followed by the thresholds at its positive coordinate neighbors. -/
def neighborThresholdField {d : ℕ} {Ω : Type*} (T : Vertex d → Ω → ℝ) (y : Vertex d) :
    Fin (d + 1) → Ω → ℝ :=
  Fin.cases (T y) (fun j => T (y + unit j))

/-- The actual finite maximum of the pole and neighboring-pole thresholds. -/
noncomputable def neighborMaximum {d : ℕ} {Ω : Type*}
    (T : Vertex d → Ω → ℝ) (y : Vertex d) : Ω → ℝ :=
  finiteFieldMax (neighborThresholdField T y)

/-- The field combining the deterministic floor, local field, and neighboring thresholds. -/
noncomputable def neighborRadialField {d : ℕ} {Ω : Type*}
    (X T : Vertex d → Ω → ℝ) (y x : Vertex d) (ω : Ω) : ℝ :=
  max 64 (max (X x ω) (2 * neighborMaximum T y ω))

/-- A measurable threshold family has a measurable neighboring maximum. -/
theorem measurable_neighborMaximum {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (T : Vertex d → Ω → ℝ) (hT : ∀ y, Measurable (T y)) (y : Vertex d) :
    Measurable (neighborMaximum T y) := by
  apply measurable_finiteFieldMax
  intro i
  refine Fin.cases ?_ ?_ i
  · exact hT y
  · intro j
    exact hT (y + unit j)

/-- The threshold at the central pole is bounded by the neighboring maximum. -/
theorem le_neighborMaximum_self {d : ℕ} {Ω : Type*} (T : Vertex d → Ω → ℝ)
    (y : Vertex d) (ω : Ω) : T y ω ≤ neighborMaximum T y ω := by
  change neighborThresholdField T y 0 ω ≤
    Finset.univ.sup' Finset.univ_nonempty (fun i => neighborThresholdField T y i ω)
  exact Finset.le_sup' (fun i => neighborThresholdField T y i ω) (Finset.mem_univ 0)

/-- Each positive coordinate-neighbor threshold is bounded by the neighboring maximum. -/
theorem le_neighborMaximum_neighbor {d : ℕ} {Ω : Type*} (T : Vertex d → Ω → ℝ)
    (y : Vertex d) (j : Fin d) (ω : Ω) : T (y + unit j) ω ≤ neighborMaximum T y ω := by
  change neighborThresholdField T y j.succ ω ≤
    Finset.univ.sup' Finset.univ_nonempty (fun i => neighborThresholdField T y i ω)
  exact Finset.le_sup' (fun i => neighborThresholdField T y i ω) (Finset.mem_univ j.succ)

/-- The combined field is measurable at every pole and lattice point. -/
theorem measurable_neighborRadialField {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X T : Vertex d → Ω → ℝ) (hX : ∀ x, Measurable (X x))
    (hT : ∀ y, Measurable (T y)) (y x : Vertex d) :
    Measurable (neighborRadialField X T y x) := by
  exact measurable_const.max ((hX x).max (measurable_const.mul (measurable_neighborMaximum T hT y)))

/-- A uniform moment and uniform threshold tails give radial scales for the neighboring field. -/
theorem exists_neighbor_radial_scale_exp_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (a s b t α : ℝ) (ha : 0 < a) (hs : 0 < s) (hb : 0 < b) (ht : 0 < t)
    (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X T : Vertex d → Ω → ℝ),
      (∀ x, Measurable (X x)) → (∀ x ω, 0 ≤ X x ω) →
      (∀ x, Integrable (fun ω => Real.exp ((X x ω / a) ^ s)) μ) →
      (∀ x, (∫ ω, Real.exp ((X x ω / a) ^ s) ∂μ) ≤ 2) →
      (∀ y, Measurable (T y)) → (∀ y ω, 0 ≤ T y ω) →
      (∀ y r, 0 < r → μ {ω | r ≤ T y ω} ≤
        ENNReal.ofReal (b * Real.exp (-(r ^ t) / b))) →
      ∀ y : Vertex d, ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 1 ≤ M ω) ∧
        Integrable (fun ω => Real.exp ((M ω / C) ^ (α * min s t))) μ ∧
        (∫ ω, Real.exp ((M ω / C) ^ (α * min s t)) ∂μ) ≤ 2 ∧
        (∀ᵐ ω ∂μ, ∀ x : Vertex d, M ω ≤
          ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
          neighborRadialField X T y x ω <
            ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α) := by
  obtain ⟨A, hA, htail⟩ := finite_max_stretched_exp_tail (J := Vertex d) d 64 a s b t
    (by norm_num) ha hs hb ht
  obtain ⟨C, hC, hscale⟩ := exists_radial_scale_exp_moment (d := d) (Ω := Ω)
    A (min s t) α hA (lt_min hs ht) hα
  refine ⟨C, hC, ?_⟩
  intro μ _ X T hXm hXn hXi hXb hTm hTn hTtail y
  have hnm : ∀ i, Measurable (neighborThresholdField T y i) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hTm y
    · intro j
      exact hTm (y + unit j)
  have hnn : ∀ i ω, 0 ≤ neighborThresholdField T y i ω := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hTn y
    · intro j
      exact hTn (y + unit j)
  have hnt : ∀ i r, 0 < r → μ {ω | r ≤ neighborThresholdField T y i ω} ≤
      ENNReal.ofReal (b * Real.exp (-(r ^ t) / b)) := by
    intro i
    refine Fin.cases ?_ ?_ i
    · exact hTtail y
    · intro j
      exact hTtail (y + unit j)
  apply hscale μ (neighborRadialField X T y)
    (measurable_neighborRadialField X T hXm hTm y) ?_ y
  intro x r hr
  exact htail μ X (neighborThresholdField T y) hXm hXn hXi hXb hnm hnn hnt x r hr

end LatticeProb.Percolation
