import LatticeProb.Prob.UniformInMeasureCompact
import LatticeProb.Topology.ReparamEDist

/-!
# Uniform comparison of laws of random curves modulo time parametrization

Let `Y y` be a random path in a pseudo-emetric space `E`, defined on a common measure space and
indexed by a parameter `y` of a pseudometric space `X` (for instance a process started at `y`,
realized by translating one process started at the origin). Write

  `familySupEDist Y y z ω = sup_t edist (Y z ω t) (Y y ω t)`

for the uniform distance between two members of the family, and `A^κ` for the open
`κ`-neighbourhood of a set `A` of curves for the distance modulo time parametrization
(`LatticeProb.ReparamEDist.thickening`).

* `measure_thickening_le_add`: for every set `A` of curves and all `κ₁, κ`,
  `μ (Y z ∈ A^κ₁) ≤ μ (Y y ∈ A^(κ₁ + κ)) + μ (κ ≤ familySupEDist Y y z)`. No measurability of
  `A` is needed: all measures are outer measures of arbitrary sets.
* `exists_forall_measure_thickening_le`: if `μ` is finite, every `familySupEDist Y y z` is
  a.e.-measurable, and `familySupEDist Y c (u n) → 0` almost everywhere along every sequence
  `u n → c ∈ K` with `K` compact, then for every `κ, θ > 0` there is `δ > 0` such that, for all
  `y ∈ K`, all `z` with `dist z y < δ`, all `κ₁` and all sets `A` of curves,
  `μ (Y z ∈ A^κ₁) ≤ μ (Y y ∈ A^(κ₁ + κ)) + θ` and `μ (Y y ∈ A^κ₁) ≤ μ (Y z ∈ A^(κ₁ + κ)) + θ`.

The second statement is a uniform one-sided Lévy–Prokhorov comparison of the laws of the curves
`Y y` and `Y z` for nearby parameters; it combines the uniform-on-compacts convergence in measure
(`LatticeProb.UniformInMeasure.exists_forall_measure_le_of_seq_ae`) with the bound of the distance
modulo time parametrization by the uniform distance.
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal

namespace LatticeProb.ReparamEDist

variable {X Ω E : Type*} [PseudoEMetricSpace E] {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω}

/-- The uniform distance `sup_t edist (Y z ω t) (Y y ω t)` between the members `Y z` and `Y y` of a
family of random paths. -/
noncomputable def familySupEDist (Y : X → Ω → ℝ≥0 → E) (y z : X) (ω : Ω) : ℝ≥0∞ :=
  ⨆ t, edist (Y z ω t) (Y y ω t)

theorem familySupEDist_comm (Y : X → Ω → ℝ≥0 → E) (y z : X) (ω : Ω) :
    familySupEDist Y y z ω = familySupEDist Y z y ω :=
  iSup_congr fun _ => edist_comm _ _

/-- Triangle inequality of `familySupEDist` in the parameters. -/
theorem familySupEDist_le_add (Y : X → Ω → ℝ≥0 → E) (c y z : X) (ω : Ω) :
    familySupEDist Y y z ω ≤ familySupEDist Y c y ω + familySupEDist Y c z ω := by
  refine iSup_le fun t => (edist_triangle_right _ _ (Y c ω t)).trans ?_
  rw [add_comm]
  exact add_le_add (le_iSup_of_le t le_rfl) (le_iSup_of_le t le_rfl)

/-- A curve uniformly `κ`-close to a curve of `A^κ₁` lies in `A^(κ₁ + κ)`. -/
theorem mem_thickening_add_of_iSup_edist_lt {f g : ℝ≥0 → E} {κ₁ κ : ℝ≥0∞} {A : Set (ℝ≥0 → E)}
    (hf : f ∈ thickening κ₁ A) (hfg : ⨆ t, edist (f t) (g t) < κ) :
    g ∈ thickening (κ₁ + κ) A :=
  thickening_thickening_subset κ₁ κ A
    ⟨f, hf, ((reparamEDist_le_iSup_edist g f).trans_eq
      (iSup_congr fun t => edist_comm (g t) (f t))).trans_lt hfg⟩

/-- **Comparison of two members of a family of random curves.** For every set `A` of curves,
`μ (Y z ∈ A^κ₁) ≤ μ (Y y ∈ A^(κ₁ + κ)) + μ (κ ≤ sup_t edist (Y z t) (Y y t))`. -/
theorem measure_thickening_le_add (Y : X → Ω → ℝ≥0 → E) (y z : X) (κ₁ κ : ℝ≥0∞)
    (A : Set (ℝ≥0 → E)) :
    μ {ω | Y z ω ∈ thickening κ₁ A} ≤
      μ {ω | Y y ω ∈ thickening (κ₁ + κ) A} + μ {ω | κ ≤ familySupEDist Y y z ω} := by
  refine (measure_mono fun ω hω => ?_).trans (measure_union_le _ _)
  by_cases h : κ ≤ familySupEDist Y y z ω
  · exact Or.inr h
  · exact Or.inl (mem_thickening_add_of_iSup_edist_lt hω (not_le.1 h))

/-- **Uniform comparison of the laws of nearby members of a family of random curves.** If the
uniform distances `familySupEDist Y y z` are a.e.-measurable and `familySupEDist Y c (u n) → 0`
almost everywhere along every sequence `u n → c ∈ K`, `K` compact, then for all `κ, θ > 0` there is
`δ > 0` such that for all `y ∈ K` and `dist z y < δ` the laws of `Y z` and `Y y` satisfy the
one-sided Lévy–Prokhorov bounds `μ (Y z ∈ A^κ₁) ≤ μ (Y y ∈ A^(κ₁ + κ)) + θ` and
`μ (Y y ∈ A^κ₁) ≤ μ (Y z ∈ A^(κ₁ + κ)) + θ`, for every `κ₁` and every set `A` of curves. -/
theorem exists_forall_measure_thickening_le [PseudoMetricSpace X] [IsFiniteMeasure μ] {K : Set X}
    (hK : IsCompact K)
    (Y : X → Ω → ℝ≥0 → E) (hF : ∀ y z, AEMeasurable (familySupEDist Y y z) μ)
    (hae : ∀ c ∈ K, ∀ u : ℕ → X, Tendsto u atTop (𝓝 c) →
      ∀ᵐ ω ∂μ, Tendsto (fun n => familySupEDist Y c (u n) ω) atTop (𝓝 0))
    {κ θ : ℝ≥0∞} (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ δ > 0, ∀ y ∈ K, ∀ z, dist z y < δ → ∀ (κ₁ : ℝ≥0∞) (A : Set (ℝ≥0 → E)),
      μ {ω | Y z ω ∈ thickening κ₁ A} ≤ μ {ω | Y y ω ∈ thickening (κ₁ + κ) A} + θ ∧
      μ {ω | Y y ω ∈ thickening κ₁ A} ≤ μ {ω | Y z ω ∈ thickening (κ₁ + κ) A} + θ := by
  obtain ⟨δ, hδ, h⟩ := UniformInMeasure.exists_forall_measure_le_of_seq_ae hK
    (familySupEDist_le_add Y) hF hae hκ hθ
  refine ⟨δ, hδ, fun y hy z hz κ₁ A => ⟨?_, ?_⟩⟩
  · exact (measure_thickening_le_add Y y z κ₁ κ A).trans (add_le_add le_rfl (h y hy z hz))
  · refine (measure_thickening_le_add Y z y κ₁ κ A).trans (add_le_add le_rfl ?_)
    rw [show familySupEDist Y z y = familySupEDist Y y z from
      funext fun ω => familySupEDist_comm Y z y ω]
    exact h y hy z hz

end LatticeProb.ReparamEDist
