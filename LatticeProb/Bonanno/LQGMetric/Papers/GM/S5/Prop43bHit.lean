/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bHit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bUnion

/-!
# Hitting points exist; Prop 5.2 (C) gives the bump of (5.7) (task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`.
* `exists_isHitPt` : for a length metric `D` and `|𝕫| > 3r`, a point `𝕩' ∈ ∂B_{3r}(0)` with
  `D(𝕫, 𝕩') = D(𝕫, cl B_{3r}(0))` exists (GM l. 3341: "the point where `𝓑_{σ}(𝕫; D_h)` first hits
  `∂B_{3r}(0)`"). Proof: a minimizer over the compact circle, and in a length space the distance
  to the closed disc equals the distance to its frontier (`infEDist_compl_eq_infEDist_frontier`).
* `ae_exists_bump_of_C` : from Prop 5.2 (C) (the clause of `P5_2`, at centre `0`), a.s. on
  `E_r ∩ {P ∩ B_{2r}(0) ≠ ∅}` the bump `φ = phiChoice(𝕩', 𝕪') ∈ 𝓖_r` at a pair of hitting
  points forces (5.4) for every `D_{h−φ}`-geodesic: the input `hC` of `gm_L5_4_union_at` (z = 0).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- hitting points exist for a length metric -/
theorem exists_isHitPt {D : ContMetric} (hD : D.IsLength) {a : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : 3 * r < ‖a‖) : ∃ x', IsHitPt D a x' r := by
  have hcont : Continuous fun y : ℂ => D.1 (a, y) :=
    D.1.continuous.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x', hx', hmin⟩ := (isCompact_sphere (0 : ℂ) (3 * r)).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 (by linarith)) hcont.continuousOn
  refine ⟨x', by simpa using hx', fun y hy => ?_⟩
  set C : Set ℂ := Metric.closedBall 0 (3 * r)
  set V : Set D.Space := D.pt '' Cᶜ
  have hV : IsOpen V := D.isOpen_image_pt Metric.isClosed_closedBall.isOpen_compl
  have haV : D.pt a ∈ V := (D.mem_image_pt).2 (by
    simp only [C, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]; exact ha)
  have heq := MetricGeometry.infEDist_compl_eq_infEDist_frontier hD hV haV
  have hfr : frontier V = D.pt '' Metric.sphere 0 (3 * r) := by
    have e1 := D.ptHomeomorph.image_frontier Cᶜ
    have e2 : (D.ptHomeomorph : ℂ → D.Space) = D.pt := rfl
    rw [e2] at e1
    rw [← e1, frontier_compl, frontier_closedBall (0 : ℂ) (by linarith : 3 * r ≠ 0)]
  have h1 : ENNReal.ofReal (D.1 (a, x')) ≤ Metric.infEDist (D.pt a) (frontier V) := by
    rw [hfr]
    refine Metric.le_infEDist.2 fun w hw => ?_
    obtain ⟨u, hu, rfl⟩ := hw
    rw [ContMetric.edist_pt]
    exact ENNReal.ofReal_le_ofReal (hmin hu)
  have h2 : Metric.infEDist (D.pt a) Vᶜ ≤ ENNReal.ofReal (D.1 (a, y)) := by
    rw [← ContMetric.edist_pt]
    exact Metric.infEDist_le_edist_of_mem (show D.pt y ∈ Vᶜ from fun h' => (D.mem_image_pt.1 h') hy)
  have h3 := (h1.trans_eq heq.symm).trans h2
  exact (ENNReal.ofReal_le_ofReal_iff (ContMetric.nonneg D a y)).1 h3

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC}

end LQGMetric.GM
