/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicGM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicCore

/-!
# GM Lemma 3.1: GM's event (3.1) and the internal event (task P2-M2D)

GM, `literature/src/1905.00383/uniqueness-final.tex` l. 1192–1194, event (3.1) (strict form,
points of `Qc`), centred at `z`, radius `R / 2`:

* `GM.gmEv D D' C R z`: the event of the field `g`;
* `GM.gmEv_subset_locEv`: a.s. `{h ∈ gmEv z} ⊆ locEv z` (GM S3.1, l. 1196–1199).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

/-- GM's event (3.1) (l. 1194), strict form, `u, v ∈ Qc ∩ B_{R/2}(z)` -/
def gmEv (D D' : DistC → ContMetric) (C R : ℝ) (z : ℂ) : Set DistC :=
  {g | ∃ u ∈ Qc ∩ Metric.ball z (R / 2), ∃ v ∈ Qc ∩ Metric.ball z (R / 2),
    gmCond (D g) (D' g) C (Metric.ball z (R / 2)) u v}

theorem gmEv_subset_locEv {γ : ℝ} {D D' : DistC → ContMetric} {c c' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (hD' : IsWeakLQGMetric γ D' c') {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (C : ℝ) {R : ℝ} (hR : 0 < R) (z : ℂ) : h ⁻¹' gmEv D D' C R z ≤ᵐ[P] locEv D D' C R z h := by
  filter_upwards [hD.length P h (detGFFPlusCont hh), hD'.length P h (detGFFPlusCont hh)]
    with ω hl hl' hmem
  obtain ⟨u, hu, v, hv, hc⟩ := hmem
  exact ⟨u, hu, v, hv,
    locCond_of_gmCond hl hl' Metric.isOpen_ball (closure_ball_half_subset hR) hu.2 hc⟩

end LQGMetric.GM
