import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm

/-!
# Circle averages of the whole-plane GFF along a countable set of centres

For a whole-plane Gaussian free field `h`, the circle-average process `(r, z) ↦ h_r(z)` has a jointly
continuous version on `(0, ∞) × ℂ`, normalized by `h_1(0)` (`LQGMetric.CircleAvg.exists_continuous_version_circleAvg`).
A version agrees with the process only at each fixed `(r, z)` almost surely. Here, for countably many radii
and countably many centres, the exceptional null sets are collected into one. Almost surely, for every
radius `r` of the countable set, the map `z ↦ h_r(z)` restricted to the countable set of centres agrees with a
continuous function on `ℂ`.

A consequence: along centres taken from the countable set that converge to a centre of the set, the circle
averages converge to the circle average at the limit centre (`ae_tendsto_circleAvg_of_countable`).
This is the form used to identify a limsup over a grid of centres with the circle average at the limit
point.
-/

open MeasureTheory Filter Topology Set

noncomputable section

namespace LatticeProb.WholePlaneGFFCircleAvgCountable

open LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- **Circle averages on a countable set of centres are restrictions of continuous functions.**
For a whole-plane GFF `h`, a countable set `W` of centres and a countable set `R` of positive radii, almost
surely, for every `r ∈ R` there is a continuous `F : ℂ → ℝ` with `h_r(z) = F z` for all `z ∈ W`. -/
theorem ae_exists_continuous_eqOn_circleAvg (hh : IsWholePlaneGFF h P) {W : Set ℂ}
    (hW : W.Countable) {R : Set ℝ} (hR : R.Countable) (hRpos : ∀ r ∈ R, 0 < r) :
    ∀ᵐ ω ∂P, ∀ r ∈ R, ∃ F : ℂ → ℝ, Continuous F ∧ ∀ z ∈ W, circleAvg (h ω) r z = F z := by
  obtain ⟨H, hHc, hHeq⟩ := CircleAvg.exists_continuous_version_circleAvg hh
  have hall : ∀ᵐ ω ∂P, ∀ r ∈ R, ∀ z ∈ W,
      H r z ω = circleAvg (h ω) r z - circleAvg (h ω) 1 0 :=
    (ae_ball_iff hR).2 fun r hr => (ae_ball_iff hW).2 fun z _ => hHeq r (hRpos r hr) z
  filter_upwards [hall] with ω hω r hr
  refine ⟨fun z => H r z ω + circleAvg (h ω) 1 0, ?_, fun z hz => ?_⟩
  · have hc : Continuous fun z : ℂ => H r z ω :=
      (hHc ω).comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => ⟨hRpos r hr, mem_univ z⟩)
    exact hc.add continuous_const
  · show circleAvg (h ω) r z = H r z ω + circleAvg (h ω) 1 0
    rw [hω r hr z hz]
    ring

/-- **Convergence of circle averages along centres of a countable set.** Almost surely, for every `r ∈ R`,
every `z₀ ∈ W` and every sequence of centres `w m ∈ W` converging to `z₀`, `h_r(w m) → h_r(z₀)`. -/
theorem ae_tendsto_circleAvg_of_countable (hh : IsWholePlaneGFF h P) {W : Set ℂ}
    (hW : W.Countable) {R : Set ℝ} (hR : R.Countable) (hRpos : ∀ r ∈ R, 0 < r) :
    ∀ᵐ ω ∂P, ∀ r ∈ R, ∀ z₀ ∈ W, ∀ w : ℕ → ℂ, (∀ m, w m ∈ W) → Tendsto w atTop (𝓝 z₀) →
      Tendsto (fun m => circleAvg (h ω) r (w m)) atTop (𝓝 (circleAvg (h ω) r z₀)) := by
  filter_upwards [ae_exists_continuous_eqOn_circleAvg hh hW hR hRpos] with ω hω r hr z₀ hz₀ w hw hwz
  obtain ⟨F, hF, hFeq⟩ := hω r hr
  rw [hFeq z₀ hz₀]
  exact ((hF.tendsto z₀).comp hwz).congr fun m => (hFeq (w m) (hw m)).symm

end LatticeProb.WholePlaneGFFCircleAvgCountable
