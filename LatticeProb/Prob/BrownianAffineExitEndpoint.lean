import LatticeProb.Prob.ExitEndpointTransform
import LatticeProb.Prob.BrownianStoppedPathClock
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianScaling
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteExit

/-! # Brownian exit endpoints under affine scaling -/

set_option autoImplicit false

noncomputable section

open MeasureTheory BouRabeeGwynne Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- A positive parabolic rescaling takes a finite exit endpoint to its
spatial image. -/
theorem brownian_exit_endpoint_scale {d : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (z : Euc d) (V : Set (Euc d)) (hV : IsOpen V) (ω : BrownianPath d)
    (hfin : continuousExitTime ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V) 0 ω ≠ ⊤) :
    z + scaledBrownianPath r ω (continuousExitTime V z (scaledBrownianPath r ω)).toNNReal =
      z + (r : ℝ)⁻¹ • ω (continuousExitTime
        ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V) 0 ω).toNNReal := by
  let f : C(Euc d, Euc d) := ⟨fun x => z + (r : ℝ)⁻¹ • x, by fun_prop⟩
  let φ : ℝ≥0 ≃o ℝ≥0 := OrderIso.mulLeft₀ (r ^ 2) (pow_pos hr 2)
  have hc : continuousExitTime ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V) 0 ω =
      openExitTime (fun t (_ : Unit) => ω t) (f ⁻¹' V) () := by
    have hp : (fun t : ℝ≥0 => 0 + ω t ∉ (f ⁻¹' V)) =
        (fun t : ℝ≥0 => ω t ∉ (f ⁻¹' V)) := by
      funext t
      simp only [zero_add]
    exact congrArg (fun p : ℝ≥0 → Prop => ⨅ t : {t // p t}, (t.val : ℝ≥0∞)) hp
  have hf : openExitTime (fun t (_ : Unit) => ω t) (f ⁻¹' V) () ≠ ⊤ := by
    rw [← hc]
    exact hfin
  have h := openExit_endpoint_comp_spatial_orderIso ω f φ V hV hf
  rw [hc]
  exact h


/-- A Brownian exit endpoint transforms by the corresponding affine map.
The preimage domain is bounded so its exit is almost surely finite. -/
theorem brownian_exit_endpoint_law_scale {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    (r : ℝ≥0) (hr : 0 < r) (z : Euc d) {V : Set (Euc d)} (hV : IsOpen V)
    (hb : Bornology.IsBounded ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V)) :
    (stoppedBrownianLaw V z μ).map BouRabeeGwynne.CurveSpace.endPoint =
      ((stoppedBrownianLaw ((fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V) 0 μ).map
        BouRabeeGwynne.CurveSpace.endPoint).map (fun x => z + (r : ℝ)⁻¹ • x) := by
  let W : Set (Euc d) := (fun x : Euc d => z + (r : ℝ)⁻¹ • x) ⁻¹' V
  let f : Euc d → Euc d := fun x => z + (r : ℝ)⁻¹ • x
  let eV : BrownianPath d → Euc d := fun ω => z + ω (continuousExitTime V z ω).toNNReal
  let eW : BrownianPath d → Euc d := fun ω => ω (continuousExitTime W 0 ω).toNNReal
  have hW : IsOpen W := hV.preimage (by fun_prop)
  have hf : Measurable f := by fun_prop
  have heV : Measurable eV := by
    simpa only [eV, Function.comp_def, stoppedBrownianCurve_endPoint] using
      (BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable.comp
        (measurable_stoppedBrownianCurve hV z))
  have heW : Measurable eW := by
    simpa only [eW, Function.comp_def, stoppedBrownianCurve_endPoint, zero_add] using
      (BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable.comp
        (measurable_stoppedBrownianCurve hW 0))
  have hfinite : ∀ᵐ ω ∂μ, continuousExitTime W 0 ω ≠ ⊤ :=
    standardBrownianLaw_ae_finiteExit hd hμ hb 0
  have hmap : μ.map eV = (μ.map eW).map f := by
    calc
      μ.map eV = (μ.map (scaledBrownianPath r)).map eV := by
        rw [standardBrownianLaw_map_scale hμ hr]
      _ = μ.map (eV ∘ scaledBrownianPath r) :=
        Measure.map_map heV (measurable_scaledBrownianPath r)
      _ = μ.map (f ∘ eW) := by
        apply Measure.map_congr
        filter_upwards [hfinite] with ω hω
        exact brownian_exit_endpoint_scale r hr z V hV ω hω
      _ = (μ.map eW).map f := (Measure.map_map hf heW).symm
  change (μ.map (stoppedBrownianCurve V z)).map BouRabeeGwynne.CurveSpace.endPoint =
    ((μ.map (stoppedBrownianCurve W 0)).map BouRabeeGwynne.CurveSpace.endPoint).map f
  rw [Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
    (measurable_stoppedBrownianCurve hV z),
    Measure.map_map BouRabeeGwynne.CurveSpace.continuous_endPoint.measurable
      (measurable_stoppedBrownianCurve hW 0)]
  simpa only [eV, eW, f, Function.comp_def, stoppedBrownianCurve_endPoint, zero_add] using hmap

end LatticeProb
end
