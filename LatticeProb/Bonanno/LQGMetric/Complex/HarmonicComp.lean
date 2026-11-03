/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Complex.HarmonicComp at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Harmonic functions composed with holomorphic maps

Conformal invariance of harmonic functions: if `u` is harmonic on an open set `V` and `f` is
holomorphic on an open set `W` with `f(W) ⊆ V`, then `u ∘ f` is harmonic on `W`. This is the
analytic form of the "conformal invariance of Brownian motion" used in Gwynne–Miller,
*Confluence of geodesics in LQG* (arXiv:1905.00381), proof of Lemma 2.14 (confluence-final.tex
864–865), where harmonic measure in `H_I` is transported to `φ(H_I)`.

Proof (standard, e.g. Garnett–Marshall, *Harmonic Measure*, §I.1): locally `u = Re F` with `F`
holomorphic (mathlib `HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), so near each point
`u ∘ f = Re (F ∘ f)`, the real part of a holomorphic function (mathlib
`AnalyticAt.harmonicAt_re`).
-/

namespace LQGMetric

open Set Metric Filter Topology InnerProductSpace

/-- `u ∘ f` is harmonic on `W` if `u` is harmonic on the open set `V` and `f` is holomorphic on
the open set `W` with `f(W) ⊆ V`. -/
theorem harmonicOnNhd_comp_holo {u : ℂ → ℝ} {f : ℂ → ℂ} {V W : Set ℂ} (hV : IsOpen V)
    (hW : IsOpen W) (hu : HarmonicOnNhd u V) (hf : DifferentiableOn ℂ f W)
    (hfV : MapsTo f W V) : HarmonicOnNhd (u ∘ f) W := by
  intro x hx
  obtain ⟨R, hR, hRV⟩ := Metric.isOpen_iff.1 hV (f x) (hfV hx)
  have huB : HarmonicOnNhd u (ball (f x) R) := fun y hy => hu y (hRV hy)
  obtain ⟨F, hF, hFu⟩ := huB.exists_analyticOnNhd_ball_re_eq
  have hfx : AnalyticAt ℂ f x := hf.analyticAt (hW.mem_nhds hx)
  have hFx : AnalyticAt ℂ F (f x) := hF (f x) (mem_ball_self hR)
  have hcomp : AnalyticAt ℂ (F ∘ f) x := hFx.comp hfx
  have hev : (fun y => ((F ∘ f) y).re) =ᶠ[𝓝 x] (u ∘ f) := by
    have : f ⁻¹' ball (f x) R ∈ 𝓝 x :=
      hfx.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hR))
    filter_upwards [this] with y hy
    exact hFu hy
  exact (harmonicAt_congr_nhds hev).1 hcomp.harmonicAt_re

end LQGMetric
