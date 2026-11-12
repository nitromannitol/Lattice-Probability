/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eFin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eConcat
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# `hfin`: a finite-length competitor path to `x ∈ ∂B_r(z)` (DEC-86 (3))

DEC-86 item (3): every `x ∈ ∂B_r(z)` is reached from `𝕫 ∉ cl B_r(z)` by a finite-`D`-length path
in `ℂ ∖ B_r(z)`, provided `D` is a length metric and satisfies an internal Hölder bound near `x`
(GM's ℰ_𝕣 condition 3, l. 1958–1962, `regC3`). Construction (DEC-86 (3)): `x_n = x + c_n ν`,
`ν = (x − z)/r`, `c_n = r₀(2/3)^n`; the internal Hölder bound in `B_{2|x_n − x_{n+1}|}(x_n) ⊆
ℂ ∖ cl B_r(z)` gives summable lengths; `𝕫 → x₀` inside the connected open set `ℂ ∖ cl B_r(z)`
(finite internal distance); concatenation `p412e_concat`. Hence the avoid-geodesics of GM (4.11)
(l. 1695) have finite length (`p412e_hfin`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.MetricGeometry
open scoped ENNReal

namespace LQGMetric.GM

/-- `ℂ ∖ cl B_r(z)` is preconnected (image of a half-plane under `w ↦ z + e^w`) -/
theorem p412e_compl_closedBall_isPreconnected (z : ℂ) {r : ℝ} (hr : 0 < r) :
    IsPreconnected (closedBall z r)ᶜ := by
  have hS : (closedBall z r)ᶜ = (fun w : ℂ => z + Complex.exp w) '' {w : ℂ | Real.log r < w.re} := by
    ext u
    simp only [mem_compl_iff, mem_closedBall, not_le, mem_image, mem_setOf_eq, dist_eq_norm]
    constructor
    · intro hu
      have hne : u - z ≠ 0 := by intro h; rw [h, norm_zero] at hu; linarith
      refine ⟨Complex.log (u - z), ?_, by rw [Complex.exp_log hne]; ring⟩
      rw [Complex.log_re]; exact Real.log_lt_log hr hu
    · rintro ⟨w, hw, rfl⟩
      rw [add_sub_cancel_left, Complex.norm_exp]
      calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
        _ < Real.exp w.re := Real.exp_lt_exp.2 hw
  rw [hS]
  exact (convex_halfSpace_re_gt (Real.log r)).isPreconnected.image _ (by fun_prop)

/-- in a length metric, internal distances in a preconnected open set are finite -/
theorem p412e_internal_ne_top {D : ContMetric} (hL : D.IsLength) {O : Set ℂ} (hO : IsOpen O)
    (hOc : IsPreconnected O) {u v : ℂ} (hu : u ∈ O) (hv : v ∈ O) : D.internal O u v ≠ ∞ := by
  -- near `w ∈ O`, `D(w, ·; O)` is finite
  have hloc : ∀ w ∈ O, ∀ᶠ w' in 𝓝 w, D.internal O w w' ≠ ∞ := by
    intro w hw
    have hc := (D.continuousOn_internal hL hO).continuousAt (x := (w, w))
      (prod_mem_nhds (hO.mem_nhds hw) (hO.mem_nhds hw))
    have h0 : D.internal O w w = 0 := internalEDist_self (D.mem_image_pt.2 hw)
    have : Tendsto (fun w' => D.internal O w w') (𝓝 w) (𝓝 0) := by
      have := hc.comp (Continuous.prodMk continuous_const continuous_id).continuousAt
      have h' : ContinuousAt (fun w' => D.internal O w w') w := by
        simpa [Function.comp_def] using this
      simpa [ContinuousAt, h0] using h'
    exact (this.eventually (gt_mem_nhds zero_lt_one)).mono fun _ h => ne_top_of_lt h
  let f : ℂ → Bool := fun w => decide (D.internal O u w ≠ ∞)
  have hf : ContinuousOn f O := by
    intro w hw
    refine (continuousAt_const (y := f w)).congr ?_ |>.continuousWithinAt
    filter_upwards [hloc w hw] with w' hw'
    have h1 := internalEDist_triangle (D.pt '' O) (D.pt u) (D.pt w) (D.pt w')
    have h2 := internalEDist_triangle (D.pt '' O) (D.pt u) (D.pt w') (D.pt w)
    have h3 : D.internal O w' w ≠ ∞ := by
      rw [ContMetric.internal, internalEDist_comm]; exact hw'
    simp only [f, ContMetric.internal] at *
    by_cases hw0 : internalEDist (D.pt '' O) (D.pt u) (D.pt w) = ∞
    · have : internalEDist (D.pt '' O) (D.pt u) (D.pt w') = ∞ := by
        by_contra hne; rw [hw0] at h2
        exact absurd (top_le_iff.1 h2) (ENNReal.add_ne_top.2 ⟨hne, h3⟩)
      simp [hw0, this]
    · have : internalEDist (D.pt '' O) (D.pt u) (D.pt w') ≠ ∞ :=
        ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hw0, hw'⟩) h1
      simp [hw0, this]
  have hconst := hOc.constant hf hu hv
  have hu0 : D.internal O u u = 0 := internalEDist_self (D.mem_image_pt.2 hu)
  simp only [f, hu0, ne_eq, decide_eq_decide] at hconst
  intro htop
  exact hconst.1 (by simp [hu0]) htop

/-- a path realising `D(u, w; U) < b`, as a curve `[0, 1] → ℂ` -/
theorem p412e_path_of_lt {D : ContMetric} {U : Set ℂ} {u w : ℂ} {b : ℝ≥0∞}
    (h : D.internal U u w < b) :
    ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = u ∧ g 1 = w ∧ MapsTo g (Icc 0 1) U ∧
      curveLength (D.pt ∘ g) 0 1 < b := by
  obtain ⟨⟨γ, hγ⟩, hlt⟩ := iInf_lt_iff.1 h
  refine ⟨D.unpt ∘ γ.extend, (D.continuous_unpt.comp γ.continuous_extend).continuousOn,
    by simp, by simp, fun t ht => ?_, hlt⟩
  have := hγ ⟨t, ht⟩
  rw [Function.comp_apply, Path.extend_extends' γ ⟨t, ht⟩]
  exact D.mem_image_pt.1 this

end LQGMetric.GM
