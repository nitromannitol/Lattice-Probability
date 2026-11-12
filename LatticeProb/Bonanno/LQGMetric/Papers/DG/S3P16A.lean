/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P16A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17C
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Adapter

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.16 as stated is false: a counterexample (task P2-DG316)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, Prop 3.16
(`prop-lfpp-approx`, DG:1432–1441). The lower bound
`δ^ζ (D̂^δ(z,w;𝕊) − δ e^{ξ ĥ_δ(v_{S_z})}) ≤ D^δ(z,w;𝕊)` fails, for every field and every `δ`, at
two points `z = (a − ε, a/2)`, `w = (a + ε, a/2)` on either side of the common side of the squares
`S_{(0,0)}`, `S_{(1,0)}` (`a = 2^{-m_δ}`): every chain of squares from `z` to `w` starts at
`S_{(0,0)}` (the only square containing `z`) and contains `S_{(1,0)}` (the only one containing
`w`), so `D̂^δ(z,w) − δ e^{ξ ĥ_δ(v_{S_z})} ≥ δ e^{ξ ĥ_δ(v_{S_{(1,0)}})} > 0`, while the segment
`[z,w]` gives `D^δ(z,w;𝕊) ≤ 2ε e^{ξ max_𝕊 h_δ} → 0` as `ε → 0`. DG's proof (DG:1500–1512) uses
the squares `S_j` with `j ≥ 1` only through the previous long piece `J_j ≥ 0`, which need not exist
for the first few squares (here `S_1 = S_{(1,0)}`, and the whole path is short).

* `not_dgProp3_16Printed : ¬ DGProp3_16Printed` — DG Proposition 3.16 as printed (DG:1436) is false;
  the corrected statement is `Blueprint.DGProp3_16` (D126).
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DG

open Blueprint

/-- the segment from `b` to `a` is a DG path in a convex set containing `a, b` (as
`DFGPS.L36.isDGPath_segment_ball`, for a convex set in place of a ball) -/
lemma p16_isDGPath_segment {C : Set ℂ} (hC : Convex ℝ C) {a b : ℂ} (ha : a ∈ C) (hb : b ∈ C) :
    IsDGPath C b a (fun t => b + (t : ℂ) * (a - b)) := by
  refine ⟨by simp, by simp, fun t ht => ?_, by fun_prop, ⟨1, ![0, 1], ?_, rfl, rfl, ?_⟩⟩
  · have := hC.add_smul_sub_mem hb ha ht
    rwa [Complex.real_smul] at this
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    exact (contDiff_const.add ((Complex.ofRealCLM.contDiff).mul contDiff_const)).contDiffOn

lemma p16_convex_sq : Convex ℝ closedUnitSquare := by
  intro x hx y hy s t hs ht hst
  simp only [closedUnitSquare, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hx hy ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h5, h6, h7, h8⟩ := hy
  refine ⟨by positivity, ?_, by positivity, ?_⟩ <;> nlinarith

lemma p16_isCompact_sq : IsCompact closedUnitSquare := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have e : closedUnitSquare = Complex.re ⁻¹' Icc 0 1 ∩ Complex.im ⁻¹' Icc 0 1 := by
      ext z; simp [closedUnitSquare, and_assoc]
    rw [e]
    exact (isClosed_Icc.preimage Complex.continuous_re).inter
      (isClosed_Icc.preimage Complex.continuous_im)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => ?_
    obtain ⟨h1, h2, h3, h4⟩ := hz
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith

end LQGMetric.DG
