/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53UF3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53UF2

/-!
# DZZ Lemma 5.3 part 1, node 4: the bad events of `w ∈ {u, v}` at the boxes `boxAt n w`
(P2-DZZ53UF)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522.

* `l53ufM`: the node-4 proxy of the box `b`: `proxyMass` (S5L53K1) at scale
  `2^{-m_b}`, `m_b = n_b + n_{ε*} + 12` (so `2^{-m_b} = ε* s_b/4096`), factor
  `c_b = (δ s_b⁻¹ e^{L^{0.91}/2})² = δ² s_b⁻² e^{L^{0.91}}` (DZZ l. 2455), region `𝕍_{c_b, 5 s_b}`.
  Node 4 needs no locality (no conditioning on `𝓕*`), so `m_b` is chosen fine enough that the
  coupling of S5L53X4 (`2^{-m} ≤ ‖a‖`) applies to every `x ∈ ∂b` beyond the cut-off
  `|x − w| ≥ ε* s_b/1600`.
* **`l53uf_hbad`**: `P(bad_w at boxAt n w) ≤ (800/ε*) · 2K⁻⁴` for every `n` with
  `12 s_n ≤ |v − u|`, from `l53WBadQ_le_cut` (S5L53UF2) and `l53uf_far_bound` (S5L53UF1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- copy of `l53_exists_sim` (S5L53Y2): the similarity with `θu = z`, `θv = z'` -/
lemma l53uf_exists_sim {u v : ℂ} (huv : u ≠ v) (z z' : ℂ) :
    ∃ a b : ℂ, simMap a b u = z ∧ simMap a b v = z' ∧ ‖a‖ = ‖z' - z‖ / ‖v - u‖ := by
  have hvu : v - u ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
  refine ⟨(z' - z) / (v - u), z - (z' - z) / (v - u) * u, ?_, ?_, norm_div _ _⟩
  · simp only [simMap]; ring
  · simp only [simMap]; field_simp; ring

/-- the far relation is antitone in the threshold `T` -/
lemma l53FarQ_of_le_T {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞} {δ T T' : ℝ} (hT : T ≤ T') {ω : Ω}
    {z z' : ℂ} (h : l53FarQ M δ T' ω z z') : l53FarQ M δ T ω z z' :=
  fun h' => h ⟨h'.1, h'.2.trans (Real.exp_le_exp.2 hT)⟩

lemma l53uf_norm_sub_le {c z z' : ℂ} {t : ℝ} (hz : z ∈ sqBox c t) (hz' : z' ∈ sqBox c t) :
    ‖z' - z‖ ≤ 2 * t := by
  simp only [sqBox, mem_ofPred_eq] at hz hz'
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im]
  have h1 := abs_sub_le z'.re c.re z.re
  have h2 := abs_sub_le z'.im c.im z.im
  rw [abs_sub_comm c.re, ] at h1
  rw [abs_sub_comm c.im] at h2
  linarith [hz.1, hz.2, hz'.1, hz'.2]

lemma l53uf_mem_dzzV {u : ℂ} (hu : u ∈ dzzVbar) : u ∈ dzzV := by
  simp only [dzzVbar, sqBox, mem_ofPred_eq, abs_le] at hu
  simp only [dzzV, mem_ofPred_eq]
  refine ⟨by linarith [hu.1.1], by linarith [hu.1.2], by linarith [hu.2.1], by linarith [hu.2.2]⟩

lemma l53uf_norm_le_one {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) : ‖v - u‖ ≤ 1 := by
  have := l53uf_norm_sub_le hu hv
  linarith

variable {P : Measure Ω} {W : WNSpace → Ω → ℝ}

end DZZ
end LQGMetric
