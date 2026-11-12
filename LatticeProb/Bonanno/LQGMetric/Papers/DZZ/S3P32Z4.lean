/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32Z4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Z3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P2

/-!
# `𝓔_{B',open} ⊆ {Φ^W_{B',δ,r} ≤ λ}` (D102 P-4bW, step (a), DZZ l. 1131–1139)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1131–1139): "each such ball can be covered by at most 4
boxes in `𝓑'_i`. Thus, each one has LQG measure at most `δ²` if `{M_{γ,s}(B) ≤ δ²} ∩ Ẽ_{δ,α} ∩
𝓔_{B'_i,open}` occurs, by the definition of `𝓔_{B'_i,open}` together with (eq-M-tilde-B-bound)".

**`phiLeW_of_open`** (deterministic): given the conclusion of (eq-M-tilde-B-bound) for `B`
(`M^W(B̃) ≤ K M̃(B̃)` for boxes within `3s` of `c_B`, i.e. `l32TildeMUpper_wickQArea`), a ring box
`B' ⊆ B_large`, grid level `B'.n + ℓ` with `2^{-(B'.n+ℓ)} ≤ s/2`, and the open event
`M̃(B̃) ≤ θ` for all `B̃ ∈ 𝓑_∂(B', 2^{-ℓ})` with `4 K θ ≤ δ²`: `PhiLeW (μIn ω) δ r B' λ` for
`λ ≥ 4 (2^ℓ + 1)` and any `r > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ}

lemma abs_sub_le_of_mem_closedBox {b : DyBox} {z w : ℂ} (hz : z ∈ b.closedBox)
    (hw : w ∈ b.closedBox) : |z.re - w.re| ≤ b.side ∧ |z.im - w.im| ≤ b.side := by
  obtain ⟨a1, a2, a3, a4⟩ := hz
  obtain ⟨b1, b2, b3, b4⟩ := hw
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

/-- **DZZ l. 1131–1139 at `μIn`** -/
theorem phiLeW_of_open {γ δh : ℝ} {ω : Ω} {B B' : DyBox} {ℓ : ℕ} {K θ : ℝ≥0∞} {δ r lam : ℝ}
    (hup : ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - B.center‖ ≤ 3 * B.side) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ δh b'.closedBox ω)
    (hB' : B'.closedBox ⊆ B.largeBox) (hlev : (2⁻¹ : ℝ) ^ (B'.n + ℓ) ≤ B.side / 2)
    (hn : 1 ≤ B'.n + ℓ) (hr : 0 < r)
    (hopen : ∀ b ∈ boxCollBdry B' ℓ, etaChaos W γ δh b.closedBox ω ≤ θ)
    (hKθ : 4 * (K * θ) ≤ ENNReal.ofReal (δ ^ 2)) (hlam : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam) :
    PhiLeW (dzzMuIn γ W ω) δ r B' lam := by
  refine phiLeW_of_corner_mass B' ℓ hn hr (fun m₁ m₂ a1 a2 a3 a4 hg hedge => ?_) hlam
  set h : ℝ := (2⁻¹ : ℝ) ^ (B'.n + ℓ) with hhdef
  have hh : 0 < h := by positivity
  have hl : h ≤ B.side / 2 := hlev
  have hN : ((2 ^ (B'.n + ℓ) : ℕ) : ℝ) * h = 1 := by
    rw [hhdef]; push_cast; rw [← mul_pow]; norm_num
  obtain ⟨T, hTc, hTm, hTcov⟩ := ball_corner_subset_four (L := B'.n + ℓ) a1 a2 a3 a4
  have hball := ball_corner_subset_dzzV hh hN a1 a2 a3 a4
  have hgf : (⟨m₁ * h, m₂ * h⟩ : ℂ) ∈ frontier B'.closedBox := mem_frontier_closedBox hg hedge
  obtain ⟨g1, g2⟩ := hB' hg
  have hnear : ∀ b ∈ T, ∀ z ∈ b.closedBox, ‖z - B.center‖ ≤ 3 * B.side := by
    intro b hb z hz
    obtain ⟨hbn, hgb⟩ := hTm b hb
    have hs : b.side = h := by rw [DyBox.side, hbn]
    obtain ⟨e1, e2⟩ := abs_sub_le_of_mem_closedBox hz hgb
    rw [hs] at e1 e2
    simp only at e1 e2 g1 g2
    rw [← hhdef] at e1 e2
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have t1 := abs_sub_le z.re (m₁ * h) B.center.re
    have t2 := abs_sub_le z.im (m₂ * h) B.center.im
    linarith
  have hθT : ∀ b ∈ T, etaChaos W γ δh b.closedBox ω ≤ θ := fun b hb =>
    hopen b ⟨(hTm b hb).1, ⟨_, (hTm b hb).2, hgf⟩⟩
  refine (dzzMuIn_ball_le_of_boxes hup hball T hTcov hnear hθT).trans ?_
  refine le_trans ?_ hKθ
  exact mul_le_mul_left (by exact_mod_cast hTc) _

end DZZ
end LQGMetric
