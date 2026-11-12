/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32F4

/-!
# Walled (Eq.boundDprime), UW4: `𝓔_{B',open} ⊆ {Φ^W ≤ λ}` relative to a dyadic wall
(P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1131–1139) with Remark 5.2: for a sub-box
`B = wEmb Bw B_p` of the wall and a ring box `B' = wEmb Bw B'_p`, the corner balls of the
pulled-back ring box `B'_p` (in `𝕍`) map onto corner balls of `B'` inside `B̄w`, where the walled
measure `dzzWall B̄w μIn` is `μIn`; they are covered by `≤ 4` real boxes of `𝓑_∂(B', 2^{-ℓ})`.

* `dist_wHom`, `image_wHom_ball`, `wPullMeas_ball`, `image_wHom_dzzV`, `wEmb_mem_boxCollBdry`;
* **`phiLeW_of_openOn`**: the walled form of `phiLeW_of_open` (S3P32Z4), same proof through the
  similarity (`phiLeW_of_corner_mass` in the pulled-back grid, `dzzMuIn_ball_le_of_boxes` for the
  real balls).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {W : WNSpace → Ω → ℝ}

lemma norm_wHom_sub (Bw : DyBox) (a b : ℂ) : ‖wHom Bw a - wHom Bw b‖ = Bw.side * ‖a - b‖ := by
  rw [wHom_apply, wHom_apply, add_sub_add_right_eq_sub, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (wside_pos Bw)]

lemma dist_wHom (Bw : DyBox) (a b : ℂ) : dist (wHom Bw a) (wHom Bw b) = Bw.side * dist a b := by
  rw [dist_eq_norm, dist_eq_norm, norm_wHom_sub]

lemma image_wHom_ball (Bw : DyBox) (g : ℂ) (ρ : ℝ) :
    wHom Bw '' ball g ρ = ball (wHom Bw g) (Bw.side * ρ) := by
  have hs := wside_pos Bw
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball, dist_wHom]; rw [mem_ball] at hy
    exact mul_lt_mul_of_pos_left hy hs
  · intro hz
    refine ⟨(wHom Bw).symm z, ?_, by simp⟩
    rw [mem_ball]
    have : dist (wHom Bw ((wHom Bw).symm z)) (wHom Bw g) < Bw.side * ρ := by simpa using hz
    rw [dist_wHom] at this
    exact lt_of_mul_lt_mul_left this hs.le

lemma wPullMeas_ball (Bw : DyBox) (ν : Measure ℂ) (g : ℂ) (ρ : ℝ) :
    wPullMeas Bw ν (ball g ρ) = ν (ball (wHom Bw g) (Bw.side * ρ)) := by
  rw [wPullMeas, Measure.map_apply (wHom Bw).symm.continuous.measurable measurableSet_ball,
    ← Homeomorph.image_eq_preimage_symm, image_wHom_ball]

lemma image_wHom_dzzV (Bw : DyBox) : wHom Bw '' dzzV = Bw.closedBox := by
  rw [← closedBox_root, ← closedBox_wEmb, wEmb_root]

lemma wEmb_mem_boxCollBdry {Bw b c : DyBox} {ℓ : ℕ} (h : b ∈ boxCollBdry c ℓ) :
    wEmb Bw b ∈ boxCollBdry (wEmb Bw c) ℓ := by
  obtain ⟨hn, z, hz1, hz2⟩ := h
  refine ⟨by simp only [wEmb]; omega, wHom Bw z, ?_, ?_⟩
  · rw [closedBox_wEmb]; exact ⟨z, hz1, rfl⟩
  · rw [closedBox_wEmb, ← (wHom Bw).image_frontier]; exact ⟨z, hz2, rfl⟩

/-- **DZZ l. 1131–1139 relative to the wall** (walled `phiLeW_of_open`). -/
theorem phiLeW_of_openOn {γ δh : ℝ} {ω : Ω} {Bw Bp Bp' : DyBox} {ℓ : ℕ} {K θ : ℝ≥0∞}
    {δ r lam : ℝ}
    (hup : ∀ b' : DyBox, (∀ z ∈ b'.closedBox, ‖z - (wEmb Bw Bp).center‖ ≤ 3 * (wEmb Bw Bp).side) →
      wickQArea γ W ω b'.closedBox ≤ K * etaChaos W γ δh b'.closedBox ω)
    (hB' : Bp'.closedBox ⊆ Bp.largeBox) (hlev : (2⁻¹ : ℝ) ^ (Bp'.n + ℓ) ≤ Bp.side / 2)
    (hn : 1 ≤ Bp'.n + ℓ) (hr : 0 < r)
    (hopen : ∀ b ∈ boxCollBdry (wEmb Bw Bp') ℓ, etaChaos W γ δh b.closedBox ω ≤ θ)
    (hKθ : 4 * (K * θ) ≤ ENNReal.ofReal (δ ^ 2)) (hlam : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam) :
    PhiLeW (wPullMeas Bw (dzzWall Bw.closedBox (dzzMuIn γ W ω))) δ r Bp' lam := by
  refine phiLeW_of_corner_mass Bp' ℓ hn hr (fun m₁ m₂ a1 a2 a3 a4 hg hedge => ?_) hlam
  set h : ℝ := (2⁻¹ : ℝ) ^ (Bp'.n + ℓ) with hhdef
  have hh : 0 < h := by positivity
  have hl : h ≤ Bp.side / 2 := hlev
  have hN : ((2 ^ (Bp'.n + ℓ) : ℕ) : ℝ) * h = 1 := by
    rw [hhdef]; push_cast; rw [← mul_pow]; norm_num
  obtain ⟨T, hTc, hTm, hTcov⟩ := ball_corner_subset_four (L := Bp'.n + ℓ) a1 a2 a3 a4
  have hball := ball_corner_subset_dzzV hh hN a1 a2 a3 a4
  have hgf : (⟨m₁ * h, m₂ * h⟩ : ℂ) ∈ frontier Bp'.closedBox := mem_frontier_closedBox hg hedge
  obtain ⟨g1, g2⟩ := hB' hg
  have hnear' : ∀ b ∈ T, ∀ z ∈ b.closedBox, ‖z - Bp.center‖ ≤ 3 * Bp.side := by
    intro b hb z hz
    obtain ⟨hbn, hgb⟩ := hTm b hb
    have hs : b.side = h := by rw [DyBox.side, hbn]
    obtain ⟨e1, e2⟩ := abs_sub_le_of_mem_closedBox hz hgb
    rw [hs] at e1 e2
    simp only at e1 e2 g1 g2
    rw [← hhdef] at e1 e2
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im]
    have t1 := abs_sub_le z.re (m₁ * h) Bp.center.re
    have t2 := abs_sub_le z.im (m₂ * h) Bp.center.im
    linarith
  set g : ℂ := ⟨m₁ * h, m₂ * h⟩ with hgdef
  have hs := wside_pos Bw
  set T' := T.image (wEmb Bw) with hT'
  have hballB : ball (wHom Bw g) (Bw.side * h) ⊆ Bw.closedBox := by
    rw [← image_wHom_ball, ← image_wHom_dzzV]; exact image_mono hball
  have hball' : ball (wHom Bw g) (Bw.side * h) ⊆ dzzV := hballB.trans (closedBox_sub_dzzV' Bw)
  have hcov' : ball (wHom Bw g) (Bw.side * h) ⊆ ⋃ b ∈ T', b.closedBox := by
    rw [← image_wHom_ball]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.1 (hTcov hz)
    exact mem_iUnion₂.2 ⟨wEmb Bw b, Finset.mem_image_of_mem _ hb, by
      rw [closedBox_wEmb]; exact ⟨z, hzb, rfl⟩⟩
  have hnear : ∀ b ∈ T', ∀ z ∈ b.closedBox,
      ‖z - (wEmb Bw Bp).center‖ ≤ 3 * (wEmb Bw Bp).side := by
    intro b hb z hz
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    rw [closedBox_wEmb] at hz
    obtain ⟨z0, hz0, rfl⟩ := hz
    rw [center_wEmb, norm_wHom_sub, side_wEmb]
    have := hnear' b0 hb0 z0 hz0
    nlinarith
  have hθT : ∀ b ∈ T', etaChaos W γ δh b.closedBox ω ≤ θ := by
    intro b hb
    obtain ⟨b0, hb0, rfl⟩ := Finset.mem_image.1 hb
    exact hopen _ (wEmb_mem_boxCollBdry ⟨(hTm b0 hb0).1, ⟨_, (hTm b0 hb0).2, hgf⟩⟩)
  rw [wPullMeas_ball, dzzWall_ball_of_subset _ hballB]
  refine (dzzMuIn_ball_le_of_boxes hup hball' T' hcov' hnear hθT).trans ?_
  refine le_trans ?_ hKθ
  exact mul_le_mul_left (by exact_mod_cast (Finset.card_image_le).trans hTc) _

end DZZ
end LQGMetric
