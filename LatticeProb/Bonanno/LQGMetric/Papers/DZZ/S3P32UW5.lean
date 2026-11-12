/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32UW4

/-!
# Walled (Eq.boundDprime), UW5: (eq-B-percolation-Psi) for one sub-box of a dyadic wall
(P2-DZZUPW, packet P-317K-UP)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1104–1147) with Remark 5.2. **`p32_enc_boxW`** is a
copy of `p32_enc_box` (S3P32F2, P2-DZZ32F) for the real box `B = wEmb Bw B_p` of the wall: the
percolation core `enc_core_gen` (S3P32F1) is run in the grid of the pulled-back box `B_p` (so the
enclosure is relative to the wall, as `l37_enc_coreW`, S3L5W3), while the site events
`𝓔^c_{B'_i,open}` (`openBad`), their probabilities (`measure_openBad_le`), their independence
(`measure_biInter_eq_prod_wnSigma`, `disjoint_thickening_bdryU`) and `Φ^W ≤ λ`
(`phiLeW_of_openOn`, S3P32UW4) are about the real boxes `wEmb Bw B'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox GMCIdent

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Walled DZZ (eq-B-percolation-Psi) for one box, explicit parameters** (l. 1104–1147). -/
theorem p32_enc_boxW (hW : IsWhiteNoise P W) {γ : ℝ} {Bw Bp : DyBox} {k h ℓ : ℕ}
    (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h) (hB1 : 1 ≤ Bp.n) {δ r lam : ℝ} (hr : 0 < r)
    (hlam : (4 * (2 ^ ℓ + 1) : ℝ) ≤ lam) {K θo θ : ℝ≥0∞}
    (hKθ : 4 * (K * θo) ≤ ENNReal.ofReal (δ ^ 2)) (hθo0 : θo ≠ 0) (hθoT : θo ≠ ⊤)
    (G : Set Ω)
    (hup : ∀ ω ∈ G, ∀ b' : DyBox,
      (∀ z ∈ b'.closedBox, ‖z - (wEmb Bw Bp).center‖ ≤ 3 * (wEmb Bw Bp).side) →
      wickQArea γ W ω b'.closedBox ≤
        K * etaChaos W γ ((2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + 2 * k)) b'.closedBox ω)
    (hRs : 2 * (((2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + 2 * k) *
        Real.log ((2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + 2 * k))⁻¹ +
        (2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + 2 * k)) / 2) + 2 * (2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + k + ℓ) <
      3 * (2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + k))
    (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ((8 * (2 ^ ℓ + 2) : ℕ) : ℝ≥0∞) *
      (ENNReal.ofReal (((2 : ℝ)⁻¹ ^ ((wEmb Bw Bp).n + k + ℓ)) ^ 2) / θo) ≤
        θ ^ ((3 + 1) ^ 2)) :
    P (G ∩ {ω | ¬ HasEnclosure Bp k fun c =>
        PhiLeW (wPullMeas Bw (dzzWall Bw.closedBox (dzzMuIn γ W ω))) δ r c lam}) ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set Bt := wEmb Bw Bp with hBt
  set δh : ℝ := (2 : ℝ)⁻¹ ^ (Bt.n + 2 * k) with hδh
  set R : ℝ := (δh * Real.log δh⁻¹ + δh) / 2 with hRdef
  have hδh0 : 0 < δh := by positivity
  have hδh1 : δh ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hR : ∀ u ∈ Ioo 0 (δh ^ 2), etaRad u ≤ R := etaRad_le_bandHalf hδh0 hδh1
  set ρ : ℝ := (3 * (2 : ℝ)⁻¹ ^ (Bt.n + k) - 2 * R - 2 * (2 : ℝ)⁻¹ ^ (Bt.n + k + ℓ)) / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hlevel : ∀ b' ∈ boxColl Bp k, (wEmb Bw b').n = Bt.n + k := fun b' hb' => by
    rw [hBt]; simp only [wEmb]; rw [hb'.1]; ring
  refine enc_core_gen P Bp hK h4 hB1 (fun b' => openBad W γ δh θo ℓ (wEmb Bw b')) _ G hθ hεθ
    (fun b' hb' => by
      have := measure_openBad_le hW γ δh ℓ (wEmb Bw b') hθo0 hθoT
      rwa [hlevel b' hb'] at this)
    (fun F hF hfar => le_of_eq (measure_biInter_eq_prod_wnSigma hW F
      (fun b' => etaReg R ρ (bdryU (wEmb Bw b') ℓ)) _ (fun b1 hb1 b2 hb2 hne => ?_)
      (fun b' _ => measurableSet_openBad hW hR hρ0 γ θo ℓ (wEmb Bw b'))))
    (fun ω hG b' hb' hnot => ?_)
  · refine Set.disjoint_prod.2 (Or.inr ?_)
    have hn : b1.n = b2.n := (hF b1 hb1).1.trans (hF b2 hb2).1.symm
    have hn' : (wEmb Bw b1).n = (wEmb Bw b2).n := by simp only [wEmb]; rw [hn]
    have hfar' := hfar b1 hb1 b2 hb2 hne
    refine disjoint_thickening_bdryU hn' ?_ ?_
    · simp only [wEmb]; rw [hn]; omega
    · rw [DyBox.side, hlevel b1 (hF b1 hb1), hρ]
      linarith
  · have hopen : ∀ b ∈ boxCollBdry (wEmb Bw b') ℓ, etaChaos W γ δh b.closedBox ω ≤ θo := by
      intro b hb
      by_contra hc
      exact hnot ⟨b, mem_bdryT.2 hb, (not_le.1 hc).le⟩
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at hK; omega
      · exact h0
    have hlev : (2⁻¹ : ℝ) ^ (b'.n + ℓ) ≤ Bp.side / 2 := by
      rw [hb'.1, DyBox.side, div_eq_mul_inv, ← pow_succ]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    exact phiLeW_of_openOn (hup ω hG) hb'.2 hlev (by rw [hb'.1]; omega) hr hopen hKθ hlam

end DZZ
end LQGMetric
