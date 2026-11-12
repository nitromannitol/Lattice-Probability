/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12V2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12V1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinAsym
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L16Good

/-!
# DZZ Lemma 3.16 in crossing form: the statement (D93, packet P-4, coarse form)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1381–1397: the percolation runs on
the boxes `B'_i ∈ 𝓑(B, ε)`, and every box of `𝓑'_i = 𝓑_∂(B'_i, t/ε)` of an open `B'_i` has
`M_{ε* s} ≤ δ²`. `HasCrossRing B K g` records exactly this in crossing form: crossings
(`HasCross`) of boxes of `𝓑(B, 2^{-k})` all of whose boundary boxes of depth `d`
(`k + d = K`) satisfy `g`. (The fine-level form `HasCross B K g` of DEC-93 P-3/P-4 does not
follow from coarse crossings; see the report of P2-DZZ93A.)

* `hasCross_mono'`, `hasEnclosure_of_hasCrossRing` (`hasEnclosure_of_hasCross` +
  `hasEnclosure_ring`).
* `encEventCross`, `DZZLemma316Cross`, `dzzLemma316Perc_of_cross`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox PercClip

/-- Monotonicity of `HasCross` on the boxes of `𝓑(B, 2^{-k})`. -/
lemma hasCross_mono' {B : DyBox} {k : ℕ} {g₁ g₂ : DyBox → Prop}
    (hg : ∀ b' ∈ boxColl B k, g₁ b' → g₂ b') (h : HasCross B k g₁) : HasCross B k g₂ := by
  obtain ⟨h, hK, hc⟩ := h
  refine ⟨h, hK, fun d hd => dzzPercClipCross_mono (fun z hz hzG => ⟨hzG.1, ?_⟩) (hc d hd)⟩
  have hX := clipX_sub (by omega) ?_ (l37ext_ge B hK) hd hz
  · exact hg _ (siteBox_mem_boxColl B hK hzG.1 hX.2.1) hzG.2
  · obtain ⟨-, -, h1, h2⟩ := hz; omega

/-- Crossings of boxes of `𝓑(B, 2^{-k})` whose boundary boxes of depth `d` (`k + d = K`) are
good (DZZ l. 1381–1397, crossing form). -/
def HasCrossRing (B : DyBox) (K : ℕ) (g : DyBox → Prop) : Prop :=
  ∃ k d : ℕ, k + d = K ∧ HasCross B k fun b' => ∀ bt ∈ boxCollBdry b' d, g bt

/-- `HasCrossRing → HasEnclosure` (Def 3.6). -/
theorem hasEnclosure_of_hasCrossRing {B : DyBox} {K : ℕ} {g : DyBox → Prop} (hB1 : 1 ≤ B.n)
    (h : HasCrossRing B K g) : HasEnclosure B K g := by
  obtain ⟨k, d, rfl, hc⟩ := h
  exact hasEnclosure_ring d (hasEnclosure_of_hasCross hB1 hc)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The crossing form of `encEventCell`. -/
def encEventCross (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (b : DyBox) : Set Ω :=
  {ω | HasCrossRing b (epsStarN αs δ) fun b' => approxLQG γ W ω b' < δ ^ 2}

/-- **DZZ Lemma 3.16, (eq-B-percolation), crossing form** (statement of `DZZLemma316Perc` with
`encEventCross`). -/
def DZZLemma316Cross (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) : Prop :=
  ∃ α₁ : ℝ, ∀ α ≥ α₁, ∃ A : ℝ, ∀ αs ≥ A, ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ b : DyBox, 1 ≤ b.n → (b.n : ℝ) ≤ dzzCmc γ * Real.logb 2 δ⁻¹ →
      P ({ω | approxLQG γ W ω b ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩ (encEventCross γ W αs δ b)ᶜ) ≤
        ENNReal.ofReal (δ ^ (10 * dzzCmc γ + 10))

end DZZ
end LQGMetric
