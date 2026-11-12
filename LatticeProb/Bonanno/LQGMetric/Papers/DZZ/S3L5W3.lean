/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L5W3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCore

/-!
# Walled DZZ Lemma 3.5, W3: enclosures relative to a dyadic wall, the percolation step
(P2-DZZL35W)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Lemma 3.7, (eq-B-percolation-Phi) (l. 990–1015),
for the enclosures needed by the walled Lemma 3.5 (l. 1047–1049 with Remark 5.2): the boxes
`B'_i` of the enclosure of a sub-box `B = wEmb Bw B'` of the wall are sub-boxes of the wall, and
the enclosure separates `B` from `∂B_large` *inside `B̄w`*. Copy of `l37_enc_core` (S3L7FinCore,
P2-DZZ3F) with the clipped annulus (`perc_annulus_peierls_clip`, D72) taken in the grid of the
pulled-back box `B'` (so the clipping rectangle is the wall instead of `𝕍`) and the sites being
the real boxes `wEmb Bw (siteBox …)`: the bad events, their independence
(`measure_biInter_boxOpen_compl`) and `Ψ ≤ λ` (`psiLe_of_boxOpen`) are about the real boxes, the
encoding (`hasEnclosure_of_sites`) is the one of `B'` in `𝕍`.

* `encEventPsiW`: `𝓔_{δ',B,ε,λ}` relative to the wall, for `B = wEmb Bw B'`;
* `wEmb_mem_boxColl`: `𝓑(B', ε)` maps into `𝓑(wEmb Bw B', ε)`;
* **`l37_enc_coreW`**: the walled (eq-B-percolation-Phi), explicit parameters.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma wEmb_mem_boxColl {Bw b c : DyBox} {k : ℕ} (h : c ∈ boxColl b k) :
    wEmb Bw c ∈ boxColl (wEmb Bw b) k := by
  refine ⟨by simp only [wEmb, h.1]; omega, ?_⟩
  rw [closedBox_wEmb, largeBox_wEmb]
  exact image_mono h.2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- `𝓔_{δ',B,ε,λ}` (`ε = 2^{-k}`) relative to the wall `B̄w`, for `B = wEmb Bw B'`: an enclosure of
the pulled-back box `B'` in `𝕍` by boxes whose real images have `Ψ_{·,δ'} ≤ λ`. -/
def encEventPsiW (γ : ℝ) (W : WNSpace → Ω → ℝ) (δ : ℝ) (Bw B' : DyBox) (k : ℕ) (lam : ℝ) :
    Set Ω :=
  {ω | HasEnclosure B' k fun c => PsiLe (approxLQG γ W ω) δ (wEmb Bw c) lam}

omit [MeasurableSpace Ω] in
lemma encEventPsiW_mono {γ δ' : ℝ} {Bw b : DyBox} {k : ℕ} {l₁ l₂ : ℝ} (h : l₁ ≤ l₂) :
    encEventPsiW γ W δ' Bw b k l₁ ⊆ encEventPsiW γ W δ' Bw b k l₂ := by
  intro ω hω
  refine hasEnclosure_mono (fun c hc => ?_) hω
  obtain ⟨N, hN, hle⟩ := hc
  exact ⟨N, hN, hle.trans h⟩

/-- **Walled DZZ Lemma 3.7, (eq-B-percolation-Phi), explicit parameters** (copy of
`l37_enc_core`): `B = wEmb Bw B'`, `1 ≤ B'.n`. -/
theorem l37_enc_coreW (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {α δ δ' a : ℝ}
    {Bw B' : DyBox} {k k'' h : ℕ} (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h) (hB1 : 1 ≤ B'.n)
    (hm : (2 : ℝ) ^ (wEmb Bw B').n ≤ δ ^ (-dzzCmc γ))
    (hjY : (2 : ℝ) ^ (2 * k) ≤ (α * Real.log δ⁻¹) ^ 2) (hkk : k ≤ k'')
    (hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log (wEmb Bw B').side⁻¹ + 4))) *
          Real.exp a < δ' ^ 2)
    (hRs : 2 * (((2 : ℝ)⁻¹ ^ ((wEmb Bw B').n + 2 * k) *
        Real.log (((2 : ℝ)⁻¹ ^ ((wEmb Bw B').n + 2 * k)) ^ 2)⁻¹ +
        2 * (2 : ℝ)⁻¹ ^ ((wEmb Bw B').n + 2 * k)) / 4) + 2 * (2 : ℝ)⁻¹ ^ ((wEmb Bw B').n + k + k'') ≤
      3 * (2 : ℝ)⁻¹ ^ ((wEmb Bw B').n + k))
    {θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ENNReal.ofReal (8 * (2 ^ k'' + 2) * Real.exp (-a)) ≤ θ ^ ((3 + 1) ^ 2)) :
    P ({ω | approxLQG γ W ω (wEmb Bw B') ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
        (encEventPsiW γ W δ' Bw B' k (8 * (2 ^ k'' + 2)))ᶜ) ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set B := wEmb Bw B' with hBdef
  set L := B'.n + k
  set c := l37c B' h
  set ext := l37ext L c
  set sb : ℤ × ℤ → DyBox := fun z => wEmb Bw (siteBox L c z) with hsb
  set Bad : ℤ × ℤ → Set Ω := fun z => (boxOpen γ W (sb z) k'' (B.n + 2 * k) a)ᶜ
  have hn' : (((h + 2 : ℕ)) : ℤ) = (h : ℤ) + 2 := by push_cast; ring
  have hN' : (((2 * h - 2 : ℕ)) : ℤ) = 2 * (h : ℤ) - 2 := by omega
  have hsbj : ∀ z, ((sb z).j : ℤ) = Bw.j * 2 ^ L + (siteBox L c z).j := fun z => by
    simp only [hsb, wEmb]; push_cast; rfl
  have hsbk : ∀ z, ((sb z).k : ℤ) = Bw.k * 2 ^ L + (siteBox L c z).k := fun z => by
    simp only [hsb, wEmb]; push_cast; rfl
  -- the Peierls bound
  have hperc := perc_annulus_peierls_clip P (h + 2) (2 * h - 2) (by omega) (by omega) ext
    (fun d => by rw [hn']; exact l37ext_ge B' hK d)
    (by rw [hN']; exact l37ext_TB B' hB1 hK) (by rw [hN']; exact l37ext_RL B' hB1 hK) Bad 3 hθ
    hεθ (fun z _ _ => measure_boxOpen_compl_le hW γ _ k'' _ a)
    (fun F hF hfar => by
      have hg : ∀ x ∈ F, InGrid L c x := fun x hx => inGrid_of_annClip (hF x hx).1
      have hinj : Set.InjOn sb F := fun x hx y hy he =>
        siteBox_injOn (hg x hx) (hg y hy) (wEmb_injective Bw he)
      have e1 : (⋂ x ∈ F, Bad x) = ⋂ b ∈ F.image sb, (boxOpen γ W b k'' (B.n + 2 * k) a)ᶜ := by
        rw [Finset.set_biInter_finset_image]
      rw [e1]
      refine Eq.trans_le (measure_biInter_boxOpen_compl hW γ (F.image sb)
        (n₁ := B.n + k) (r := 3) (R := ((2 : ℝ)⁻¹ ^ (B.n + 2 * k) *
          Real.log (((2 : ℝ)⁻¹ ^ (B.n + 2 * k)) ^ 2)⁻¹ + 2 * (2 : ℝ)⁻¹ ^ (B.n + 2 * k)) / 4)
        (fun b hb => by
          obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb
          simp only [hsb, hBdef, wEmb, siteBox]; omega)
        (fun u hu => etaRad_le_band (lt_trans (by positivity) hu.1) (by positivity) hu.2.le
          (pow_le_one₀ (by norm_num) (by norm_num)))
        (by push_cast; linarith)
        (fun b₁ hb₁ b₂ hb₂ hne => ?_)) (le_of_eq (Finset.prod_image hinj))
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb₂
      have hxy : x ≠ y := fun he => hne (by rw [he])
      have j1 := siteBox_j (hg x hx); have j2 := siteBox_j (hg y hy)
      have k1 := siteBox_k (hg x hx); have k2 := siteBox_k (hg y hy)
      have i1 := hsbj x; have i2 := hsbj y; have i3 := hsbk x; have i4 := hsbk y
      have := hfar x hx y hy hxy
      simp only [PercFar] at this
      push_cast at this
      omega)
  rw [hn', hN'] at hperc
  -- the decomposition event is almost sure
  have hdec0 : P (decompEvent W)ᶜ = 0 := by
    have := ae_iff.1 (ae_decompEvent (P := P) hW)
    simpa [compl_def] using this
  refine (measure_mono (t := (decompEvent W)ᶜ ∪
    {ω | ¬ PercEnclosureClip ((h : ℤ) + 2) (2 * (h : ℤ) - 2) ext {z | ω ∉ Bad z}}) ?_).trans ?_
  · rintro ω ⟨⟨hM, hE⟩, hnot⟩
    by_cases hdec : ω ∈ decompEvent W
    · right
      rintro ⟨U, hU, hne, hconn, hsep⟩
      apply hnot
      refine hasEnclosure_of_sites B' hK _ U (fun z hz => inGrid_of_annClip (hU z hz).2.1)
        (fun z hz => (hU z hz).2.2) (fun z hz => ?_) hne hconn
        (fun Γ s e hΓ hs he hrt => hsep Γ s e (fun z hz => annClip_of_inGrid (hΓ z hz)) hs he hrt)
      obtain ⟨hzG, hzc, d, hd, -⟩ := hU z hz
      have hopen : ω ∈ boxOpen γ W (sb z) k'' (B.n + 2 * k) a := by
        simpa [Bad] using hzG
      exact psiLe_of_boxOpen hW hγ hE.2 hdec hm hjY (by omega) hM
        (wEmb_mem_boxColl (siteBox_mem_boxColl B' hK (inGrid_of_annClip hzc) hd)) hopen hsmall
    · left; exact hdec
  · refine (measure_union_le _ _).trans ?_
    rw [hdec0, zero_add]
    exact hperc

end DZZ
end LQGMetric
