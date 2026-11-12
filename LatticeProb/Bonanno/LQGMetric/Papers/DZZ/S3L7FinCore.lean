/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7FinCore at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinPath
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7PercIndep
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7MainBox
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusClipPeierls

/-!
# DZZ Lemma 3.7, (eq-B-percolation-Phi): the percolation step with explicit parameters (P2-DZZ3F)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 990–1015): the boxes
`B'_i ∈ 𝓑(B, 2^{-k})` are the sites of the annulus `h + 2 ≤ ‖z‖_∞ ≤ 2h - 2` (`2^k = 2h`),
clipped to the grid of `𝕍` (decision D72); a site is closed when `𝓔_{B'_i, open}` fails
(`boxOpen`, band level `B.n + 2k`, i.e. `η^{ε² s}_{ts}` with `t = 2^{-(k+k'')}`). The Peierls
bound `perc_annulus_peierls_clip` (with `κ`-independence `r = 3`) gives an open enclosure
outside an event of probability `≤ 4 (2N + 1) (8θ)^{N - n + 1}`; open boxes have
`Ψ_{B'_i, δ'} ≤ 8 (2^{k''} + 2)` (`psiLe_of_boxOpen`); the encoding is `hasEnclosure_of_sites`.

* `l37_enc_core`: (eq-B-percolation-Phi) with all parameters explicit; the asymptotic choice of
  the parameters is in `S3L7FinAsym`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- The clipping rectangle of the grid of `𝕍` at level `L`, seen from the base index `c`. -/
def l37ext (L : ℕ) (c : ℤ × ℤ) : PercDir → ℤ
  | .T => 2 ^ L - 1 - c.2
  | .B => c.2
  | .R => 2 ^ L - 1 - c.1
  | .L => c.1

lemma inGrid_of_annClip {L : ℕ} {c z : ℤ × ℤ} (h : annClip (l37ext L c) z) : InGrid L c z := by
  have hT := h .T; have hB := h .B; have hR := h .R; have hL := h .L
  simp only [annDir, l37ext] at hT hB hR hL
  exact ⟨by omega, by omega, by omega, by omega⟩

lemma annClip_of_inGrid {L : ℕ} {c z : ℤ × ℤ} (h : InGrid L c z) : annClip (l37ext L c) z := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  intro d; cases d <;> simp only [annDir, l37ext] <;> omega

lemma l37_pow (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) :
    (2 : ℤ) ^ (B.n + k) = 2 ^ B.n * (2 * h) := by
  rw [pow_add]; congr 1; exact_mod_cast hK

lemma l37ext_ge (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) (d : PercDir) :
    -((h : ℤ) + 2) ≤ l37ext (B.n + k) (l37c B h) d := by
  have e := l37_pow B hK
  have hj : (B.j : ℤ) + 1 ≤ 2 ^ B.n := by exact_mod_cast B.hj
  have hk : (B.k : ℤ) + 1 ≤ 2 ^ B.n := by exact_mod_cast B.hk
  have h0 : (0 : ℤ) ≤ h := by positivity
  have mj := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℤ) ≤ 2 * h)
  have mk := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℤ) ≤ 2 * h)
  have pj : (0 : ℤ) ≤ 2 * h * B.j := by positivity
  have pk : (0 : ℤ) ≤ 2 * h * B.k := by positivity
  cases d <;> simp only [l37ext, l37c] <;> nlinarith

lemma l37ext_TB (B : DyBox) (hB1 : 1 ≤ B.n) {k h : ℕ} (hK : 2 ^ k = 2 * h) :
    2 * (h : ℤ) - 2 < l37ext (B.n + k) (l37c B h) .T ∨
      2 * (h : ℤ) - 2 < l37ext (B.n + k) (l37c B h) .B := by
  have e := l37_pow B hK
  have hk : (B.k : ℤ) + 1 ≤ 2 ^ B.n := by exact_mod_cast B.hk
  have h2 : (2 : ℤ) ≤ 2 ^ B.n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B.n := pow_le_pow_right₀ (by norm_num) hB1
  have h0 : (0 : ℤ) ≤ h := by positivity
  simp only [l37ext, l37c]
  rcases Nat.eq_zero_or_pos B.k with hk0 | hk0
  · left; rw [hk0, e]; push_cast; nlinarith
  · right
    have : (1 : ℤ) ≤ B.k := by exact_mod_cast hk0
    nlinarith

lemma l37ext_RL (B : DyBox) (hB1 : 1 ≤ B.n) {k h : ℕ} (hK : 2 ^ k = 2 * h) :
    2 * (h : ℤ) - 2 < l37ext (B.n + k) (l37c B h) .R ∨
      2 * (h : ℤ) - 2 < l37ext (B.n + k) (l37c B h) .L := by
  have e := l37_pow B hK
  have hj : (B.j : ℤ) + 1 ≤ 2 ^ B.n := by exact_mod_cast B.hj
  have h2 : (2 : ℤ) ≤ 2 ^ B.n := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ B.n := pow_le_pow_right₀ (by norm_num) hB1
  have h0 : (0 : ℤ) ≤ h := by positivity
  simp only [l37ext, l37c]
  rcases Nat.eq_zero_or_pos B.j with hj0 | hj0
  · left; rw [hj0, e]; push_cast; nlinarith
  · right
    have : (1 : ℤ) ≤ B.j := by exact_mod_cast hj0
    nlinarith

lemma siteBox_injOn {L : ℕ} {c : ℤ × ℤ} {x y : ℤ × ℤ} (hx : InGrid L c x) (hy : InGrid L c y)
    (he : siteBox L c x = siteBox L c y) : x = y := by
  have j1 := siteBox_j hx; have j2 := siteBox_j hy
  have k1 := siteBox_k hx; have k2 := siteBox_k hy
  rw [he] at j1 k1
  exact Prod.ext (by omega) (by omega)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 3.7, (eq-B-percolation-Phi), explicit parameters** (l. 990–1015).
`ε = 2^{-k} = 1/(2h)`, `t = 2^{-(k+k'')}`, band level `B.n + 2k` (`η^{ε² s}_{ts}`), threshold
`a` for the normalized band exponents, `r = 3` for the independence (`κ`). -/
theorem l37_enc_core (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) {α δ δ' a : ℝ} {B : DyBox}
    {k k'' h : ℕ} (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h) (hB1 : 1 ≤ B.n)
    (hm : (2 : ℝ) ^ B.n ≤ δ ^ (-dzzCmc γ)) (hjY : (2 : ℝ) ^ (2 * k) ≤ (α * Real.log δ⁻¹) ^ 2)
    (hkk : k ≤ k'')
    (hsmall : δ ^ 2 * ((2 : ℝ)⁻¹ ^ (k + k'')) ^ 2 *
      Real.exp (γ * (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹)) +
        γ ^ 2 / 2 * (2 * Real.sqrt 8608 * Real.sqrt (Real.log B.side⁻¹ + 4))) * Real.exp a <
      δ' ^ 2)
    (hRs : 2 * (((2 : ℝ)⁻¹ ^ (B.n + 2 * k) * Real.log (((2 : ℝ)⁻¹ ^ (B.n + 2 * k)) ^ 2)⁻¹ +
        2 * (2 : ℝ)⁻¹ ^ (B.n + 2 * k)) / 4) + 2 * (2 : ℝ)⁻¹ ^ (B.n + k + k'') ≤
      3 * (2 : ℝ)⁻¹ ^ (B.n + k))
    {θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ENNReal.ofReal (8 * (2 ^ k'' + 2) * Real.exp (-a)) ≤ θ ^ ((3 + 1) ^ 2)) :
    P ({ω | approxLQG γ W ω B ≤ δ ^ 2} ∩ eventEFine γ W α δ ∩
        (encEventPsi γ W δ' B k (8 * (2 ^ k'' + 2)))ᶜ) ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set L := B.n + k
  set c := l37c B h
  set ext := l37ext L c
  set Bad : ℤ × ℤ → Set Ω := fun z => (boxOpen γ W (siteBox L c z) k'' (B.n + 2 * k) a)ᶜ
  have hn' : (((h + 2 : ℕ)) : ℤ) = (h : ℤ) + 2 := by push_cast; ring
  have hN' : (((2 * h - 2 : ℕ)) : ℤ) = 2 * (h : ℤ) - 2 := by omega
  -- the Peierls bound
  have hperc := perc_annulus_peierls_clip P (h + 2) (2 * h - 2) (by omega) (by omega) ext
    (fun d => by rw [hn']; exact l37ext_ge B hK d)
    (by rw [hN']; exact l37ext_TB B hB1 hK) (by rw [hN']; exact l37ext_RL B hB1 hK) Bad 3 hθ hεθ
    (fun z _ _ => measure_boxOpen_compl_le hW γ _ k'' _ a)
    (fun F hF hfar => by
      have hg : ∀ x ∈ F, InGrid L c x := fun x hx => inGrid_of_annClip (hF x hx).1
      have hinj : Set.InjOn (siteBox L c) F := fun x hx y hy he =>
        siteBox_injOn (hg x hx) (hg y hy) he
      have e1 : (⋂ x ∈ F, Bad x) = ⋂ b ∈ F.image (siteBox L c),
          (boxOpen γ W b k'' (B.n + 2 * k) a)ᶜ := by
        rw [Finset.set_biInter_finset_image]
      rw [e1]
      refine Eq.trans_le (measure_biInter_boxOpen_compl hW γ (F.image (siteBox L c))
        (n₁ := L) (r := 3) (R := ((2 : ℝ)⁻¹ ^ (B.n + 2 * k) *
          Real.log (((2 : ℝ)⁻¹ ^ (B.n + 2 * k)) ^ 2)⁻¹ + 2 * (2 : ℝ)⁻¹ ^ (B.n + 2 * k)) / 4)
        (fun b hb => by obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 hb; rfl)
        (fun u hu => etaRad_le_band (lt_trans (by positivity) hu.1) (by positivity) hu.2.le
          (pow_le_one₀ (by norm_num) (by norm_num)))
        (by
          have e : L + k'' = B.n + k + k'' := rfl
          rw [e]; push_cast; linarith)
        (fun b₁ hb₁ b₂ hb₂ hne => ?_)) (le_of_eq (Finset.prod_image hinj))
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb₁
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb₂
      have hxy : x ≠ y := fun he => hne (by rw [he])
      have j1 := siteBox_j (hg x hx); have j2 := siteBox_j (hg y hy)
      have k1 := siteBox_k (hg x hx); have k2 := siteBox_k (hg y hy)
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
      refine hasEnclosure_of_sites B hK _ U (fun z hz => inGrid_of_annClip (hU z hz).2.1)
        (fun z hz => (hU z hz).2.2) (fun z hz => ?_) hne hconn
        (fun Γ s e hΓ hs he hrt => hsep Γ s e (fun z hz => annClip_of_inGrid (hΓ z hz)) hs he hrt)
      obtain ⟨hzG, hzc, d, hd, -⟩ := hU z hz
      have hopen : ω ∈ boxOpen γ W (siteBox L c z) k'' (B.n + 2 * k) a := by
        simpa [Bad] using hzG
      exact psiLe_of_boxOpen hW hγ hE.2 hdec hm hjY (by omega) hM
        (siteBox_mem_boxColl B hK (inGrid_of_annClip hzc) hd) hopen hsmall
    · left; exact hdec
  · refine (measure_union_le _ _).trans ?_
    rw [hdec0, zero_add]
    exact hperc

end DZZ
end LQGMetric
