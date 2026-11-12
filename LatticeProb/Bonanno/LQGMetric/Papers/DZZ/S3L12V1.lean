/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L12V1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L316P1
import LatticeProb.Bonanno.LQGMetric.Perc.AnnulusClipCross

/-!
# DZZ Def 3.6 / Lemma 3.16 in crossing form (decision D93, packet P-2)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 920–939 (Def 3.6), l. 1005–1016
(the percolation argument of Lemma 3.7), l. 1381–1404 (Lemma 3.16). Decision D93 (DEC-93 §3.2):
the enclosure of Def 3.6 is produced, as in our Perc library, from four clipped long-way
`4`-crossings of good boxes of `𝓑(B, 2^{-k})` (one per active side rectangle of the annulus
`h + 2 ≤ ‖z‖_∞ ≤ 2h - 2`, `2^k = 2h`, in the grid of `hasEnclosure_of_sites`); `HasCross`
keeps them, `HasEnclosure` (path separation) follows.

* `HasCross`: the crossing form of Def 3.6.
* `hasEnclosure_of_hasCross`: gluing (`perc_annulus_enclosure_clip`) and encoding
  (`hasEnclosure_of_sites`), as at the end of `l316_enc_open`.
* `l316_cross_open`: `l316_enc_open` ending at `perc_annulus_peierls_clip_cross`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox PercClip

/-- **DZZ Def 3.6, crossing form** (D93): every active side rectangle of the clipped annulus
`h + 2 ≤ ‖z‖_∞ ≤ 2h - 2` (`2^k = 2h`) of the level-`(n_B + k)` grid around `B` has a long-way
`4`-crossing of grid sites whose boxes are good. -/
def HasCross (B : DyBox) (k : ℕ) (good : DyBox → Prop) : Prop :=
  ∃ h : ℕ, 2 ^ k = 2 * h ∧ ∀ d, (2 * (h : ℤ) - 2) < l37ext (B.n + k) (l37c B h) d →
    PercClipCross ((h : ℤ) + 2) (2 * (h : ℤ) - 2) d
      (clipLo (2 * (h : ℤ) - 2) (l37ext (B.n + k) (l37c B h)) d)
      (clipHi (2 * (h : ℤ) - 2) (l37ext (B.n + k) (l37c B h)) d)
      {z | InGrid (B.n + k) (l37c B h) z ∧ good (siteBox (B.n + k) (l37c B h) z)}

/-- Monotonicity of a clipped crossing in the set of good sites. -/
lemma dzzPercClipCross_mono {n N lo hi : ℤ} {d : PercDir} {G G' : Set (ℤ × ℤ)}
    (hG : ∀ z ∈ clipRect n N d lo hi, z ∈ G → z ∈ G') (h : PercClipCross n N d lo hi G) :
    PercClipCross n N d lo hi G' := by
  obtain ⟨a, b, ha, hb, haR, haG, hr⟩ := h
  exact ⟨a, b, ha, hb, haR, hG a haR haG,
    percStepIn_mono (S' := {z | z ∈ clipRect n N d lo hi ∧ z ∈ G'})
      (fun z hz => ⟨hz.1, hG z hz.1 hz.2⟩) (fun _ _ h => h) hr⟩

/-- **Crossings give an enclosure** (D93): `HasCross → HasEnclosure` (for `B ≠ [0,1]²`). -/
theorem hasEnclosure_of_hasCross {B : DyBox} {k : ℕ} {good : DyBox → Prop} (hB1 : 1 ≤ B.n)
    (hc : HasCross B k good) : HasEnclosure B k good := by
  obtain ⟨h, hK, hc⟩ := hc
  by_cases h4 : 4 ≤ h
  · obtain ⟨U, hU, hne, hconn, hsep⟩ := percEnclosureClip_of_cross ((h : ℤ) + 2)
      (2 * (h : ℤ) - 2) (by omega) (by omega) _ (l37ext_ge B hK) (l37ext_TB B hB1 hK)
      (l37ext_RL B hB1 hK) _ hc
    exact hasEnclosure_of_sites B hK _ U (fun z hz => (hU z hz).1.1)
      (fun z hz => (hU z hz).2.2) (fun z hz => (hU z hz).1.2) hne hconn
      (fun Γ s e hΓ hs he hrt => hsep Γ s e (fun z hz => annClip_of_inGrid (hΓ z hz)) hs he hrt)
  · exfalso
    obtain ⟨d, hd⟩ : ∃ d, 2 * (h : ℤ) - 2 < l37ext (B.n + k) (l37c B h) d := by
      rcases l37ext_TB B hB1 hK with h1 | h1
      · exact ⟨_, h1⟩
      · exact ⟨_, h1⟩
    obtain ⟨a, -, -, -, ⟨-, -, h1, h2⟩, -⟩ := hc d hd
    omega

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Peierls step of DZZ Lemma 3.7 / 3.16, crossing form** (l. 990–1015, D93): crossings by
open boxes outside an event of probability `≤ 4 (2N+1) (8θ)^{N-n+1}`. -/
theorem l316_cross_open (hW : IsWhiteNoise P W) (γ a : ℝ) {B : DyBox}
    {k k'' h : ℕ} (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h) (hB1 : 1 ≤ B.n)
    (hRs : 2 * (((2 : ℝ)⁻¹ ^ (B.n + 2 * k) * Real.log (((2 : ℝ)⁻¹ ^ (B.n + 2 * k)) ^ 2)⁻¹ +
        2 * (2 : ℝ)⁻¹ ^ (B.n + 2 * k)) / 4) + 2 * (2 : ℝ)⁻¹ ^ (B.n + k + k'') ≤
      3 * (2 : ℝ)⁻¹ ^ (B.n + k))
    {θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ENNReal.ofReal (8 * (2 ^ k'' + 2) * Real.exp (-a)) ≤ θ ^ ((3 + 1) ^ 2)) :
    P {ω | ¬ HasCross B k fun b' => ω ∈ boxOpen γ W b' k'' (B.n + 2 * k) a} ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set L := B.n + k
  set c := l37c B h
  set ext := l37ext L c
  set Bad : ℤ × ℤ → Set Ω := fun z => (boxOpen γ W (siteBox L c z) k'' (B.n + 2 * k) a)ᶜ
  have hn' : (((h + 2 : ℕ)) : ℤ) = (h : ℤ) + 2 := by push_cast; ring
  have hN' : (((2 * h - 2 : ℕ)) : ℤ) = 2 * (h : ℤ) - 2 := by omega
  have hperc := perc_annulus_peierls_clip_cross P (h + 2) (2 * h - 2) (by omega) (by omega) ext
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
  refine (measure_mono ?_).trans hperc
  intro ω hnot hall
  apply hnot
  refine ⟨h, hK, fun d hd => dzzPercClipCross_mono (fun z hz hzG => ⟨?_, ?_⟩) (hall d hd)⟩
  · exact inGrid_of_annClip (clipX_sub (by omega) (by omega) (l37ext_ge B hK) hd hz).1
  · simpa [Bad] using hzG

end DZZ
end LQGMetric
