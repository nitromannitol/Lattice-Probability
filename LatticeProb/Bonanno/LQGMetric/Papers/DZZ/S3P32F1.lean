/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Z4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7FinCore

/-!
# DZZ Prop 3.2 at `μIn`, (eq-B-percolation-Psi): the percolation core with abstract site events
(P2-DZZ32F)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1104–1147): "We can now apply the percolation
argument as in the proof of Lemma 3.7, with parameters … `p = t^{0.9}` and `κ = 2` here."

* `enc_core_gen`: the Peierls step of `l37_enc_core` (S3L7FinCore, DZZ Lemma 3.7 l. 990–1015)
  with the closed-site events `Bad b'` and the goodness `good ω b'` abstract: site probabilities
  `≤ ε`, independence of sites at index distance `≥ 4`, and `ω ∈ G`, `ω ∉ Bad b' ⇒ good ω b'`.
  The proof is the text of `l37_enc_core` without the Ψ-specific parts.
* `measure_biInter_eq_prod_wnSigma`: events measurable for the white noise on pairwise disjoint
  regions are independent (`IsWhiteNoise.iIndepFun_of_pairwise_disjoint`), finite form.
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

/-- **The percolation step of DZZ Lemma 3.7 with abstract site events** (l. 990–1015, used again
at l. 1144–1147). -/
theorem enc_core_gen (P : Measure Ω) (B : DyBox) {k h : ℕ} (hK : 2 ^ k = 2 * h) (h4 : 4 ≤ h)
    (hB1 : 1 ≤ B.n) (Bad : DyBox → Set Ω) (good : Ω → DyBox → Prop) (G : Set Ω)
    {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((3 + 1) ^ 2))
    (hε : ∀ b' ∈ boxColl B k, P (Bad b') ≤ ε)
    (hind : ∀ F : Finset DyBox, (∀ b ∈ F, b ∈ boxColl B k) →
      (∀ B₁ ∈ F, ∀ B₂ ∈ F, B₁ ≠ B₂ → (B₁.j + 3 + 1 ≤ B₂.j ∨ B₂.j + 3 + 1 ≤ B₁.j ∨
        B₁.k + 3 + 1 ≤ B₂.k ∨ B₂.k + 3 + 1 ≤ B₁.k)) →
      P (⋂ b ∈ F, Bad b) ≤ ∏ b ∈ F, P (Bad b))
    (hgood : ∀ ω ∈ G, ∀ b' ∈ boxColl B k, ω ∉ Bad b' → good ω b') :
    P (G ∩ {ω | ¬ HasEnclosure B k (good ω)}) ≤
      4 * ((2 * (2 * h - 2) + 1 : ℕ) * (8 * θ) ^ ((2 * h - 2) - (h + 2) + 1)) := by
  set L := B.n + k
  set c := l37c B h
  set ext := l37ext L c
  set Bad' : ℤ × ℤ → Set Ω := fun z => Bad (siteBox L c z)
  have hn' : (((h + 2 : ℕ)) : ℤ) = (h : ℤ) + 2 := by push_cast; ring
  have hN' : (((2 * h - 2 : ℕ)) : ℤ) = 2 * (h : ℤ) - 2 := by omega
  have hperc := perc_annulus_peierls_clip P (h + 2) (2 * h - 2) (by omega) (by omega) ext
    (fun d => by rw [hn']; exact l37ext_ge B hK d)
    (by rw [hN']; exact l37ext_TB B hB1 hK) (by rw [hN']; exact l37ext_RL B hB1 hK) Bad' 3 hθ hεθ
    (fun z hz hd => by
      obtain ⟨d, hd⟩ := hd
      have hN : annBox (2 * (h : ℤ) - 2) z := by rw [← hN']; exact hd.1
      exact hε _ (siteBox_mem_boxColl B hK (inGrid_of_annClip hz) hN))
    (fun F hF hfar => by
      have hg : ∀ x ∈ F, InGrid L c x := fun x hx => inGrid_of_annClip (hF x hx).1
      have hinj : Set.InjOn (siteBox L c) F := fun x hx y hy he =>
        siteBox_injOn (hg x hx) (hg y hy) he
      have e1 : (⋂ x ∈ F, Bad' x) = ⋂ b ∈ F.image (siteBox L c), Bad b := by
        rw [Finset.set_biInter_finset_image]
      rw [e1]
      refine (hind (F.image (siteBox L c)) (fun b hb => ?_) (fun b₁ hb₁ b₂ hb₂ hne => ?_)).trans
        (le_of_eq (Finset.prod_image hinj))
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb
        obtain ⟨-, d, hd⟩ := hF x hx
        exact siteBox_mem_boxColl B hK (hg x hx) (by rw [← hN']; exact hd.1)
      · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hb₁
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hb₂
        have hxy : x ≠ y := fun he => hne (by rw [he])
        have j1 := siteBox_j (hg x hx); have j2 := siteBox_j (hg y hy)
        have k1 := siteBox_k (hg x hx); have k2 := siteBox_k (hg y hy)
        have := hfar x hx y hy hxy
        simp only [PercFar] at this
        push_cast at this
        omega)
  rw [hn', hN'] at hperc
  refine (measure_mono (t := {ω | ¬ PercEnclosureClip ((h : ℤ) + 2) (2 * (h : ℤ) - 2) ext
    {z | ω ∉ Bad' z}}) ?_).trans hperc
  rintro ω ⟨hG, hnot⟩ ⟨U, hU, hne, hconn, hsep⟩
  apply hnot
  refine hasEnclosure_of_sites B hK _ U (fun z hz => inGrid_of_annClip (hU z hz).2.1)
    (fun z hz => (hU z hz).2.2) (fun z hz => ?_) hne hconn
    (fun Γ s e hΓ hs he hrt => hsep Γ s e (fun z hz => annClip_of_inGrid (hΓ z hz)) hs he hrt)
  obtain ⟨hzG, hzc, d, hd⟩ := hU z hz
  exact hgood ω hG _ (siteBox_mem_boxColl B hK (inGrid_of_annClip hzc) hd.1)
    hzG

/-- **Independence over disjoint white-noise regions**, finite form. -/
theorem measure_biInter_eq_prod_wnSigma (hW : IsWhiteNoise P W) {ι : Type} [DecidableEq ι]
    (F : Finset ι) (A : ι → Set (ℝ × ℂ)) (E : ι → Set Ω)
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (A i) (A j))
    (hE : ∀ i ∈ F, MeasurableSet[wnSigma W (A i)] (E i)) :
    P (⋂ i ∈ F, E i) = ∏ i ∈ F, P (E i) := by
  classical
  set A' : ι → Set (ℝ × ℂ) := fun i => if i ∈ F then A i else ∅
  have hA' : Pairwise fun i j => Disjoint (A' i) (A' j) := by
    intro i j hij
    by_cases hi : i ∈ F
    · by_cases hj : j ∈ F
      · simp only [A', hi, hj, ite_true]; exact hdisj i hi j hj hij
      · simp only [A', hj, ite_false]; exact disjoint_empty _
    · simp only [A', hi, ite_false]; exact empty_disjoint _
  have h := hW.iIndepFun_of_pairwise_disjoint hA'
  rw [iIndepFun_iff_iIndep] at h
  refine h.meas_biInter fun i hi => ?_
  have e : A' i = A i := by simp only [A', hi, ite_true]
  show MeasurableSet[wnSigma W (A' i)] (E i)
  rw [e]; exact hE i hi

end DZZ
end LQGMetric
