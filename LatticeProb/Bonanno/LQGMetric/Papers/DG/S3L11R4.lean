/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L11R4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11R3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11V

/-!
# DG Lemma 3.11 for vertical rectangles at `μ = μ_ĥ`: geometry of the reflection (P2-DG105r)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1335 ("similarly" for the
`2^{-m} × 2^{-m+1}` rectangles). `L311LevelInputV` asks for good squares of the reflected
measure `(μ_ĥ).map swapC` on the grid of side `s/32` of `s ℛ_n + swapC b`. The square of site
`x` of that grid is the reflection of the square of site `x.swap` of the grid of side `s/32`
with offset `l311BV s b = b + (s/32)(1 − i)` in the original coordinates (`swapC_sqOne_V`).
So the vertical inputs are DG's horizontal events for the squares of the vertical rectangle
`l313StrV s b n` itself, in the original coordinates; the reflection only enters through
`goodSq_map_swapC` (the Liouville graph distance is invariant under the isometry `swapC`,
`dgLGD_map_swapC_le`). No reflected noise is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

open WhiteNoise SupTail GMCIdent

/-- the offset of the original-coordinate grid whose site `x.swap` reflects to site `x` of the
grid of `s ℛ_n + swapC b` (side `t = s/32`) -/
def l311BV (t : ℝ) (b : ℂ) : ℂ := ⟨b.re + t, b.im - t⟩

lemma sqX_l311BV (t : ℝ) (b : ℂ) (x : ℤ × ℤ) : sqX t (l311BV t b) x.swap = sqY t (swapC b) x := by
  simp only [sqX, sqY, l311BV, swapC_im, Prod.fst_swap]; ring

lemma sqY_l311BV (t : ℝ) (b : ℂ) (x : ℤ × ℤ) : sqY t (l311BV t b) x.swap = sqX t (swapC b) x := by
  simp only [sqX, sqY, l311BV, swapC_re, Prod.snd_swap]; ring

lemma swapC_sqOne_V (t : ℝ) (b : ℂ) (x : ℤ × ℤ) :
    swapC '' sqOne t (l311BV t b) x.swap = sqOne t (swapC b) x := by
  rw [image_swapC]; ext u
  simp only [mem_preimage, sqOne, Complex.mem_reProdIm, swapC_re, swapC_im, sqX_l311BV,
    sqY_l311BV]
  tauto

lemma sqOne_V_eq (t : ℝ) (b : ℂ) (x : ℤ × ℤ) :
    sqOne t (l311BV t b) x.swap = swapC '' sqOne t (swapC b) x := by
  rw [← swapC_sqOne_V, image_image]; simp only [swapC_swapC, image_id']

lemma swapC_mem_sqMids_V {t : ℝ} {b : ℂ} {x : ℤ × ℤ} {u : ℂ} (hu : u ∈ sqMids t (swapC b) x) :
    swapC u ∈ sqMids t (l311BV t b) x.swap := by
  simp only [sqMids, mem_insert_iff, mem_singleton_iff, sqX_l311BV, sqY_l311BV] at hu ⊢
  rcases hu with rfl | rfl | rfl | rfl
  · right; right; left; rfl
  · right; right; right; rfl
  · left; rfl
  · right; left; rfl

/-- **the reflection of good squares** (DG:1335): a good square of `μ` at site `x.swap` of the
grid with offset `l311BV t b` gives a good square of `μ ∘ swapC⁻¹` at site `x` of the grid with
offset `swapC b` -/
lemma goodSq_map_swapC {μ : Measure ℂ} {ε t M : ℝ} {b : ℂ} {x : ℤ × ℤ}
    (h : goodSq μ ε t (l311BV t b) M x.swap) : goodSq (μ.map swapC) ε t (swapC b) M x := by
  intro u hu v hv
  have hle := dgLGD_map_swapC_le μ ε (sqOne t (l311BV t b) x.swap) (swapC u) (swapC v)
  rw [swapC_sqOne_V, swapC_swapC, swapC_swapC] at hle
  exact (ENat.toENNReal_le.2 hle).trans (h _ (swapC_mem_sqMids_V hu) _ (swapC_mem_sqMids_V hv))

lemma percFar_swap {r : ℕ} {x y : ℤ × ℤ} (h : PercFar r x y) : PercFar r x.swap y.swap := by
  unfold PercFar at h ⊢
  simp only [Prod.fst_swap, Prod.snd_swap]
  tauto

lemma swapC_square (a c : ℝ) : swapC '' (Icc a c ×ℂ Icc a c) = Icc a c ×ℂ Icc a c := by
  rw [image_swapC]; ext u
  simp only [mem_preimage, Complex.mem_reProdIm, swapC_re, swapC_im]
  tauto

lemma swapC_l311K0 : swapC '' l311K0 = l311K0 := by
  unfold l311K0 ferniqueBox; exact swapC_square _ _

lemma swapC_interior_l311K0 : swapC '' interior l311K0 = interior l311K0 := by
  have := swapCHomeo.image_interior l311K0
  simp only [swapCHomeo, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk] at this
  rw [this, swapC_l311K0]

lemma swapC_affineC (s : ℝ) (c w : ℂ) :
    swapC (affineC s c w) = affineC s (swapC c) (swapC w) := by
  apply Complex.ext <;> simp [affineC_re, affineC_im]

lemma l311Corner_V (s : ℝ) (b : ℂ) (x : ℤ × ℤ) :
    l311Corner s (l311BV (s / 32) b) x.swap = swapC (l311Corner s (swapC b) x) := by
  apply Complex.ext
  · simp only [l311Corner, swapC_re, sqX_l311BV]
  · simp only [l311Corner, swapC_im, sqY_l311BV]

/-- every grid square's `S(1)` lies in the vertical rectangle `s ℛ_n^{V'} + b` -/
lemma l311_sqOne_sub_strV {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) {s : ℝ} (hs : 0 < s)
    (b : ℂ) : sqOne (s / 32) (l311BV (s / 32) b) x.swap ⊆ l313StrV s b n := by
  rw [sqOne_V_eq, ← swapC_l313Str]
  exact image_mono (l311_sqOne_sub_str hx hs (swapC b))

/-- the hypothesis `hTK` of `ae_goodSq_scale` for the vertical grid -/
lemma l311_affine_K0V {n : ℕ} {x : ℤ × ℤ} (hx : l311Grid n x) {s : ℝ} (hs : 0 < s) {b : ℂ}
    (hQ : l313StrV s b n ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6)) :
    affineC s (l311Corner s (l311BV (s / 32) b) x.swap) '' l311K0 ⊆ interior l311K0 := by
  have hQ' : l313Str s (swapC b) n ⊆ Icc (1 / 6) (5 / 6) ×ℂ Icc (1 / 6) (5 / 6) := by
    have e : l313Str s (swapC b) n = swapC '' l313StrV s b n := by
      rw [← swapC_l313Str, image_image]; simp only [swapC_swapC, image_id']
    rw [e, ← swapC_square]
    exact image_mono hQ
  have h := image_mono (f := swapC) (l311_affine_K0 hx hs hQ')
  rw [swapC_interior_l311K0, image_image] at h
  rw [l311Corner_V]
  intro u hu
  obtain ⟨w, hw, rfl⟩ := hu
  have hw' : swapC w ∈ l311K0 := by rw [← swapC_l311K0]; exact mem_image_of_mem _ hw
  have := h ⟨swapC w, hw', rfl⟩
  simp only [swapC_affineC, swapC_swapC] at this
  exact this

end DG
end LQGMetric
