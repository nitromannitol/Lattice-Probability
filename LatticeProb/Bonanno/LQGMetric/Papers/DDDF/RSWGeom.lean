/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.RSWGeom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

/-!
# RSW geometry: iterating DDDF Lemma 11 (DF Lemma 4.8) down to scale `2^{-p}`

Task P2-DDDFRSW (DDDF Prop 14 = Prop 7, `tightness.tex` l. 783–810; DF arXiv:1809.02607,
proof of Thm 3.1, DF:624–678). DDDF Step 1/2 (l. 794, 800): "By Lemma 11 [...] Furthermore, by
iterating, [...] `L_{a/2^p, b/2^p}`". Every left–right crossing of `[0,a] × [0,b]` (`a < b`) has a
subpath crossing one of finitely many rectangles isometric to `[0, a/2] × [0, b/2]` in the thin
direction (`RectCross.crossing_thin_subrect`); we normalize each such rectangle to
`[0, a/2] × [0, b/2]` by a rigid motion `z ↦ u z + c` (`|u| = 1`; a translation, or a translation
composed with the rotation by `-i`) and iterate `p` times.

* `CrossData c K A B`: the curve `c` has a sub-arc in `K` from `A` to `B` (either time direction).
* `Forces a b G S`: every left–right crossing of `[0,a] × [0,b]` has `CrossData` for
  `g⁻¹(S i)` for some motion `g ∈ G` (finite) and index `i`.
* `forces_step`, `forces_iter`: from `[0, a/2^p] × [0, b/2^p]` up to `[0,a] × [0,b]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric
namespace DDDF

open RectCross

/-- the curve `c` has a sub-arc `c([s,t])` (or `c([t,s])`) in `K` from `c s ∈ A` to `c t ∈ B` -/
def CrossData (c : ℝ → ℂ) (K A B : Set ℂ) : Prop :=
  ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, (∀ u ∈ uIcc s t, c u ∈ K) ∧ c s ∈ A ∧ c t ∈ B

/-- the rigid motion `z ↦ g.1 z + g.2` -/
def mot (g : ℂ × ℂ) (z : ℂ) : ℂ := g.1 * z + g.2

/-- composition of motions -/
def motComp (g h : ℂ × ℂ) : ℂ × ℂ := (g.1 * h.1, g.1 * h.2 + g.2)

theorem mot_motComp (g h : ℂ × ℂ) (z : ℂ) : mot (motComp g h) z = mot g (mot h z) := by
  simp only [mot, motComp]; ring

/-- every left–right crossing of `[0,a] × [0,b]` has `CrossData` for some `g⁻¹(S i)`, `g ∈ G` -/
def Forces {ι : Type*} (a b : ℝ) (G : Set (ℂ × ℂ)) (S : ι → Set ℂ × Set ℂ × Set ℂ) : Prop :=
  G.Finite ∧ (∀ g ∈ G, ‖g.1‖ = 1) ∧ ∀ {z₀ z₁ : ℂ} (γ : Path z₀ z₁),
    (∀ τ, γ τ ∈ rect 0 a 0 b) → z₀.re = 0 → z₁.re = a →
    ∃ g ∈ G, ∃ i, CrossData γ.extend (mot g ⁻¹' (S i).1) (mot g ⁻¹' (S i).2.1)
      (mot g ⁻¹' (S i).2.2)

theorem image_affine_uIcc (s t a b : ℝ) :
    (fun v => s + (t - s) * v) '' uIcc a b = uIcc (s + (t - s) * a) (s + (t - s) * b) := by
  rw [show (fun v => s + (t - s) * v) = (fun x => s + x) ∘ (fun v => (t - s) * v) from rfl,
    image_comp, image_const_mul_uIcc, image_const_add_uIcc]

/-- transport of `Forces` along a reparametrized, rigidly moved sub-arc -/
theorem forces_transport {ι : Type*} {S : ι → Set ℂ × Set ℂ × Set ℂ} {a' b' : ℝ}
    {G : Set (ℂ × ℂ)} (hF : Forces a' b' G S) {z₀ z₁ : ℂ} (γ : Path z₀ z₁) (h : ℂ × ℂ)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hrect : ∀ u ∈ uIcc s t, mot h (γ.extend u) ∈ rect 0 a' 0 b')
    (h0 : (mot h (γ.extend s)).re = 0) (h1 : (mot h (γ.extend t)).re = a') :
    ∃ g ∈ G, ∃ i, CrossData γ.extend (mot (motComp g h) ⁻¹' (S i).1)
      (mot (motComp g h) ⁻¹' (S i).2.1) (mot (motComp g h) ⁻¹' (S i).2.2) := by
  set σ : ℝ → ℝ := fun v => s + (t - s) * v with hσ
  have hσI : ∀ v ∈ Icc (0 : ℝ) 1, σ v ∈ uIcc s t := fun v hv => by
    have : σ v ∈ σ '' uIcc 0 1 := mem_image_of_mem _ (by rwa [uIcc_of_le zero_le_one])
    rw [hσ, image_affine_uIcc] at this
    simpa using this
  let γ' : Path (mot h (γ.extend s)) (mot h (γ.extend t)) :=
    { toFun := fun τ => mot h (γ.extend (σ τ))
      continuous_toFun := by
        simp only [hσ, mot]
        fun_prop
      source' := by simp [hσ]
      target' := by simp [hσ] }
  have hγ' : ∀ v ∈ Icc (0 : ℝ) 1, γ'.extend v = mot h (γ.extend (σ v)) := fun v hv => by
    rw [Path.extend_apply _ hv]; rfl
  obtain ⟨g, hg, i, s', hs', t', ht', hK, hA, hB⟩ :=
    hF.2.2 γ' (fun τ => hrect _ (hσI τ τ.2)) h0 h1
  have hst : uIcc s t ⊆ Icc 0 1 := uIcc_subset_Icc hs ht
  refine ⟨g, hg, i, σ s', hst (hσI s' hs'), σ t', hst (hσI t' ht'), fun u hu => ?_, ?_, ?_⟩
  · rw [hσ, ← image_affine_uIcc] at hu
    obtain ⟨v, hv, rfl⟩ := hu
    have := hK v hv
    rw [mem_preimage, hγ' v (uIcc_subset_Icc hs' ht' hv)] at this
    rw [mem_preimage, mot_motComp]; exact this
  · have := hA; rw [mem_preimage, hγ' s' hs'] at this
    rw [mem_preimage, mot_motComp]; exact this
  · have := hB; rw [mem_preimage, hγ' t' ht'] at this
    rw [mem_preimage, mot_motComp]; exact this

/-- the normalizing motion of a horizontal strip rectangle `[0, a/2] × [y, y + b/2]` -/
def motLR (y : ℝ) : ℂ × ℂ := (1, -((y : ℂ) * Complex.I))

/-- the normalizing motion of a rectangle `[0, b/2] × [y, y + a/2]` crossed bottom–top -/
def motBT (b y : ℝ) : ℂ × ℂ := (-Complex.I, -(y : ℂ) + ((b / 2 : ℝ) : ℂ) * Complex.I)

theorem mot_motLR_re (y : ℝ) (z : ℂ) : (mot (motLR y) z).re = z.re := by
  simp [mot, motLR]

theorem mot_motLR_im (y : ℝ) (z : ℂ) : (mot (motLR y) z).im = z.im - y := by
  simp [mot, motLR]; ring

theorem mot_motBT_re (b y : ℝ) (z : ℂ) : (mot (motBT b y) z).re = z.im - y := by
  simp [mot, motBT]; ring

theorem mot_motBT_im (b y : ℝ) (z : ℂ) : (mot (motBT b y) z).im = b / 2 - z.re := by
  simp [mot, motBT]; ring

/-- **One step** (DDDF Lemma 11 = DF Lemma 4.8 + normalization by rigid motions). -/
theorem forces_step {ι : Type*} {S : ι → Set ℂ × Set ℂ × Set ℂ} {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {G : Set (ℂ × ℂ)} (hF : Forces (a / 2) (b / 2) G S) :
    ∃ G' : Set (ℂ × ℂ), Forces a b G' S := by
  set δ := (b - a) / 4 with hδ
  set N := ⌊b / δ⌋₊ + 1
  set H : Set (ℂ × ℂ) := (fun k : ℕ => motLR (k * δ)) '' Iic N ∪
    (fun k : ℕ => motBT b (k * δ)) '' Iic N
  have hH : H.Finite := ((finite_Iic N).image _).union ((finite_Iic N).image _)
  have hHn : ∀ h ∈ H, ‖h.1‖ = 1 := by
    rintro h (⟨k, -, rfl⟩ | ⟨k, -, rfl⟩) <;> simp [motLR, motBT]
  refine ⟨image2 motComp G H, hF.1.image2 _ hH, ?_, ?_⟩
  · rintro _ ⟨g, hg, h, hh, rfl⟩
    simp only [motComp, norm_mul, hF.2.1 g hg, hHn h hh, mul_one]
  intro z₀ z₁ γ hγ hz₀ hz₁
  obtain ⟨k, hk, hcr⟩ := crossing_thin_subrect ha hab γ hγ hz₀ hz₁
  rw [← hδ] at hk hcr
  have hsI : ∀ {s t : ℝ}, 0 ≤ s → s ≤ t → t ≤ 1 → s ∈ Icc (0 : ℝ) 1 ∧ t ∈ Icc (0 : ℝ) 1 :=
    fun h0 h1 h2 => ⟨⟨h0, h1.trans h2⟩, ⟨h0.trans h1, h2⟩⟩
  rcases hcr with ⟨s, t, h0, hst, h1, hR, hdir⟩ | ⟨s, t, h0, hst, h1, hR, hdir⟩
  · have hm : motLR (k * δ) ∈ H := Or.inl ⟨k, hk, rfl⟩
    have hrect : ∀ u ∈ uIcc s t, mot (motLR (k * δ)) (γ.extend u) ∈ rect 0 (a / 2) 0 (b / 2) :=
      fun u hu => by
        rw [uIcc_of_le hst] at hu
        obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR u hu
        refine ⟨?_, ?_⟩ <;> simp only [mot_motLR_re, mot_motLR_im, mem_Icc] <;>
          constructor <;> linarith
    obtain ⟨hs, ht⟩ := hsI h0 hst h1
    rcases hdir with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · obtain ⟨g, hg, i, hc⟩ := forces_transport hF γ _ hs ht hrect
        (by rw [mot_motLR_re]; exact e0) (by rw [mot_motLR_re]; exact e1)
      exact ⟨_, mem_image2_of_mem hg hm, i, hc⟩
    · obtain ⟨g, hg, i, hc⟩ := forces_transport hF γ _ ht hs
        (fun u hu => hrect u (uIcc_comm s t ▸ hu))
        (by rw [mot_motLR_re]; exact e1) (by rw [mot_motLR_re]; exact e0)
      exact ⟨_, mem_image2_of_mem hg hm, i, hc⟩
  · have hm : motBT b (k * δ) ∈ H := Or.inr ⟨k, hk, rfl⟩
    have hrect : ∀ u ∈ uIcc s t, mot (motBT b (k * δ)) (γ.extend u) ∈
        rect 0 (a / 2) 0 (b / 2) := fun u hu => by
      rw [uIcc_of_le hst] at hu
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hR u hu
      refine ⟨?_, ?_⟩ <;> simp only [mot_motBT_re, mot_motBT_im, mem_Icc] <;>
        constructor <;> linarith
    obtain ⟨hs, ht⟩ := hsI h0 hst h1
    rcases hdir with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · obtain ⟨g, hg, i, hc⟩ := forces_transport hF γ _ hs ht hrect
        (by rw [mot_motBT_re, e0]; ring) (by rw [mot_motBT_re, e1]; ring)
      exact ⟨_, mem_image2_of_mem hg hm, i, hc⟩
    · obtain ⟨g, hg, i, hc⟩ := forces_transport hF γ _ ht hs
        (fun u hu => hrect u (uIcc_comm s t ▸ hu))
        (by rw [mot_motBT_re, e1]; ring) (by rw [mot_motBT_re, e0]; ring)
      exact ⟨_, mem_image2_of_mem hg hm, i, hc⟩

/-- **Iteration** (DDDF l. 794 "by iterating"): from scale `2^{-p}` up to scale `1`. -/
theorem forces_iter {ι : Type*} {S : ι → Set ℂ × Set ℂ × Set ℂ} (p : ℕ) :
    ∀ {a b : ℝ}, 0 < a → a < b → ∀ {G : Set (ℂ × ℂ)}, Forces (a / 2 ^ p) (b / 2 ^ p) G S →
      ∃ G' : Set (ℂ × ℂ), Forces a b G' S := by
  induction p with
  | zero => intro a b _ _ G hF; simp only [pow_zero, div_one] at hF; exact ⟨G, hF⟩
  | succ p ih =>
    intro a b ha hab G hF
    have e : ∀ x : ℝ, x / 2 ^ (p + 1) = x / 2 / 2 ^ p := fun x => by rw [pow_succ]; ring
    rw [e, e] at hF
    obtain ⟨G', hG'⟩ := ih (by positivity) (by linarith) hF
    exact forces_step ha hab hG'

end DDDF
end LQGMetric
