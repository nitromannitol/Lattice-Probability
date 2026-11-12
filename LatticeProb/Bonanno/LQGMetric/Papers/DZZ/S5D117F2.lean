/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5D117F2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117F

/-!
# D117, packet P-BIG, part 2: (eq-geodesic-range) and the truncation on the big-ball event

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-geodesic-range) l. 2340–2345 and l. 2562–2563:
on the event that balls of radius `≥ r` inside `𝕍` have mass `> 2δ²` (`DZZBigBalls`, S5D117F),
a geodesic to `∂𝕍_{v,κ}` truncated at its first exit only uses balls of radius `< r`, hence stays
within distance `2r` of `𝕍_{v,κ}`. Here (deterministic, the measure is a walled `dzzWall 𝕍 ν`):

* `ball_small_of_big`: on the event, a ball of mass `≤ δ²` has radius `< r` and lies in `𝕍`;
* `ball_subset_sqBox_of_big`: such a ball meeting `𝕍_{c,l}` lies in `𝕍_{c,l+4r}`;
* **`lgdMinSet_frontier_sqBox_eq_wall`** ((eq-geodesic-range), `r = κ/4`):
  `min_{∂𝕍_{v,κ}} D_δ(v,·) = min_{∂𝕍_{v,κ}} D̄^{v,2κ}_δ(v,·)`;
* **`lgdMinSet_cover_le_of_big`** (the truncation of l. 2562–2563): for pieces `L i` covering
  `∂𝕍_{u,l}` and walls `K i ⊇ 𝕍_{u,l+4r}`, `⨅ᵢ min_{x ∈ L i} D^{K i}_δ(u, x) ≤ D_δ(u, y)` for every
  `y ∉ int 𝕍_{u,l}`.

The truncation needs the margin `4r` around the *whole* box `𝕍_{u,l}` (the truncated chain may
protrude by `< 2r` on every side), not only around `L`: see the report (DEC-117 §2(a)(ii)).
Own elementary argument, from `lgdMinSet_dzzWall_le_of_exit` (S3P32X).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- the big-ball property of `DZZBigBalls` at a fixed `δ` -/
def BigBallsAt (μ : Measure ℂ) (r δ : ℝ) : Prop :=
  ∀ (x : ℂ) (ρ : ℝ), r ≤ ρ → ball x ρ ⊆ dzzV → ENNReal.ofReal (2 * δ ^ 2) < μ (ball x ρ)

/-- on the big-ball event, a ball of mass `≤ δ²` of the walled measure has radius `< r` and lies
in `𝕍` -/
lemma ball_small_of_big {ν : Measure ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hbig : BigBallsAt (dzzWall dzzV ν) r δ) {x : ℂ} {ρ : ℝ}
    (hm : dzzWall dzzV ν (ball x ρ) ≤ ENNReal.ofReal (δ ^ 2)) : ball x ρ ⊆ dzzV ∧ ρ < r := by
  have hV : ball x ρ ⊆ dzzV := by
    by_contra h
    rw [dzzWall_ball_of_not_subset isClosed_dzzV ν h] at hm
    exact ENNReal.ofReal_ne_top (top_le_iff.1 hm)
  refine ⟨hV, lt_of_not_ge fun hr => ?_⟩
  have h1 := hbig x ρ hr hV
  have h2 : ENNReal.ofReal (δ ^ 2) < ENNReal.ofReal (2 * δ ^ 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith [sq_pos_of_pos hδ])
  exact absurd (h1.trans_le hm) (not_lt.2 h2.le)

/-- such a ball meeting `𝕍_{c,l}` lies in `𝕍_{c,l+4r}` -/
lemma ball_subset_sqBox_of_big {ν : Measure ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hbig : BigBallsAt (dzzWall dzzV ν) r δ) {c x : ℂ} {l ρ : ℝ}
    (hm : dzzWall dzzV ν (ball x ρ) ≤ ENNReal.ofReal (δ ^ 2))
    (hne : (ball x ρ ∩ sqBox c l).Nonempty) : ball x ρ ⊆ sqBox c (l + 4 * r) := by
  have hρ := (ball_small_of_big hδ hbig hm).2
  obtain ⟨p, hp, hpc⟩ := hne
  intro z hz
  have hzp : ‖z - p‖ < 2 * r := by
    have := dist_triangle z x p
    rw [mem_ball] at hz hp
    rw [← dist_eq_norm]
    linarith [dist_comm p x]
  have h1 := Complex.abs_re_le_norm (z - p)
  have h2 := Complex.abs_im_le_norm (z - p)
  obtain ⟨hp1, hp2⟩ := hpc
  simp only [Complex.sub_re, Complex.sub_im] at h1 h2
  refine ⟨?_, ?_⟩
  · calc |z.re - c.re| ≤ |z.re - p.re| + |p.re - c.re| := by
          rw [show z.re - c.re = (z.re - p.re) + (p.re - c.re) by ring]; exact abs_add_le _ _
      _ ≤ (l + 4 * r) / 2 := by linarith
  · calc |z.im - c.im| ≤ |z.im - p.im| + |p.im - c.im| := by
          rw [show z.im - c.im = (z.im - p.im) + (p.im - c.im) by ring]; exact abs_add_le _ _
      _ ≤ (l + 4 * r) / 2 := by linarith

/-- the open box with closure `𝕍_{c,l}` -/
def openBoxC (c : ℂ) (l : ℝ) : Set ℂ :=
  Ioo (c.re - l / 2) (c.re + l / 2) ×ℂ Ioo (c.im - l / 2) (c.im + l / 2)

lemma isOpen_openBoxC (c : ℂ) (l : ℝ) : IsOpen (openBoxC c l) := isOpen_Ioo.reProdIm isOpen_Ioo

lemma mem_openBoxC_self (c : ℂ) {l : ℝ} (hl : 0 < l) : c ∈ openBoxC c l :=
  Complex.mem_reProdIm.mpr ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma closure_openBoxC_subset (c : ℂ) (l : ℝ) : closure (openBoxC c l) ⊆ sqBox c l := by
  refine closure_minimal (fun z hz => ?_) (isClosed_sqBox c l)
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hz
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

lemma frontier_openBoxC_subset (c : ℂ) {l : ℝ} (hl : 0 < l) :
    frontier (sqBox c l) ⊆ (openBoxC c l)ᶜ := by
  rw [← frontier_openBox_eq c hl]
  exact (isOpen_openBoxC c l).frontier_eq ▸ fun z hz => hz.2

/-- **truncation on the big-ball event** (DZZ l. 2562–2563, with the margin `4r` around the
whole box): if the pieces `L i` cover `∂𝕍_{u,l}` and every wall `K i` contains `𝕍_{u,l+4r}`, then
`⨅ᵢ min_{x ∈ L i} D^{K i}_δ(u, x) ≤ D_δ(u, y)` for every `y` outside the open box. -/
theorem lgdMinSet_cover_le_of_big {ν : Measure ℂ} {r δ : ℝ} (hδ : 0 < δ)
    (hbig : BigBallsAt (dzzWall dzzV ν) r δ) {u y : ℂ} {l : ℝ} (hl : 0 < l)
    (hy : y ∉ openBoxC u l) {ι : Type*} (L K : ι → Set ℂ)
    (hL : frontier (sqBox u l) ⊆ ⋃ i, L i) (hK : ∀ i, sqBox u (l + 4 * r) ⊆ K i) :
    ⨅ i, lgdMinSet (dzzWall (K i) (dzzWall dzzV ν)) δ {u} (L i) ≤
      lgdDZZ (dzzWall dzzV ν) δ u y := by
  set μ := dzzWall dzzV ν
  have hex := lgdMinSet_dzzWall_le_of_exit μ δ (isOpen_openBoxC u l) (mem_openBoxC_self u hl) hy
    (K := sqBox u (l + 4 * r)) fun c ρ hne hm => ball_subset_sqBox_of_big hδ hbig hm
      (hne.mono (inter_subset_inter_right _ (closure_openBoxC_subset u l)))
  refine le_trans ?_ hex
  refine le_iInf₂ fun x hx => le_iInf₂ fun z hz => ?_
  rw [mem_singleton_iff.mp hx]
  rw [openBoxC, frontier_openBox_eq u hl] at hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hL hz)
  refine (iInf_le _ i).trans ((iInf₂_le u (mem_singleton u)).trans ((iInf₂_le z hi).trans ?_))
  exact lgdDZZ_mono_measure (dzzWall_anti (hK i) μ) δ u z

/-- **(eq-geodesic-range)** (DZZ l. 2340–2345): on the big-ball event at radius `κ/4`,
`min_{∂𝕍_{v,κ}} D_δ(v,·) = min_{∂𝕍_{v,κ}} D̄^{v,2κ}_δ(v,·)`. -/
theorem lgdMinSet_frontier_sqBox_eq_wall {ν : Measure ℂ} {δ κ : ℝ} (hδ : 0 < δ) (hκ : 0 < κ)
    (hbig : BigBallsAt (dzzWall dzzV ν) (κ / 4) δ) (v : ℂ) :
    lgdMinSet (dzzWall (sqBox v (2 * κ)) (dzzWall dzzV ν)) δ {v} (frontier (sqBox v κ)) =
      lgdMinSet (dzzWall dzzV ν) δ {v} (frontier (sqBox v κ)) := by
  set μ := dzzWall dzzV ν
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    rw [mem_singleton_iff.mp hx]
    have h := lgdMinSet_cover_le_of_big hδ hbig hκ (frontier_openBoxC_subset v hκ hy)
      (ι := Unit) (fun _ => frontier (sqBox v κ)) (fun _ => sqBox v (2 * κ))
      (fun z hz => mem_iUnion.2 ⟨(), hz⟩) (fun _ => by
        rw [show κ + 4 * (κ / 4) = 2 * κ by ring])
    simpa using h
  · exact iInf₂_mono fun x _ => iInf₂_mono fun y _ =>
      lgdDZZ_mono_measure (le_dzzWall _ μ) δ x y

end DZZ
end LQGMetric
