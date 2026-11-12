/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom56CPlan at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom56CGlob

/-!
# GM Lemma 5.6: planar facts about the two corridors (task P2-M2L56b)

GM = Gwynne–Miller, arXiv:1905.00383, `uniqueness-final.tex`, proof of Lemma 5.6 (l. 2963–2989),
corridors of decision D69. For the grid corridor `rectC c e (50 s) (2 s)` of `exists_corridor`:

* `corrU_facts` (corridor at `u`, `|u − z| = R`, axis within `45°` of the outward normal):
  `u, c` lie in it; all its points are within `104 s` of `u`; `|c − z| ≤ R − 25 s`; its points
  outside `B_{19 s}(u)` satisfy `|x − z| ≤ R − 4 s`;
* `corrV_facts` (corridor at `v`, `|v − z| = R`, axis within `45°` of the inward normal):
  the same first two facts; its points outside `B_{19 s}(v)` satisfy `|x − z| ≥ R + 4 s`; and the
  points `q` of the segment from `c` to `v' = z + (3/2)(v − z)` satisfy `|q − z| ≥ R + 30 s` and
  `|q − v| ≥ 30 s`.
Own elementary arguments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

lemma corr_mem {c e u : ℂ} {s : ℝ} (hs : 0 < s)
    (hξ1 : 48.5 * s ≤ ((u - c) * (starRingEnd ℂ) e).re)
    (hξ2 : ((u - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s)
    (hη : |((u - c) * (starRingEnd ℂ) e).im| ≤ s / 2) :
    u ∈ rectC c e (50 * s) (2 * s) ∧ c ∈ rectC c e (50 * s) (2 * s) := by
  refine ⟨⟨abs_le.2 ⟨by linarith, by linarith⟩, hη.trans (by linarith)⟩, ?_⟩
  simp only [rectC, mem_ofPred_eq, sub_self, zero_mul, Complex.zero_re, Complex.zero_im, abs_zero]
  constructor <;> positivity

lemma corr_near {c e u x : ℂ} {s : ℝ} (he : ‖e‖ = 1) (hu : u ∈ rectC c e (50 * s) (2 * s))
    (hx : x ∈ rectC c e (50 * s) (2 * s)) : dist x u ≤ 104 * s := by
  have h1 := norm_le_rectC he hx
  have h2 := norm_le_rectC he hu
  rw [dist_eq_norm]
  calc ‖x - u‖ = ‖(x - c) - (u - c)‖ := by ring_nf
    _ ≤ ‖x - c‖ + ‖u - c‖ := norm_sub_le _ _
    _ ≤ 104 * s := by linarith

/-- the corridor at `u`; see the module docstring -/
theorem corrU_facts {z c e u : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 20000 * s ≤ R) (he : ‖e‖ = 1)
    (hu : dist u z = R) (ha : 7 / 10 * R ≤ ((u - z) * (starRingEnd ℂ) e).re)
    (hξ1 : 48.5 * s ≤ ((u - c) * (starRingEnd ℂ) e).re)
    (hξ2 : ((u - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s)
    (hη : |((u - c) * (starRingEnd ℂ) e).im| ≤ s / 2) :
    dist c z ≤ R - 25 * s ∧
      ∀ x ∈ rectC c e (50 * s) (2 * s), 19 * s ≤ dist x u → dist x z ≤ R - 4 * s := by
  rw [dist_eq_norm] at hu
  refine ⟨?_, ?_⟩
  · rw [dist_eq_norm]
    refine depth_in' (c := c) (w := c) hs hR he hu ha ?_ ?_ ?_
    · simp only [sub_self, zero_mul, Complex.zero_re, sub_zero]; exact le_trans (by linarith) hξ1
    · simp only [sub_self, zero_mul, Complex.zero_re, sub_zero]; linarith
    · simp only [sub_self, zero_mul, Complex.zero_im, sub_zero]; linarith
  · intro x hx hxu
    rw [dist_eq_norm] at hxu ⊢
    obtain ⟨t1, t2, t3⟩ := rect_far_end hs he hx hξ1 hξ2 hη hxu
    exact depth_in hs hR he hu ha t1 t2 t3

/-- the corridor at `v`; see the module docstring -/
theorem corrV_facts {z c e v : ℂ} {R s : ℝ} (hs : 0 < s) (hR : 20000 * s ≤ R) (he : ‖e‖ = 1)
    (hv : dist v z = R) (ha : ((v - z) * (starRingEnd ℂ) e).re ≤ -(7 / 10 * R))
    (hξ1 : 48.5 * s ≤ ((v - c) * (starRingEnd ℂ) e).re)
    (hξ2 : ((v - c) * (starRingEnd ℂ) e).re ≤ 49.5 * s)
    (hη : |((v - c) * (starRingEnd ℂ) e).im| ≤ s / 2) :
    (∀ x ∈ rectC c e (50 * s) (2 * s), 19 * s ≤ dist x v → R + 4 * s ≤ dist x z) ∧
      ∀ q ∈ segment ℝ c (z + (3 / 2 : ℂ) * (v - z)), R + 30 * s ≤ dist q z ∧ 30 * s ≤ dist q v := by
  rw [dist_eq_norm] at hv
  have hR0 : 0 < R := by linarith
  refine ⟨?_, ?_⟩
  · intro x hx hxv
    rw [dist_eq_norm] at hxv ⊢
    obtain ⟨t1, -, t3⟩ := rect_far_end hs he hx hξ1 hξ2 hη hxv
    exact depth_out hs hR he hv ha t1 t3
  intro q hq
  set w := (starRingEnd ℂ) (v - z)
  have key : ∀ p : ℂ, ((p - z) * w).re = (p * w).re - (z * w).re := by
    intro p; rw [sub_mul, Complex.sub_re]
  have hc : R ^ 2 + 30 * R * s ≤ ((c - z) * w).re := by
    refine depth_out_lin (c := c) (w := c) hs hR0.le he hv ha ?_ ?_
    · simp only [sub_self, zero_mul, Complex.zero_re, sub_zero]; exact le_trans (by linarith) hξ1
    · simp only [sub_self, zero_mul, Complex.zero_im, sub_zero]; linarith
  have hvv : ((v - z) * w).re = R ^ 2 := by
    simp only [w, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, hv]
  have hv' : R ^ 2 + 30 * R * s ≤ ((z + (3 / 2 : ℂ) * (v - z) - z) * w).re := by
    have : (z + (3 / 2 : ℂ) * (v - z) - z) * w = (3 / 2 : ℂ) * ((v - z) * w) := by ring
    rw [this, Complex.mul_re, hvv]
    have : ((v - z) * w).im = 0 := by
      simp only [w, Complex.mul_conj, Complex.ofReal_im]
    rw [this]
    norm_num
    nlinarith
  have hq' : R ^ 2 + 30 * R * s ≤ ((q - z) * w).re := by
    rw [key] at hc hv' ⊢
    have := segment_re_ge (M := R ^ 2 + 30 * R * s + (z * w).re) hq (by linarith) (by linarith)
    linarith
  have h1 : ((q - z) * w).re ≤ ‖q - z‖ * R := by
    have := re_mul_conj_le (q - z) (v - z); rwa [hv] at this
  have h2 : ((q - v) * w).re ≤ ‖q - v‖ * R := by
    have := re_mul_conj_le (q - v) (v - z); rwa [hv] at this
  have h3 : ((q - v) * w).re = ((q - z) * w).re - R ^ 2 := by
    rw [← hvv, ← Complex.sub_re, ← sub_mul]; ring_nf
  rw [dist_eq_norm, dist_eq_norm]
  constructor
  · by_contra hc'; rw [not_le] at hc'
    have := mul_lt_mul_of_pos_right hc' hR0
    nlinarith
  · by_contra hc'; rw [not_le] at hc'
    have := mul_lt_mul_of_pos_right hc' hR0
    nlinarith

end LQGMetric.GM
