/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54H2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54H1

/-!
# D117 P-54C (4): the contradiction of DZZ L5.4 in the reflection configuration (P2-DZZ54C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2553–2568
(DEC-117 §2(a), DEC-123 §1). In the configuration `u₅₄ = 19/40 + i/2`, `v₅₄ = dzzRefl u₅₄`,
`L = {1/2} × [s,t]` (the right side of `𝕍_{u₅₄,1/20}`), all walls are `K₅₄ = 𝕍̃_{u₅₄,v₅₄}`.

`cfg_whp`: for `ι > 0`, `κ` with `2ι ≤ κχ`, `κ < 1`, `2κ ≤ ξ`, uniformly over the segments of
length in `[δ^{2κ}, δ^κ]`, `P[log min_{x∈L} D^{K₅₄}_δ(u₅₄,x) < (χ − ι) log δ⁻¹] → 0`.

Proof (DZZ's contradiction, l. 2557–2568): if not, along a sequence of scales and segments
`P[·] > η`; P3.17 (walled at `K₅₄`, `DZZProp317In`) gives `E log Q_u < (χ − 3ι/4) log δ⁻¹`, so
w.h.p. `Q_u ≤ δ^{−χ+ι/2}`; by the reflection (`prob_mirror_eq`) the same for `Q_v`; w.h.p. the
ring crossings around `L` cost `≤ 2 δ^{−χ+ι}` (`ring_pairs_whp`); the gluing (`glue₅₄`) then gives
`D̃(u₅₄,v₅₄) ≤ 4 δ^{ι/4} δ^{−χ+ι/4}`, against the lower bound `D̃ ≥ δ^{−χ+ι/4}` w.h.p. (L5.3 and
P3.17, `dzz_lgd_lower_whpIn`). The four probabilities add up to `< 1`: contradiction.
The exponents follow DEC-117 §2(a)(i) (segments `δ^κ` with `κχ ≥ 2ι`, not DZZ's `δ^{2ι}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- the vertical segment `{1/2} × [s,t]` -/
def vSeg (s t : ℝ) : Set ℂ := {(1 / 2 : ℝ)} ×ℂ Icc s t

lemma mem_vSeg {s t : ℝ} {z : ℂ} : z ∈ vSeg s t ↔ z.re = 1 / 2 ∧ s ≤ z.im ∧ z.im ≤ t := by
  simp [vSeg, Complex.mem_reProdIm]

/-- the admissible segments at scale `δ` -/
def SegC (κ δ s t : ℝ) : Prop := 19 / 40 ≤ s ∧ t ≤ 21 / 40 ∧ δ ^ (2 * κ) ≤ t - s ∧ t - s ≤ δ ^ κ

lemma vSeg_subset_K₅₄ {s t : ℝ} (hs : 19 / 40 ≤ s) (ht : t ≤ 21 / 40) : vSeg s t ⊆ K₅₄ := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := mem_vSeg.1 hz
  refine ⟨?_, ?_⟩ <;> simp only [c₅₄] <;> rw [abs_le] <;> constructor <;> linarith

lemma vSeg_adm {s t : ℝ} (hs : 19 / 40 ≤ s) (ht : t ≤ 21 / 40) (hst : s ≤ t) :
    IsConnected (vSeg s t) ∧ t - s ≤ Metric.diam (vSeg s t) := by
  refine ⟨isConnected_reProdIm isConnected_singleton (isConnected_Icc hst), ?_⟩
  have hb : Bornology.IsBounded (vSeg s t) :=
    (Metric.isBounded_closedBall.subset (sqBox_subset_closedBall c₅₄ (by norm_num))).subset
      (vSeg_subset_K₅₄ hs ht)
  have hp : (⟨1 / 2, s⟩ : ℂ) ∈ vSeg s t := mem_vSeg.2 ⟨rfl, le_rfl, hst⟩
  have hq : (⟨1 / 2, t⟩ : ℂ) ∈ vSeg s t := mem_vSeg.2 ⟨rfl, hst, le_rfl⟩
  refine le_trans ?_ (Metric.dist_le_diam_of_mem hb hp hq)
  rw [Complex.dist_of_re_eq (show (⟨1 / 2, s⟩ : ℂ).re = (⟨1 / 2, t⟩ : ℂ).re from rfl),
    Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]

lemma vSeg_props {ξ : ℝ} (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1 / 80) {s t : ℝ} (hs : 19 / 40 ≤ s) (ht : t ≤ 21 / 40) :
    ∀ z ∈ vSeg s t, z ∈ dzzVXi ξ ∧ z ∈ kXi K₅₄ ξ ∧ ξ ≤ dist u₅₄ z := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := mem_vSeg.1 hz
  have hi : |z.im - 1 / 2| ≤ 1 / 40 := by rw [abs_le]; constructor <;> linarith
  refine ⟨mem_dzzVXi_of_near (a := 1 / 40) (by rw [h1]; norm_num) hi (by linarith) hξ0, ?_, ?_⟩
  · refine mem_kXi_sqBox ?_ ?_
    · simp only [c₅₄]; rw [h1, sub_self, abs_zero]; linarith
    · simp only [c₅₄]; linarith
  · rw [dist_eq_norm]
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, h1]; simp only [u₅₄]; norm_num; linarith

end DZZ
end LQGMetric
