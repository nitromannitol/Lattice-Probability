/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7Perc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7MainBox

/-!
# DZZ Lemma 3.7: finite range of openness (P2-DZZ3E)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) proof of Lemma 3.7, l. 992–999:
`𝓔_{B'_i,open}` and `𝓔_{B'_{i'},open}` are independent when `|B'_i − B'_{i'}| ≥ κ ε s`, since
`ε² s log(1/(ε² s)) ≤ ε s`.

* `bdryCenters B k''`: the centres of the boxes of `𝓑_∂(B, 2^{-k''})`.
* `etaRad_le_band`: `r(u) ≤ (e log(e²)⁻¹ + 2e)/4` for `u < e²`, `e ≤ 1` (from `etaRad_le_of_le`).
* `re_gap`, `im_gap`: centres of boundary boxes of two same-level boxes whose column (row) indices
  differ by more than `r` are `≥ r s' − 2 t s` apart.
* `disjoint_bandSupp_of_far`: the band regions of two such boxes are disjoint once
  `2R + 2 ts ≤ r s'` (input `hdisj` of `measure_biInter_band_bad_eq_prod`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- Centres of the boxes of `𝓑_∂(B, 2^{-k''})`. -/
def bdryCenters (B : DyBox) (k'' : ℕ) : Finset ℂ :=
  (boxCollBdry_finite B k'').toFinset.image DyBox.center

lemma mem_bdryCenters {B : DyBox} {k'' : ℕ} {w : ℂ} :
    w ∈ bdryCenters B k'' ↔ ∃ bt ∈ boxCollBdry B k'', bt.center = w := by
  simp [bdryCenters]

/-- `r(u) ≤ (e log (e²)⁻¹ + 2e)/4` for `0 < u ≤ e² ≤ 1`. -/
lemma etaRad_le_band {u e : ℝ} (hu : 0 < u) (he : 0 < e) (hue : u ≤ e ^ 2) (he1 : e ≤ 1) :
    etaRad u ≤ (e * Real.log (e ^ 2)⁻¹ + 2 * e) / 4 := by
  have h := etaRad_le_of_le hu hue (pow_le_one₀ he.le he1)
  rwa [Real.sqrt_sq he.le] at h

lemma bdry_point {B bt : DyBox} {k'' : ℕ} (h : bt ∈ boxCollBdry B k'') :
    ∃ z, z ∈ bt.closedBox ∧ z ∈ B.closedBox :=
  let ⟨z, hz, hzf⟩ := h.2
  ⟨z, hz, (isClosed_closedBox B).frontier_subset hzf⟩

lemma side_bdry {B bt : DyBox} {k'' : ℕ} (h : bt ∈ boxCollBdry B k'') :
    bt.side = (2 : ℝ)⁻¹ ^ (B.n + k'') := by
  unfold DyBox.side; rw [h.1]

lemma re_gap {B1 B2 bt1 bt2 : DyBox} {k'' r : ℕ} (hn : B1.n = B2.n)
    (h1 : bt1 ∈ boxCollBdry B1 k'') (h2 : bt2 ∈ boxCollBdry B2 k'') (hj : B1.j + r + 1 ≤ B2.j) :
    r * B1.side - 2 * (2 : ℝ)⁻¹ ^ (B1.n + k'') ≤ bt2.center.re - bt1.center.re := by
  obtain ⟨z1, hz1, hzB1⟩ := bdry_point h1
  obtain ⟨z2, hz2, hzB2⟩ := bdry_point h2
  have a1 := abs_sub_center_re_le hz1
  have a2 := abs_sub_center_re_le hz2
  rw [side_bdry h1] at a1; rw [side_bdry h2, ← hn] at a2
  have hs : B2.side = B1.side := by unfold DyBox.side; rw [hn]
  have b1 := hzB1.2.1
  have b2 := hzB2.1
  rw [hs] at b2
  have hjr : (B1.j : ℝ) + r + 1 ≤ B2.j := by exact_mod_cast hj
  have := B1.side_pos'
  rw [abs_le] at a1 a2
  nlinarith

lemma im_gap {B1 B2 bt1 bt2 : DyBox} {k'' r : ℕ} (hn : B1.n = B2.n)
    (h1 : bt1 ∈ boxCollBdry B1 k'') (h2 : bt2 ∈ boxCollBdry B2 k'') (hk : B1.k + r + 1 ≤ B2.k) :
    r * B1.side - 2 * (2 : ℝ)⁻¹ ^ (B1.n + k'') ≤ bt2.center.im - bt1.center.im := by
  obtain ⟨z1, hz1, hzB1⟩ := bdry_point h1
  obtain ⟨z2, hz2, hzB2⟩ := bdry_point h2
  have a1 := abs_sub_center_im_le hz1
  have a2 := abs_sub_center_im_le hz2
  rw [side_bdry h1] at a1; rw [side_bdry h2, ← hn] at a2
  have hs : B2.side = B1.side := by unfold DyBox.side; rw [hn]
  have b1 := hzB1.2.2.2
  have b2 := hzB2.2.2.1
  rw [hs] at b2
  have hkr : (B1.k : ℝ) + r + 1 ≤ B2.k := by exact_mod_cast hk
  have := B1.side_pos'
  rw [abs_le] at a1 a2
  nlinarith

/-- **Finite range** (DZZ l. 992–999): boxes of one level with index distance `> r` have disjoint
band regions once `2R + 2 · 2^{-(n+k'')} ≤ r s'`. -/
theorem disjoint_bandSupp_of_far {B1 B2 : DyBox} (hn : B1.n = B2.n) {k'' r : ℕ} {a b R : ℝ}
    (hfar : B1.j + r + 1 ≤ B2.j ∨ B2.j + r + 1 ≤ B1.j ∨ B1.k + r + 1 ≤ B2.k ∨
      B2.k + r + 1 ≤ B1.k)
    (hR : 2 * R + 2 * (2 : ℝ)⁻¹ ^ (B1.n + k'') ≤ r * B1.side) :
    Disjoint (bandSupp a b R (bdryCenters B1 k'')) (bandSupp a b R (bdryCenters B2 k'')) := by
  have hs : B2.side = B1.side := by unfold DyBox.side; rw [hn]
  rw [Set.disjoint_left]
  rintro ⟨u, x⟩ ⟨-, hx1⟩ ⟨-, hx2⟩
  simp only [mem_iUnion, Metric.mem_ball, exists_prop] at hx1 hx2
  obtain ⟨w1, hw1, d1⟩ := hx1
  obtain ⟨w2, hw2, d2⟩ := hx2
  obtain ⟨bt1, hbt1, rfl⟩ := mem_bdryCenters.1 hw1
  obtain ⟨bt2, hbt2, rfl⟩ := mem_bdryCenters.1 hw2
  have hd : dist bt1.center bt2.center < 2 * R := by
    have := dist_triangle_left bt1.center bt2.center x; linarith
  rw [Complex.dist_eq] at hd
  have hre := Complex.abs_re_le_norm (bt1.center - bt2.center)
  have him := Complex.abs_im_le_norm (bt1.center - bt2.center)
  simp only [Complex.sub_re, Complex.sub_im] at hre him
  rcases hfar with h | h | h | h
  · have := re_gap hn hbt1 hbt2 h
    rw [abs_le] at hre; linarith
  · have := re_gap hn.symm hbt2 hbt1 h
    rw [hs, ← hn] at this; rw [abs_le] at hre; linarith
  · have := im_gap hn hbt1 hbt2 h
    rw [abs_le] at him; linarith
  · have := im_gap hn.symm hbt2 hbt1 h
    rw [hs, ← hn] at this; rw [abs_le] at him; linarith

end DZZ
end LQGMetric
