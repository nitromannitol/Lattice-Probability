/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiA3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA2

/-!
# DZZ Proposition 5.1, upper bound at `μIn` for interior pairs: the chain (D129, P-129A)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Prop 5.1 (l. 2254–2258), proof of
the upper bound l. 2308–2331: points `y_i = u + (i/l)(v − u)`, `0 ≤ i ≤ l`, each tilde box
`𝕍̃_{y_i,y_{i+1}}` coupled to the reference box (`hasRate_tilde_link`, S5ChiA2), and
`D_δ(u,v) ≤ ∑ D̃_δ(y_i,y_{i+1})`.

**DEVIATIONS DV-D129-2** (D129 §6): DZZ take `|y_{i+1} − y_i| ≤ 2ξ/√5` (l. 2311), which puts
`𝕍̃_{y_i,y_{i+1}}` in `𝕍` but not necessarily in `𝕍^ξ`; we take `l` so large that every point of
`𝕍̃_{y_i,y_{i+1}}` is within `m/2` of the segment `[u,v]`, `m` the coordinate margin of `u, v` in
`𝕍°` (so `𝕍̃ ⊆ 𝕍^{m/2}`), and `|y_{i+1} − y_i| ≤ |v̄ − ū| = 1/20`.
**DV-D129-1**: the bound is kept with its rate (`HasRate`, S5ChiA1).

* `lgdDZZ_chain_le_chi`: the iterated triangle inequality (`lgdDZZ_triangle`, S5L54G1);
* `exists_margin_openSquare`, `mem_dzzVXi_of_near_point`, `norm_sub_mid_le_of_mem_tildeBox`
  (own elementary geometry; the last copies the estimate inside `tildeBox_subset_dzzVXi`,
  S5L53B11);
* **`hasRate_dzzMuIn_upper_interior`** (D129 §4, P-129A, exact statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the iterated triangle inequality along a chain -/
lemma lgdDZZ_chain_le_chi (μ : Measure ℂ) (δ : ℝ) (y : ℕ → ℂ) (n : ℕ) :
    ((lgdDZZ μ δ (y 0) (y (n + 1)) : ℕ∞) : ℝ≥0∞) ≤
      ∑ i ∈ Finset.range (n + 1), ((lgdDZZ μ δ (y i) (y (i + 1)) : ℕ∞) : ℝ≥0∞) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    refine (ENat.toENNReal_le.2 (lgdDZZ_triangle μ δ (y 0) (y (n + 1)) (y (n + 1 + 1)))).trans ?_
    rw [ENat.toENNReal_add]
    exact add_le_add ih le_rfl

/-- points of `𝕍̃_{x,y}` are within `2|y − x|` of the midpoint (the estimate in the proof of
`tildeBox_subset_dzzVXi`, S5L53B11) -/
lemma norm_sub_mid_le_of_mem_tildeBox {x y z : ℂ} (hxy : x ≠ y) (hz : z ∈ tildeBox x y) :
    ‖z - (x + y) / 2‖ ≤ 2 * ‖y - x‖ := by
  have hd : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy.symm)
  have hw := (Complex.norm_le_abs_re_add_abs_im ((z - (x + y) / 2) * starRingEnd ℂ (y - x))).trans
    (add_le_add hz.1 hz.2)
  rw [norm_mul, Complex.norm_conj] at hw
  by_contra h
  push Not at h
  nlinarith

/-- the segment `[u,v]` of two points of `𝕍°` has a positive coordinate margin -/
lemma exists_margin_openSquare {u v : ℂ} (hu : u ∈ openSquare) (hv : v ∈ openSquare) :
    ∃ m : ℝ, 0 < m ∧ m < 1 ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      m ≤ (u + (t : ℂ) * (v - u)).re ∧ (u + (t : ℂ) * (v - u)).re ≤ 1 - m ∧
      m ≤ (u + (t : ℂ) * (v - u)).im ∧ (u + (t : ℂ) * (v - u)).im ≤ 1 - m := by
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  set m := min (min (min u.re (1 - u.re)) (min u.im (1 - u.im)))
    (min (min v.re (1 - v.re)) (min v.im (1 - v.im))) with hm
  have a1 : m ≤ u.re := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have a2 : m ≤ 1 - u.re := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have a3 : m ≤ u.im := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have a4 : m ≤ 1 - u.im := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have b1 : m ≤ v.re := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have b2 : m ≤ 1 - v.re := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have b3 : m ≤ v.im := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have b4 : m ≤ 1 - v.im :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hm0 : 0 < m := lt_min (lt_min (lt_min hu1 (by linarith)) (lt_min hu3 (by linarith)))
    (lt_min (lt_min hv1 (by linarith)) (lt_min hv3 (by linarith)))
  refine ⟨m, hm0, by linarith, fun t ht0 ht1 => ?_⟩
  simp only [Complex.add_re, Complex.add_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.sub_re, Complex.sub_im]
  have h1 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a1)
  have h2 := mul_nonneg ht0 (sub_nonneg.2 b1)
  have h3 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a2)
  have h4 := mul_nonneg ht0 (sub_nonneg.2 b2)
  have h5 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a3)
  have h6 := mul_nonneg ht0 (sub_nonneg.2 b3)
  have h7 := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 a4)
  have h8 := mul_nonneg ht0 (sub_nonneg.2 b4)
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- points within `m/2` of a point with coordinate margin `m` lie in `𝕍^{m/2}` -/
lemma mem_dzzVXi_of_near_point {y z : ℂ} {m : ℝ} (hm : 0 < m) (h1 : m ≤ y.re)
    (h2 : y.re ≤ 1 - m) (h3 : m ≤ y.im) (h4 : y.im ≤ 1 - m) (hz : ‖z - y‖ ≤ m / 2) :
    z ∈ dzzVXi (m / 2) := by
  have hre := (Complex.abs_re_le_norm (z - y)).trans hz
  have him := (Complex.abs_im_le_norm (z - y)).trans hz
  rw [Complex.sub_re, abs_le] at hre
  rw [Complex.sub_im, abs_le] at him
  refine mem_dzzVXi_of_near (a := 1 / 2 - m / 2) (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith) (by linarith)

/-- the chain `y_i = u + (i/l)(v − u)` (DZZ l. 2309–2311) -/
def chiChain (u v : ℂ) (l : ℕ) (i : ℕ) : ℂ := u + ((i / l : ℝ) : ℂ) * (v - u)

lemma chiChain_succ_sub (u v : ℂ) (l i : ℕ) :
    chiChain u v l (i + 1) - chiChain u v l i = ((1 / l : ℝ) : ℂ) * (v - u) := by
  simp only [chiChain]; push_cast; ring

lemma chiChain_mid (u v : ℂ) (l i : ℕ) :
    (chiChain u v l i + chiChain u v l (i + 1)) / 2 =
      u + ((((i : ℝ) + 1 / 2) / l : ℝ) : ℂ) * (v - u) := by
  simp only [chiChain]; push_cast; ring

/-- **DZZ Proposition 5.1, upper bound, at `μIn` for interior pairs, with rate** (l. 2308–2331;
D129 §4 P-129A): for `u ≠ v ∈ 𝕍°`, `P[D^𝕍_δ(u,v) > δ^{−χ−ι}] ≤ C(δ^c + e^{−(log δ⁻¹)^{0.7}})`,
given DZZ L5.3 at `μIn` and the walled P3.17 at `dgWalls`. -/
theorem hasRate_dzzMuIn_upper_interior (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {χ : ℝ} (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    {u v : ℂ} (hu : u ∈ openSquare) (hv : v ∈ openSquare) (huv : u ≠ v) {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ((lgdDZZ (dzzMuIn γ W ω) δ u v : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι)))}) := by
  obtain ⟨m, hm0, hm1, hseg⟩ := exists_margin_openSquare hu hv
  set d := ‖v - u‖ with hd
  have hd0 : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 huv.symm)
  set n : ℕ := ⌈(20 + 4 / m) * d⌉₊ with hn
  set l : ℕ := n + 1 with hl
  have hl0 : (0 : ℝ) < l := by positivity
  have hlb : (20 + 4 / m) * d ≤ l := by
    rw [hl, Nat.cast_add, Nat.cast_one]; linarith [Nat.le_ceil ((20 + 4 / m) * d)]
  have h4m : 0 ≤ 4 / m * d := by positivity
  have hstep : ∀ i, ‖chiChain u v l (i + 1) - chiChain u v l i‖ = d / l := by
    intro i
    rw [chiChain_succ_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  have hstep20 : d / l ≤ 1 / 20 := by
    rw [div_le_iff₀ hl0]; nlinarith
  have hstepm : 2 * (d / l) ≤ m / 2 := by
    have : 4 / m * d * m = 4 * d := by field_simp
    rw [mul_div_assoc', div_le_iff₀ hl0]; nlinarith
  set ξc := min (m / 2) (1 / 4) with hξc
  have hξc0 : 0 < ξc := lt_min (by linarith) (by norm_num)
  have hne : ∀ i, chiChain u v l i ≠ chiChain u v l (i + 1) := by
    intro i h
    have := hstep i
    rw [← h, sub_self, norm_zero] at this
    exact (div_pos hd0 hl0).ne' this.symm
  have hbox : ∀ i < l, tildeBox (chiChain u v l i) (chiChain u v l (i + 1)) ⊆ dzzVXi ξc := by
    intro i hi z hz
    have hz' := norm_sub_mid_le_of_mem_tildeBox (hne i) hz
    rw [hstep, chiChain_mid] at hz'
    have ht0 : (0 : ℝ) ≤ ((i : ℝ) + 1 / 2) / l := by positivity
    have ht1 : ((i : ℝ) + 1 / 2) / l ≤ 1 := by
      rw [div_le_one hl0]
      have : ((i + 1 : ℕ) : ℝ) ≤ l := by exact_mod_cast hi
      push_cast at this; linarith
    obtain ⟨g1, g2, g3, g4⟩ := hseg _ ht0 ht1
    exact dzzVXi_anti_chi (min_le_left _ _)
      (mem_dzzVXi_of_near_point hm0 g1 g2 g3 g4 (hz'.trans hstepm))
  have href := fun ι' (hι' : 0 < ι') => hasRate_ref_upper hW hγ hγ2 hL hwalls hι'
  have hlink : ∀ i < l, HasRate P (fun δ => {ω |
      ((lgdDZZ (dzzWall (tildeBox (chiChain u v l i) (chiChain u v l (i + 1))) (dzzMuIn γ W ω)) δ
        (chiChain u v l i) (chiChain u v l (i + 1)) : ℕ∞) : ℝ≥0∞) ≤
      ENNReal.ofReal (δ ^ (-(χ + ι / 2)))}) := fun i hi =>
    hasRate_tilde_link hW hγ hγ2 chiRefU_mem chiRefV_mem chiRef_ne (hne i)
      (by rw [hstep, chiRef_norm]; exact hstep20) hξc0 (min_le_right _ _) (hbox i hi) href
      (by positivity)
  refine (hasRate_biInter_range l hlink).mono ?_
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (l : ℝ) ≤ δ ^ (-(ι / 2)) :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(ι / 2) < 0)).eventually_ge_atTop _
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδl hδ ω hω
  have hδ0 : 0 < δ := hδ
  simp only [mem_iInter, Finset.mem_range, mem_ofPred_eq] at hω ⊢
  have hchain := lgdDZZ_chain_le_chi (dzzMuIn γ W ω) δ (chiChain u v l) n
  have h0 : chiChain u v l 0 = u := by simp [chiChain]
  have hlast : chiChain u v l (n + 1) = v := by
    simp only [chiChain]
    rw [← hl, div_self hl0.ne']; simp
  rw [h0, hlast] at hchain
  have hp : 0 ≤ δ ^ (-(χ + ι / 2)) := (Real.rpow_pos_of_pos hδ0 _).le
  calc ((lgdDZZ (dzzMuIn γ W ω) δ u v : ℕ∞) : ℝ≥0∞) ≤ _ := hchain
    _ ≤ ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (δ ^ (-(χ + ι / 2))) :=
        Finset.sum_le_sum fun i hi =>
          (ENat.toENNReal_le.2 (lgdDZZ_mono_measure (le_dzzWall _ _) _ _ _)).trans
            (hω i (Finset.mem_range.1 hi))
    _ = ENNReal.ofReal (l * δ ^ (-(χ + ι / 2))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (δ ^ (-(χ + ι))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : δ ^ (-(χ + ι)) = δ ^ (-(ι / 2)) * δ ^ (-(χ + ι / 2)) := by
          rw [← Real.rpow_add hδ0]; ring_nf
        rw [this]
        exact mul_le_mul_of_nonneg_right hδl hp

end DZZ
end LQGMetric
