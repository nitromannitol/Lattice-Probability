/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.CrosscutRadial at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoEilenberg

/-!
# Crosscuts by circle arcs, part I: radial projection and collars

Toward GM (arXiv:1905.00383) tex l. 2478–2479: for `K` compact connected with `ℂ ∖ K`
connected and a component `Y` of `∂B ∖ K` (`B` a closed Euclidean disc), `Y` divides `ℂ ∖ K` into
one bounded and one unbounded component (Pommerenke, *Boundary Behaviour of Conformal Maps*,
Prop. 2.12, for crosscuts of simply connected domains). This file has the elementary local
geometry near `Y`:

* `rproj c r`: radial projection to the circle `sphere c r`, with `dist_rproj_le`
  (`‖π z - y‖ ≤ 2‖z - y‖` for `y` on the circle);
* `cc_sphere_open`: a component of `sphere c r ∖ K` is relatively open in the circle;
* `col K c r Y σ` (`σ = -1` inner, `σ = 1` outer): the radial collar
  `{c + (1 + σ t δ(y)) (y - c) : y ∈ Y, 0 < t < 1}` with `δ(y) = min (1/2) (infDist y K / (4r))`;
  it is preconnected (`col_isPreconnected`), avoids `K` and the circle (`col_not_mem`), has `Y` in
  its closure (`subset_closure_col`), and every point near `Y` off the circle lies in one of the two
  collars (`mem_col_of_near`).

Own elementary arguments (cost rule; standard plane geometry, no source needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter Complex

namespace LQGMetric.Topo.Crosscut

/-- Radial projection of `z ≠ c` to the circle `sphere c r`. -/
def rproj (c : ℂ) (r : ℝ) (z : ℂ) : ℂ := c + ((r / ‖z - c‖ : ℝ) : ℂ) * (z - c)

theorem norm_rproj_sub {c z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : z ≠ c) :
    ‖rproj c r z - c‖ = r := by
  have hn : ‖z - c‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hz)
  simp only [rproj, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), div_mul_cancel₀ _ hn]

theorem rproj_mem_sphere {c z : ℂ} {r : ℝ} (hr : 0 ≤ r) (hz : z ≠ c) :
    rproj c r z ∈ sphere c r := by
  rw [mem_sphere, dist_eq_norm]; exact norm_rproj_sub hr hz

theorem rproj_of_mem {c z : ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ sphere c r) : rproj c r z = z := by
  rw [mem_sphere, dist_eq_norm] at hz
  simp [rproj, hz, div_self hr.ne']

theorem norm_rproj_sub_self {c z : ℂ} {r : ℝ} (hz : z ≠ c) :
    ‖rproj c r z - z‖ = |r - ‖z - c‖| := by
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have : rproj c r z - z = ((r / ‖z - c‖ - 1 : ℝ) : ℂ) * (z - c) := by
    simp only [rproj]; push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← abs_of_pos hn, ← abs_mul,
    abs_of_pos hn, sub_mul, div_mul_cancel₀ _ hn.ne', one_mul]

theorem abs_norm_sub_le {c y z : ℂ} {r : ℝ} (hy : y ∈ sphere c r) :
    |r - ‖z - c‖| ≤ ‖z - y‖ := by
  rw [mem_sphere, dist_eq_norm] at hy
  rw [← hy]
  calc |‖y - c‖ - ‖z - c‖| ≤ ‖(y - c) - (z - c)‖ := abs_norm_sub_norm_le _ _
    _ = ‖z - y‖ := by rw [sub_sub_sub_cancel_right, norm_sub_rev]

theorem dist_rproj_le {c y z : ℂ} {r : ℝ} (hy : y ∈ sphere c r) (hz : z ≠ c) :
    ‖rproj c r z - y‖ ≤ 2 * ‖z - y‖ := by
  calc ‖rproj c r z - y‖ ≤ ‖rproj c r z - z‖ + ‖z - y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖z - y‖ + ‖z - y‖ := by
        gcongr; rw [norm_rproj_sub_self hz]; exact abs_norm_sub_le hy
    _ = 2 * ‖z - y‖ := by ring

theorem continuousOn_rproj (c : ℂ) (r : ℝ) : ContinuousOn (rproj c r) {z | z ≠ c} := by
  refine continuousOn_const.add (ContinuousOn.mul ?_ (by fun_prop))
  refine Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.div (by fun_prop) ?_)
  intro z hz; exact norm_ne_zero_iff.2 (sub_ne_zero.2 hz)

/-- A component of `sphere c r ∖ K` (`K` closed, nonempty) is relatively open in the circle. -/
theorem cc_sphere_open {K : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {c y : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : y ∈ sphere c r) (hyK : y ∉ K) :
    ∃ ρ > 0, ball y ρ ∩ sphere c r ⊆ connectedComponentIn (sphere c r \ K) y := by
  have hd := (hK.notMem_iff_infDist_pos hKne).1 hyK
  have hyc : ‖y - c‖ = r := by rwa [mem_sphere, dist_eq_norm] at hy
  set ρ := min (infDist y K / 2) (r / 2)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  refine ⟨ρ, hρ, ?_⟩
  have hc : ∀ z ∈ ball y ρ, z ≠ c := by
    intro z hz hzc
    rw [mem_ball, dist_eq_norm, hzc, norm_sub_rev, hyc] at hz
    linarith [min_le_right (infDist y K / 2) (r / 2)]
  have himg : IsPreconnected (rproj c r '' ball y ρ) :=
    (convex_ball y ρ).isPreconnected.image _ ((continuousOn_rproj c r).mono hc)
  have hsub : rproj c r '' ball y ρ ⊆ sphere c r \ K := by
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨rproj_mem_sphere hr.le (hc z hz), fun hK' => ?_⟩
    have h1 := infDist_le_dist_of_mem (x := y) hK'
    have h2 := dist_rproj_le hy (hc z hz)
    rw [mem_ball, dist_eq_norm] at hz
    rw [dist_comm, dist_eq_norm] at h1
    linarith [min_le_left (infDist y K / 2) (r / 2)]
  have hy' : y ∈ rproj c r '' ball y ρ := ⟨y, mem_ball_self hρ, rproj_of_mem hr hy⟩
  intro w ⟨hw, hwS⟩
  exact himg.subset_connectedComponentIn hy' hsub ⟨w, hw, rproj_of_mem hr hwS⟩

/-- The collar width `δ(y) = min (1/2) (infDist y K / (4r))`. -/
def cw (K : Set ℂ) (r : ℝ) (y : ℂ) : ℝ := min (1 / 2) (infDist y K / (4 * r))

/-- The collar map `(y, t) ↦ c + (1 + σ t δ(y)) (y - c)`. -/
def colMap (K : Set ℂ) (c : ℂ) (r σ : ℝ) (p : ℂ × ℝ) : ℂ :=
  c + ((1 + σ * p.2 * cw K r p.1 : ℝ) : ℂ) * (p.1 - c)

/-- The radial collar of `Y` (inner for `σ = -1`, outer for `σ = 1`). -/
def col (K : Set ℂ) (c : ℂ) (r : ℝ) (Y : Set ℂ) (σ : ℝ) : Set ℂ :=
  colMap K c r σ '' (Y ×ˢ Ioo 0 1)

theorem continuous_colMap (K : Set ℂ) (c : ℂ) (r σ : ℝ) : Continuous (colMap K c r σ) := by
  unfold colMap cw
  have := Metric.continuous_infDist_pt (α := ℂ) K
  fun_prop

theorem col_isPreconnected {K Y : Set ℂ} {c : ℂ} {r σ : ℝ} (hY : IsPreconnected Y) :
    IsPreconnected (col K c r Y σ) :=
  (hY.prod isPreconnected_Ioo).image _ (continuous_colMap K c r σ).continuousOn

theorem cw_pos {K : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {r : ℝ} (hr : 0 < r) {y : ℂ}
    (hy : y ∉ K) : 0 < cw K r y :=
  lt_min (by norm_num) (div_pos ((hK.notMem_iff_infDist_pos hKne).1 hy) (by positivity))

theorem colMap_sub_self (K : Set ℂ) (c : ℂ) (r σ : ℝ) (p : ℂ × ℝ) :
    colMap K c r σ p - p.1 = ((σ * p.2 * cw K r p.1 : ℝ) : ℂ) * (p.1 - c) := by
  simp only [colMap]; push_cast; ring

theorem colMap_sub_center (K : Set ℂ) (c : ℂ) (r σ : ℝ) (p : ℂ × ℝ) :
    colMap K c r σ p - c = ((1 + σ * p.2 * cw K r p.1 : ℝ) : ℂ) * (p.1 - c) := by
  simp only [colMap]; ring

/-- Collar points avoid `K` and satisfy `‖z - c‖ = (1 + σ s) r` with `0 < s ≤ 1/2`. -/
theorem col_prop {K Y : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {c : ℂ} {r σ : ℝ}
    (hr : 0 < r) (hσ : |σ| = 1) (hY : Y ⊆ sphere c r \ K) {z : ℂ} (hz : z ∈ col K c r Y σ) :
    z ∉ K ∧ ∃ s : ℝ, 0 < s ∧ s ≤ 1 / 2 ∧ ‖z - c‖ = (1 + σ * s) * r := by
  obtain ⟨⟨y, t⟩, ⟨hyY, ht0, ht1⟩, rfl⟩ := hz
  have hyc : ‖y - c‖ = r := by
    have := (hY hyY).1; rwa [mem_sphere, dist_eq_norm] at this
  have hδ := cw_pos hK hKne hr (hY hyY).2
  have hδ2 : cw K r y ≤ 1 / 2 := min_le_left _ _
  have hδ4 : cw K r y ≤ infDist y K / (4 * r) := min_le_right _ _
  have htδ : 0 < t * cw K r y := mul_pos ht0 hδ
  have htδ' : t * cw K r y ≤ 1 / 2 := by nlinarith
  refine ⟨fun hzK => ?_, t * cw K r y, htδ, htδ', ?_⟩
  · have h1 := infDist_le_dist_of_mem (x := y) hzK
    rw [dist_eq_norm, norm_sub_rev, colMap_sub_self, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, hyc] at h1
    have : |σ * t * cw K r y| = t * cw K r y := by
      rw [mul_assoc, abs_mul, hσ, one_mul, abs_of_pos htδ]
    rw [this] at h1
    have h4 : t * cw K r y * r < infDist y K := by
      have : t * cw K r y < infDist y K / (4 * r) := by nlinarith
      rw [lt_div_iff₀ (by positivity)] at this; nlinarith
    exact absurd h1 (not_le.2 (by simpa using h4))
  · rw [colMap_sub_center, norm_mul, Complex.norm_real, Real.norm_eq_abs, hyc]
    have : 0 ≤ 1 + σ * (t * cw K r y) := by
      have : |σ * (t * cw K r y)| ≤ 1 / 2 := by rw [abs_mul, hσ, one_mul, abs_of_pos htδ]; exact htδ'
      linarith [neg_abs_le (σ * (t * cw K r y))]
    simp only [mul_assoc] at this ⊢
    rw [abs_of_nonneg this]

/-- Every point of `Y` is a limit of collar points. -/
theorem subset_closure_col {K Y : Set ℂ} {c : ℂ} {r σ : ℝ} {y : ℂ} (hy : y ∈ Y) :
    y ∈ closure (col K c r Y σ) := by
  have hf : Continuous fun t : ℝ => colMap K c r σ (y, t) :=
    (continuous_colMap K c r σ).comp (continuous_const.prodMk continuous_id)
  have h0 : colMap K c r σ (y, 0) = y := by simp [colMap]
  have ht : Tendsto (fun t : ℝ => colMap K c r σ (y, t)) (𝓝[>] 0) (𝓝 y) := by
    have := hf.tendsto 0; rw [h0] at this; exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht'
  exact ⟨(y, t), ⟨hy, ht'⟩, rfl⟩

/-- Points close to `Y` and off the circle lie in the inner or the outer collar. -/
theorem mem_col_of_near {K Y : Set ℂ} (hK : IsClosed K) (hKne : K.Nonempty) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hY : Y ⊆ sphere c r \ K) {y : ℂ} (hy : y ∈ Y) {ρo : ℝ} (hρo : 0 < ρo)
    (hball : ball y ρo ∩ sphere c r ⊆ Y) :
    ∃ ρ > 0, ∀ z ∈ ball y ρ, z ∉ sphere c r → z ∈ col K c r Y (-1) ∪ col K c r Y 1 := by
  have hyS := (hY hy).1
  have hyc : ‖y - c‖ = r := by rwa [mem_sphere, dist_eq_norm] at hyS
  have hd := (hK.notMem_iff_infDist_pos hKne).1 (hY hy).2
  set d := infDist y K
  set ρ := min (min (d / 8) (r / 4)) (ρo / 2)
  have hρ1 : ρ ≤ d / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hρ2 : ρ ≤ r / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hρ3 : ρ ≤ ρo / 2 := min_le_right _ _
  have hρ : 0 < ρ := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  refine ⟨ρ, hρ, fun z hz hzS => ?_⟩
  rw [mem_ball, dist_eq_norm] at hz
  have hzc : z ≠ c := by
    intro hzc; rw [hzc, norm_sub_rev, hyc] at hz; linarith
  have hn : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  have hnr : ‖z - c‖ ≠ r := fun h => hzS (by rw [mem_sphere, dist_eq_norm, h])
  set n := ‖z - c‖
  set y' := rproj c r z
  have hy'S : y' ∈ sphere c r := rproj_mem_sphere hr.le hzc
  have hy'y : ‖y' - y‖ < 2 * ρ := (dist_rproj_le hyS hzc).trans_lt (by linarith)
  have hy'Y : y' ∈ Y := hball ⟨by rw [mem_ball, dist_eq_norm]; linarith, hy'S⟩
  have hrn : |r - n| < ρ := (abs_norm_sub_le hyS).trans_lt hz
  have hrn0 : 0 < |r - n| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hnr))
  have hd' : d ≤ infDist y' K + ‖y' - y‖ := by
    have := infDist_le_infDist_add_dist (x := y) (y := y') (s := K)
    rwa [dist_comm, dist_eq_norm] at this
  set δ := cw K r y'
  have hδ : |r - n| < r * δ := by
    simp only [δ, cw]
    rw [mul_min_of_nonneg _ _ hr.le]
    have e : r * (infDist y' K / (4 * r)) = infDist y' K / 4 := by field_simp
    rw [e]
    exact lt_min (by linarith) (by linarith)
  have hδ0 : 0 < δ := by
    by_contra h; push Not at h; nlinarith
  set t := |r - n| / (r * δ)
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos hrn0 (by positivity), (div_lt_one (by positivity)).2 hδ⟩
  have key : ∀ σ : ℝ, σ * |r - n| = n - r → colMap K c r σ (y', t) = z := by
    intro σ hσ
    have h1 : (1 + σ * t * δ) * (r / n) = 1 := by
      have : σ * t * δ = (n - r) / r := by
        simp only [t]; rw [← hσ]; field_simp
      rw [this]; field_simp; ring
    show c + ((1 + σ * t * δ : ℝ) : ℂ) * (y' - c) = z
    have hy'c : y' - c = ((r / n : ℝ) : ℂ) * (z - c) := by simp only [y', rproj, n]; ring
    rw [hy'c, ← mul_assoc, ← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul,
      add_sub_cancel]
  rcases lt_or_gt_of_ne hnr with h | h
  · refine Or.inl ⟨(y', t), ⟨hy'Y, ht⟩, key (-1) ?_⟩
    rw [abs_of_pos (by linarith)]; ring
  · refine Or.inr ⟨(y', t), ⟨hy'Y, ht⟩, key 1 ?_⟩
    rw [abs_of_neg (by linarith)]; ring

end LQGMetric.Topo.Crosscut
