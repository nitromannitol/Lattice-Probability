/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eFin2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412eFin
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupStab
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity

/-!
# `hfin` on `ℰ_𝕣` (DEC-86 (3)): avoid-geodesics have finite length

* `p412e_finpath` (DEC-86 (3), deterministic): for a length metric `D`, `x ∈ ∂B_r(z)`,
  `𝕫 ∉ cl B_r(z)` and an internal Hölder bound `D(u, w; B_{2|u−w|}(u)) ≤ C|u − w|^χ` near `x`,
  there is a finite-length path from `𝕫` to `x` in `ℂ ∖ B_r(z)`. Construction: `x_n = x + c_nν`,
  `c_n = r₀(2/3)^n`, `ν = (x − z)/r`; `B_{2|x_n−x_{n+1}|}(x_n) ⊆ ℂ ∖ cl B_r(z)`; the pieces have
  lengths `≤ |C|(c_n/3)^χ + 2^{-n}` (summable); `𝕫 → x₀` in the connected open set
  `ℂ ∖ cl B_r(z)` (`p412e_internal_ne_top`); `p412e_concat`.
* `p412e_hfin`: hence `IsAvoidGeod D 𝕫 z r x Q T → D.len Q 0 T ≠ ⊤` (minimality of `Q`).
* `p412e_hH_of_regC3`, `p412e_hfin_regC3`: GM's condition 3 of `ℰ_𝕣` (l. 1958–1962, `regC3`)
  gives the Hölder bound at every `x ∈ B_{4ℓ𝕣}(𝕣V)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open LQGMetric.MetricGeometry LQGMetric.Blueprint
open scoped ENNReal

namespace LQGMetric.GM

/-- **DEC-86 (3)**, deterministic part: a finite-length path from `𝕫` to `x ∈ ∂B_r(z)` in
`ℂ ∖ B_r(z)` -/
theorem p412e_finpath {D : ContMetric} (hL : D.IsLength) {𝕫 z x : ℂ} {r : ℝ} (hr : 0 < r)
    (hx : x ∈ sphere z r) (h𝕫 : 𝕫 ∉ closedBall z r) {r₀ C χ : ℝ} (hr₀ : 0 < r₀) (hχ : 0 < χ)
    (hH : ∀ u ∈ closedBall x r₀, ∀ w ∈ closedBall x r₀, u ≠ w →
      D.internal (ball u (2 * ‖u - w‖)) u w ≤ ENNReal.ofReal (C * ‖u - w‖ ^ χ)) :
    ∃ Q' : ℝ → ℂ, ContinuousOn Q' (Icc 0 1) ∧ Q' 0 = 𝕫 ∧ Q' 1 = x ∧
      MapsTo Q' (Icc 0 1) (ball z r)ᶜ ∧ D.len Q' 0 1 ≠ ∞ := by
  have hxz' : ‖x - z‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.1 hx
  set ν : ℂ := (x - z) / r with hνdef
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hν : ‖ν‖ = 1 := by
    rw [hνdef, norm_div, hxz', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
  have hxz : x - z = (r : ℂ) * ν := by rw [hνdef]; field_simp
  set c : ℕ → ℝ := fun n => r₀ * (2 / 3) ^ n with hcdef
  set xs : ℕ → ℂ := fun n => x + (c n : ℂ) * ν with hxsdef
  have hc0 : ∀ n, 0 < c n := fun n => by positivity
  have hcle : ∀ n, c n ≤ r₀ := fun n => by
    have : (2 / 3 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    simp only [hcdef]; nlinarith
  have hnd : ∀ n, ‖xs n - xs (n + 1)‖ = c n / 3 := fun n => by
    have : xs n - xs (n + 1) = ((c n / 3 : ℝ) : ℂ) * ν := by
      simp only [hxsdef, hcdef]; push_cast; ring
    rw [this, norm_mul, hν, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hc0 n])]
  have hxsx : ∀ n, ‖xs n - x‖ = c n := fun n => by
    simp only [hxsdef, add_sub_cancel_left, norm_mul, hν, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (hc0 n)]
  have hxsz : ∀ n, ‖xs n - z‖ = r + c n := fun n => by
    have : xs n - z = ((r + c n : ℝ) : ℂ) * ν := by
      simp only [hxsdef]; rw [show x + (c n : ℂ) * ν - z = (x - z) + c n * ν by ring, hxz]
      push_cast; ring
    rw [this, norm_mul, hν, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hc0 n])]
  have hballO : ∀ n, ball (xs n) (2 * ‖xs n - xs (n + 1)‖) ⊆ (closedBall z r)ᶜ := by
    intro n w hw
    rw [mem_ball, dist_eq_norm, hnd] at hw
    simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
    have := norm_sub_norm_le (xs n - z) (xs n - w)
    rw [hxsz, show xs n - z - (xs n - w) = w - z by ring, norm_sub_rev] at this
    linarith [hc0 n]
  have hmemB : ∀ n, xs n ∈ closedBall x r₀ := fun n => by
    rw [mem_closedBall, dist_eq_norm, hxsx]; exact hcle n
  -- the pieces `x_n → x_{n+1}`
  set b : ℕ → ℝ := fun n => |C| * (c n / 3) ^ χ + (1 / 2) ^ n with hbdef
  have hpiece : ∀ n, ∃ g : ℝ → ℂ, ContinuousOn g (Icc 0 1) ∧ g 0 = xs n ∧ g 1 = xs (n + 1) ∧
      MapsTo g (Icc 0 1) (closedBall z r)ᶜ ∧ curveLength (D.pt ∘ g) 0 1 < ENNReal.ofReal (b n) := by
    intro n
    have hne : xs n ≠ xs (n + 1) := by
      intro h; have := hnd n; rw [h, sub_self, norm_zero] at this; linarith [hc0 n]
    have h1 := hH _ (hmemB n) _ (hmemB (n + 1)) hne
    rw [hnd] at h1
    have h2 : D.internal (ball (xs n) (2 * ‖xs n - xs (n + 1)‖)) (xs n) (xs (n + 1)) <
        ENNReal.ofReal (b n) := by
      rw [hnd]
      have hA : C * (c n / 3) ^ χ ≤ |C| * (c n / 3) ^ χ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      have hB : |C| * (c n / 3) ^ χ < b n := by
        have : (0 : ℝ) < (1 / 2) ^ n := by positivity
        simp only [hbdef]; linarith
      exact h1.trans_lt ((ENNReal.ofReal_le_ofReal hA).trans_lt
        ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hB))
    obtain ⟨g, hg1, hg2, hg3, hg4, hg5⟩ := p412e_path_of_lt h2
    exact ⟨g, hg1, hg2, hg3, hg4.mono_right (hballO n), hg5⟩
  choose g hgc hg0 hg1 hgO hglen using hpiece
  have hO : IsOpen (closedBall z r)ᶜ := isClosed_closedBall.isOpen_compl
  have hx0O : xs 0 ∈ (closedBall z r)ᶜ := by
    simp only [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le, hxsz]; linarith [hc0 0]
  obtain ⟨g₀, hg₀c, hg₀0, hg₀1, hg₀O, hg₀len⟩ := p412e_path_of_lt (b := ∞)
    (lt_top_iff_ne_top.2 (p412e_internal_ne_top hL hO
      (p412e_compl_closedBall_isPreconnected z hr) h𝕫 hx0O))
  let γ : ℕ → ℝ → D.Space := fun k => match k with
    | 0 => D.pt ∘ g₀
    | n + 1 => D.pt ∘ g n
  have hγc : ∀ k, ContinuousOn (γ k) (Icc 0 1) := by
    intro k; cases k with
    | zero => exact D.continuous_pt.comp_continuousOn hg₀c
    | succ n => exact D.continuous_pt.comp_continuousOn (hgc n)
  have hγj : ∀ k, γ k 1 = γ (k + 1) 0 := by
    intro k; cases k with
    | zero => simp [γ, hg₀1, hg0]
    | succ n => simp [γ, hg1, hg0]
  have hxs_t : Tendsto xs atTop (𝓝 x) := by
    have hc : Tendsto c atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3)
        (by norm_num)).const_mul r₀
      simpa using this
    have := tendsto_const_nhds (x := x) |>.add
      ((Complex.continuous_ofReal.tendsto 0).comp hc |>.mul_const ν)
    simpa [Function.comp_def] using this
  have hγp : Tendsto (fun k => γ k 0) atTop (𝓝 (D.pt x)) := by
    rw [← tendsto_add_atTop_iff_nat 1]
    have : (fun k => γ (k + 1) 0) = D.pt ∘ xs := by
      funext k; simp [γ, hg0]
    rw [this]; exact (D.continuous_pt.tendsto x).comp hxs_t
  have hbsum : Summable b := by
    have hq0 : (0 : ℝ) ≤ (2 / 3) ^ χ := by positivity
    have hq1 : (2 / 3 : ℝ) ^ χ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hχ
    have heq : (fun n => (c n / 3) ^ χ) = fun n => (r₀ / 3) ^ χ * ((2 / 3) ^ χ) ^ n := by
      funext n
      rw [show c n / 3 = r₀ / 3 * (2 / 3) ^ n by simp only [hcdef]; ring,
        Real.mul_rpow (by positivity) (by positivity), Real.rpow_pow_comm (by norm_num)]
    have h1 : Summable fun n => (c n / 3) ^ χ := by
      rw [heq]; exact (summable_geometric_of_lt_one hq0 hq1).mul_left _
    exact (h1.mul_left |C|).add (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hγs : ∑' k, curveLength (γ k) 0 1 ≠ ∞ := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    refine ENNReal.add_ne_top.2 ⟨hg₀len.ne, ?_⟩
    refine ne_top_of_le_ne_top (b := ∑' n, ENNReal.ofReal (b n)) ?_
      (ENNReal.tsum_le_tsum fun n => (hglen n).le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hbsum]
    exact ENNReal.ofReal_ne_top
  obtain ⟨hcont, hc0', hc1', hlen, himg⟩ := p412e_concat hγc hγj hγp hγs
  refine ⟨D.unpt ∘ p412eCat γ (D.pt x), D.continuous_unpt.comp_continuousOn hcont, ?_, ?_, ?_,
    ne_top_of_le_ne_top hγs hlen⟩
  · simp [hc0', γ, hg₀0]
  · simp [hc1']
  · intro t ht
    have hsub : (closedBall z r)ᶜ ⊆ (ball z r)ᶜ := compl_subset_compl.2 ball_subset_closedBall
    rcases himg t ht with h | ⟨k, s, hs, h⟩
    · rw [Function.comp_apply, h]
      simp [mem_sphere.1 hx]
    · rw [Function.comp_apply, h]
      cases k with
      | zero => exact hsub (hg₀O hs)
      | succ n => exact hsub (hgO n hs)

/-- **`hfin`** (DEC-86 (3)): under the internal Hölder bound near `x`, an avoid-geodesic to `x`
has finite length (it is not longer than the competitor of `p412e_finpath`) -/
theorem p412e_hfin {D : ContMetric} (hL : D.IsLength) {𝕫 z x : ℂ} {r : ℝ} (hr : 0 < r)
    {Q : ℝ → ℂ} {T : ℝ} (hQ : IsAvoidGeod D 𝕫 z r x Q T) {r₀ C χ : ℝ} (hr₀ : 0 < r₀)
    (hχ : 0 < χ)
    (hH : ∀ u ∈ closedBall x r₀, ∀ w ∈ closedBall x r₀, u ≠ w →
      D.internal (ball u (2 * ‖u - w‖)) u w ≤ ENNReal.ofReal (C * ‖u - w‖ ^ χ)) :
    D.len Q 0 T ≠ ∞ := by
  obtain ⟨hT, -, hQ0, -, hx, hout, hmin⟩ := hQ
  rcases eq_or_lt_of_le hT with h0 | h0
  · subst h0; simp [ContMetric.len, curveLength_self]
  have h𝕫 : 𝕫 ∉ closedBall z r := hQ0 ▸ hout 0 ⟨le_rfl, h0⟩
  obtain ⟨Q', h1, h2, h3, h4, h5⟩ := p412e_finpath hL hr hx h𝕫 hr₀ hχ hH
  exact ne_top_of_le_ne_top h5 (hmin Q' 0 1 zero_le_one h1 h2 h3 h4)

/-- GM's condition 3 of `ℰ_𝕣` (`regC3`, l. 1958–1962) gives the internal Hölder bound of
`p412e_finpath` near every `x ∈ B_{4ℓ𝕣}(𝕣V)` -/
theorem p412e_hH_of_regC3 {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) {ω : Ω} (hω : ω ∈ regC3 D h R 𝕣 a)
    (hs : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0) {x : ℂ} (hx : x ∈ regRegion R 𝕣) :
    ∃ r₀ > 0, ∀ u ∈ closedBall x r₀, ∀ w ∈ closedBall x r₀, u ≠ w →
      (D (h ω)).internal (ball u (2 * ‖u - w‖)) u w ≤
        ENNReal.ofReal (scaleFac R.ξ R.c (h ω) 𝕣 0 / 𝕣 ^ R.χ * ‖u - w‖ ^ R.χ) := by
  obtain ⟨ε, hε, hεs⟩ := Metric.isOpen_iff.1 (isOpen_thickening : IsOpen (regRegion R 𝕣)) x hx
  set s := scaleFac R.ξ R.c (h ω) 𝕣 0
  refine ⟨min (ε / 2) (a * 𝕣 / 2), lt_min (by linarith) (by positivity), fun u hu w hw hne => ?_⟩
  have hu' : u ∈ regRegion R 𝕣 := hεs (closedBall_subset_ball (by
    linarith [min_le_left (ε / 2) (a * 𝕣 / 2)]) hu)
  have hw' : w ∈ regRegion R 𝕣 := hεs (closedBall_subset_ball (by
    linarith [min_le_left (ε / 2) (a * 𝕣 / 2)]) hw)
  have hle : ‖u - w‖ ≤ a * 𝕣 := by
    have := dist_triangle_right u w x
    rw [dist_eq_norm] at this
    linarith [mem_closedBall.1 hu, mem_closedBall.1 hw, min_le_right (ε / 2) (a * 𝕣 / 2)]
  have h3 := (hω u hu' w hw' hle).2 hne
  have hnorm : ‖(u - w) / (𝕣 : ℂ)‖ ^ R.χ = ‖u - w‖ ^ R.χ / 𝕣 ^ R.χ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h𝕣,
      Real.div_rpow (norm_nonneg _) h𝕣.le]
  rw [hnorm] at h3
  have hone : ENNReal.ofReal s * ENNReal.ofReal s⁻¹ = 1 := by
    rw [← ENNReal.ofReal_mul hs.le, mul_inv_cancel₀ hs.ne', ENNReal.ofReal_one]
  calc (D (h ω)).internal (ball u (2 * ‖u - w‖)) u w
      = ENNReal.ofReal s * (ENNReal.ofReal s⁻¹ * (D (h ω)).internal (ball u (2 * ‖u - w‖)) u w) := by
        rw [← mul_assoc, hone, one_mul]
    _ ≤ ENNReal.ofReal s * ENNReal.ofReal (‖u - w‖ ^ R.χ / 𝕣 ^ R.χ) := by gcongr
    _ = ENNReal.ofReal (s / 𝕣 ^ R.χ * ‖u - w‖ ^ R.χ) := by
        rw [← ENNReal.ofReal_mul hs.le]; congr 1; ring

/-- **`hfin` on `ℰ_𝕣`** (DEC-86 (3)): on condition 3 of `ℰ_𝕣`, avoid-geodesics to points
`x ∈ ∂B_r(z) ∩ B_{4ℓ𝕣}(𝕣V)` have finite length -/
theorem p412e_hfin_regC3 {Ω : Type} {D : DistC → ContMetric} {h : Ω → DistC} {R : RegPar}
    {𝕣 a : ℝ} (h𝕣 : 0 < 𝕣) (ha : 0 < a) (hχ : 0 < R.χ) (hc : 0 < R.c 𝕣) {ω : Ω}
    (hω : ω ∈ regC3 D h R 𝕣 a) (hL : (D (h ω)).IsLength) {𝕫 z x : ℂ} {r : ℝ} (hr : 0 < r)
    {Q : ℝ → ℂ} {T : ℝ} (hQ : IsAvoidGeod (D (h ω)) 𝕫 z r x Q T) (hx : x ∈ regRegion R 𝕣) :
    (D (h ω)).len Q 0 T ≠ ∞ := by
  have hs : 0 < scaleFac R.ξ R.c (h ω) 𝕣 0 := by unfold scaleFac; positivity
  obtain ⟨r₀, hr₀, hH⟩ := p412e_hH_of_regC3 h𝕣 ha hω hs hx
  exact p412e_hfin hL hr hQ hr₀ hχ hH

end LQGMetric.GM
