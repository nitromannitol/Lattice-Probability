import LatticeProb.LQG.GMCScaleGrid
import LatticeProb.LQG.GMCScaleSandwich
import LatticeProb.LQG.GMCScaleIncrement
import LatticeProb.LQG.WeylOffOrigin
import LatticeProb.Gauss.CircleAverageModulusUniform

/-!
# Approximations of the γ-LQG measure along all radii of a dyadic band

For a whole-plane Gaussian free field `h` with circle averages `h_s(z)`, `0 < γ < 2`, and a continuous compactly
supported weight `g`, we show that almost surely
`sup_{s ∈ [2^{-k}/2, 2^{-k}]} |∫ g d(s^{γ²/2} e^{γ h_s(z)} dz) - ∫ g d(2^{-k γ²/2} e^{γ h_{2^{-k}}(z)} dz)| → 0`
as `k → ∞`. Consequently, if the dyadic approximations converge, then the approximations along the scales
`r 2^{-k}` converge to the same limit, for every ratio `r ∈ [1/2, 1]` simultaneously.

The proof combines three ingredients:
* the grid estimate (`IsWholePlaneGFF.ae_eventually_grid`): at the `N_k + 1` radii
  `s_{k,j} = 2^{-k} (1 - j / (2 N_k))`, `N_k = ⌊2^{ck/2}⌋`, the approximations are within `2^{-θ k}` of the
  dyadic one, for the weight `g` and for `|g|`;
* the uniform modulus of the circle averages in the radius
  (`IsWholePlaneGFF.ae_eventually_abs_circle_sub_le`), which controls `|h_s(z) - h_{s_{k,j}}(z)|` for the grid
  radius `s_{k,j}` nearest to `s`;
* the deterministic comparison of the approximations at two radii
  (`GMCScaleSandwich.abs_integral_recentred_sub_le`).
-/

open MeasureTheory Filter Topology Real

namespace LatticeProb.LQG.GMCRatioLimit

open LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid

/-- `|log x - log y| ≤ |x - y| / m` for `x, y ≥ m > 0`. -/
theorem abs_log_sub_log_le {x y m : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y) :
    |log x - log y| ≤ |x - y| / m := by
  have hx0 : 0 < x := hm.trans_le hx
  have hy0 : 0 < y := hm.trans_le hy
  have key : ∀ a b : ℝ, 0 < a → m ≤ b → log a - log b ≤ |a - b| / m := by
    intro a b ha hb
    have hb0 : 0 < b := hm.trans_le hb
    rw [← log_div ha.ne' hb0.ne']
    calc log (a / b) ≤ a / b - 1 := log_le_sub_one_of_pos (div_pos ha hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ |a - b| / b := by gcongr; exact le_abs_self _
      _ ≤ |a - b| / m := div_le_div_of_nonneg_left (abs_nonneg _) hm hb
  rw [abs_le]
  refine ⟨?_, key x y hx0 hy⟩
  have := key y x hy0 hx
  rw [abs_sub_comm] at this
  linarith

/-- Every radius `s ∈ [2^{-k}/2, 2^{-k}]` lies within `2^{-k} / (2 N_k)` of a grid radius `s_{k,j}`, `j ≤ N_k`. -/
theorem exists_gridScale_near (N : ℕ → ℕ) {k : ℕ} (hN : 1 ≤ N k) {s : ℝ} (hs1 : dyadicScale k / 2 ≤ s)
    (hs2 : s ≤ dyadicScale k) :
    ∃ j ≤ N k, |s - gridScale N k j| ≤ dyadicScale k / (2 * N k) := by
  have hε : 0 < dyadicScale k := pow_pos (by norm_num) k
  have hNpos : (0 : ℝ) < N k := by exact_mod_cast hN
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (1 - s / dyadicScale k) * (2 * N k) := ⟨_, rfl⟩
  have hsε : s / dyadicScale k ≤ 1 := (div_le_one hε).2 hs2
  have hsε' : 1 / 2 ≤ s / dyadicScale k := by rw [le_div_iff₀ hε]; linarith
  have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg (by linarith) (by positivity)
  have hxN : x ≤ N k := by rw [hx]; nlinarith
  refine ⟨⌊x⌋₊, Nat.floor_le_of_le hxN, ?_⟩
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have h2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have key : s - gridScale N k ⌊x⌋₊ = dyadicScale k * ((⌊x⌋₊ : ℝ) - x) / (2 * N k) := by
    unfold gridScale
    rw [hx]
    field_simp
    ring
  rw [key, abs_div, abs_mul, abs_of_pos hε, abs_of_pos (by positivity : (0 : ℝ) < 2 * N k)]
  gcongr
  calc dyadicScale k * |(⌊x⌋₊ : ℝ) - x| ≤ dyadicScale k * 1 := by
        gcongr
        rw [abs_le]
        constructor <;> linarith
    _ = dyadicScale k := mul_one _

/-- The grid count `N_k = ⌊2^{ck/2}⌋` is at least `1`, and the grid mesh `2^{-k} / (2 N_k)` is at most
`2^{-k} 2^{-ck/2}`. -/
theorem one_le_gridCount_and_mesh_le {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    1 ≤ gridCount c k ∧ dyadicScale k / (2 * gridCount c k) ≤ dyadicScale k * dyadicScale k ^ (c / 2) := by
  have hε : 0 < dyadicScale k := pow_pos (by norm_num) k
  have hε1 : dyadicScale k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hx1 : 1 ≤ dyadicScale k ^ (-(c / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε hε1 (by linarith)
  have hN1 : 1 ≤ gridCount c k := Nat.le_floor (by simpa using hx1)
  have hlt : dyadicScale k ^ (-(c / 2)) < gridCount c k + 1 := Nat.lt_floor_add_one _
  have hpos : 0 < dyadicScale k ^ (c / 2) := rpow_pos_of_pos hε _
  have hN1' : (1 : ℝ) ≤ gridCount c k := by exact_mod_cast hN1
  refine ⟨hN1, ?_⟩
  have hone : 1 ≤ dyadicScale k ^ (c / 2) * (2 * gridCount c k) := by
    calc (1 : ℝ) = dyadicScale k ^ (c / 2) * dyadicScale k ^ (-(c / 2)) := by
          rw [Real.rpow_neg hε.le, mul_inv_cancel₀ hpos.ne']
      _ ≤ dyadicScale k ^ (c / 2) * (2 * gridCount c k) := by gcongr; linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- The integral of `f` against the approximation `s^{γ²/2} e^{γ h_s(z)} dz`, written with a recentring constant
`H`: `∫ f d(lqgApprox γ h s) = e^{γ H} ∫ f(z) s^{γ²/2} e^{γ (h_s(z) - H)} dz`. -/
theorem integral_lqgApprox_eq_exp_mul {γ s : ℝ} {h : ℝ → ℂ → ℝ} (hs : 0 ≤ s) (hm : Measurable (h s))
    (f : ℂ → ℝ) (H : ℝ) :
    ∫ z, f z ∂(lqgApprox γ h s) =
      rexp (γ * H) * ∫ z, f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H))) := by
  rw [WeylOffOriginDerived.integral_lqgApprox hs hm, ← integral_const_mul]
  congr 1
  funext z
  rw [mul_sub, Real.exp_sub]
  field_simp

/-- Continuity of `z ↦ h_s(z)` for `s > 0` from the joint continuity of the circle averages. -/
theorem continuous_slice {h : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {s : ℝ} (hs : 0 < s) :
    Continuous (h s) :=
  hcont.comp_continuous (Continuous.prodMk_right s) fun z => ⟨hs, Set.mem_univ z⟩

/-- Integrability of `f(z) s^{γ²/2} e^{γ (h_s(z) - H)}` for continuous compactly supported `f`. -/
theorem integrable_mul_recentred {γ s H : ℝ} {h : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) (hs : 0 < s) {f : ℂ → ℝ}
    (hfc : Continuous f) (hfs : HasCompactSupport f) :
    Integrable fun z => f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H))) := by
  have hc := continuous_slice hcont hs
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact hfs.mul_right

/-- The difference of the approximations at two radii, recentred: `∫ g dμ_s - ∫ g dμ_ε = e^{γ H}
∫ g(z) (s^{γ²/2} e^{γ (h_s(z) - H)} - ε^{γ²/2} e^{γ (h_ε(z) - H)}) dz`. -/
theorem integral_lqgApprox_sub_eq {γ s ε H : ℝ} {h : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) (hs : 0 < s) (hε : 0 < ε)
    {f : ℂ → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f) :
    ∫ z, f z ∂(lqgApprox γ h s) - ∫ z, f z ∂(lqgApprox γ h ε) =
      rexp (γ * H) * ∫ z, f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - H))) := by
  have h1 := integrable_mul_recentred (γ := γ) (H := H) hcont hs hfc hfs
  have h2 := integrable_mul_recentred (γ := γ) (H := H) hcont hε hfc hfs
  have hsub : ∫ z, f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H)) -
      ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - H))) =
      (∫ z, f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H)))) -
        ∫ z, f z * (ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - H))) := by
    calc _ = ∫ z, (f z * (s ^ (γ ^ 2 / 2) * rexp (γ * (h s z - H))) -
          f z * (ε ^ (γ ^ 2 / 2) * rexp (γ * (h ε z - H)))) := by
          congr 1
          funext z
          ring
      _ = _ := integral_sub h1 h2
  rw [hsub, integral_lqgApprox_eq_exp_mul hs.le (continuous_slice hcont hs).measurable f H,
    integral_lqgApprox_eq_exp_mul hε.le (continuous_slice hcont hε).measurable f H]
  ring

/-- **Comparison of the approximations at two radii.** If `s, s' ≥ m > 0` and `|h_s(z) - h_{s'}(z)| ≤ η` on the
support of `g`, then `|∫ g dμ_s - ∫ g dμ_{s'}| ≤ (e^{(γ²/2) |s - s'| / m + |γ| η} - 1) ∫ |g| dμ_{s'}`, where
`μ_s = s^{γ²/2} e^{γ h_s(z)} dz`. -/
theorem abs_integral_lqgApprox_sub_le {γ : ℝ} {h : ℝ → ℂ → ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℂ => h p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) {g : ℂ → ℝ}
    (hgc : Continuous g) (hgs : HasCompactSupport g) {s s' η m : ℝ} (hm : 0 < m) (hs : m ≤ s) (hs' : m ≤ s')
    (hη : ∀ z, g z ≠ 0 → |h s z - h s' z| ≤ η) :
    |∫ z, g z ∂(lqgApprox γ h s) - ∫ z, g z ∂(lqgApprox γ h s')| ≤
      (rexp (γ ^ 2 / 2 * (|s - s'| / m) + |γ| * η) - 1) * ∫ z, |g z| ∂(lqgApprox γ h s') := by
  have hs0 : 0 < s := hm.trans_le hs
  have hs'0 : 0 < s' := hm.trans_le hs'
  have hms := (continuous_slice hcont hs0).measurable
  have hms' := (continuous_slice hcont hs'0).measurable
  rw [integral_lqgApprox_eq_exp_mul hs0.le hms g 0, integral_lqgApprox_eq_exp_mul hs'0.le hms' g 0,
    integral_lqgApprox_eq_exp_mul hs'0.le hms' (fun z => |g z|) 0]
  simp only [mul_zero, Real.exp_zero, one_mul]
  have key := GMCScaleSandwich.abs_integral_recentred_sub_le (μ := volume) (γ := γ) (H₀ := 0) hs0 hs'0 hη
    (integrable_mul_recentred hcont hs0 hgc hgs) (integrable_mul_recentred hcont hs'0 hgc hgs)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun z => ?_))
  · have hlog := abs_log_sub_log_le hm hs hs'
    have hγ2 : 0 ≤ γ ^ 2 / 2 := by positivity
    gcongr
  · positivity

/-- `∑_k 2^{-ck} < ∞` for `c > 0`. -/
theorem summable_dyadicScale_rpow {c : ℝ} (hc : 0 < c) : Summable fun k : ℕ => dyadicScale k ^ c := by
  refine (Gauss.summable_exp_log_dyadicScale_mul hc).congr fun k => ?_
  rw [Real.rpow_def_of_pos (show 0 < dyadicScale k from pow_pos (by norm_num) k)]

/-- Consecutive dyadic scales: `2^{-n}/2 ≤ 2^{-(n+1)} ≤ 2^{-n}`. -/
theorem dyadicScale_succ_mem (n : ℕ) :
    dyadicScale n / 2 ≤ dyadicScale (n + 1) ∧ dyadicScale (n + 1) ≤ dyadicScale n := by
  have h : 0 < dyadicScale n := pow_pos (by norm_num) n
  unfold dyadicScale at h ⊢
  rw [pow_succ]
  constructor <;> linarith

end LatticeProb.LQG.GMCRatioLimit

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Weakening the exponent of an `L¹` increment bound `K ε^c` to any `0 < c₀ ≤ c` (for `ε ≤ 1`). -/
theorem increment_bound_mono {γ R K c c₀ : ℝ} {g : ℂ → ℝ} (hc₀ : c₀ ≤ c)
    (hK : ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
      ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c) :
    ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
      ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c₀ := by
  have hK0 : 0 ≤ K := by
    have h1 := hK 1 1 one_pos le_rfl (by norm_num) le_rfl
    simp only [Real.one_rpow, mul_one] at h1
    exact (integral_nonneg fun ω => abs_nonneg _).trans h1
  intro ε s hε hε1 hs1 hs2
  exact (hK ε s hε hε1 hs1 hs2).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hε hε1 hc₀) hK0)

/-- **Approximations of the LQG measure along all radii of a dyadic band.** For a whole-plane GFF, `0 < γ < 2` and
a continuous compactly supported `g`, almost surely there is a sequence `u_k → 0` such that for all large `k` and
every radius `s ∈ [2^{-k}/2, 2^{-k}]`,
`|∫ g d(s^{γ²/2} e^{γ h_s(z)} dz) - ∫ g d(2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz)| ≤ u_k`. -/
theorem ae_exists_tendsto_zero_integral_lqgApprox_sub (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, ∃ u : ℕ → ℝ, Tendsto u atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∀ s : ℝ,
      dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
      |∫ z, g z ∂(lqgApprox γ (hcirc ω) s) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))| ≤ u k := by
  have hd : ∀ k, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hd1 : ∀ k, dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hdp : ∀ p : ℝ, 0 < p → Tendsto (fun k => dyadicScale k ^ p) atTop (𝓝 0) := by
    intro p hp
    have h0 : Tendsto (fun k : ℕ => dyadicScale k) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [Real.zero_rpow hp.ne'] using h0.rpow_const (Or.inr hp.le)
  obtain ⟨R, K, c, hR, hc, hgR, hK⟩ := hh.scaleIncrementL1Bound hγ0 hγ2 g hgc hgs
  obtain ⟨R', K', c', hR', hc', hgR', hK'⟩ :=
    hh.scaleIncrementL1Bound hγ0 hγ2 (fun z => |g z|) hgc.abs hgs.abs
  obtain ⟨c₀, hc₀, hc₀c, hc₀c'⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ c₀ ≤ c ∧ c₀ ≤ c' :=
    ⟨min c c', lt_min hc hc', min_le_left _ _, min_le_right _ _⟩
  have hsum : ∀ K₁ : ℝ, Summable fun k =>
      ((gridCount c₀ k : ℝ) + 1) * (K₁ * dyadicScale k ^ c₀ / dyadicScale k ^ (c₀ / 4)) :=
    fun K₁ => summable_gridCount (by positivity) (by linarith)
  have hG1 := hh.ae_eventually_grid γ hgc hgs hR hgR (increment_bound_mono hc₀c hK) (hsum K)
  have hG2 := hh.ae_eventually_grid γ hgc.abs hgs.abs hR' hgR' (increment_bound_mono hc₀c' hK') (hsum K')
  obtain ⟨β, hβ, hmod⟩ := hh.ae_eventually_abs_circle_sub_le (a := c₀ / 4) (by positivity) R
  have hlim := hh.ae_exists_tendsto_integral_lqgApprox_of_scales γ hgc.abs hgs.abs hR' hgR' hK'
    (σ := dyadicScale) hd (by simp [dyadicScale]) dyadicScale_succ_mem (summable_dyadicScale_rpow hc')
  filter_upwards [hG1, hG2, hmod, hlim, hh.ae_continuousOn_circle] with ω h1 h2 h3 hℓ hcont
  obtain ⟨ℓ, hℓ⟩ := hℓ
  set E := rexp (γ * hcirc ω R 0) with hE
  set E' := rexp (γ * hcirc ω R' 0) with hE'
  set t : ℕ → ℝ := fun k => γ ^ 2 / 2 * (2 * dyadicScale k ^ (c₀ / 2)) + |γ| * dyadicScale k ^ β with ht
  refine ⟨fun k => (rexp (t k) - 1) * (∫ z, |g z| ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) +
    E' * dyadicScale k ^ (c₀ / 4)) + E * dyadicScale k ^ (c₀ / 4), ?_, ?_⟩
  · have htt : Tendsto t atTop (𝓝 0) := by
      have := ((hdp _ (by positivity : 0 < c₀ / 2)).const_mul 2).const_mul (γ ^ 2 / 2) |>.add
        ((hdp β hβ).const_mul |γ|)
      simpa using this
    have hexp : Tendsto (fun k => rexp (t k) - 1) atTop (𝓝 0) := by
      have := ((Real.continuous_exp.tendsto 0).comp htt).sub_const 1
      simpa using this
    have := (hexp.mul (hℓ.add ((hdp _ (by positivity : 0 < c₀ / 4)).const_mul E'))).add
      ((hdp _ (by positivity : 0 < c₀ / 4)).const_mul E)
    simpa using this
  · filter_upwards [h1, h2, h3, eventually_ge_atTop 1] with k hk1 hk2 hk3 hk s hs1 hs2
    have hε := hd k
    have hεlt : dyadicScale k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    obtain ⟨hN1, hmesh⟩ := one_le_gridCount_and_mesh_le hc₀.le k
    obtain ⟨j, hj, hjs⟩ := exists_gridScale_near (gridCount c₀) hN1 hs1 hs2
    obtain ⟨hsj1, hsj2⟩ := gridScale_mem_Icc (gridCount c₀) hj
    obtain ⟨sj, hsj⟩ : ∃ sj, sj = gridScale (gridCount c₀) k j := ⟨_, rfl⟩
    have hg1 := hk1 j hj
    have hg2 := hk2 j hj
    rw [← hsj] at hg1 hg2 hsj1 hsj2 hjs
    have hsj0 : 0 < sj := (half_pos hε).trans_le hsj1
    have hjs' : |s - sj| ≤ dyadicScale k * dyadicScale k ^ (c₀ / 2) := hjs.trans hmesh
    have hlt : |s - sj| < dyadicScale k * dyadicScale k ^ (c₀ / 4) :=
      hjs'.trans_lt (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_gt hε hεlt (by linarith)) hε)
    have hη : ∀ z, g z ≠ 0 → |hcirc ω s z - hcirc ω sj z| ≤ dyadicScale k ^ β := fun z hz =>
      hk3 z (by linarith [hgR z hz]) s sj hs1 hs2 hsj1 hsj2 hlt
    have hA := abs_integral_lqgApprox_sub_le (γ := γ) hcont hgc hgs (half_pos hε) hs1 hsj1 hη
    have hB := integral_lqgApprox_sub_eq (γ := γ) (H := hcirc ω R 0) hcont hsj0 hε hgc hgs
    have hC := integral_lqgApprox_sub_eq (γ := γ) (H := hcirc ω R' 0) hcont hsj0 hε hgc.abs hgs.abs
    have hE0 : 0 < E := exp_pos _
    have hBb : |∫ z, g z ∂(lqgApprox γ (hcirc ω) sj) -
        ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))| ≤ E * dyadicScale k ^ (c₀ / 4) := by
      rw [hB, abs_mul, abs_of_pos hE0]
      exact mul_le_mul_of_nonneg_left hg1.le hE0.le
    have hCb : ∫ z, |g z| ∂(lqgApprox γ (hcirc ω) sj) ≤
        ∫ z, |g z| ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) + E' * dyadicScale k ^ (c₀ / 4) := by
      have : ∫ z, |g z| ∂(lqgApprox γ (hcirc ω) sj) -
          ∫ z, |g z| ∂(lqgApprox γ (hcirc ω) (dyadicScale k)) ≤ E' * dyadicScale k ^ (c₀ / 4) := by
        rw [hC]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hg2.le) (exp_pos _).le
      linarith
    have hexp : rexp (γ ^ 2 / 2 * (|s - sj| / (dyadicScale k / 2)) + |γ| * dyadicScale k ^ β) - 1 ≤
        rexp (γ ^ 2 / 2 * (2 * dyadicScale k ^ (c₀ / 2)) + |γ| * dyadicScale k ^ β) - 1 := by
      have hq : |s - sj| / (dyadicScale k / 2) ≤ 2 * dyadicScale k ^ (c₀ / 2) := by
        rw [div_le_iff₀ (half_pos hε)]
        nlinarith [hjs']
      gcongr
    have hexp0 : 0 ≤ rexp (γ ^ 2 / 2 * (|s - sj| / (dyadicScale k / 2)) + |γ| * dyadicScale k ^ β) - 1 :=
      sub_nonneg.2 (Real.one_le_exp (by positivity))
    have hI0 : 0 ≤ ∫ z, |g z| ∂(lqgApprox γ (hcirc ω) sj) := integral_nonneg fun z => abs_nonneg _
    calc |∫ z, g z ∂(lqgApprox γ (hcirc ω) s) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))|
        ≤ |∫ z, g z ∂(lqgApprox γ (hcirc ω) s) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) sj)| +
          |∫ z, g z ∂(lqgApprox γ (hcirc ω) sj) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))| :=
          abs_sub_le _ _ _
      _ ≤ _ := add_le_add (hA.trans (mul_le_mul hexp hCb hI0 (hexp0.trans hexp))) hBb

/-- Almost surely, the approximations `∫ g d(2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz)` converge. -/
theorem ae_exists_tendsto_integral_lqgApprox_dyadicScale (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ,
      Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) atTop (𝓝 ℓ) := by
  obtain ⟨R, K, c, hR, hc, hgR, hK⟩ := hh.scaleIncrementL1Bound hγ0 hγ2 g hgc hgs
  exact hh.ae_exists_tendsto_integral_lqgApprox_of_scales γ hgc hgs hR hgR hK (σ := dyadicScale)
    (fun k => pow_pos (by norm_num) k) (by simp [dyadicScale]) dyadicScale_succ_mem
    (summable_dyadicScale_rpow hc)

/-- **Convergence along every ratio.** For a whole-plane GFF, `0 < γ < 2` and a continuous compactly supported `g`,
almost surely the dyadic approximations `∫ g d(2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz)` converge to some `ℓ`, and for every
ratio `r ∈ [1/2, 1]` simultaneously the approximations at the scales `r 2^{-k}` converge to the same `ℓ`. -/
theorem ae_tendsto_integral_lqgApprox_ratio (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, ∃ ℓ : ℝ,
      Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) atTop (𝓝 ℓ) ∧
      ∀ r ∈ Set.Icc (1 / 2 : ℝ) 1,
        Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (r * dyadicScale k))) atTop (𝓝 ℓ) := by
  filter_upwards [hh.ae_exists_tendsto_integral_lqgApprox_dyadicScale hγ0 hγ2 hgc hgs,
    hh.ae_exists_tendsto_zero_integral_lqgApprox_sub hγ0 hγ2 hgc hgs] with ω hℓ hu
  obtain ⟨ℓ, hℓ⟩ := hℓ
  obtain ⟨u, hu, hev⟩ := hu
  refine ⟨ℓ, hℓ, fun r hr => ?_⟩
  have hdiff : Tendsto (fun k => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (r * dyadicScale k)) -
      ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hu
    filter_upwards [hev] with k hk
    have hd : 0 < dyadicScale k := pow_pos (by norm_num) k
    rw [Real.norm_eq_abs]
    exact hk _ (by nlinarith [hr.1]) (by nlinarith [hr.2])
  simpa using hℓ.add hdiff

end LatticeProb.Gauss.IsWholePlaneGFF
