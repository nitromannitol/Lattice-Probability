/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61H3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61H2

/-!
# D117 P-61G (6): `dzzL61GlueK_of_scale` (P2-DZZ125)

The assembly of handoff P2-DZZ61G §6 (DZZ l. 2562–2568, 2605), see S6L61H2 for the plan.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- the exponent arithmetic of P-61G (handoff P2-DZZ61G §3, DEC-125 §3): with
`40 δ^κ ≤ s < 80 δ^κ` (`s = 2^{−m} = ‖a‖`), `δ' = δ / (s e^{λ})` satisfies
`δ'^{−(χ+ι/2)} + 1 ≤ δ^{−(χ−ι)}/40` as soon as the `λ`-cost is small (own elementary proof). -/
lemma glue_arith {χ ι κ : ℝ} (hι : 0 < ι) (hκ : 0 < κ) (hκχ : 2 * ι ≤ κ * χ)
    {δ s lam : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs1 : 40 * δ ^ κ ≤ s) (hs2 : s < 80 * δ ^ κ)
    (hsmall : (80 : ℝ) ^ (χ + ι / 2) * Real.exp ((χ + ι / 2) * lam) * s ^ (ι / (2 * κ)) ≤ 1 / 80)
    (hbig : 80 ≤ δ ^ (-(χ - ι))) :
    (δ / (s * Real.exp lam)) ^ (-(χ + ι / 2)) + 1 ≤ δ ^ (-(χ - ι)) / 40 := by
  set e := χ + ι / 2 with he
  have hχι : 0 < χ := by
    by_contra h; push Not at h; nlinarith
  have he0 : 0 < e := by positivity
  have hdk : 0 < δ ^ κ := Real.rpow_pos_of_pos hδ κ
  have hs0 : 0 < s := by linarith
  set X := s * Real.exp lam with hX
  have hX0 : 0 < X := by positivity
  have h1 : (δ / X) ^ (-e) = X ^ e / δ ^ e := by
    rw [Real.rpow_neg (by positivity), Real.div_rpow hδ.le hX0.le, inv_div]
  have h2 : X ^ e ≤ (80 : ℝ) ^ e * Real.exp (e * lam) * (δ ^ κ) ^ e := by
    have : X ^ e ≤ (80 * δ ^ κ * Real.exp lam) ^ e :=
      Real.rpow_le_rpow hX0.le (by rw [hX]; gcongr) he0.le
    refine this.trans (le_of_eq ?_)
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity)
      (by positivity), ← Real.exp_mul, mul_comm lam e]
    ring
  have h3 : (δ ^ κ) ^ e / δ ^ e = δ ^ (-(χ - ι)) * δ ^ (ι / 2) * δ ^ ((κ - 1) * e + (χ - 3 * ι / 2)) := by
    rw [← Real.rpow_mul hδ.le, ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_sub hδ]
    congr 1; ring
  have h4 : δ ^ ((κ - 1) * e + (χ - 3 * ι / 2)) ≤ 1 :=
    Real.rpow_le_one hδ.le hδ1 (by rw [he]; nlinarith)
  have h5 : δ ^ (ι / 2) ≤ s ^ (ι / (2 * κ)) := by
    rw [show ι / 2 = κ * (ι / (2 * κ)) by field_simp, Real.rpow_mul hδ.le]
    exact Real.rpow_le_rpow hdk.le (by linarith) (by positivity)
  set D := δ ^ (-(χ - ι)) with hD
  have hD0 : 0 ≤ D := by positivity
  have hmain : (δ / X) ^ (-e) ≤ D / 80 := by
    rw [h1, div_le_iff₀ (Real.rpow_pos_of_pos hδ e)]
    have hδe := Real.rpow_pos_of_pos hδ e
    have h3' : (δ ^ κ) ^ e = D * δ ^ (ι / 2) * δ ^ ((κ - 1) * e + (χ - 3 * ι / 2)) * δ ^ e := by
      rw [← h3]; field_simp
    have hA : 0 ≤ (80 : ℝ) ^ e * Real.exp (e * lam) := by positivity
    have hB : 0 ≤ δ ^ ((κ - 1) * e + (χ - 3 * ι / 2)) := by positivity
    calc X ^ e ≤ (80 : ℝ) ^ e * Real.exp (e * lam) * (δ ^ κ) ^ e := h2
      _ = (80 : ℝ) ^ e * Real.exp (e * lam) * δ ^ (ι / 2) *
          δ ^ ((κ - 1) * e + (χ - 3 * ι / 2)) * D * δ ^ e := by rw [h3']; ring
      _ ≤ (80 : ℝ) ^ e * Real.exp (e * lam) * s ^ (ι / (2 * κ)) * 1 * D * δ ^ e := by gcongr
      _ ≤ 1 / 80 * 1 * D * δ ^ e := by gcongr
      _ = D / 80 * δ ^ e := by ring
  rw [hX] at hmain
  linarith

lemma ringU₀_mem_dzzVbar : ringU₀ ∈ dzzVbar := by
  refine ⟨?_, ?_⟩ <;> simp [ringU₀] <;> norm_num [abs_of_nonneg, abs_of_nonpos]

lemma ringV₀_mem_dzzVbar : ringV₀ ∈ dzzVbar := by
  refine ⟨?_, ?_⟩ <;> simp [ringV₀] <;> norm_num [abs_of_nonneg, abs_of_nonpos]

lemma dist_ringU₀_ringV₀ : dist ringU₀ ringV₀ = 1 / 40 := by
  rw [dist_comm, dist_eq_norm, ringV₀_sub_ringU₀]
  norm_num

lemma ringU₀_ne_ringV₀ : ringU₀ ≠ ringV₀ := by
  intro h; have := dist_ringU₀_ringV₀; rw [h, dist_self] at this; norm_num at this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **`DZZL61GlueK` from the scale-uniform similarity coupling** (DZZ l. 2562–2568, 2605;
handoff P2-DZZ61G §6 with `κ < 1`, D125). -/
theorem dzzL61GlueK_of_scale {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {α χ ι κ ξ : ℝ} (hα1 : α < 1) (hι : 0 < ι) (hκ : 0 < κ)
    (hκχ : 2 * ι ≤ κ * χ) (hκ1 : κ < 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    {u : ℂ} (hu : u ∈ dzzVbar)
    (hsc : DZZSimCoupleScale γ ξ (tildeBox ringU₀ ringV₀))
    (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
      (tildeBox ringU₀ ringV₀) ξ)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω)) δ ringU₀ ringV₀ < ⊤) :
    DZZL61GlueK P (dzzMuIn γ W) α χ u ι κ := by
  intro L v hLv
  have hχ : 0 < χ := by by_contra h; push Not at h; nlinarith
  have hχι : 0 < χ - ι := by nlinarith
  set K₀ := tildeBox ringU₀ ringV₀
  -- DZZ Lemma 5.3 + Proposition 3.17 at the fixed pair, at `ι/2`
  have hd₀ : 2 * ξ ≤ dist ringU₀ ringV₀ := by rw [dist_ringU₀_ringV₀]; linarith
  have hU : ringU₀ ∈ dzzVXi ξ := mem_dzzVXi_of_near (a := 1 / 80)
    (by simp [ringU₀]) (by simp [ringU₀]) (by linarith) hξ.le
  have hV : ringV₀ ∈ dzzVXi ξ := mem_dzzVXi_of_near (a := 1 / 80)
    (by simp [ringV₀]) (by simp [ringV₀]) (by linarith) hξ.le
  have hT := dzz_lem53_upper_whp hL53 ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar ringU₀_ne_ringV₀
    h317 (mem_kXi_tildeBox_left' ringU₀_ne_ringV₀ hd₀)
    (mem_kXi_tildeBox_right' ringU₀_ne_ringV₀ hd₀) hU hV
    (by rw [dist_ringU₀_ringV₀]; linarith) hfin (half_pos hι)
  obtain ⟨C, hC, hpair⟩ := prob_not_pairsOK_le hW hγ hγ2 hsc
  -- the dyadic scale `2^{-m} ∈ [40 δ^κ, 80 δ^κ)`
  have hm : ∀ δ : ℝ, ∃ n : ℕ, 0 < δ → 40 * δ ^ κ ≤ 1 →
      (1 / 2 : ℝ) ^ (n + 1) < 40 * δ ^ κ ∧ 40 * δ ^ κ ≤ (1 / 2) ^ n := by
    intro δ
    by_cases h : 0 < δ ∧ 40 * δ ^ κ ≤ 1
    · obtain ⟨n, h1, h2⟩ := exists_nat_pow_near_of_lt_one
        (by have := Real.rpow_pos_of_pos h.1 κ; positivity) h.2
        (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
      exact ⟨n, fun _ _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose mf hmf using hm
  set lamf : ℝ → ℝ := fun δ => ((mf δ : ℝ) + 1) ^ (3 / 4 : ℝ)
  set dpf : ℝ → ℝ := fun δ => δ / ((1 / 2 : ℝ) ^ mf δ * Real.exp (lamf δ))
  set Nf : ℝ → ℕ := fun δ => ⌊δ ^ (-(χ - ι)) / 40⌋₊
  set G : ℝ → ℝ≥0∞ := fun s => P {ω | ¬ ((lgdDZZ (dzzWall K₀ (dzzMuIn γ W ω)) s ringU₀ ringV₀ :
    ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (s ^ (-(χ + ι / 2)))}
  -- eventual facts
  have hpos : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have hsmallk : ∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ^ κ < ε := fun ε hε =>
    tendsto_rpow_nhdsGT_zero hκ (Iio_mem_nhds hε)
  have hE1 := hsmallk (1 / 40) (by norm_num)
  have hmf' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (1 / 2 : ℝ) ^ (mf δ + 1) < 40 * δ ^ κ ∧
      40 * δ ^ κ ≤ (1 / 2) ^ mf δ := by
    filter_upwards [hpos, hE1] with δ h1 h2
    exact hmf δ h1.1 (by linarith)
  -- `m → ∞`
  have hT1 : Tendsto mf (𝓝[>] (0 : ℝ)) atTop := by
    refine tendsto_atTop.2 fun M => ?_
    filter_upwards [hmf', hsmallk ((1 / 2 : ℝ) ^ M / 40) (by positivity)] with δ h1 h2
    by_contra hlt
    push Not at hlt
    have : (1 / 2 : ℝ) ^ M ≤ (1 / 2) ^ (mf δ + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hlt
    linarith [h1.1]
  -- `δ' → 0⁺`
  have hdp0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < dpf δ := by
    filter_upwards [hpos] with δ h; exact div_pos h.1 (by positivity)
  have hdp1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), dpf δ ≤ δ ^ (1 - κ) := by
    filter_upwards [hpos, hmf'] with δ h1 h2
    have hk := Real.rpow_pos_of_pos h1.1 κ
    have hl : 1 ≤ Real.exp (lamf δ) := Real.one_le_exp (by positivity)
    have hden : δ ^ κ ≤ (1 / 2 : ℝ) ^ mf δ * Real.exp (lamf δ) := by
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (mf δ)]
    calc dpf δ ≤ δ / δ ^ κ := div_le_div_of_nonneg_left h1.1.le hk hden
      _ = δ ^ (1 - κ) := by rw [Real.rpow_sub h1.1, Real.rpow_one]
  have hT3 : Tendsto dpf (𝓝[>] (0 : ℝ)) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hdp0⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_rpow_nhdsGT_zero (by linarith)) (hdp0.mono fun _ h => h.le) hdp1
  -- the threshold: `δ'^{−(χ+ι/2)} ≤ N` and `40 N ≤ δ^{−(χ−ι)}`
  set qe := ι / (2 * κ)
  have hq : 0 < qe := by positivity
  have hcost : ∀ᶠ δ in 𝓝[>] (0 : ℝ), (80 : ℝ) ^ (χ + ι / 2) *
      Real.exp ((χ + ι / 2) * ((mf δ : ℝ) + 1) ^ (3 / 4 : ℝ) - Real.log 2 * qe * mf δ) ≤ 1 / 80 := by
    have h := ((tendsto_exp_rpow34_sub (χ + ι / 2)
      (mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hq)).const_mul
      ((80 : ℝ) ^ (χ + ι / 2))).comp hT1
    rw [mul_zero] at h
    exact h.eventually (eventually_le_nhds (by norm_num))
  have hbig : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 80 ≤ δ ^ (-(χ - ι)) := by
    filter_upwards [hpos, tendsto_rpow_nhdsGT_zero hχι (Iio_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 80))] with δ h1 h2
    rw [Real.rpow_neg h1.1.le]
    have h3 : 0 < δ ^ (χ - ι) := Real.rpow_pos_of_pos h1.1 _
    rw [le_inv_comm₀ (by norm_num) h3]
    exact (show δ ^ (χ - ι) < 1 / 80 from h2).le.trans (by norm_num)
  have hthr : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ENNReal.ofReal (dpf δ ^ (-(χ + ι / 2))) ≤ (Nf δ : ℝ≥0∞) := by
    filter_upwards [hpos, hmf', hcost, hbig] with δ h1 h2 h3 h4
    have hs2 : (1 / 2 : ℝ) ^ mf δ < 80 * δ ^ κ := by
      have := h2.1; rw [pow_succ] at this; linarith
    have hsq : ((1 / 2 : ℝ) ^ mf δ) ^ qe = Real.exp (-(Real.log 2 * qe * mf δ)) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, one_div, Real.log_inv]
      congr 1; ring
    have hsmall : (80 : ℝ) ^ (χ + ι / 2) * Real.exp ((χ + ι / 2) * lamf δ) *
        ((1 / 2 : ℝ) ^ mf δ) ^ (ι / (2 * κ)) ≤ 1 / 80 := by
      rw [hsq, mul_assoc, ← Real.exp_add]
      simp only [lamf]
      rw [show (χ + ι / 2) * ((mf δ : ℝ) + 1) ^ (3 / 4 : ℝ) + -(Real.log 2 * qe * mf δ) =
        (χ + ι / 2) * ((mf δ : ℝ) + 1) ^ (3 / 4 : ℝ) - Real.log 2 * qe * mf δ by ring]
      exact h3
    have ha := glue_arith hι hκ hκχ h1.1 h1.2.le h2.2 hs2 hsmall h4
    rw [← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Nat.lt_floor_add_one (δ ^ (-(χ - ι)) / 40)
    simp only [dpf, Nf]
    linarith
  have hN40 : ∀ δ : ℝ, 0 < δ →
      (((40 * Nf δ : ℕ) : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(χ - ι))) := by
    intro δ hδ
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast]
    refine ENNReal.ofReal_le_ofReal ?_
    have := Nat.floor_le (div_nonneg (Real.rpow_nonneg hδ.le (-(χ - ι))) (by norm_num : (0 : ℝ) ≤ 40))
    push_cast
    simp only [Nf]
    linarith
  -- the per-scale bound
  set ε0 : ℝ := min (1 / 1000) ((1 - α) / 400)
  have hε0 : 0 < ε0 := lt_min (by norm_num) (by linarith)
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), P {ω | ¬ ((lgdMinSet (dzzMuIn γ W ω) δ {v δ}
      (frontier (sqBox u (1 / 20))) : ℝ≥0∞) ≤
      (lgdMinSet (dzzMuIn γ W ω) δ (L δ) (frontier (sqBox u (1 / 20))) : ℝ≥0∞) +
        ENNReal.ofReal (δ ^ (-(χ - ι))))} ≤
      40 * (ENNReal.ofReal (C * Real.exp (-lamf δ ^ 2 / (C * (mf δ + 1)))) + G (dpf δ)) := by
    filter_upwards [hpos, hmf', hthr, hLv, hsmallk ε0 hε0] with δ h1 h2 h3 h4 h5
    set m := mf δ
    set d : ℝ := (1 / 2 : ℝ) ^ m / 40 with hd_def
    have hd : 0 < d := by positivity
    have hmd : (1 / 2 : ℝ) ^ m = 40 * d := by rw [hd_def]; ring
    have hdk : δ ^ κ ≤ d := by rw [hd_def]; linarith [h2.2]
    have hd2 : d < 2 * ε0 := by
      have := h2.1; rw [pow_succ] at this
      rw [hd_def]; nlinarith
    have hd3 : d < 2 / 1000 := hd2.trans_le (by linarith [min_le_left (1 / 1000 : ℝ) ((1 - α) / 400)])
    have hd4 : 4 * d ≤ (1 - α) / 40 := by
      have := min_le_right (1 / 1000 : ℝ) ((1 - α) / 400); linarith
    obtain ⟨hL, hvL⟩ := h4
    have hvbox : v δ ∈ sqBox u (α / 20) := (isClosed_sqBox u _).frontier_subset (hL.1 hvL)
    obtain ⟨hvr, hvi⟩ := hvbox
    obtain ⟨hur, hui⟩ := near_of_mem_dzzVbar hu
    have hv' : ∀ z, ‖z - v δ‖ ≤ 17 * d → z ∈ dzzVXi ξ := by
      intro z hz
      have e1 := (Complex.abs_re_le_norm (z - v δ)).trans hz
      have e2 := (Complex.abs_im_le_norm (z - v δ)).trans hz
      rw [Complex.sub_re] at e1
      rw [Complex.sub_im] at e2
      refine mem_dzzVXi_of_near (a := 1 / 10) ?_ ?_ (by linarith) hξ.le
      · have := abs_sub_le z.re (v δ).re (1 / 2)
        have := abs_sub_le (v δ).re u.re (1 / 2)
        linarith
      · have := abs_sub_le z.im (v δ).im (1 / 2)
        have := abs_sub_le (v δ).im u.im (1 / 2)
        linarith
    have hx' : ∀ x ∈ L δ, |x.re - (v δ).re| ≤ 2 * d ∧ |x.im - (v δ).im| ≤ 2 * d := by
      intro x hx
      obtain ⟨s, t, y, hLe, -, hst⟩ := hL.2
      rcases hLe with hLe | hLe
      · rw [hLe, Complex.mem_reProdIm] at hx hvL
        obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
        obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hvL
        rw [mem_singleton_iff] at hx3 hv3
        refine ⟨abs_sub_le_iff.2 ⟨by linarith, by linarith⟩, ?_⟩
        rw [hx3, hv3, sub_self, abs_zero]; positivity
      · rw [hLe, Complex.mem_reProdIm] at hx hvL
        obtain ⟨hx3, ⟨hx1, hx2⟩⟩ := hx
        obtain ⟨hv3, ⟨hv1, hv2⟩⟩ := hvL
        rw [mem_singleton_iff] at hx3 hv3
        refine ⟨?_, abs_sub_le_iff.2 ⟨by linarith, by linarith⟩⟩
        rw [hx3, hv3, sub_self, abs_zero]; positivity
    have hy' : ∀ y ∈ frontier (sqBox u (1 / 20)),
        4 * d ≤ |y.re - (v δ).re| ∨ 4 * d ≤ |y.im - (v δ).im| := by
      intro y hy
      rcases edge_of_mem_frontier_sqBox' (by norm_num : (0 : ℝ) < 1 / 20) hy with h | h
      · left
        have := abs_sub_abs_le_abs_sub (y.re - u.re) ((v δ).re - u.re)
        rw [show y.re - u.re - ((v δ).re - u.re) = y.re - (v δ).re by ring] at this
        linarith
      · right
        have := abs_sub_abs_le_abs_sub (y.im - u.im) ((v δ).im - u.im)
        rw [show y.im - u.im - ((v δ).im - u.im) = y.im - (v δ).im by ring] at this
        linarith
    have hP := hpair m d hd hmd (v δ) hv' (lamf δ) δ (by positivity) h1.1 (Nf δ)
    refine le_trans (measure_mono (t := {ω | ¬ ∀ j : Fin 5, PairsOK (dzzMuIn γ W ω) δ (Nf δ)
      (ringC (v δ) d j) (ringW d j)}) ?_) (hP.trans ?_)
    · intro ω hω hall
      apply hω
      have key : lgdMinSet (dzzMuIn γ W ω) δ {v δ} (frontier (sqBox u (1 / 20))) ≤
          lgdMinSet (dzzMuIn γ W ω) δ (L δ) (frontier (sqBox u (1 / 20))) +
            ((40 * Nf δ : ℕ) : ℕ∞) := by
        unfold lgdMinSet
        simp only [ENat.iInf_add]
        refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
        refine (iInf₂_le (v δ) (mem_singleton _)).trans ((iInf₂_le y hy).trans ?_)
        exact ring_glue_lgd hd hall (hx' x hx) (hy' y hy)
      refine (ENat.toENNReal_le.2 key).trans ?_
      rw [ENat.toENNReal_add]
      exact add_le_add le_rfl (hN40 δ h1.1)
    · gcongr
      refine measure_mono fun ω hω hle => hω (hle.trans h3)
  -- the limit
  have a1 : Tendsto (fun δ => ENNReal.ofReal (C * Real.exp (-lamf δ ^ 2 / (C * (mf δ + 1)))))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp ((tendsto_scaleTail hC).comp hT1)
  have a2 : Tendsto (fun δ => G (dpf δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := hT.comp hT3
  have hF := ENNReal.Tendsto.const_mul (a1.add a2) (Or.inr (by norm_num : (40 : ℝ≥0∞) ≠ ⊤))
  rw [add_zero, mul_zero] at hF
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF
    (Eventually.of_forall fun _ => zero_le) hbound

/-- `dzzL61GlueK_of_scale` with the coupling discharged by `dzzSimCoupleScale_of` (S5D125C). -/
theorem dzzL61GlueK_of_lem53 {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {α χ ι κ ξ : ℝ} (hα1 : α < 1) (hι : 0 < ι) (hκ : 0 < κ)
    (hκχ : 2 * ι ≤ κ * χ) (hκ1 : κ < 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    {u : ℂ} (hu : u ∈ dzzVbar)
    (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
      (tildeBox ringU₀ ringV₀) ξ)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω)) δ ringU₀ ringV₀ < ⊤) :
    DZZL61GlueK P (dzzMuIn γ W) α χ u ι κ := by
  have hK : tildeBox ringU₀ ringV₀ ⊆ dzzVXi ξ := fun z hz => by
    have h := tildeBox_subset_dzzVXi ringU₀_mem_dzzVbar ringV₀_mem_dzzVbar ringU₀_ne_ringV₀ hz
    exact ⟨h.1, le_trans (by linarith) h.2⟩
  exact dzzL61GlueK_of_scale hW hγ hγ2 hα1 hι hκ hκχ hκ1 hξ hξ1 hu
    (dzzSimCoupleScale_of hγ hγ2 hξ (by linarith) (isClosed_tildeBox _ _) hK) hL53 h317 hfin

end DZZ
end LQGMetric
