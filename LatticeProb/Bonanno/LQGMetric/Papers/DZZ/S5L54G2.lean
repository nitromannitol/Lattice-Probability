/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54G2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61H3

/-!
# D117 P-54C (2): the 40 crossings of a ring around a moving centre, w.p. → 1 (P2-DZZ54C)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2562–2568 ("each of the four
rectangle crossings can be formed by a constant number of point to point geodesics"; "by
(eq-delta_0) and a similar scaling argument as in the proof of (eq-z-open) we have that with
probability tending to 1 … `D̃(x,y) ≤ δ^{−χ+ι}` for all such `(x,y)`").

`ring_pairs_whp` is the probabilistic half of `dzzL61GlueK_of_scale` (S6L61H3, P2-DZZ125),
copied and cut at the event `∀ j, PairsOK …` (near-miss adaptation (c) of AGENT_GUIDE: the
original proves the L6.1 gluing inequality directly), with a bound uniform over the centres
`c` with `|c − (1/2 + i/2)|_∞ ≤ 1/20`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

/-- the 40 tilde distances of the ring of centre `c` at some scale `d ∈ [δ^κ, 1/1000)` are
`≤ N` with `40 N ≤ δ^{−e}` -/
def RingOK (μ : Measure ℂ) (δ κ e : ℝ) (c : ℂ) : Prop :=
  ∃ d : ℝ, δ ^ κ ≤ d ∧ d < 1 / 1000 ∧ ∃ N : ℕ, ((40 * N : ℕ) : ℝ) ≤ δ ^ (-e) ∧
    ∀ j : Fin 5, PairsOK μ δ N (ringC c d j) (ringW d j)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **the ring crossings w.p. → 1, uniformly in the centre** (DZZ l. 2566–2568; the proof of
`dzzL61GlueK_of_scale`, S6L61H3). -/
theorem ring_pairs_whp {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {χ ι κ ξ : ℝ} (hι : 0 < ι) (hκ : 0 < κ)
    (hκχ : 2 * ι ≤ κ * χ) (hκ1 : κ < 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1 / 80)
    (hsc : DZZSimCoupleScale γ ξ (tildeBox ringU₀ ringV₀))
    (hL53 : DZZLem53Exp P (dzzMuIn γ W) χ)
    (h317 : DZZProp317In P (fun ω => dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω))
      (tildeBox ringU₀ ringV₀) ξ)
    (hfin : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ ω ∂P,
      lgdDZZ (dzzWall (tildeBox ringU₀ ringV₀) (dzzMuIn γ W ω)) δ ringU₀ ringV₀ < ⊤) :
    ∃ f : ℝ → ℝ≥0∞, Tendsto f (𝓝[>] 0) (𝓝 0) ∧ ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ c : ℂ,
      |c.re - 1 / 2| ≤ 1 / 20 → |c.im - 1 / 2| ≤ 1 / 20 →
      P {ω | ¬ RingOK (dzzMuIn γ W ω) δ κ (χ - ι) c} ≤ f δ := by
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
  have hN40' : ∀ δ : ℝ, 0 < δ → ((40 * Nf δ : ℕ) : ℝ) ≤ δ ^ (-(χ - ι)) := by
    intro δ hδ
    have := Nat.floor_le (div_nonneg (Real.rpow_nonneg hδ.le (-(χ - ι))) (by norm_num : (0 : ℝ) ≤ 40))
    push_cast
    simp only [Nf]
    linarith
  -- the per-scale bound
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ c : ℂ, |c.re - 1 / 2| ≤ 1 / 20 → |c.im - 1 / 2| ≤ 1 / 20 →
      P {ω | ¬ RingOK (dzzMuIn γ W ω) δ κ (χ - ι) c} ≤
      40 * (ENNReal.ofReal (C * Real.exp (-lamf δ ^ 2 / (C * (mf δ + 1)))) + G (dpf δ)) := by
    filter_upwards [hpos, hmf', hthr, hsmallk (1 / 2000) (by norm_num)] with δ h1 h2 h3 h5 c hcr hci
    set m := mf δ
    set d : ℝ := (1 / 2 : ℝ) ^ m / 40 with hd_def
    have hd : 0 < d := by positivity
    have hmd : (1 / 2 : ℝ) ^ m = 40 * d := by rw [hd_def]; ring
    have hdk : δ ^ κ ≤ d := by rw [hd_def]; linarith [h2.2]
    have hd2 : d < 1 / 1000 := by
      have := h2.1; rw [pow_succ] at this
      rw [hd_def]; nlinarith
    have hv' : ∀ z, ‖z - c‖ ≤ 17 * d → z ∈ dzzVXi ξ := by
      intro z hz
      have e1 := (Complex.abs_re_le_norm (z - c)).trans hz
      have e2 := (Complex.abs_im_le_norm (z - c)).trans hz
      rw [Complex.sub_re] at e1
      rw [Complex.sub_im] at e2
      refine mem_dzzVXi_of_near (a := 1 / 10) ?_ ?_ (by linarith) hξ.le
      · have := abs_sub_le z.re c.re (1 / 2)
        linarith
      · have := abs_sub_le z.im c.im (1 / 2)
        linarith
    have hP := hpair m d hd hmd c hv' (lamf δ) δ (by positivity) h1.1 (Nf δ)
    refine le_trans (measure_mono (t := {ω | ¬ ∀ j : Fin 5, PairsOK (dzzMuIn γ W ω) δ (Nf δ)
      (ringC c d j) (ringW d j)}) ?_) (hP.trans ?_)
    · intro ω hω hall
      exact hω ⟨d, hdk, hd2, Nf δ, hN40' δ h1.1, hall⟩
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
  exact ⟨_, hF, hbound⟩

end DZZ
end LQGMetric
