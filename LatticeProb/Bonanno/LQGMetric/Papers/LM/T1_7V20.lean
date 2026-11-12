/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V20 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V13
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V16
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V18
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7V19

/-!
# LM Theorem 1.7: proof of the per-measure node `T17VarG` (limit `ε → 0`, D107 §3(v))

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1000–1089), repaired by decision D107
(`decisions/DEC-107.md` §3(i)–(v)): for each mesh `ε_j = 1/(j+1)`, Efron–Stein averaged over the
grid shift (`t17v_es_avg`), the per-metric product bound (`t17v_perD`) for the pointwise limit and
the mesh-uniform bound (`t17v_perD₂`) for domination (`t17v_int_ES_le`), reverse Fatou
(`t17v_fatou`), and `κ → 0`. Consequently `lmThm1_7 : LMThm1_7` and `lmCor1_8 : Blueprint.LMCor1_8`
hold unconditionally.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.LM

/-- `ε³ #𝒮 ≤ ε (2R + 5ε)²` -/
lemma t17v_eps_card {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    ε ^ 3 * (t17Box ε R).card ≤ ε * (2 * R + 5 * ε) ^ 2 := by
  rw [t17v_card_box]
  have hc0 : (0 : ℤ) ≤ ⌈R / ε⌉ := Int.ceil_nonneg (div_nonneg hR hε.le)
  have ht : (((2 * ⌈R / ε⌉ + 3).toNat : ℕ) : ℝ) = 2 * (⌈R / ε⌉ : ℝ) + 3 := by
    have h3 : (0 : ℤ) ≤ 2 * ⌈R / ε⌉ + 3 := by omega
    have : (((2 * ⌈R / ε⌉ + 3).toNat : ℕ) : ℤ) = 2 * ⌈R / ε⌉ + 3 := Int.toNat_of_nonneg h3
    exact_mod_cast this
  rw [ht]
  have h1 : (⌈R / ε⌉ : ℝ) ≤ R / ε + 1 := (Int.ceil_lt_add_one _).le
  have h0 : (0 : ℝ) ≤ ⌈R / ε⌉ := by exact_mod_cast hc0
  have h2 : ε * (⌈R / ε⌉ : ℝ) ≤ R + ε := by
    have := mul_le_mul_of_nonneg_left h1 hε.le
    rwa [mul_add, mul_div_cancel₀ R hε.ne', mul_one] at this
  have h4 : ε * (2 * (⌈R / ε⌉ : ℝ) + 3) ≤ 2 * R + 5 * ε := by nlinarith
  have h5 : 0 ≤ ε * (2 * (⌈R / ε⌉ : ℝ) + 3) := by positivity
  calc ε ^ 3 * (2 * (⌈R / ε⌉ : ℝ) + 3) ^ 2 = ε * (ε * (2 * (⌈R / ε⌉ : ℝ) + 3)) ^ 2 := by ring
    _ ≤ ε * (2 * R + 5 * ε) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h5 h4 2) hε.le

/-- **the per-measure node holds** -/
theorem t17VarG : T17VarG := by
  intro ν _ hL C hC1 hcopy z w n hz hw hprod
  have hC0 : 0 < C := zero_lt_one.trans hC1
  set R : ℝ := (n : ℝ) + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set εj : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1) with hεjdef
  have hεj : ∀ j, 0 < εj j := fun j => by positivity
  have hεj1 : ∀ j, εj j ≤ 1 := fun j => by
    simp only [hεjdef]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hz1 : ‖z‖ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hw1 : ‖w‖ < ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hmR : ((n + 1 : ℕ) : ℝ) ≤ R := by push_cast; rfl
  set F : ContMetric → ℝ := fun d => (t17F (n + 1) z w d).toReal with hFdef
  set F₀ : ContMetric → ℝ := fun d => (t17F n z w d).toReal with hF₀def
  have hFm : Measurable F := (measurable_t17F (n + 1) z w).ennreal_toReal
  have hF₀m : Measurable F₀ := (measurable_t17F n z w).ennreal_toReal
  have hF2 := t17v_memLp_F ν hL hC0 hcopy hz1 hw1
  -- the data for each mesh
  have hdata := fun j => t17v_es_avg ν hL hC0.le hcopy hmR hz1 hw1 (hεj j) (hprod j) hF2
  choose Φ hΦ hΦF K hK hslice hvar using hdata
  set G : ℕ → ContMetric → ℝ≥0∞ := fun j d => ∫⁻ θ, t17ES (εj j) R F (Φ j) ν θ d ∂t17Λ
  have hGm : ∀ j, Measurable (G j) := fun j =>
    (t17v_measurable_ES (εj j) R hFm (hΦ j) ν).lintegral_prod_left'
  have hint : ∀ j, ∀ᵐ d ∂ν, ∀ Γ : ℝ, (∀ᵐ θ ∂(volume : Measure (ℝ × ℝ)), θ.1 ∈ Icc (0 : ℝ) 1 →
        θ.2 ∈ Icc (0 : ℝ) 1 → ∃ b : t17Box (εj j) R → ℝ, (∀ k, 0 ≤ b k) ∧
          (∀ (k : t17Box (εj j) R) (d'' : ContMetric),
            T17Compat C (εj j) θ (t17Box (εj j) R) d d'' k →
            max (F d'' - F d) 0 ^ 2 ≤ b k) ∧ ∑ k, b k ≤ Γ) →
      G j d ≤ ENNReal.ofReal Γ := fun j => by
    have := hK j
    exact t17v_int_ES_le ν hL hC0.le hcopy hFm (hΦ j) (K j) (hslice j) (hΦF j) (hprod j)
  -- bounds on `F`, `F₀`
  obtain ⟨B, hB⟩ := t17v_F_bdd ν hL hC0 hcopy hz1 hw1
  obtain ⟨B₀, hB₀⟩ := t17v_F_bdd ν hL hC0 hcopy hz hw
  set B' := (ENNReal.ofReal B).toReal
  set B₀' := (ENNReal.ofReal B₀).toReal
  have hFB : ∀ᵐ d ∂ν, 0 ≤ F d ∧ F d ≤ B' := by
    filter_upwards [hB] with d hd
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1⟩
  have hF₀B : ∀ᵐ d ∂ν, F d ≤ F₀ d ∧ F₀ d ≤ B₀' := by
    filter_upwards [hB₀, hL] with d hd hdl
    exact ⟨ENNReal.toReal_mono hd.2 (t17_chainInf_succ_le hdl n z w),
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hd.1⟩
  -- domination
  set Dc : ℝ := (C ^ 2 - 1) * B' * (C ^ 2 * (B' + 1) + (2 * R + 5) ^ 2)
  have hGD : ∀ j, G j ≤ᵐ[ν] fun _ => ENNReal.ofReal Dc := by
    intro j
    filter_upwards [hint j, hL, hFB] with d hd hdl hdB
    refine (hd _ (t17v_perD₂ hdl hC1.le hz hw (hεj j))).trans (ENNReal.ofReal_le_ofReal ?_)
    have hc : 0 ≤ C ^ 2 - 1 := by nlinarith
    have he3 : εj j ^ 3 ≤ 1 := pow_le_one₀ (hεj j).le (hεj1 j)
    have hcard := t17v_eps_card (hεj j) hR0
    have hcard' : εj j * (2 * R + 5 * εj j) ^ 2 ≤ (2 * R + 5) ^ 2 := by
      have h1 : 2 * R + 5 * εj j ≤ 2 * R + 5 := by linarith [hεj1 j]
      have h2 : (2 * R + 5 * εj j) ^ 2 ≤ (2 * R + 5) ^ 2 :=
        pow_le_pow_left₀ (by linarith [hεj j]) h1 2
      have h3 : 0 ≤ (2 * R + 5 * εj j) ^ 2 := sq_nonneg _
      nlinarith [hεj j, hεj1 j]
    have hb1 : 0 ≤ (C ^ 2 - 1) * F d := mul_nonneg hc hdB.1
    have hb2 : C ^ 2 * (F d + εj j ^ 3) + εj j ^ 3 * (t17Box (εj j) R).card ≤
        C ^ 2 * (B' + 1) + (2 * R + 5) ^ 2 := by
      have : C ^ 2 * (F d + εj j ^ 3) ≤ C ^ 2 * (B' + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [hdB.2]) (sq_nonneg C)
      linarith
    have hb3 : 0 ≤ C ^ 2 * (F d + εj j ^ 3) + εj j ^ 3 * (t17Box (εj j) R).card := by
      have : 0 ≤ εj j ^ 3 := by positivity
      positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hdB.2 hc) hb2 hb3
      (mul_nonneg hc (hdB.1.trans hdB.2))
  -- the pointwise limit
  have hε0 : Tendsto εj atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε3 : Tendsto (fun j => εj j ^ 3) atTop (𝓝 0) := by simpa using hε0.pow 3
  have hcard0 : Tendsto (fun j => εj j ^ 3 * ((t17Box (εj j) R).card : ℝ)) atTop (𝓝 0) := by
    have hup : Tendsto (fun j => εj j * (2 * R + 5 * εj j) ^ 2) atTop (𝓝 0) := by
      have := hε0.mul ((tendsto_const_nhds (x := 2 * R)).add (hε0.const_mul 5) |>.pow 2)
      simpa using this
    exact squeeze_zero (fun j => by have := hεj j; positivity)
      (fun j => t17v_eps_card (hεj j) hR0) hup
  have hH : ∀ᵐ d ∂ν, limsup (fun j => G j d) atTop ≤
      ENNReal.ofReal (C ^ 4 * ((F₀ d - F d) * F d)) := by
    filter_upwards [ae_all_iff.2 hint, hL] with d hd hdl
    have hκ : ∀ i : ℕ, limsup (fun j => G j d) atTop ≤
        ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d)) := by
      intro i
      obtain ⟨ε₀, hε₀, hP⟩ := t17v_perD hdl hC1.le hz hw (κ := 1 / ((i : ℝ) + 1)) (by positivity)
      set Γ : ℕ → ℝ := fun j => C ^ 2 * (F₀ d - F d + εj j ^ 3 + 1 / ((i : ℝ) + 1)) *
        (C ^ 2 * (F d + εj j ^ 3) + εj j ^ 3 * (t17Box (εj j) R).card) with hΓdef
      have hΓ : Tendsto Γ atTop
          (𝓝 (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d))) := by
        have h1 := ((tendsto_const_nhds (x := F₀ d - F d)).add hε3).add
          (tendsto_const_nhds (x := 1 / ((i : ℝ) + 1)))
        have h2 := (tendsto_const_nhds (x := F d)).add hε3
        have := (h1.const_mul (C ^ 2)).mul ((h2.const_mul (C ^ 2)).add hcard0)
        rw [show C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d) =
          C ^ 2 * (F₀ d - F d + 0 + 1 / ((i : ℝ) + 1)) * (C ^ 2 * (F d + 0) + 0) by ring]
        exact this
      have hev : ∀ᶠ j in atTop, G j d ≤ ENNReal.ofReal (Γ j) := by
        have hεe : ∀ᶠ j in atTop, εj j < ε₀ := (tendsto_order.1 hε0).2 ε₀ hε₀
        filter_upwards [hεe] with j hj
        exact hd j _ (hP (εj j) (hεj j) hj)
      calc limsup (fun j => G j d) atTop ≤ limsup (fun j => ENNReal.ofReal (Γ j)) atTop :=
            limsup_le_limsup hev (by isBoundedDefault) (by isBoundedDefault)
        _ = ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d)) :=
            ((ENNReal.continuous_ofReal.tendsto _).comp hΓ).limsup_eq
    have hlim : Tendsto (fun i : ℕ =>
        ENNReal.ofReal (C ^ 2 * (F₀ d - F d + 1 / ((i : ℝ) + 1)) * (C ^ 2 * F d))) atTop
        (𝓝 (ENNReal.ofReal (C ^ 4 * ((F₀ d - F d) * F d)))) := by
      have h1 := (tendsto_const_nhds (x := F₀ d - F d)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have h2 := (ENNReal.continuous_ofReal.tendsto _).comp
        ((h1.const_mul (C ^ 2)).mul_const (C ^ 2 * F d))
      have e : C ^ 2 * (F₀ d - F d + 0) * (C ^ 2 * F d) = C ^ 4 * ((F₀ d - F d) * F d) := by ring
      rw [e] at h2
      exact h2
    exact ge_of_tendsto' hlim hκ
  -- reverse Fatou and the real form
  have hDfin : ∫⁻ _, ENNReal.ofReal Dc ∂ν ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hmain := t17v_fatou hGm hDfin hGD hvar hH
  have hbd : ∀ᵐ d ∂ν, 0 ≤ C ^ 4 * ((F₀ d - F d) * F d) ∧
      C ^ 4 * ((F₀ d - F d) * F d) ≤ C ^ 4 * (B₀' * B') := by
    filter_upwards [hFB, hF₀B] with d h1 h2
    have hC4 : 0 ≤ C ^ 4 := by positivity
    refine ⟨mul_nonneg hC4 (mul_nonneg (by linarith) h1.1), mul_le_mul_of_nonneg_left ?_ hC4⟩
    exact mul_le_mul (by linarith) h1.2 h1.1 (by linarith)
  have hI : Integrable (fun d => C ^ 4 * ((F₀ d - F d) * F d)) ν := by
    refine Integrable.of_bound ((measurable_const.mul ((hF₀m.sub hFm).mul hFm)).aestronglyMeasurable)
      (C ^ 4 * (B₀' * B')) ?_
    filter_upwards [hbd] with d hd
    rw [Real.norm_eq_abs, abs_of_nonneg hd.1]
    exact hd.2
  have hnn : 0 ≤ᵐ[ν] fun d => C ^ 4 * ((F₀ d - F d) * F d) := hbd.mono fun d hd => hd.1
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn,
    ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hnn), integral_const_mul] at hmain
  exact hmain

/-- **LM Corollary 1.8** (`cor-bilip-msrble`, l. 317–332) -/
theorem lmCor1_8 : Blueprint.LMCor1_8 := lmCor1_8_of_varG t17VarG

end LQGMetric.LM
