/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Lemma35 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Exist.CrudeBounds

/-!
# DGZ Lemma 3.5, uniform version (packet P-X5b, target T4)

Source: DGZ arXiv:2310.03996, Lemma 3.5 (with (3.6), (3.7)); planning audit HA5, Details D5 and
finding G5 (uniformity in `n > m ≥ 1`), D3 (quantiles: only `P[D ≤ q_p] ≥ p` and `P[D < q_p] ≤ p`
are used, never continuity of the law, G6).

Notation (HA5): `h_n = H_{2^{-n},1}`, `D_n = D^ξ(h_n)` (`lfppDistance d ξ`), `a^{(p)}_n` the lower
`p`-quantile of the law of `D_n` (`LQGMetric.lowerQuantile`).

**Statement** (`lemma35`). For `ξ > 0` and `p ∈ (0,1)` there is `C_p`, depending only on `κ`, `d`,
`ξ` and `p`, such that for all `n > m ≥ 1`
`e^{-C_p √(mn)} a^{(p)}_{n-m} ≤ a^{(p)}_n ≤ e^{C_p √(mn)} a^{(p)}_{n-m}`,
where `a^{(p)}_n` and `a^{(p)}_{n-m}` may be computed over two different white noises (on different
probability spaces), so the statement does not depend on the realization. `lemma35_log` is the
logarithmic form `|log a^{(p)}_n - log a^{(p)}_{n-m}| ≤ C_p √(mn)`, and
`IsBandVersion.lowerQuantile_lfppDistance_eq` records that `a^{(p)}` itself does not depend on the
realization (law transfer).

**Proof** (HA5 D5). On the probability space of `h_n = H`, take a continuous version `Y` of
`h_{n-m}`; then `B = H - Y` is a continuous version of `h_{n-m,n} = H_{2^{-n},2^{-(n-m)}}`
(`SupB.sub_isBandVersion`). By law transfer (`IsBandVersion.map_lfppDistance_eq`), `D^ξ(Y)` has the
law of `D_{n-m}` over any white noise. With `M = t √(mn)`, on the event `sup_{[-2,2]^d} |B| < M`
the weight comparison gives `e^{-ξM} D^ξ(Y) ≤ D^ξ(H) ≤ e^{ξM} D^ξ(Y)`. By Lemma 3.4′
(`lemma34'_small_exists`) fix `t` with `P*(sup |B| ≥ t √(mn)) ≤ δ := min(p, 1-p)/4` for all
`n > m ≥ 1`. Then (generic quantile transfers `L35.lowerQuantile_le_mul_of_le_mul`,
`L35.mul_lowerQuantile_le_of_mul_le`):

* upper: `a^{(p)}_n ≤ e^{ξM} q_{(1+p)/2}(D^ξ(Y))`, since `(1+p)/2 - δ ≥ p`;
* lower: `a^{(p)}_n ≥ e^{-ξM} q_{p/2}(D^ξ(Y))`, since `p/2 + δ < p`;

and DGZ Lemma 3.2 (`IsBandVersion.lowerQuantile_lfppDistance_le_exp_mul`, packet P-X5) compares
`q_{(1+p)/2}` and `q_{p/2}` with `q_p` within `e^{c ξ √((n-m) log 2)}`. Finally
`√(n - m) ≤ √(mn)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Real
open scoped ENNReal

namespace HigherDimLFPP

namespace L35

/-! ### Transfer of quantiles along a coupling -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Upper quantile transfer**: if `D₁ ≤ c D₂` outside a set `Bad` with `P*(Bad) ≤ δ`, and
`p + δ ≤ p₂`, then `q_p(D₁) ≤ c q_{p₂}(D₂)`. -/
theorem lowerQuantile_le_mul_of_le_mul [IsProbabilityMeasure P] {D₁ D₂ : Ω → ℝ}
    (h₁ : AEMeasurable D₁ P) (h₂ : AEMeasurable D₂ P) {c : ℝ} (hc : 0 ≤ c) {Bad : Set Ω}
    {δ : ℝ≥0∞} (hBad : P Bad ≤ δ) (hG : ∀ ω, ω ∉ Bad → D₁ ω ≤ c * D₂ ω) {p p₂ : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) (hp₂0 : 0 < p₂) (hp₂1 : p₂ < 1) (hlev : p + δ ≤ p₂) :
    LQGMetric.lowerQuantile (P.map D₁) p ≤ c * LQGMetric.lowerQuantile (P.map D₂) p₂ := by
  set b := LQGMetric.lowerQuantile (P.map D₂) p₂ with hb_def
  have hb : p₂ ≤ (P.map D₂) (Iic b) :=
    (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp₂0 hp₂1).2 le_rfl
  rw [Measure.map_apply_of_aemeasurable h₂ measurableSet_Iic] at hb
  have hsub : D₂ ⁻¹' Iic b ⊆ D₁ ⁻¹' Iic (c * b) ∪ Bad := fun ω hω => by
    by_cases hω' : ω ∈ Bad
    · exact Or.inr hω'
    · exact Or.inl ((hG ω hω').trans (mul_le_mul_of_nonneg_left hω hc))
  have h3 : p₂ ≤ P (D₁ ⁻¹' Iic (c * b)) + δ :=
    hb.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hBad)))
  have hδtop : δ ≠ ⊤ := by
    have : δ ≤ p₂ := le_add_self.trans hlev
    exact (this.trans_lt (hp₂1.trans ENNReal.one_lt_top)).ne
  refine (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1).1 ?_
  rw [Measure.map_apply_of_aemeasurable h₁ measurableSet_Iic]
  exact ENNReal.le_of_add_le_add_right hδtop (hlev.trans h3)

/-- **Lower quantile transfer**: if `c D₂ ≤ D₁` outside a set `Bad` with `P*(Bad) ≤ δ`, `c > 0`
and `p₃ + δ < p`, then `c q_{p₃}(D₂) ≤ q_p(D₁)`. -/
theorem mul_lowerQuantile_le_of_mul_le [IsProbabilityMeasure P] {D₁ D₂ : Ω → ℝ}
    (h₁ : AEMeasurable D₁ P) (h₂ : AEMeasurable D₂ P) {c : ℝ} (hc : 0 < c) {Bad : Set Ω}
    {δ : ℝ≥0∞} (hBad : P Bad ≤ δ) (hG : ∀ ω, ω ∉ Bad → c * D₂ ω ≤ D₁ ω) {p p₃ : ℝ≥0∞}
    (hp0 : 0 < p) (hp1 : p < 1) (hp₃0 : 0 < p₃) (hp₃1 : p₃ < 1) (hlev : p₃ + δ < p) :
    c * LQGMetric.lowerQuantile (P.map D₂) p₃ ≤ LQGMetric.lowerQuantile (P.map D₁) p := by
  set b' := LQGMetric.lowerQuantile (P.map D₂) p₃ with hb'_def
  set q := LQGMetric.lowerQuantile (P.map D₁) p with hq_def
  by_contra hlt
  push Not at hlt
  have hq : p ≤ (P.map D₁) (Iic q) :=
    (LQGMetric.le_measure_Iic_iff_lowerQuantile_le hp0 hp1).2 le_rfl
  rw [Measure.map_apply_of_aemeasurable h₁ measurableSet_Iic] at hq
  have hb' : (P.map D₂) (Iio b') ≤ p₃ := by
    rw [LQGMetric.measure_Iio_eq_one_sub]
    have h := (LQGMetric.isQuantile_lowerQuantile (μ := P.map D₂) hp₃0 hp₃1).2
    calc 1 - (P.map D₂) (Ici b') ≤ 1 - (1 - p₃) := tsub_le_tsub_left h 1
      _ = p₃ := ENNReal.sub_sub_cancel ENNReal.one_ne_top hp₃1.le
  rw [Measure.map_apply_of_aemeasurable h₂ measurableSet_Iio] at hb'
  have hsub : D₁ ⁻¹' Iic q ⊆ D₂ ⁻¹' Iio b' ∪ Bad := fun ω hω => by
    by_cases hω' : ω ∈ Bad
    · exact Or.inr hω'
    · left
      have h1 := hG ω hω'
      have h2 : D₁ ω ≤ q := hω
      exact lt_of_mul_lt_mul_left (h1.trans_lt (h2.trans_lt hlt)) hc.le
  have h3 : p ≤ p₃ + δ :=
    hq.trans ((measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add hb' hBad)))
  exact absurd h3 (not_le.2 hlev)

end Transfer

/-! ### Levels -/

/-- The levels of the proof: for `r = p.toReal ∈ (0,1)` and `δ = min(r, 1-r)/4`,
`p + δ ≤ (1+r)/2` and `r/2 + δ < p`. -/
theorem levels {p : ℝ≥0∞} (hp1 : p < 1) {r δ : ℝ} (hr : r = p.toReal) (hr0 : 0 < r)
    (hr1 : r < 1) (hδ : δ = min r (1 - r) / 4) :
    p + ENNReal.ofReal δ ≤ ENNReal.ofReal ((1 + r) / 2) ∧
      ENNReal.ofReal (r / 2) + ENNReal.ofReal δ < p := by
  have hptop : p ≠ ⊤ := (hp1.trans ENNReal.one_lt_top).ne
  have hpr : p = ENNReal.ofReal r := by rw [hr, ENNReal.ofReal_toReal hptop]
  have hm0 : 0 ≤ min r (1 - r) := le_min hr0.le (by linarith)
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hδr : δ ≤ r / 4 := by
    rw [hδ]
    have := min_le_left r (1 - r)
    linarith
  have hδq : δ ≤ (1 - r) / 4 := by
    rw [hδ]
    have := min_le_right r (1 - r)
    linarith
  constructor
  · rw [hpr, ← ENNReal.ofReal_add hr0.le hδ0]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [hpr, ← ENNReal.ofReal_add (by positivity) hδ0]
    exact (ENNReal.ofReal_lt_ofReal_iff hr0).2 (by linarith)

/-- `√((n - m) log 2) ≤ √(mn) √(log 2)` for `m ≤ n`, `1 ≤ m`. -/
theorem sqrt_log_le {m n : ℕ} (hm : 1 ≤ m) :
    √(Real.log (1 / ((2 : ℝ) ^ (n - m))⁻¹)) ≤ √((m : ℝ) * n) * √(Real.log 2) := by
  rw [one_div, inv_inv, Real.log_pow, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right ?_ (Real.log_nonneg one_le_two))
  have h1 : ((n - m : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end L35

open L35 Conc

variable {d : ℕ}

/-- **Realization independence of the quantiles** (law transfer, HA5 A1-7): versions of the same
band field `H_{a,b}` over two white noises (possibly on different probability spaces) give the same
law of `D^ξ`, hence the same lower quantiles `a^{(p)}`. -/
theorem IsBandVersion.lowerQuantile_lfppDistance_eq {κ : Rd d → ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ} {a b : ℝ} {H : Rd d → Ω → ℝ}
    {H' : Rd d → Ω' → ℝ} (hH : IsBandVersion P W κ a b H) (hH' : IsBandVersion P' W' κ a b H')
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') (ξ : ℝ) (p : ℝ≥0∞) :
    LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p =
      LQGMetric.lowerQuantile (P'.map fun ω => lfppDistance d ξ (fun z => H' z ω)) p := by
  rw [hH.map_lfppDistance_eq hH' hW hW' ξ (measurable_lfppDistance_continuousMap ξ)]

/-- **DGZ Lemma 3.5, uniform version** (HA5 D5; finding G5). Let `ξ > 0` and `p ∈ (0,1)`. There
is `C ≥ 0`, depending only on `κ`, `d`, `ξ` and `p`, such that for all `n > m ≥ 1`, every white
noise `W` with a continuous version `H` of `h_n = H_{2^{-n},1}` and every white noise `W'` (possibly
on another probability space) with a continuous version `H'` of `h_{n-m} = H_{2^{-(n-m)},1}`,
`e^{-C√(mn)} a^{(p)}_{n-m} ≤ a^{(p)}_n ≤ e^{C√(mn)} a^{(p)}_{n-m}`, where `a^{(p)}_n` is the lower
`p`-quantile of the law of `D^ξ(H)` and `a^{(p)}_{n-m}` that of `D^ξ(H')`. -/
theorem lemma35 [NeZero d] {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ) {ξ : ℝ} (hξ : 0 < ξ)
    {p : ℝ≥0∞} (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
      {P' : Measure Ω'} {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}, IsWhiteNoise P W →
      IsWhiteNoise P' W' → ∀ {m n : ℕ}, 1 ≤ m → m < n →
        ∀ {H : Rd d → Ω → ℝ} {H' : Rd d → Ω' → ℝ},
          IsBandVersion P W κ ((2 : ℝ) ^ n)⁻¹ 1 H →
          IsBandVersion P' W' κ ((2 : ℝ) ^ (n - m))⁻¹ 1 H' →
          Real.exp (-(C * √((m : ℝ) * n))) *
              LQGMetric.lowerQuantile (P'.map fun ω => lfppDistance d ξ (fun z => H' z ω)) p ≤
            LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p ∧
          LQGMetric.lowerQuantile (P.map fun ω => lfppDistance d ξ (fun z => H z ω)) p ≤
            Real.exp (C * √((m : ℝ) * n)) *
              LQGMetric.lowerQuantile (P'.map fun ω => lfppDistance d ξ (fun z => H' z ω)) p := by
  -- levels and constants
  obtain ⟨hr0, hr1⟩ := Crude.toReal_mem_Ioo hp0 hp1
  set r : ℝ := p.toReal with hr
  set δ : ℝ := min r (1 - r) / 4 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min r (1 - r) := lt_min hr0 (by linarith)
    positivity
  obtain ⟨hup, hlow⟩ := levels hp1 hr hr0 hr1 hδ
  set p₂ : ℝ≥0∞ := ENNReal.ofReal ((1 + r) / 2) with hp₂
  set p₃ : ℝ≥0∞ := ENNReal.ofReal (r / 2) with hp₃
  have hp₂0 : 0 < p₂ := ENNReal.ofReal_pos.2 (by linarith)
  have hp₂1 : p₂ < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  have hp₃0 : 0 < p₃ := ENNReal.ofReal_pos.2 (by linarith)
  have hp₃1 : p₃ < 1 := ENNReal.ofReal_lt_one.2 (by linarith)
  obtain ⟨t, ht0, ht⟩ := lemma34'_small_exists hκ hδ0
  set c₂ : ℝ := quantileConst p.toReal + quantileConst p₂.toReal with hc₂
  set c₃ : ℝ := quantileConst p₃.toReal + quantileConst p.toReal with hc₃
  have hc₂0 : 0 ≤ c₂ := add_nonneg (quantileConst_nonneg _) (quantileConst_nonneg _)
  have hc₃0 : 0 ≤ c₃ := add_nonneg (quantileConst_nonneg _) (quantileConst_nonneg _)
  have hlog2 : 0 ≤ √(Real.log 2) := Real.sqrt_nonneg _
  refine ⟨ξ * t + (c₂ + c₃) * ξ * √(Real.log 2), by positivity, ?_⟩
  intro Ω Ω' _ _ P P' W W' hW hW' m n hm hmn H H' hH hH'
  have := hW.isProbabilityMeasure
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  -- the coarse field `Y` on `Ω` and the band `B = H - Y`
  obtain ⟨Y, hY⟩ := exists_isBandVersion (b := 1) hκ hW (dyadic_pos (n - m))
  have hle : ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ (n - m))⁻¹ := Crude.band_le m n
  have hc1 : ((2 : ℝ) ^ (n - m))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hB := SupB.sub_isBandVersion hκ hW (dyadic_pos n) hle hc1 hH hY
  set M : ℝ := t * √((m : ℝ) * n) with hM
  set Bad : Set Ω := {ω | ∃ z ∈ Osc.box (0 : Rd d) 2, M ≤ |H z ω - Y z ω|} with hBad_def
  have hBad : P Bad ≤ ENNReal.ofReal δ := ht hW hm hmn.le hB le_rfl
  -- the coupling on the good event
  set D : Ω → ℝ := fun ω => lfppDistance d ξ (fun z => H z ω) with hD
  set D' : Ω → ℝ := fun ω => lfppDistance d ξ (fun z => Y z ω) with hD'
  have hDm : AEMeasurable D P := (hH.measurable_lfppDistance ξ).aemeasurable
  have hD'm : AEMeasurable D' P := (hY.measurable_lfppDistance ξ).aemeasurable
  have hgood : ∀ ω, ω ∉ Bad → ∀ z ∈ cube d, |H z ω - Y z ω| ≤ M := fun ω hω z hz =>
    le_of_not_ge fun h => hω ⟨z, Osc.closure_cube_subset_box (subset_closure hz), h⟩
  have hup' : ∀ ω, ω ∉ Bad → D ω ≤ Real.exp (ξ * M) * D' ω := by
    intro ω hω
    have h := lfppDistOn_le_exp_mul (ζ := ξ) (x := 0) (y := e₁ d) (hH.continuous ω)
      (hY.continuous ω) (hgood ω hω)
    rwa [abs_of_pos hξ, ← lfppDistance_eq_lfppDistOn, ← lfppDistance_eq_lfppDistOn] at h
  have hlow' : ∀ ω, ω ∉ Bad → Real.exp (-(ξ * M)) * D' ω ≤ D ω := by
    intro ω hω
    have h := lfppDistOn_le_exp_mul (ζ := ξ) (x := 0) (y := e₁ d) (hY.continuous ω)
      (hH.continuous ω) fun z hz => by rw [abs_sub_comm]; exact hgood ω hω z hz
    rw [abs_of_pos hξ, ← lfppDistance_eq_lfppDistOn, ← lfppDistance_eq_lfppDistOn] at h
    have he := Real.exp_pos (ξ * M)
    rw [Real.exp_neg, inv_mul_le_iff₀ he]
    exact h
  -- law transfer: `a^{(p)}_{n-m}` does not depend on the realization
  have hlaw : P'.map (fun ω => lfppDistance d ξ (fun z => H' z ω)) = P.map D' :=
    (hY.map_lfppDistance_eq hH' hW hW' ξ (measurable_lfppDistance_continuousMap ξ)).symm
  rw [hlaw]
  -- DGZ Lemma 3.2 for `Y` (band `(2^{-(n-m)}, 1)`)
  have hab : ((2 : ℝ) ^ (n - m))⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (Nat.sub_ne_zero_of_lt hmn))
  have hq₂ := hY.lowerQuantile_lfppDistance_le_exp_mul hd hκ hW (dyadic_pos (n - m)) hab hξ hp0
    hp1 hp₂0 hp₂1
  have hq₃ := hY.lowerQuantile_lfppDistance_le_exp_mul hd hκ hW (dyadic_pos (n - m)) hab hξ hp₃0
    hp₃1 hp0 hp1
  rw [← hc₂] at hq₂
  rw [← hc₃] at hq₃
  -- positivity of the quantiles of `D'`
  have hD'pos : ∀ᵐ ω ∂P, 0 < D' ω := ae_of_all _ fun ω => lfppDistance_pos hd (hY.continuous ω)
  have hqp := lowerQuantile_map_pos hD'm hD'pos hp0 hp1
  -- the exponent bound
  set v : ℝ := Real.log (1 / ((2 : ℝ) ^ (n - m))⁻¹) with hv
  have hsv : √v ≤ √((m : ℝ) * n) * √(Real.log 2) := sqrt_log_le hm
  have hmn0 : 0 ≤ √((m : ℝ) * n) := Real.sqrt_nonneg _
  set C : ℝ := ξ * t + (c₂ + c₃) * ξ * √(Real.log 2) with hC
  have hexp₂ : ξ * M + c₂ * ξ * √v ≤ C * √((m : ℝ) * n) := by
    have h1 : c₂ * ξ * √v ≤ c₂ * ξ * (√((m : ℝ) * n) * √(Real.log 2)) :=
      mul_le_mul_of_nonneg_left hsv (by positivity)
    have h2 : 0 ≤ c₃ * ξ * √(Real.log 2) * √((m : ℝ) * n) := by positivity
    rw [hM, hC]
    nlinarith
  have hexp₃ : ξ * M + c₃ * ξ * √v ≤ C * √((m : ℝ) * n) := by
    have h1 : c₃ * ξ * √v ≤ c₃ * ξ * (√((m : ℝ) * n) * √(Real.log 2)) :=
      mul_le_mul_of_nonneg_left hsv (by positivity)
    have h2 : 0 ≤ c₂ * ξ * √(Real.log 2) * √((m : ℝ) * n) := by positivity
    rw [hM, hC]
    nlinarith
  constructor
  · -- lower bound
    have hL := mul_lowerQuantile_le_of_mul_le hDm hD'm (Real.exp_pos (-(ξ * M))) hBad hlow' hp0
      hp1 hp₃0 hp₃1 hlow
    -- `q_p(D') ≤ e^{c₃ ξ √v} q_{p₃}(D')`
    have hq₃' : Real.exp (-(c₃ * ξ * √v)) * LQGMetric.lowerQuantile (P.map D') p ≤
        LQGMetric.lowerQuantile (P.map D') p₃ := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos _)]
      exact hq₃
    calc Real.exp (-(C * √((m : ℝ) * n))) * LQGMetric.lowerQuantile (P.map D') p
        ≤ Real.exp (-(ξ * M)) * (Real.exp (-(c₃ * ξ * √v)) *
            LQGMetric.lowerQuantile (P.map D') p) := by
          rw [← mul_assoc, ← Real.exp_add]
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hqp.le
      _ ≤ Real.exp (-(ξ * M)) * LQGMetric.lowerQuantile (P.map D') p₃ :=
          mul_le_mul_of_nonneg_left hq₃' (Real.exp_pos _).le
      _ ≤ LQGMetric.lowerQuantile (P.map D) p := hL
  · -- upper bound
    have hU := lowerQuantile_le_mul_of_le_mul hDm hD'm (Real.exp_pos (ξ * M)).le hBad hup' hp0
      hp1 hp₂0 hp₂1 hup
    calc LQGMetric.lowerQuantile (P.map D) p
        ≤ Real.exp (ξ * M) * LQGMetric.lowerQuantile (P.map D') p₂ := hU
      _ ≤ Real.exp (ξ * M) * (Real.exp (c₂ * ξ * √v) *
            LQGMetric.lowerQuantile (P.map D') p) :=
          mul_le_mul_of_nonneg_left hq₂ (Real.exp_pos _).le
      _ ≤ Real.exp (C * √((m : ℝ) * n)) * LQGMetric.lowerQuantile (P.map D') p := by
          rw [← mul_assoc, ← Real.exp_add]
          exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hexp₂) hqp.le

end HigherDimLFPP
