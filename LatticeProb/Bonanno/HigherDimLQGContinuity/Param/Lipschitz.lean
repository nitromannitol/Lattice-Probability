/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGContinuity.Param.Lipschitz at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLQGContinuity.Param.Defs
import LatticeProb.Bonanno.HigherDimLQGMetric.KernelIndep.LowerBound

/-!
# D-PHI: `ϕ(ξ) = ξ Q(ξ)` is `√(2d)`-Lipschitz (packet PAR)

Blueprint Part A §1, `a:lem-pathwise`, `a:lem-suptail`, `a:lem-constlim`, `a:thm-dphi` (NA1 R1 Steps 1–3;
ruling N3; [C] Lemma 2.1, l. 121, 137–141). For `d ≥ 2` and `ξ, η ≥ 0`, `|ϕ(ξ) - ϕ(η)| ≤ √(2d) |ξ - η|`.

Proof (convergence in probability, no expectations): fix a nonnegative admissible kernel, a white noise and
band versions `H_ε` of the band field from `ε` to `1`. For `ζ ≥ 0`,
`X^ζ_ε = log L(ζ, H_ε) / log ε → 1 - ϕ(ζ)` in probability (`distExp_isDistanceExponent` for `ζ > 0`;
`L(0, ·) = 1` for `ζ = 0`). Pathwise, `|log L(ζ, φ) - log L(ζ', φ)| ≤ |ζ - ζ'| sup_U |φ|`, and
`sup_{[-2,2]^d} |H_ε| ≤ (√(2d) + δ) log ε⁻¹` with probability `→ 1`. Two constant limits in probability whose
difference is eventually at most `c` with probability `→ 1` differ by at most `c`.

Main statements: `phiXi_lipschitz_nonneg`, `phiXi_lipschitz` (all of `ℝ`, since `ϕ(ξ) = ϕ(max ξ 0)`),
`phiXi_continuous`, `one_sub_sqrt_mul_le_phiXi`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd WN IsLFPPKernel IsWhiteNoise IsBandVersion IsLFPPExponent lfppDistance)

/-! ### Pathwise comparison in the parameter (`a:lem-pathwise`) -/

/-- `L(ζ, φ) = L(1, ζ φ)`: the parameter can be moved into the field. -/
theorem lfppDistance_eq_one_mul (d : ℕ) (ζ : ℝ) (φ : Rd d → ℝ) :
    lfppDistance d ζ φ = lfppDistance d 1 (fun z => ζ * φ z) := by
  simp only [lfppDistance, HigherDimLFPP.lfppLength, one_mul]

/-- **Pathwise comparison** (`a:lem-pathwise`): if `|φ| ≤ M` on the cube, then
`|log L(ζ, φ) - log L(ζ', φ)| ≤ |ζ - ζ'| M`. -/
theorem abs_log_lfppDistance_param_sub_le {d : ℕ} {φ : Rd d → ℝ} (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ z ∈ HigherDimLFPP.cube d, |φ z| ≤ M) (ζ ζ' : ℝ) :
    |Real.log (lfppDistance d ζ φ) - Real.log (lfppDistance d ζ' φ)| ≤ |ζ - ζ'| * M := by
  rw [lfppDistance_eq_one_mul d ζ, lfppDistance_eq_one_mul d ζ']
  have hc : ∀ a : ℝ, Continuous fun z => a * φ z := fun a => continuous_const.mul hφ
  have h := HigherDimLFPP.abs_log_lfppDistance_sub_le (ζ := 1) (hc ζ) (hc ζ')
    (M := |ζ - ζ'| * M) (fun z hz => by
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM z hz) (abs_nonneg _))
  simpa only [abs_one, one_mul] using h

/-- `L(0, φ) = 1`, in logarithmic form. -/
theorem log_lfppDistance_zero {d : ℕ} (hd : 0 < d) (φ : Rd d → ℝ) :
    Real.log (lfppDistance d 0 φ) = 0 := by
  rw [lfppDistance_eq_one_mul d 0]
  simp only [zero_mul]
  have h := HigherDimLFPP.abs_log_lfppDistance_le (ζ := 1) hd
    (continuous_const : Continuous fun _ : Rd d => (0 : ℝ)) (M := 0) (fun z _ => by simp)
  rw [mul_zero] at h
  exact abs_nonpos_iff.1 h

/-! ### The exponent at every `ζ ≥ 0` -/

/-- For `ζ ≥ 0`, `log L(ζ, H_ε) / log ε → 1 - ϕ(ζ)` in probability. -/
theorem isLFPPExponent_phiXi {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {H : ℝ → Rd d → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    IsLFPPExponent H P ζ (1 - phiXi d ζ) := by
  rcases hζ.lt_or_eq with hζ | rfl
  · rw [phiXi_of_pos hζ]
    exact distExp_isDistanceExponent hd hζ κ hκ Ω P W hW H hH
  · rw [phiXi_zero, sub_self]
    unfold IsLFPPExponent
    have h0 : (fun ε ω => Real.log (lfppDistance d 0 (fun z => H ε z ω)) / Real.log ε) =
        fun (_ : ℝ) (_ : Ω) => (0 : ℝ) := by
      funext ε ω
      rw [log_lfppDistance_zero (by omega), zero_div]
    rw [h0]
    intro δ hδ
    simp only [edist_self, nonpos_iff_eq_zero, hδ.ne', ofPred_false, measure_empty]
    exact tendsto_const_nhds

/-! ### The supremum of the band field (`a:lem-suptail`) -/

/-- **Band supremum tail** (`a:lem-suptail`): for `δ > 0`,
`P{∃ z ∈ [-2, 2]^d, (√(2d) + δ) log ε⁻¹ < |H_ε(z)|} → 0` as `ε ↓ 0`. -/
theorem bandSup_abs_tail {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (hκ : IsLFPPKernel κ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ} (hW : IsWhiteNoise P W)
    {H : ℝ → Rd d → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun ε : ℝ => P {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) 2,
      (Real.sqrt (2 * d) + δ) * Real.log ε⁻¹ < |H ε z ω|}) (𝓝[>] 0) (𝓝 0) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨L, -, hB⟩ := HigherDimLFPP.exists_bandSup_bounds hκ
  have hδ2 : 0 < δ / 2 := by positivity
  have hrate := band_supMean_limsup d L (δ / 2) hδ2
  have hbound : Tendsto (fun ε : ℝ => ENNReal.ofReal
      (2 * Real.exp (-((δ / 2) ^ 2 / 2 * Real.log ε⁻¹)))) (𝓝[>] 0) (𝓝 0) := by
    have hc : 0 < (δ / 2) ^ 2 / 2 := by positivity
    have hh := log_inv_tendsto_atTop.const_mul_atTop hc
    have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hh).const_mul 2
    have he' := ENNReal.tendsto_ofReal he
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using he'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num), hrate] with ε hε hr
  set ℓ : ℝ := Real.log ε⁻¹ with hℓdef
  have hℓ : 0 < ℓ := Real.log_pos (one_lt_inv_iff₀.2 hε)
  set M : ℝ := HigherDimLFPP.SupB.supMean d L ℓ (d * Real.log (4 / ε + 1)) with hMdef
  set u : ℝ := δ / 2 * ℓ with hudef
  have hu : 0 ≤ u := (mul_pos hδ2 hℓ).le
  have ht := (hB hW hε.1 hε.2.le (hH ε hε) hℓ (by simp [hℓdef, one_div])
    (0 : Rd d) (by norm_num : (0 : ℝ) ≤ 2)).2.2.2 hu
  have h22 : (2 : ℝ) * 2 / ε = 4 / ε := by ring
  rw [h22] at ht
  have hM : M < (Real.sqrt (2 * d) + δ / 2) * ℓ := (div_lt_iff₀ hℓ).1 hr
  calc P {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) 2,
        (Real.sqrt (2 * d) + δ) * ℓ < |H ε z ω|}
      ≤ P {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) 2, M + u < |H ε z ω|} := by
        refine measure_mono fun ω hω => ?_
        obtain ⟨z, hz, hlt⟩ := hω
        refine ⟨z, hz, lt_trans ?_ hlt⟩
        rw [hudef]
        linarith
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * ℓ))) := ht
    _ = ENNReal.ofReal (2 * Real.exp (-((δ / 2) ^ 2 / 2 * ℓ))) := by
        congr 3
        rw [hudef]
        field_simp

/-! ### Constant limits in probability (`a:lem-constlim`) -/

/-- **Constant limits** (`a:lem-constlim`, first claim): if `F_i → a` and `G_i → b` in measure and
`P{c < |F_i - G_i|} → 0`, then `|a - b| ≤ c`. -/
theorem abs_sub_le_of_tendstoInMeasure_const {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {l : Filter ι} [l.NeBot] {F G : ι → Ω → ℝ} {a b c : ℝ}
    (hF : TendstoInMeasure P F l (fun _ => a)) (hG : TendstoInMeasure P G l (fun _ => b))
    (hFG : Tendsto (fun i => P {ω | c < |F i ω - G i ω|}) l (𝓝 0)) : |a - b| ≤ c := by
  by_contra hn
  have hlt : c < |a - b| := lt_of_not_ge hn
  set r : ℝ := (|a - b| - c) / 3 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have h1 := (tendstoInMeasure_iff_dist.1 hF) r hr
  have h2 := (tendstoInMeasure_iff_dist.1 hG) r hr
  have hsum : Tendsto (fun i => P {ω | r ≤ dist (F i ω) a} + P {ω | r ≤ dist (G i ω) b} +
      P {ω | c < |F i ω - G i ω|}) l (𝓝 0) := by
    simpa only [add_zero] using (h1.add h2).add hFG
  obtain ⟨i, hi⟩ := (hsum.eventually (Iio_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hsub : (univ : Set Ω) ⊆ ({ω | r ≤ dist (F i ω) a} ∪ {ω | r ≤ dist (G i ω) b}) ∪
      {ω | c < |F i ω - G i ω|} := by
    intro ω _
    by_contra hω
    simp only [mem_union, mem_ofPred_eq, not_or, not_le, not_lt, Real.dist_eq] at hω
    obtain ⟨⟨hFa, hGb⟩, hFG'⟩ := hω
    have htri : |a - b| ≤ |F i ω - a| + |F i ω - G i ω| + |G i ω - b| := by
      calc |a - b| = |(F i ω - G i ω) - (F i ω - a) + (G i ω - b)| := by ring_nf
        _ ≤ |(F i ω - G i ω) - (F i ω - a)| + |G i ω - b| := abs_add_le _ _
        _ ≤ |F i ω - G i ω| + |F i ω - a| + |G i ω - b| := by
          gcongr
          exact abs_sub _ _
        _ = |F i ω - a| + |F i ω - G i ω| + |G i ω - b| := by ring
    linarith
  have hle : (1 : ℝ≥0∞) ≤ P {ω | r ≤ dist (F i ω) a} + P {ω | r ≤ dist (G i ω) b} +
      P {ω | c < |F i ω - G i ω|} := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono hsub).trans ((measure_union_le _ _).trans
      (add_le_add_left (measure_union_le _ _) _))
  exact (not_lt_of_ge hle) hi

/-- **Constant limits** (`a:lem-constlim`, second claim): if `F_i → lam` in measure and
`P{F_i ≤ A} → 0` for every `A < c`, then `c ≤ lam`. -/
theorem par_le_limit_of_lower_tails {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {l : Filter ι} [l.NeBot] {F : ι → Ω → ℝ} {lam c : ℝ}
    (hF : TendstoInMeasure P F l (fun _ => lam))
    (htail : ∀ A : ℝ, A < c → Tendsto (fun i => P {ω | F i ω ≤ A}) l (𝓝 0)) :
    c ≤ lam := by
  by_contra hn
  have hlc : lam < c := lt_of_not_ge hn
  set A : ℝ := (lam + c) / 2 with hAdef
  have hAc : A < c := by rw [hAdef]; linarith
  have hlA : lam < A := by rw [hAdef]; linarith
  have h1 := (tendstoInMeasure_iff_dist.1 hF) (A - lam) (sub_pos.2 hlA)
  have hsum : Tendsto (fun i => P {ω | A - lam ≤ dist (F i ω) lam} + P {ω | F i ω ≤ A})
      l (𝓝 0) := by
    simpa only [add_zero] using h1.add (htail A hAc)
  obtain ⟨i, hi⟩ := (hsum.eventually (Iio_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hsub : (univ : Set Ω) ⊆ {ω | A - lam ≤ dist (F i ω) lam} ∪ {ω | F i ω ≤ A} := by
    intro ω _
    by_cases hω : F i ω ≤ A
    · exact Or.inr hω
    · left
      have hlt : A < F i ω := lt_of_not_ge hω
      simp only [mem_ofPred_eq, Real.dist_eq]
      rw [abs_of_nonneg (by linarith : 0 ≤ F i ω - lam)]
      linarith
  have hle : (1 : ℝ≥0∞) ≤ P {ω | A - lam ≤ dist (F i ω) lam} + P {ω | F i ω ≤ A} := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  exact (not_lt_of_ge hle) hi

/-! ### D-PHI (`a:thm-dphi`) -/

/-- The approximate Lipschitz bound: for `ζ, ζ' ≥ 0` and `δ > 0`,
`|ϕ(ζ) - ϕ(ζ')| ≤ (√(2d) + δ) |ζ - ζ'|`. -/
theorem phiXi_lipschitz_nonneg_add {d : ℕ} (hd : 2 ≤ d) {ζ ζ' : ℝ} (hζ : 0 ≤ ζ) (hζ' : 0 ≤ ζ')
    {δ : ℝ} (hδ : 0 < δ) :
    |phiXi d ζ - phiXi d ζ'| ≤ (Real.sqrt (2 * d) + δ) * |ζ - ζ'| := by
  obtain ⟨κ, hκ⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨W, hW⟩ := HigherDimLFPP.exists_isWhiteNoise d
  have := hW.isProbabilityMeasure
  obtain ⟨H, hH⟩ := exists_bandVersion_family hκ hW
  have hX := isLFPPExponent_phiXi hd hκ hW hH hζ
  have hX' := isLFPPExponent_phiXi hd hκ hW hH hζ'
  set c : ℝ := (Real.sqrt (2 * d) + δ) * |ζ - ζ'| with hcdef
  have htail : Tendsto (fun ε : ℝ => LQGDimension.ExistAsm.stdP {ω |
      c < |Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε -
        Real.log (lfppDistance d ζ' (fun z => H ε z ω)) / Real.log ε|}) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (bandSup_abs_tail hd hκ hW hH hδ) (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hn
    push Not at hn
    set ℓ : ℝ := Real.log ε⁻¹ with hℓdef
    have hℓ : 0 < ℓ := Real.log_pos (one_lt_inv_iff₀.2 hε)
    have hM : ∀ z ∈ HigherDimLFPP.cube d, |H ε z ω| ≤ (Real.sqrt (2 * d) + δ) * ℓ :=
      fun z hz => hn z (HigherDimLFPP.Osc.closure_cube_subset_box (subset_closure hz))
    have hp := abs_log_lfppDistance_param_sub_le ((hH ε hε).continuous ω) hM ζ ζ'
    have hlogε : Real.log ε = -ℓ := by rw [hℓdef, Real.log_inv]; ring
    have habs : |Real.log (lfppDistance d ζ (fun z => H ε z ω)) / Real.log ε -
        Real.log (lfppDistance d ζ' (fun z => H ε z ω)) / Real.log ε| =
        |Real.log (lfppDistance d ζ (fun z => H ε z ω)) -
          Real.log (lfppDistance d ζ' (fun z => H ε z ω))| / ℓ := by
      rw [← sub_div, abs_div, hlogε, abs_neg, abs_of_pos hℓ]
    rw [habs, lt_div_iff₀ hℓ] at hω
    have : c * ℓ = |ζ - ζ'| * ((Real.sqrt (2 * d) + δ) * ℓ) := by rw [hcdef]; ring
    linarith
  have h := abs_sub_le_of_tendstoInMeasure_const hX hX' htail
  have heq : (1 - phiXi d ζ) - (1 - phiXi d ζ') = -(phiXi d ζ - phiXi d ζ') := by ring
  rwa [heq, abs_neg] at h

/-- **D-PHI** (`a:thm-dphi`, NA1 R1): for `d ≥ 2` and `ζ, ζ' ≥ 0`,
`|ϕ(ζ) - ϕ(ζ')| ≤ √(2d) |ζ - ζ'|`. -/
theorem phiXi_lipschitz_nonneg {d : ℕ} (hd : 2 ≤ d) {ζ ζ' : ℝ} (hζ : 0 ≤ ζ) (hζ' : 0 ≤ ζ') :
    |phiXi d ζ - phiXi d ζ'| ≤ Real.sqrt (2 * d) * |ζ - ζ'| := by
  have hlim : Tendsto (fun δ : ℝ => (Real.sqrt (2 * d) + δ) * |ζ - ζ'|) (𝓝[>] 0)
      (𝓝 (Real.sqrt (2 * d) * |ζ - ζ'|)) := by
    have h : Tendsto (fun δ : ℝ => (Real.sqrt (2 * d) + δ) * |ζ - ζ'|) (𝓝 0)
        (𝓝 ((Real.sqrt (2 * d) + 0) * |ζ - ζ'|)) :=
      ((continuous_const.add continuous_id).mul continuous_const).tendsto 0
    rw [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ =>
    phiXi_lipschitz_nonneg_add hd hζ hζ' hδ)

/-- **D-PHI on all of `ℝ`**: `|ϕ(ξ) - ϕ(η)| ≤ √(2d) |ξ - η|` for all real `ξ, η` (`ϕ = 1` on `(-∞, 0]`). -/
theorem phiXi_lipschitz {d : ℕ} (hd : 2 ≤ d) (ξ η : ℝ) :
    |phiXi d ξ - phiXi d η| ≤ Real.sqrt (2 * d) * |ξ - η| := by
  rw [← phiXi_max_zero d ξ, ← phiXi_max_zero d η]
  exact (phiXi_lipschitz_nonneg hd (le_max_right ξ 0) (le_max_right η 0)).trans
    (mul_le_mul_of_nonneg_left (abs_max_sub_max_le_abs ξ η 0) (Real.sqrt_nonneg _))

/-- `ϕ` is `√(2d)`-Lipschitz, as a `LipschitzWith` statement. -/
theorem phiXi_lipschitzWith {d : ℕ} (hd : 2 ≤ d) :
    LipschitzWith (Real.toNNReal (Real.sqrt (2 * d))) (phiXi d) := by
  refine LipschitzWith.of_dist_le_mul fun ξ η => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact phiXi_lipschitz hd ξ η

theorem phiXi_continuous {d : ℕ} (hd : 2 ≤ d) : Continuous (phiXi d) :=
  (phiXi_lipschitzWith hd).continuous

theorem gapXi_continuous {d : ℕ} (hd : 2 ≤ d) : Continuous (gapXi d) :=
  (phiXi_continuous hd).sub (continuous_const.mul continuous_id)

/-- `1 - √(2d) ξ ≤ ϕ(ξ)` for `ξ ≥ 0` (contains `HigherDimLQGMetric.distExp_ge`). -/
theorem one_sub_sqrt_mul_le_phiXi {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    1 - Real.sqrt (2 * d) * ξ ≤ phiXi d ξ := by
  have h := phiXi_lipschitz hd ξ 0
  rw [phiXi_zero, sub_zero, abs_of_nonneg hξ] at h
  linarith [neg_abs_le (phiXi d ξ - 1)]

/-- The gap is non-increasing on `ℝ`: `g(u) ≤ g(t)` for `t ≤ u` (from D-PHI). -/
theorem gapXi_antitone {d : ℕ} (hd : 2 ≤ d) : Antitone (gapXi d) := by
  intro t u htu
  have h := phiXi_lipschitz hd u t
  rw [abs_of_nonneg (sub_nonneg.2 htu)] at h
  simp only [gapXi]
  linarith [le_abs_self (phiXi d u - phiXi d t)]

end HigherDimLQGContinuity
