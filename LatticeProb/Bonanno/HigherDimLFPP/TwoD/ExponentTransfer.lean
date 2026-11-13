/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.ExponentTransfer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.LemmaA1
import LatticeProb.Bonanno.HigherDimLFPP.TwoD.Plane
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Compare
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.IsLFPPExponent

/-!
# Exponent transfer between `H_{ε,1}` and the coupled circle averages (packet P-X10, target T4)

Source: `source/higher-dimensional-lfpp-limit.pdf`, App. A.2, last paragraph ("if two fields differ
by at most `M_ε` on `U`, every path cost and hence every distance differs by a multiplicative
factor between `e^{-ζ M_ε}` and `e^{ζ M_ε}`. In (A.3), `M_ε / log ε⁻¹ → 0` in probability, which
proves equality of the exponents"); planning audit HA5, Details D12, Claim 4; ruling H12.

In the coupled realization (`H ε` versions of `H_{ε,1}`, `h r` versions of the circle averages,
the same white noise):

* `abs_log_lfppDistance_coupled_le`: for `ε ∈ (0,1)`,
  `|log D^ξ(H_{ε,1}) - log D^ξ_{LD}(h_ε)| ≤ |ξ| sup_{[-3,3]²} |h_ε - H_{ε,1}|`, where `D^ξ` is the
  frozen distance in `ℝ²` and `D^ξ_{LD}` is `LQGDimension.lfppDistance` in `ℂ`
  (`lqg_lfppDistance_eq`: the same paths under `cToR2`, and the weight comparison
  `abs_log_lfppDistance_sub_le` of P-X1, since `(-2,2)² ⊆ [-3,3]²`);
* with Lemma A.1 (`lemmaA1_circle`, `sup = O_P(√(log ε⁻¹)) = o_P(log ε⁻¹)`), the two families
  `log D / log ε` differ by `o_P(1)` (`tendsto_measure_abs_sub_coupled`), and an `o_P(1)`
  perturbation does not change limits in probability (`TwoD.tendstoInMeasure_of_abs_sub`);
* `isLFPPExponent_iff_coupled` (target T4): `IsLFPPExponent H P ξ λ` (frozen, `d = 2`) iff
  `LQGDimension.IsLFPPExponent h P ξ λ`, for every `ξ` and `λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLFPP

namespace TwoD

/-- **Asymptotically negligible perturbations** preserve convergence in measure. -/
theorem tendstoInMeasure_of_abs_sub {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {l : Filter ι} {X Y : ι → α → ℝ} {g : α → ℝ} (hX : TendstoInMeasure μ X l g)
    (hXY : ∀ δ > 0, Tendsto (fun i => μ {x | δ ≤ |X i x - Y i x|}) l (𝓝 0)) :
    TendstoInMeasure μ Y l g := by
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro δ hδ
  have h1 := hX (δ / 2) (by positivity)
  have h2 := hXY (δ / 2) (by positivity)
  have h3 : Tendsto (fun i => μ {x | δ / 2 ≤ dist (X i x) (g x)} +
      μ {x | δ / 2 ≤ |X i x - Y i x|}) l (𝓝 0) := by
    simpa only [add_zero] using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun i => zero_le)
    fun i => (measure_mono fun x hx => ?_).trans (measure_union_le _ _)
  simp only [mem_ofPred_eq, mem_union, Real.dist_eq] at hx ⊢
  by_contra hn
  push Not at hn
  have : |Y i x - g x| ≤ |X i x - g x| + |X i x - Y i x| := by
    calc |Y i x - g x| = |(X i x - g x) - (X i x - Y i x)| := by ring_nf
      _ ≤ |X i x - g x| + |X i x - Y i x| := abs_sub _ _
  linarith

/-- Suprema over `[-3,3]²` of continuous functions are finite. -/
theorem bddAbove_box3 {f : Rd 2 → ℝ} (hf : Continuous f) :
    BddAbove (range fun x : {x : Rd 2 // ∀ i, |x i| ≤ 3} => f x.1) := by
  have hK : IsCompact {x : Rd 2 | ∀ i, |x i| ≤ 3} := by
    have : {x : Rd 2 | ∀ i, |x i| ≤ 3} = Osc.box 0 3 := by
      ext x
      simp only [Osc.box, mem_ofPred_eq, PiLp.zero_apply, sub_zero]
    rw [this]
    exact Osc.isCompact_box 0 3
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM ⟨x.1, x.2, rfl⟩⟩

end TwoD

open TwoD

section Coupled

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {W : WN 2 → Ω → ℝ} {κ : Rd 2 → ℝ}

/-- **Weight comparison in the coupled realization**: for `ε ∈ (0,1)`,
`|log D^ξ(H_{ε,1}) - log D^ξ_{LD}(h_ε)| ≤ |ξ| sup_{[-3,3]²} |h_ε - H_{ε,1}|`. -/
theorem abs_log_lfppDistance_coupled_le {H : ℝ → Rd 2 → Ω → ℝ}
    (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) {h : ℝ → ℂ → Ω → ℝ}
    (hh : ∀ r > 0, IsCircleVersion P W κ r (h r)) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (ξ : ℝ)
    (ω : Ω) :
    |Real.log (lfppDistance 2 ξ fun z => H ε z ω) -
        Real.log (LQGDimension.lfppDistance ξ fun z => h ε z ω)| ≤
      |ξ| * ⨆ x : {x : Rd 2 // ∀ i, |x i| ≤ 3}, |h ε (cToR2.symm x.1) ω - H ε x.1 ω| := by
  have hHc : Continuous fun z => H ε z ω := (hH ε hε).continuous ω
  have hhc : Continuous fun x => h ε (cToR2.symm x) ω :=
    ((hh ε hε.1).continuous ω).comp cToR2.symm.continuous
  rw [lqg_lfppDistance_eq]
  refine abs_log_lfppDistance_sub_le hHc hhc fun z hz => ?_
  have hz3 : ∀ i, |z i| ≤ 3 := fun i => (hz i).le.trans (by norm_num)
  rw [abs_sub_comm]
  exact le_ciSup (f := fun x : {x : Rd 2 // ∀ i, |x i| ≤ 3} => |h ε (cToR2.symm x.1) ω - H ε x.1 ω|)
    (bddAbove_box3 ((hhc.sub hHc).abs)) ⟨z, hz3⟩

/-- **The two exponent families differ by `o_P(1)`** (HA5 D12, Claim 4): for every `δ > 0`,
`P(δ ≤ |log D^ξ(H_{ε,1})/log ε - log D^ξ_{LD}(h_ε)/log ε|) → 0` as `ε ↓ 0`. -/
theorem tendsto_measure_abs_sub_coupled (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd 2 → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {h : ℝ → ℂ → Ω → ℝ} (hh : ∀ r > 0, IsCircleVersion P W κ r (h r)) (ξ : ℝ) :
    ∀ δ > 0, Tendsto (fun ε => P {ω |
      δ ≤ |Real.log (lfppDistance 2 ξ fun z => H ε z ω) / Real.log ε -
        Real.log (LQGDimension.lfppDistance ξ fun z => h ε z ω) / Real.log ε|}) (𝓝[>] 0)
      (𝓝 0) := by
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro η' hη'
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη'
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr1
  obtain ⟨M, hM0, hM⟩ := lemmaA1_circle hκ hW hH hh r hr
  set a : ℝ := |ξ| * M / δ with ha
  have ha0 : 0 ≤ a := by positivity
  set ε₁ : ℝ := min 2⁻¹ (Real.exp (-(a ^ 2))) with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (by norm_num) (Real.exp_pos _)
  filter_upwards [Ioo_mem_nhdsGT hε₁0] with ε hε
  have hε0 : 0 < ε := hε.1
  have hε2 : ε ∈ Ioo (0 : ℝ) 2⁻¹ := ⟨hε0, hε.2.trans_le (min_le_left _ _)⟩
  have hε1 : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε0, hε2.2.trans (by norm_num)⟩
  refine (measure_mono ?_).trans ((hM ε hε2).trans hr2.le)
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  by_contra hn
  push Not at hn
  set ℓ : ℝ := Real.log ε⁻¹ with hℓ
  set S : ℝ := ⨆ x : {x : Rd 2 // ∀ i, |x i| ≤ 3}, |h ε (cToR2.symm x.1) ω - H ε x.1 ω| with hS
  -- `ℓ > a²`
  have hℓa : a ^ 2 < ℓ := by
    have h1 : ε < Real.exp (-(a ^ 2)) := hε.2.trans_le (min_le_right _ _)
    have h2 : Real.log ε < -(a ^ 2) := by
      rw [← Real.exp_lt_exp, Real.exp_log hε0]
      exact h1
    rw [hℓ, Real.log_inv]
    linarith
  have hℓ0 : 0 < ℓ := lt_of_le_of_lt (sq_nonneg a) hℓa
  have hsqrt : a < √ℓ := by
    rw [← Real.sqrt_sq ha0]
    exact Real.sqrt_lt_sqrt (sq_nonneg a) hℓa
  have hsℓ : 0 < √ℓ := Real.sqrt_pos.2 hℓ0
  -- `|ξ| M √ℓ < δ ℓ`
  have hkey : |ξ| * (M * √ℓ) < δ * ℓ := by
    have h1 : |ξ| * M < δ * √ℓ := by
      rw [ha, div_lt_iff₀ hδ] at hsqrt
      linarith
    have h2 : δ * ℓ = δ * √ℓ * √ℓ := by
      rw [mul_assoc, Real.mul_self_sqrt hℓ0.le]
    rw [h2, ← mul_assoc]
    exact mul_lt_mul_of_pos_right h1 hsℓ
  have hdiff := abs_log_lfppDistance_coupled_le hH hh hε1 ξ ω
  rw [← hS] at hdiff
  have hlogε : Real.log ε = -ℓ := by rw [hℓ, Real.log_inv, neg_neg]
  have habs : |Real.log (lfppDistance 2 ξ fun z => H ε z ω) / Real.log ε -
      Real.log (LQGDimension.lfppDistance ξ fun z => h ε z ω) / Real.log ε| =
      |Real.log (lfppDistance 2 ξ fun z => H ε z ω) -
        Real.log (LQGDimension.lfppDistance ξ fun z => h ε z ω)| / ℓ := by
    rw [← sub_div, abs_div, hlogε, abs_neg, abs_of_pos hℓ0]
  rw [habs, le_div_iff₀ hℓ0] at hω
  have h3 : |ξ| * S ≤ |ξ| * (M * √ℓ) := mul_le_mul_of_nonneg_left hn (abs_nonneg ξ)
  linarith

/-- **Exponent transfer** (target T4; HA5 D12, Claim 4): in the coupled realization, `λ` is the
frozen LFPP exponent of `H_{ε,1}` (`d = 2`) at `ξ` iff it is `LQGDimension`'s LFPP exponent of the
circle averages `h_ε` at `ξ`. -/
theorem isLFPPExponent_iff_coupled (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {H : ℝ → Rd 2 → Ω → ℝ} (hH : ∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε))
    {h : ℝ → ℂ → Ω → ℝ} (hh : ∀ r > 0, IsCircleVersion P W κ r (h r)) (ξ lam : ℝ) :
    IsLFPPExponent H P ξ lam ↔ LQGDimension.IsLFPPExponent h P ξ lam := by
  have key := tendsto_measure_abs_sub_coupled hκ hW hH hh ξ
  constructor
  · intro hX
    exact tendstoInMeasure_of_abs_sub hX key
  · intro hY
    refine tendstoInMeasure_of_abs_sub hY fun δ hδ => ?_
    simpa only [abs_sub_comm] using key δ hδ

/-- **HA5 D12, Claim 4** (target T4, statement form with the frozen names). -/
theorem exponentTransfer : ∀ κ : Rd 2 → ℝ, IsLFPPKernel κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN 2 → Ω → ℝ)
      (H : ℝ → Rd 2 → Ω → ℝ) (h : ℝ → ℂ → Ω → ℝ), IsWhiteNoise P W →
      (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
      (∀ r > 0, IsCircleVersion P W κ r (h r)) →
      ∀ ξ lam : ℝ, IsLFPPExponent H P ξ lam ↔ LQGDimension.IsLFPPExponent h P ξ lam :=
  fun _ hκ _ _ _ _ _ _ hW hH hh => isLFPPExponent_iff_coupled hκ hW hH hh

end Coupled

end HigherDimLFPP
