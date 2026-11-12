/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W9 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W8

/-!
# D97, packet P-1: `M^W` does not charge circles

* `measurable_wickMeasC_apply`, **`lintegral_wickMeasC`**: `E wickMeasC n (U) = Leb(U)` (Wick
  normalisation: `E e^{γ h̃ − γ²/2 Var h̃} = 1`, Tonelli);
* **`ae_wickQArea_sphere`**: a.s. `M^W(∂B(c, q)) = 0` for all rational `c, q`: by the vague lower
  bound on open sets and Fatou, `M^W(S) ≤ Y := ⨅_k liminf_n wickMeasC n (U_k)` for open
  neighbourhoods `U_k` of `S ∩ (0,1)²` shrinking to the circle `S`, and `E Y ≤ Leb(U_k) → 0`.

This discharges the hypothesis `hS` of `isChaosLimit_wickQArea`. Own glue (D97), the first-moment
argument of `GMCIdent5.lintegral_tildeM_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {W : WNSpace → Ω' → ℝ}

lemma measurable_wickDensC_uncurry (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) :
    Measurable fun p : Ω' × ℂ => ENNReal.ofReal
      (Real.exp (γ * coarseVer hW n p.2 p.1 - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) p.2)) := by
  have hδ : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  have hV : Continuous fun z => tildeVar ((2 : ℝ)⁻¹ ^ n) z := by
    unfold tildeVar
    exact continuous_const.mul ((GMCIdent.continuous_tildeKer hW hδ).norm.pow 2)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((((GMCIdent5.measurable_coarseVer_uncurry hW n).comp measurable_swap).const_mul γ).sub
      ((hV.measurable.comp measurable_snd).const_mul _)))

lemma measurable_wickMeasC_apply (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) {U : Set ℂ}
    (hU : MeasurableSet U) : Measurable fun ω => wickMeasC hW γ n ω U := by
  simp_rw [wickMeasC, withDensity_apply _ hU]
  exact (measurable_wickDensC_uncurry hW γ n).lintegral_prod_right'

/-- `E wickMeasC n (U) = Leb(U)`. -/
theorem lintegral_wickMeasC (hW : IsWhiteNoise P' W) (γ : ℝ) (n : ℕ) {U : Set ℂ}
    (hU : MeasurableSet U) : ∫⁻ ω, wickMeasC hW γ n ω U ∂P' = volume U := by
  have hP := hW.isProbabilityMeasure
  simp_rw [wickMeasC, withDensity_apply _ hU]
  rw [lintegral_lintegral_swap (measurable_wickDensC_uncurry hW γ n).aemeasurable]
  rw [← setLIntegral_one]
  refine setLIntegral_congr_fun hU fun z _ => ?_
  set V := tildeVar ((2 : ℝ)⁻¹ ^ n) z
  have hint := (integrable_exp_tildeHInf hW γ n z).mul_const (Real.exp (-(γ ^ 2 / 2 * V)))
  have hae : (fun ω => Real.exp (γ * coarseVer hW n z ω - γ ^ 2 / 2 * V)) =ᵐ[P']
      fun ω => Real.exp (γ * tildeHInf W ((2 : ℝ)⁻¹ ^ n) z ω) * Real.exp (-(γ ^ 2 / 2 * V)) := by
    filter_upwards [(coarseVer_spec hW n).2.2 z] with ω h
    rw [h, ← Real.exp_add, sub_eq_add_neg]
  rw [← ofReal_integral_eq_lintegral_ofReal ((integrable_congr hae).2 hint)
    (Eventually.of_forall fun ω => (Real.exp_pos _).le), integral_congr_ae hae,
    integral_mul_const, integral_exp_tildeHInf hW γ n z, ← Real.exp_add]
  have : γ ^ 2 / 2 * (Real.pi * ‖wndKernelL2 openSquare (Ioi (((2 : ℝ)⁻¹ ^ n) ^ 2)) z‖ ^ 2) +
      -(γ ^ 2 / 2 * V) = 0 := by simp only [V, tildeVar]; ring
  rw [this, Real.exp_zero, ENNReal.ofReal_one]

/-- **a.s. `M^W` does not charge the rational circles.** -/
theorem ae_wickQArea_sphere (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P', ∀ (c : ℚ × ℚ) (q : ℚ), wickQArea γ W ω (sphere (ratPt c) q) = 0 := by
  have hP := hW.isProbabilityMeasure
  rw [ae_all_iff]; intro c; rw [ae_all_iff]; intro q
  set S := sphere (ratPt c) (q : ℝ)
  set U : ℕ → Set ℂ := fun k => thickening (1 / ((k : ℝ) + 1)) S ∩ openSquare
  have hUo : ∀ k, IsOpen (U k) := fun k => isOpen_thickening.inter isOpen_openSquare
  set L : ℕ → Ω' → ℝ≥0∞ := fun k ω => liminf (fun n => wickMeasC hW γ n ω (U k)) atTop
  have hLm : ∀ k, Measurable (L k) := fun k =>
    Measurable.liminf fun n => measurable_wickMeasC_apply hW γ n (hUo k).measurableSet
  set Y : Ω' → ℝ≥0∞ := fun ω => ⨅ k, L k ω
  have hYm : Measurable Y := Measurable.iInf hLm
  -- `E Y = 0`
  have hvolS : volume S = 0 := Measure.addHaar_sphere volume _ _
  have hlim : Tendsto (fun k : ℕ => volume (cthickening (1 / ((k : ℝ) + 1)) S)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure ℂ))
      (isCompact_sphere (ratPt c) (q : ℝ))
    rw [hvolS] at h1
    exact h1.comp tendsto_one_div_add_atTop_nhds_zero_nat
  have hEY : ∫⁻ ω, Y ω ∂P' = 0 := by
    refine le_antisymm (ge_of_tendsto' hlim fun k => ?_) zero_le
    calc ∫⁻ ω, Y ω ∂P' ≤ ∫⁻ ω, L k ω ∂P' := lintegral_mono fun ω => iInf_le _ k
      _ ≤ liminf (fun n => ∫⁻ ω, wickMeasC hW γ n ω (U k) ∂P') atTop :=
          lintegral_liminf_le fun n => measurable_wickMeasC_apply hW γ n (hUo k).measurableSet
      _ = volume (U k) := by
          simp_rw [lintegral_wickMeasC hW γ _ (hUo k).measurableSet]; exact liminf_const _
      _ ≤ volume (cthickening (1 / ((k : ℝ) + 1)) S) :=
          measure_mono (inter_subset_left.trans (thickening_subset_cthickening _ _))
  have hY0 : ∀ᵐ ω ∂P', Y ω = 0 := (lintegral_eq_zero_iff hYm).1 hEY
  filter_upwards [hY0, ae_isVagueLimitOn_wickMeasC hW hγ hγ2] with ω hY hv
  -- `M^W(S) ≤ L k ω` for all `k`
  have hSL : ∀ k, wickQArea γ W ω S ≤ L k ω := by
    intro k
    have hSO : wickQArea γ W ω S = wickQArea γ W ω (S ∩ openSquare) := by
      refine le_antisymm ?_ (measure_mono inter_subset_left)
      rw [← measure_inter_add_sdiff S isOpen_openSquare.measurableSet]
      rw [measure_mono_null (s := S \ openSquare) (fun z hz => hz.2) hv.1, add_zero]
    rw [hSO]
    refine (measure_mono (inter_subset_inter_left _
      (self_subset_thickening (show (0 : ℝ) < 1 / ((k : ℝ) + 1) by positivity) S))).trans ?_
    refine le_of_forall_lt_imp_le_of_dense fun b hb => ?_
    have hev := eventually_lt_of_open hv (fun n K hK _ => wickMeasC_lt_top hW γ n ω hK) (hUo k)
      inter_subset_right hb
    exact le_liminf_of_le (by isBoundedDefault) (hev.mono fun n hn => hn.le)
  exact le_antisymm (le_of_le_of_eq (le_iInf hSL) hY) zero_le

/-- The continuous version `ζ_{2^{-n}} = coarseVer hW n` of `h̃_{2^{-n}}`, indexed by the scale. -/
def wickZeta (hW : IsWhiteNoise P' W) (s : ℝ) (z : ℂ) (ω : Ω') : ℝ :=
  coarseVer hW (Nat.log 2 ⌊s⁻¹⌋₊) z ω

lemma wickZeta_pow (hW : IsWhiteNoise P' W) (n : ℕ) (z : ℂ) (ω : Ω') :
    wickZeta hW ((1 / 2 : ℝ) ^ n) z ω = coarseVer hW n z ω := by
  have e : ⌊((1 / 2 : ℝ) ^ n)⁻¹⌋₊ = 2 ^ n := by
    rw [one_div, inv_pow, inv_inv, show (2 : ℝ) ^ n = ((2 ^ n : ℕ) : ℝ) by push_cast; rfl,
      Nat.floor_natCast]
  rw [wickZeta, e, Nat.log_pow (by norm_num)]

/-- `wickZeta` satisfies the hypotheses `hc₁`, `hv₁` of `dzz_lemma310_var`. -/
lemma wickZeta_spec (hW : IsWhiteNoise P' W) :
    (∀ (j : ℕ) (ω : Ω'), Continuous fun x => wickZeta hW ((1 / 2 : ℝ) ^ j) x ω) ∧
      ∀ (j : ℕ) (x : ℂ), wickZeta hW ((1 / 2 : ℝ) ^ j) x =ᵐ[P']
        tildeHInf W ((1 / 2 : ℝ) ^ j) x := by
  refine ⟨fun j ω => ?_, fun j x => ?_⟩
  · have e : (fun x => wickZeta hW ((1 / 2 : ℝ) ^ j) x ω) = fun x => coarseVer hW j x ω :=
      funext fun x => wickZeta_pow hW j x ω
    rw [e]; exact (coarseVer_spec hW j).1 ω
  · have e : wickZeta hW ((1 / 2 : ℝ) ^ j) x = coarseVer hW j x :=
      funext fun ω => wickZeta_pow hW j x ω
    rw [e, one_div]; exact (coarseVer_spec hW j).2.2 x

/-- **`IsChaosLimit` for `M^W`** (DZZ (eq-def-M-eta)), given only that a.s. no mass of the
approximations escapes to `∂𝕍`. -/
theorem isChaosLimit_wickQArea_of_tight (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hT : ∀ᵐ ω ∂P', StripTight fun n => wickMeasC hW γ n ω) :
    ∀ᵐ ω ∂P', IsChaosLimit γ (fun s z => wickZeta hW s z ω) tildeVar
      (fun n => (1 / 2 : ℝ) ^ n) (wickQArea γ W ω) :=
  isChaosLimit_wickQArea hW hγ hγ2 (wickZeta hW) (wickZeta_pow hW) hT
    (ae_wickQArea_sphere hW hγ hγ2)

end DZZ
end LQGMetric
