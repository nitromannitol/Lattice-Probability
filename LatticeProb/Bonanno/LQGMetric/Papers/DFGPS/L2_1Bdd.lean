/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1Bdd at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Localized
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont
import LatticeProb.Bonanno.LQGMetric.Statement.GFF

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: the bounded continuous part, and the reduction to the GFF

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:735–737: "If `f` is a bounded
continuous function, we similarly obtain a.s. `lim_{ε→0} sup_{z∈U} |f*_ε(z) − f̂*_ε(z)| = 0` …
This gives (eqn-localized-approx) in the case of a whole-plane GFF plus a bounded continuous
function."

* `abs_heatMollify_sub_locMollify_ofCont_le`: for `|f| ≤ M`,
  `|f*_ε(z) − f̂*_ε(z)| ≤ 2M e^{−1/(8ε)}` for all `z` (the integrand `(1 − ψ_ε(z−w)) p_{ε²/2}(z,w)`
  vanishes on `B_{√ε/2}(z)`, and off it `p_{ε²/2} ≤ 2 e^{−1/(8ε)} p_{ε²}`; own elementary bound,
  the paper says "similarly").
* `heatMollify_add_ofCont`: additivity of `heatMollify` when the GFF limit exists.
* `lem2_1_approx_of_gff`: (eqn-localized-approx) for `IsGFFPlusBddCont` from the GFF case
  `Lem2_1GffApprox` (the paper's first case, T:711–734, for any additive constant, together with
  the existence of the limit defining `h*_ε(z)` for all small `ε` and `z ∈ Ū`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped Real

namespace LQGMetric.DFGPS

open LFPP

lemma heatKernel_half_le {ε : ℝ} (hε : 0 < ε) (z w : ℂ) (hw : Real.sqrt ε / 2 ≤ ‖z - w‖) :
    heatKernel (ε ^ 2 / 2) z w ≤ 2 * Real.exp (-(1 / (8 * ε))) * heatKernel (ε ^ 2) z w := by
  unfold heatKernel
  have ht : ε / 4 ≤ ‖z - w‖ ^ 2 := by
    have h0 : 0 ≤ Real.sqrt ε / 2 := by positivity
    have := pow_le_pow_left₀ h0 hw 2
    rw [div_pow, Real.sq_sqrt hε.le] at this
    linarith
  set t := ‖z - w‖ ^ 2
  have e1 : -t / (2 * (ε ^ 2 / 2)) = -t / (2 * ε ^ 2) + -t / (2 * ε ^ 2) := by
    field_simp; ring
  have e2 : -t / (2 * ε ^ 2) ≤ -(1 / (8 * ε)) := by
    rw [neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hpre : (2 * π * (ε ^ 2 / 2))⁻¹ = 2 * (2 * π * ε ^ 2)⁻¹ := by
    field_simp
  rw [e1, Real.exp_add, hpre]
  have hp : 0 ≤ (2 * π * ε ^ 2)⁻¹ := by positivity
  calc 2 * (2 * π * ε ^ 2)⁻¹ * (Real.exp (-t / (2 * ε ^ 2)) * Real.exp (-t / (2 * ε ^ 2)))
      ≤ 2 * (2 * π * ε ^ 2)⁻¹ * (Real.exp (-(1 / (8 * ε))) * Real.exp (-t / (2 * ε ^ 2))) := by
        gcongr
    _ = _ := by ring

lemma locTest_apply' (ε : ℝ) (hε : 0 < ε) (z w : ℂ) :
    locTest ε hε z w = locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w := rfl

/-- **The bounded continuous part** (DFGPS T:735): `|f*_ε(z) − f̂*_ε(z)| ≤ 2M e^{−1/(8ε)}`. -/
theorem abs_heatMollify_sub_locMollify_ofCont_le (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    |heatMollify ε (ofCont f) z - locMollify ε hε (ofCont f) z| ≤
      M * (2 * Real.exp (-(1 / (8 * ε)))) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hs : 0 < ε ^ 2 / 2 := by positivity
  rw [heatMollify_ofCont f M hM ε hε.ne' z]
  show |_ - ofCont f (locTest ε hε z)| ≤ _
  rw [ofCont_apply_heat]
  have i1 : Integrable fun w => f w * heatKernel (ε ^ 2 / 2) z w := by
    simpa only [mul_comm] using integrable_heatKernel_mul_of_bdd f M hM _ hs z
  have i2 : Integrable fun w => locTest ε hε z w * f w :=
    ((locTest ε hε z).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (locTest ε hε z).hasCompactSupport.mul_right
  rw [← integral_sub i1 i2]
  set c := 2 * Real.exp (-(1 / (8 * ε)))
  have hc : 0 ≤ c := by positivity
  have ig : Integrable fun w => M * c * heatKernel (ε ^ 2) z w :=
    (integrable_heatKernel _ (by positivity) z).const_mul _
  have key := norm_integral_le_of_norm_le (f := fun w => f w * heatKernel (ε ^ 2 / 2) z w -
    locTest ε hε z w * f w) ig (Eventually.of_forall fun w => ?_)
  · rw [integral_const_mul, integral_heatKernel _ (by positivity), mul_one] at key
    simpa only [Real.norm_eq_abs] using key
  · rw [locTest_apply']
    have hb0 := locBump_nonneg ε hε (z - w)
    have hb1 := locBump_le_one ε hε (z - w)
    have hp := heatKernel_nonneg (ε ^ 2 / 2) hs.le z w
    have e : f w * heatKernel (ε ^ 2 / 2) z w -
        locBump ε hε (z - w) * heatKernel (ε ^ 2 / 2) z w * f w =
        (1 - locBump ε hε (z - w)) * heatKernel (ε ^ 2 / 2) z w * f w := by ring
    rw [e, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - locBump ε hε (z - w)),
      abs_of_nonneg hp]
    by_cases hw : ‖z - w‖ ≤ Real.sqrt ε / 2
    · have h1 : locBump ε hε (z - w) = 1 := locBump_eq_one ε hε hw
      rw [h1, sub_self, zero_mul, zero_mul]
      have := heatKernel_nonneg (ε ^ 2) (by positivity) z w
      positivity
    · push Not at hw
      have hk := heatKernel_half_le hε z w hw.le
      have hk0 := heatKernel_nonneg (ε ^ 2) (by positivity) z w
      calc (1 - locBump ε hε (z - w)) * heatKernel (ε ^ 2 / 2) z w * |f w|
          ≤ 1 * (c * heatKernel (ε ^ 2) z w) * M := by
            gcongr
            · linarith
            · exact hM w
        _ = M * c * heatKernel (ε ^ 2) z w := by ring

/-- `heatMollify` is additive on `g + f` once the limit for `g` exists. -/
lemma heatMollify_add_ofCont (g : DistC) (f : C(ℂ, ℝ)) (M : ℝ) (hM : ∀ w, |f w| ≤ M)
    {ε : ℝ} (hε : 0 < ε) (z : ℂ) {L : ℝ}
    (hg : Tendsto (fun n : ℕ => g (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) :
    heatMollify ε (g + ofCont f) z = heatMollify ε g z + heatMollify ε (ofCont f) z := by
  have hs : 0 < ε ^ 2 / 2 := by positivity
  have hf := tendsto_ofCont_heatTrunc f _ hs z (integrable_heatKernel_mul_of_bdd f M hM _ hs z)
  have hsum : Tendsto (fun n : ℕ => (g + ofCont f) (heatTrunc (ε ^ 2 / 2) z n)) atTop
      (𝓝 (L + ∫ w, heatKernel (ε ^ 2 / 2) z w * f w)) := by
    simpa only [ContinuousLinearMap.add_apply] using hg.add hf
  unfold heatMollify
  rw [hsum.limUnder_eq, hg.limUnder_eq, hf.limUnder_eq]

/-- **The GFF case of (eqn-localized-approx)** (DFGPS T:711–734), any additive constant, with
the existence of the limit defining `h*_ε(z)` for all small `ε` and `z ∈ Ū` (implicit in the
paper, which treats `h*_ε(z)` as defined). Open node. -/
def Lem2_1GffApprox.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC), IsWholePlaneGFF g P →
    ∀ U : Set ℂ, Bornology.IsBounded U →
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      (∃ L : ℝ, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      |heatMollify ε (g ω) z - locMollify ε hε (g ω) z| ≤ δ

lemma tendsto_exp_neg_inv_eight :
    Tendsto (fun ε : ℝ => Real.exp (-(1 / (8 * ε)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => 8 * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => 8 * ε) (𝓝 0) (𝓝 (8 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos (by norm_num : (0 : ℝ) < 8) hε
  have h2 := (tendsto_inv_nhdsGT_zero.comp h1)
  have h3 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h2
  refine h3.congr fun ε => ?_
  simp [one_div]

/-- **DFGPS Lemma 2.1, (eqn-localized-approx)** for a whole-plane GFF plus a bounded continuous
function, from the GFF case (T:735–738). -/
theorem lem2_1_approx_of_gff.{u} (HG : Lem2_1GffApprox.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} (hh : IsGFFPlusBddCont h P) {U : Set ℂ}
    (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : 0 < ε, ∀ z ∈ closure U,
      |heatMollify ε (h ω) z - locMollify ε hε (h ω) z| ≤ δ := by
  obtain ⟨-, f, -, hfb, hg⟩ := hh
  filter_upwards [HG P _ hg U hU] with ω hω δ hδ
  obtain ⟨M, hM⟩ := hfb ω
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), M * (2 * Real.exp (-(1 / (8 * ε)))) ≤ δ / 2 := by
    have : Tendsto (fun ε : ℝ => M * (2 * Real.exp (-(1 / (8 * ε))))) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_exp_neg_inv_eight.const_mul 2).const_mul M
    exact this.eventually (ge_mem_nhds (by linarith))
  filter_upwards [hω (δ / 2) (by linarith), hsmall] with ε h1 h2 hε z hz
  obtain ⟨⟨L, hL⟩, hb⟩ := h1 hε z hz
  have hdec : h ω = (h ω - ofCont (f ω)) + ofCont (f ω) := (sub_add_cancel _ _).symm
  rw [hdec, heatMollify_add_ofCont _ (f ω) M hM hε z hL]
  have hloc : locMollify ε hε ((h ω - ofCont (f ω)) + ofCont (f ω)) z =
      locMollify ε hε (h ω - ofCont (f ω)) z + locMollify ε hε (ofCont (f ω)) z := by
    unfold locMollify; rfl
  rw [hloc]
  have hf := abs_heatMollify_sub_locMollify_ofCont_le (f ω) M hM ε hε z
  calc |heatMollify ε (h ω - ofCont (f ω)) z + heatMollify ε (ofCont (f ω)) z -
        (locMollify ε hε (h ω - ofCont (f ω)) z + locMollify ε hε (ofCont (f ω)) z)|
      = |(heatMollify ε (h ω - ofCont (f ω)) z - locMollify ε hε (h ω - ofCont (f ω)) z) +
          (heatMollify ε (ofCont (f ω)) z - locMollify ε hε (ofCont (f ω)) z)| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hb (hf.trans h2)
    _ = δ := by ring

end LQGMetric.DFGPS
