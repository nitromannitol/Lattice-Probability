/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta9A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W12
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta3

/-!
# `M^W ≥ c · M̃_{γ,δ,η}` from a density comparison (P2-DZZETA2, step (1), analytic part)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1193–1195, "similarly to (eq-M-tilde-B-bound)"):
`M_γ(S̃) ≥ c · M̃_{γ,ε²s',η}(S̃)` where `c = e^{-2αγ√L log L} δ'² s^{-2}`. DZZ obtain it from the
pointwise comparison of the approximating densities, `e^{γ h̃_{2^{-n}} − γ²/2 Var} ≥ c e^{γ η^{δ̂}_{2^{-n}}
− γ²/2 Var}`, and the definitions (eq-def-M-eta) (l. 1209–1213) and (eq-def-tilde-M) (l. 677–683) of the
two measures as limits of their approximations. This file is that limit step:

* `ofReal_mul_etaChaos_le_of_compact`: for a compact `K ⊆ (0,1)²`, vague convergence
  `wickMeasC → M^W` (`ae_isVagueLimitOn_wickMeasC`), the density comparison for large `n` and
  `etaApprox → etaChaos` (`ae_tendsto_etaApprox`) give `c M̃(K) ≤ M^W(K)` (portmanteau,
  `eventually_lt_of_compact`).
* `ae_etaChaos_le_iSup_inner`: a.s. `M̃(B) ≤ sup_k M̃(B ∩ [1/(k+3), 1 − 1/(k+3)]²)` (no mass of
  `M̃` on `∂𝕍`: `E M̃(B ∖ I_k) ≤ Leb(B ∖ I_k) → 0`), so the comparison extends to compact
  `B ⊆ 𝕍` touching `∂𝕍` (`ae_ofReal_mul_etaChaos_le`).

Own glue (the limit passages DZZ leave implicit).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper GMCIdent GMCIdent3 GMCIdent4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- the density `e^{γ h̃_{2^{-n}}(z) − γ²/2 Var h̃_{2^{-n}}(z)}` of `wickMeasC` -/
def wickDensC (hW : IsWhiteNoise P W) (γ : ℝ) (n : ℕ) (z : ℂ) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * coarseVer hW n z ω - γ ^ 2 / 2 * tildeVar ((2 : ℝ)⁻¹ ^ n) z))

/-- **Limit step of DZZ l. 1193–1195** on a compact `K ⊆ (0,1)²` (deterministic). -/
theorem ofReal_mul_etaChaos_le_of_compact (hW : IsWhiteNoise P W) {γ δ c : ℝ} {ω : Ω}
    (hv : IsVagueLimitOn openSquare (fun n => wickMeasC hW γ n ω) (wickQArea γ W ω))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ openSquare)
    (hd : ∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict K),
      ENNReal.ofReal c * etaDens W γ δ n z ω ≤ wickDensC hW γ n z ω)
    (ht : Tendsto (fun n => etaApprox W γ δ n K ω) atTop (𝓝 (etaChaos W γ δ K ω))) :
    ENNReal.ofReal c * etaChaos W γ δ K ω ≤ wickQArea γ W ω K := by
  by_contra hlt
  push Not at hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hlt
  have h1 := eventually_lt_of_compact hv (fun n K' hK' _ => wickMeasC_lt_top hW γ n ω hK') hK
    hKU hb1
  have ht' : Tendsto (fun n => ENNReal.ofReal c * etaApprox W γ δ n K ω) atTop
      (𝓝 (ENNReal.ofReal c * etaChaos W γ δ K ω)) :=
    ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.ofReal_ne_top)
  have h2 := (tendsto_order.1 ht').1 b hb2
  obtain ⟨n, hn1, hn2, hn3⟩ := (h1.and (h2.and hd)).exists
  refine absurd hn1 (not_lt.2 (le_trans hn2.le ?_))
  rw [etaApprox, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, wickMeasC,
    withDensity_apply _ hK.measurableSet]
  exact lintegral_mono_ae hn3

/-- the inner squares `[1/(k+3), 1 − 1/(k+3)]²` exhausting `(0,1)²` -/
def innerSq (k : ℕ) : Set ℂ :=
  {z | 1 / ((k : ℝ) + 3) ≤ z.re ∧ z.re ≤ 1 - 1 / ((k : ℝ) + 3) ∧
    1 / ((k : ℝ) + 3) ≤ z.im ∧ z.im ≤ 1 - 1 / ((k : ℝ) + 3)}

lemma isClosed_innerSq (k : ℕ) : IsClosed (innerSq k) := by
  unfold innerSq
  refine (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
    (isClosed_le Complex.continuous_im continuous_const)))

lemma innerSq_subset_openSquare (k : ℕ) : innerSq k ⊆ openSquare := by
  intro z ⟨h1, h2, h3, h4⟩
  have hp : (0 : ℝ) < 1 / ((k : ℝ) + 3) := by positivity
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma innerSq_mono {k l : ℕ} (h : k ≤ l) : innerSq k ⊆ innerSq l := by
  intro z ⟨h1, h2, h3, h4⟩
  have hkl : 1 / ((l : ℝ) + 3) ≤ 1 / ((k : ℝ) + 3) :=
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 3)
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma iUnion_innerSq : ⋃ k, innerSq k = openSquare := by
  refine subset_antisymm (iUnion_subset innerSq_subset_openSquare) fun z ⟨h1, h2, h3, h4⟩ => ?_
  set a := min (min z.re (1 - z.re)) (min z.im (1 - z.im))
  have ha : 0 < a := lt_min (lt_min h1 (by linarith)) (lt_min h3 (by linarith))
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / a)
  have hk' : 1 / ((k : ℝ) + 3) ≤ a := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ ha] at hk
    nlinarith
  have := min_le_left (min z.re (1 - z.re)) (min z.im (1 - z.im))
  have := min_le_right (min z.re (1 - z.re)) (min z.im (1 - z.im))
  have := min_le_left z.re (1 - z.re); have := min_le_right z.re (1 - z.re)
  have := min_le_left z.im (1 - z.im); have := min_le_right z.im (1 - z.im)
  exact mem_iUnion.2 ⟨k, by refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith⟩

lemma volume_dzzV_diff_openSquare : volume (dzzV \ openSquare) = 0 := by
  have h : dzzV \ openSquare ⊆ ({z : ℂ | z.re = 0} ∪ {z | z.re = 1}) ∪
      ({z : ℂ | z.im = 0} ∪ {z | z.im = 1}) := by
    intro z ⟨⟨h1, h2, h3, h4⟩, hz⟩
    by_contra hc
    simp only [mem_union, mem_setOf_eq, not_or] at hc
    exact hz ⟨lt_of_le_of_ne h1 (Ne.symm hc.1.1), lt_of_le_of_ne h2 hc.1.2,
      lt_of_le_of_ne h3 (Ne.symm hc.2.1), lt_of_le_of_ne h4 hc.2.2⟩
  refine measure_mono_null h (measure_union_null (measure_union_null (volume_re_eq 0)
    (volume_re_eq 1)) (measure_union_null (volume_im_eq 0) (volume_im_eq 1)))

lemma dzzV_subset_closedBall : dzzV ⊆ Metric.closedBall (0 : ℂ) 2 := by
  intro z ⟨h1, h2, h3, h4⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
  rw [abs_of_nonneg h1, abs_of_nonneg h3]; linarith

lemma volume_lt_top_of_subset_dzzV {B : Set ℂ} (hB : B ⊆ dzzV) : volume B < ⊤ :=
  (measure_mono (hB.trans dzzV_subset_closedBall)).trans_lt measure_closedBall_lt_top

lemma measurableSet_innerSq (k : ℕ) : MeasurableSet (innerSq k) :=
  (isClosed_innerSq k).measurableSet

/-- **no mass of `M̃_{γ,δ,η}` on `∂𝕍`**: a.s. `M̃(B) ≤ sup_k M̃(B ∩ I_k)` for `B ⊆ 𝕍` -/
theorem ae_etaChaos_le_iSup_inner (hW : IsWhiteNoise P W) (γ δ : ℝ) {B : Set ℂ}
    (hB : MeasurableSet B) (hBV : B ⊆ dzzV) :
    ∀ᵐ ω ∂P, etaChaos W γ δ B ω ≤ ⨆ k, etaChaos W γ δ (B ∩ innerSq k) ω := by
  have hfin : ∀ {A : Set ℂ}, A ⊆ B → volume A ≠ ⊤ := fun hA =>
    (volume_lt_top_of_subset_dzzV (hA.trans hBV)).ne
  set D : ℕ → Set ℂ := fun k => B \ innerSq k with hD
  have hDm : ∀ k, MeasurableSet (D k) := fun k => hB.diff (measurableSet_innerSq k)
  have hDa : Antitone D := fun k l hkl => diff_subset_diff_right (innerSq_mono hkl)
  have hDvol : ⨅ k, volume (D k) = 0 := by
    rw [← hDa.measure_iInter (fun k => (hDm k).nullMeasurableSet) ⟨0, hfin diff_subset⟩]
    refine measure_mono_null ?_ volume_dzzV_diff_openSquare
    intro z hz
    simp only [mem_iInter, hD, mem_diff] at hz
    refine ⟨hBV (hz 0).1, fun ho => ?_⟩
    rw [← iUnion_innerSq] at ho
    obtain ⟨k, hk⟩ := mem_iUnion.1 ho
    exact (hz k).2 hk
  -- a.s. `inf_k M̃(D k) = 0`
  have hY : ∀ᵐ ω ∂P, ⨅ k, etaChaos W γ δ (D k) ω = 0 := by
    have hm : Measurable fun ω => ⨅ k, etaChaos W γ δ (D k) ω :=
      Measurable.iInf fun k => measurable_etaChaos hW γ δ (D k)
    refine (lintegral_eq_zero_iff hm).1 (le_antisymm ?_ zero_le)
    rw [← hDvol]
    refine le_iInf fun k => ?_
    exact (lintegral_mono fun ω => iInf_le _ k).trans (lintegral_etaChaos_le hW γ δ (hDm k))
  have hT : ∀ᵐ ω ∂P, Tendsto (fun n => etaApprox W γ δ n B ω) atTop
      (𝓝 (etaChaos W γ δ B ω)) := ae_tendsto_etaApprox hW γ δ hB (hfin subset_rfl)
  have hT1 : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n => etaApprox W γ δ n (B ∩ innerSq k) ω) atTop
      (𝓝 (etaChaos W γ δ (B ∩ innerSq k) ω)) := ae_all_iff.2 fun k =>
    ae_tendsto_etaApprox hW γ δ (hB.inter (measurableSet_innerSq k)) (hfin inter_subset_left)
  have hT2 : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n => etaApprox W γ δ n (D k) ω) atTop
      (𝓝 (etaChaos W γ δ (D k) ω)) := ae_all_iff.2 fun k =>
    ae_tendsto_etaApprox hW γ δ (hDm k) (hfin diff_subset)
  filter_upwards [hY, hT, hT1, hT2] with ω hY hT hT1 hT2
  have hsplit : ∀ k, etaChaos W γ δ B ω =
      etaChaos W γ δ (B ∩ innerSq k) ω + etaChaos W γ δ (D k) ω := by
    intro k
    refine tendsto_nhds_unique hT ?_
    have e : (fun n => etaApprox W γ δ n B ω) = fun n =>
        etaApprox W γ δ n (B ∩ innerSq k) ω + etaApprox W γ δ n (D k) ω := by
      funext n
      exact (lintegral_inter_add_diff _ B (measurableSet_innerSq k)).symm
    rw [e]
    exact (hT1 k).add (hT2 k)
  calc etaChaos W γ δ B ω
      ≤ ⨅ k, ((⨆ l, etaChaos W γ δ (B ∩ innerSq l) ω) + etaChaos W γ δ (D k) ω) :=
        le_iInf fun k => (hsplit k).le.trans (add_le_add_left (le_iSup
          (fun l => etaChaos W γ δ (B ∩ innerSq l) ω) k) _)
    _ = (⨆ l, etaChaos W γ δ (B ∩ innerSq l) ω) + ⨅ k, etaChaos W γ δ (D k) ω :=
        (ENNReal.add_iInf).symm
    _ = ⨆ l, etaChaos W γ δ (B ∩ innerSq l) ω := by rw [hY, add_zero]

/-- **DZZ l. 1193–1195, limit step** for a compact `B ⊆ 𝕍`: a.s., for every `c ≥ 0`, the density
comparison for large `n` (a.e. on `B`) gives `c M̃_{γ,δ,η}(B) ≤ M^W(B)`. -/
theorem ae_ofReal_mul_etaChaos_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (δ : ℝ) {B : Set ℂ} (hB : IsCompact B) (hBV : B ⊆ dzzV) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, (∀ᶠ n in atTop, ∀ᵐ z ∂(volume.restrict B),
      ENNReal.ofReal c * etaDens W γ δ n z ω ≤ wickDensC hW γ n z ω) →
      ENNReal.ofReal c * etaChaos W γ δ B ω ≤ wickQArea γ W ω B := by
  have hK : ∀ k, IsCompact (B ∩ innerSq k) := fun k => hB.inter_right (isClosed_innerSq k)
  have hT : ∀ᵐ ω ∂P, ∀ k, Tendsto (fun n => etaApprox W γ δ n (B ∩ innerSq k) ω) atTop
      (𝓝 (etaChaos W γ δ (B ∩ innerSq k) ω)) := ae_all_iff.2 fun k =>
    ae_tendsto_etaApprox hW γ δ (hK k).measurableSet
      (volume_lt_top_of_subset_dzzV (inter_subset_left.trans hBV)).ne
  filter_upwards [ae_isVagueLimitOn_wickMeasC hW hγ hγ2, hT,
    ae_etaChaos_le_iSup_inner hW γ δ hB.measurableSet hBV] with ω hv hT hsup c hd
  refine (mul_le_mul_right hsup _).trans ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun k => ?_
  refine (ofReal_mul_etaChaos_le_of_compact hW hv (hK k)
    (inter_subset_right.trans (innerSq_subset_openSquare k)) ?_ (hT k)).trans
    (measure_mono inter_subset_left)
  filter_upwards [hd] with n hn
  exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hn

end DZZ
end LQGMetric
