/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea2
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeCirc
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc4
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Fact
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgCont
import Mathlib.Topology.UrysohnsLemma

/-!
Ding–Gwynne (arXiv:1807.01072) show that adding a continuous function `f` to a GFF `h`
multiplies its LQG area measure by `e^{γ f}`.

The cone field of DMS Def. 4.10 (`coneField (lateralPartC X) A Q`) is a whole-plane GFF plus a
function continuous on `ℂ \ {0}`. This file proves the deterministic density-change statement for the
whole-plane approximations `areaApproxC` on an open set `U` on which the added function `g` is
continuous (only local integrability on `ℂ` is assumed, so `g` may be singular off `U`):

* `tendsto_mollAvg_ofFunC`: the mollified circle averages of `ofFunC g` converge to the circle
  average of `g` on circles inside `U` (localization of LM's `CircleAvg.tendsto_mollAvg_ofCont`
  through a Urysohn cut-off, as in `ConeCirc.tendsto_mollAvg_radial`);
* `circleAvg_add_ofFunC`: `(x + g)_r(z) = x_r(z) + g_r(z)` where the circle average of `x` exists;
* `tendstoUniformlyOn_circleAverage`: `g_{2^{-k}} → g` uniformly on compacts of `U` (the argument
  of LM `DG.tendstoUniformlyOn_circleAvg`, localized);
* **`isVagueLimitOn_areaApproxC_of_shift`**: if `areaApproxC γ x → μ` vaguely on `U` and the
  circle averages of `y` are those of `x` plus `ψ_k → g` (uniformly on compacts of `U`) then
  `areaApproxC γ y → e^{γ g} μ` vaguely on `U` (LM `DG.tendsto_integral_mul_of_unif`);
* **`isVagueLimitOn_areaApproxC_add_ofFunC`**: the case `y = x + ofFunC g`.

Own elementary glue (Ding–Gwynne state the density change); the analytic lemmas are copied and adapted
from LQGMetric (`Papers/DG/S3D105Mu.lean`, `Papers/DG/S3D105Sc4.lean`, `Field/CircleAvgCont.lean`)
and `ConeCirc.lean`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort

namespace ConeArea3

open LQGMetric

/-! ### Circle averages of `ofFunC g` for `g` continuous on an open set -/

/-- a continuous function agreeing with `g` near a compact `S ⊆ U` (`g` continuous on `U`) -/
lemma exists_continuous_eqOn_thickening {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContinuousOn g U) {S : Set ℂ} (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ δ > 0, ∃ G : C(ℂ, ℝ), EqOn G g (thickening δ S) := by
  obtain ⟨δ, hδ, hsub⟩ := hS.exists_cthickening_subset_open hU hSU
  have hcl : IsCompact (closure (thickening δ S)) :=
    hS.cthickening.of_isClosed_subset isClosed_closure (closure_thickening_subset_cthickening δ S)
  have hts : cthickening (δ / 2) S ⊆ thickening δ S :=
    cthickening_subset_thickening' hδ (by linarith) S
  obtain ⟨χ, hχs, hχ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_thickening hcl
    isClosed_cthickening hts
  have hχU : tsupport χ ⊆ U := hχs.trans (thickening_subset_cthickening δ S |>.trans hsub)
  refine ⟨δ / 2, by linarith, ⟨fun z => χ z * g z, ?_⟩, fun z hz => ?_⟩
  · refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact χ.continuous.continuousAt.mul (hg.continuousAt (hU.mem_nhds hz))
    · have h0 : (χ : ℂ → ℝ) =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hχU h)
      have h1 : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 z] fun w => χ w * g w :=
        Filter.Eventually.mono h0 fun w hw => by
          simp only [Pi.zero_apply] at hw
          simp [hw]
      exact continuousAt_const.congr h1
  · have : χ z = 1 := hχ1 (thickening_subset_cthickening _ _ hz)
    simp [this]

/-- **mollified circle averages of `ofFunC g`** on a circle inside the open set where `g` is
continuous (LM `CircleAvg.tendsto_mollAvg_ofCont`, localized) -/
theorem tendsto_mollAvg_ofFunC {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume) {U : Set ℂ}
    (hU : IsOpen U) (hg : ContinuousOn g U) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzU : sphere z r ⊆ U) :
    Tendsto (fun n => CircleAvg.mollAvg (ofFunC g) n z r) atTop
      (𝓝 (Real.circleAverage g z r)) := by
  obtain ⟨δ, hδ, G, hG⟩ := exists_continuous_eqOn_thickening hU hg (isCompact_sphere z r) hzU
  have habs : |r| = r := abs_of_pos hr
  have hc : Real.circleAverage (⇑G) z r = Real.circleAverage g z r := by
    apply Real.circleAverage_congr_sphere
    intro x hx
    rw [habs] at hx
    exact hG (self_subset_thickening hδ _ hx)
  have hlim := CircleAvg.tendsto_mollAvg_ofCont G r z
  rw [hc] at hlim
  have hev : ∀ᶠ n : ℕ in atTop, (2 : ℝ)⁻¹ ^ n ≤ δ :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).eventually
      (Iic_mem_nhds hδ)
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  unfold CircleAvg.mollAvg
  apply Real.circleAverage_congr_sphere
  intro x hx
  rw [habs] at hx
  refine ConeCirc.ofFunC_bumpTest_eq G.continuous.locallyIntegrable hgl (δ := δ) (fun y hy => ?_) hn
  exact hG (mem_thickening_iff.2 ⟨x, hx, hy⟩)

/-- **`(x + g)_r(z) = x_r(z) + g_r(z)`** wherever the circle average of `x` exists as a limit -/
theorem circleAvg_add_ofFunC {x : Field} {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume)
    {U : Set ℂ} (hU : IsOpen U) (hg : ContinuousOn g U) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hzU : sphere z r ⊆ U) {a : ℝ}
    (ha : Tendsto (fun n => CircleAvg.mollAvg x n z r) atTop (𝓝 a)) :
    circleAvg (x + ofFunC g) r z = circleAvg x r z + Real.circleAverage g z r := by
  rw [CircleAvg.circleAvg_eq_of_tendsto ha]
  apply CircleAvg.circleAvg_eq_of_tendsto
  have hsplit : ∀ n, CircleAvg.mollAvg (x + ofFunC g) n z r =
      CircleAvg.mollAvg x n z r + CircleAvg.mollAvg (ofFunC g) n z r := by
    intro n
    simp only [CircleAvg.mollAvg_eq, add_apply]
  simp_rw [hsplit]
  exact ha.add (tendsto_mollAvg_ofFunC hgl hU hg hr hzU)

/-- circle averages of a measurable function are measurable in the centre -/
lemma measurable_circleAverage {g : ℂ → ℝ} (hg : Measurable g) (r : ℝ) :
    Measurable fun z => Real.circleAverage g z r := by
  have hm : Measurable fun q : ℂ × ℝ => g (circleMap q.1 r q.2) := hg.comp (by
    simp only [circleMap]; fun_prop)
  have := (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc 0 (2 * Real.pi)))).const_smul (2 * Real.pi)⁻¹
  convert this.measurable using 1
  funext z
  simp only [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rfl

/-- **`g_{2^{-k}} → g` uniformly on compacts of `U`** (LM `DG.tendstoUniformlyOn_circleAvg`
localized to the open set of continuity) -/
theorem tendstoUniformlyOn_circleAverage {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContinuousOn g U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn (fun k z => Real.circleAverage g z (QuantumZipper.radius k)) g atTop K := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hu := hK.cthickening.uniformContinuousOn_of_continuous (hg.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηu⟩ := hu (ε / 2) (by positivity)
  have hr : Tendsto QuantumZipper.radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hr.eventually (gt_mem_nhds (lt_min hη hδ))] with k hk z hz
  set r := QuantumZipper.radius k
  have hr0 : 0 < r := QuantumZipper.radius_pos k
  have habs : |r| = r := abs_of_pos hr0
  have hk1 : r < η := lt_of_lt_of_le hk (min_le_left _ _)
  have hk2 : r < δ := lt_of_lt_of_le hk (min_le_right _ _)
  have hsph : ∀ w ∈ sphere z |r|, w ∈ cthickening δ K := fun w hw => by
    rw [habs, mem_sphere] at hw
    exact mem_cthickening_of_dist_le w z δ K hz (by linarith)
  have hci : CircleIntegrable g z r :=
    ContinuousOn.circleIntegrable' ((hg.mono hsub).mono fun w hw => hsph w hw)
  have hconst : CircleIntegrable (fun _ => g z) z r :=
    ContinuousOn.circleIntegrable' continuousOn_const
  have e : Real.circleAverage (fun w => g w - g z) z r = Real.circleAverage g z r - g z := by
    rw [Real.circleAverage_fun_sub hci hconst, Real.circleAverage_const]
  have hle : Real.circleAverage (fun w => |g w - g z|) z r ≤ ε / 2 := by
    refine Real.circleAverage_mono_on_of_le_circle
      (ContinuousOn.circleIntegrable' ?_) fun w hw => ?_
    · exact (((hg.mono hsub).mono fun w hw => hsph w hw).sub continuousOn_const).abs
    · have h1 := hsph w hw
      have h2 : z ∈ cthickening δ K := self_subset_cthickening K hz
      rw [habs, mem_sphere] at hw
      have := hηu w h1 z h2 (by rw [hw]; exact hk1)
      rw [Real.dist_eq] at this
      exact this.le
  have h3 := (Real.abs_circleAverage_le_circleAverage_abs (f := fun w => g w - g z)
    (c := z) (R := r)).trans hle
  rw [e] at h3
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-! ### The density factor -/

/-- the density of `areaApproxC γ x k` -/
lemma areaApproxC_eq (γ : ℝ) (x : Field) (k : ℕ) :
    areaApproxC γ x k = volume.withDensity fun z => ENNReal.ofReal
      (QuantumZipper.radius k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg x (QuantumZipper.radius k) z)) :=
  rfl

lemma measurable_circleAvg_center (x : Field) (r : ℝ) : Measurable fun z => circleAvg x r z :=
  measurable_circleAvg.comp (f := fun z : ℂ => (x, r, z))
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- **Deterministic density-change form**: if `areaApproxC γ x → μ` vaguely on the open set `U` and, on
every compact `K ⊆ U` at fine scales, the circle averages of `y` are a.e. those of `x` plus
`ψ_k`, with `ψ_k → g` uniformly on compacts of `U` (`g` continuous on `U`), then
`areaApproxC γ y → e^{γ g} μ` vaguely on `U` -/
theorem isVagueLimitOn_areaApproxC_of_shift {γ : ℝ} {x y : Field} {U : Set ℂ} (hU : IsOpen U)
    {μ : Measure ℂ} (hx : QuantumZipper.IsVagueLimitOn U (areaApproxC γ x) μ)
    {g : ℂ → ℝ} (hgm : Measurable g) (hg : ContinuousOn g U)
    {ψ : ℕ → ℂ → ℝ} (hψm : ∀ k, Measurable (ψ k))
    (hψ : ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn ψ g atTop K)
    (hxy : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ K →
      circleAvg y (QuantumZipper.radius k) z = circleAvg x (QuantumZipper.radius k) z + ψ k z) :
    QuantumZipper.IsVagueLimitOn U (areaApproxC γ y)
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) := by
  have hρm : Measurable fun z => Real.exp (γ * g z) :=
    Real.measurable_exp.comp (hgm.const_mul γ)
  refine ⟨withDensity_absolutelyContinuous μ _ hx.1, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · -- finiteness on compacts
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hg.mono hKU)
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (Real.exp (γ * g z)) ∂μ
        ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp (|γ| * M)) ∂μ := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h1 := hM z hz
          rw [Real.norm_eq_abs] at h1
          calc γ * g z ≤ |γ * g z| := le_abs_self _
            _ = |γ| * |g z| := abs_mul _ _
            _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = ENNReal.ofReal (Real.exp (|γ| * M)) * μ K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hx.2.1 K hK hKU)
  -- the test function `F = f e^{γ g}`
  set F : ℂ → ℝ := fun z => f z * Real.exp (γ * g z) with hF
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact hf.continuousAt.mul (Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul (hg.continuousAt (hU.mem_nhds hz))))
    · have h0 : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hfU h)
      have h1 : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 z] F :=
        Filter.Eventually.mono h0 fun w hw => by
          simp only [Pi.zero_apply] at hw
          simp [hF, hw]
      exact continuousAt_const.congr h1
  have hFs : tsupport F ⊆ tsupport f := tsupport_mul_subset_left
  have hFcs : HasCompactSupport F := hfc.mul_right
  set e : ℕ → ℂ → ℝ := fun k z => Real.exp (γ * (ψ k z - g z)) with he
  have hem : ∀ k, Measurable (e k) := fun k =>
    Real.measurable_exp.comp (((hψm k).sub hgm).const_mul γ)
  have hK : IsCompact (tsupport f) := hfc
  have hunif : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ tsupport F, |e k z - 1| < η := by
    intro η hη
    set η' := min 1 (η / 4) / (|γ| + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hψ _ hK hfU) η' hη'0] with k hk z hz
    have h1 := hk z (hFs hz)
    rw [Real.dist_eq, abs_sub_comm] at h1
    have h2 : |γ * (ψ k z - g z)| < min 1 (η / 4) := by
      rw [abs_mul]
      calc |γ| * |ψ k z - g z| ≤ (|γ| + 1) * |ψ k z - g z| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (|γ| + 1) * η' := mul_lt_mul_of_pos_left h1 (by positivity)
        _ = min 1 (η / 4) := by rw [hη']; field_simp
    have h3 := Real.abs_exp_sub_one_le (h2.le.trans (min_le_left _ _))
    have h4 : min 1 (η / 4) ≤ η / 4 := min_le_right _ _
    show |Real.exp (γ * (ψ k z - g z)) - 1| < η
    linarith
  have hlim := DG.tendsto_integral_mul_of_unif hx hem hFc hFcs (hFs.trans hfU) hunif
  have hval : ∫ z, f z ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) =
      ∫ z, F z ∂μ := by
    rw [GMCIdent4.integral_withDensity_ofReal hρm (fun z => (Real.exp_pos _).le)]
    simp only [hF, mul_comm]
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [hxy _ hK hfU] with k hk
  have hDm : ∀ w : Field, Measurable fun z => QuantumZipper.radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg w (QuantumZipper.radius k) z) := fun w =>
    measurable_const.mul (Real.measurable_exp.comp
      ((measurable_circleAvg_center w _).const_mul γ))
  have hD0 : ∀ (w : Field) z, 0 ≤ QuantumZipper.radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg w (QuantumZipper.radius k) z) := fun w z =>
    mul_nonneg (Real.rpow_nonneg (QuantumZipper.radius_pos k).le _) (Real.exp_pos _).le
  rw [areaApproxC_eq, areaApproxC_eq, GMCIdent4.integral_withDensity_ofReal (hDm x) (hD0 x),
    GMCIdent4.integral_withDensity_ofReal (hDm y) (hD0 y)]
  refine integral_congr_ae ?_
  filter_upwards [hk] with z hz
  by_cases hzK : z ∈ tsupport f
  · rw [hz hzK]
    have : Real.exp (γ * (circleAvg x (QuantumZipper.radius k) z + ψ k z)) =
        Real.exp (γ * circleAvg x (QuantumZipper.radius k) z) *
          (Real.exp (γ * g z) * Real.exp (γ * (ψ k z - g z))) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    simp only [hF, he, this]
    ring
  · have h0 : f z = 0 := image_eq_zero_of_notMem_tsupport hzK
    simp [hF, h0]

/-- **Density change for `x + g`**: if `areaApproxC γ x → μ` vaguely on `U`, the circle averages of `x`
exist at a.e. point and every dyadic scale, and `g` is locally integrable and continuous on `U`,
then `areaApproxC γ (x + g) → e^{γ g} μ` vaguely on `U` -/
theorem isVagueLimitOn_areaApproxC_add_ofFunC {γ : ℝ} {x : Field} {U : Set ℂ} (hU : IsOpen U)
    {μ : Measure ℂ} (hx : QuantumZipper.IsVagueLimitOn U (areaApproxC γ x) μ)
    (hc : ConeArea.HasCircleAvgs x) {g : ℂ → ℝ} (hgm : Measurable g)
    (hgl : LocallyIntegrable g volume) (hg : ContinuousOn g U) :
    QuantumZipper.IsVagueLimitOn U (areaApproxC γ (x + ofFunC g))
      (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * g z))) := by
  refine isVagueLimitOn_areaApproxC_of_shift hU hx hgm hg
    (fun k => measurable_circleAverage hgm _) (fun K hK hKU =>
      tendstoUniformlyOn_circleAverage hU hg hK hKU) fun K hK hKU => ?_
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hr : Tendsto QuantumZipper.radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [hr.eventually (gt_mem_nhds hδ)] with k hk
  filter_upwards [hc k] with z ⟨a, ha⟩ hzK
  refine circleAvg_add_ofFunC hgl hU hg (QuantumZipper.radius_pos k) (fun w hw => hsub ?_) ha
  rw [mem_sphere] at hw
  exact mem_cthickening_of_dist_le w z δ K hzK (by linarith)

end ConeArea3

end MatedCRTHarmonic.MoTPort
