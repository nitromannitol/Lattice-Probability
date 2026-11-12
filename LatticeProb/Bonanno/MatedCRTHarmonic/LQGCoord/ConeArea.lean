/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.ConeArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeOfFun
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea5

/-!
# The area of a cone-type field along all radii (deterministic)

Let `h = X − ofFunC g₁ + ofFunC g₂` where `X` is a field whose area approximations
converge along all radii (`HasAreaLimitS γ X μX`), and `g₁, g₂` are measurable, locally integrable,
continuous off the cone point `0`, with `G = g₂ − g₁ ≤ c(−log|w|) + C` near `0` (the α-log
singularity of the quantum cone, `c ≥ 0`). If moreover the weighted masses of `X` near `0` are
uniformly small (`ConeGood.tight`, proved for the whole-plane GFF in `ConeTight`), then

  `areaS γ h s → coneMeasure γ μX g₁ g₂ = e^{γ G} 1_{ℂ∖{0}} μX` vaguely on `ℂ` as `s → 0⁺`

(`hasAreaLimitS_cone`). Proof: `areaS γ h s = e^{γ G_s} areaS γ X s` with `G_s(z) = ⨍_{∂B(z,s)} G`
(`areaS_cone_eq`, for a.e. `z`); off `0`, `G_s → G` uniformly on compacts, so LQGMetric's
`DG.tendsto_integral_mul_of_unif` gives the punctured limit; near `0`, Jensen's formula
(MoTPort `circleAverage_logBound`) bounds `e^{γ G_s}` by `e^{γC} max(|z|, s)^{−γc}`, whence
tightness; QuantumZipper's `isVagueLimitOn_of_local_of_tight` glues, along every sequence of
radii (the filter `𝓝[>] 0` is countably generated). This is the continuum version of MoTPort's
`ConeArea2`–`ConeArea5` (dyadic radii).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling QuantumZipper

/-- `G_s(z) = ⨍_{∂B(z,s)} g₂ − ⨍_{∂B(z,s)} g₁` -/
def coneShift (g₁ g₂ : ℂ → ℝ) (s : ℝ) (z : ℂ) : ℝ :=
  Real.circleAverage g₂ z s - Real.circleAverage g₁ z s

lemma measurable_coneShift {g₁ g₂ : ℂ → ℝ} (h₁ : Measurable g₁) (h₂ : Measurable g₂) (s : ℝ) :
    Measurable (coneShift g₁ g₂ s) :=
  (MoTPort.ConeArea3.measurable_circleAverage h₂ s).sub
    (MoTPort.ConeArea3.measurable_circleAverage h₁ s)

/-- The deterministic hypotheses on a cone-type field `X − ofFunC g₁ + ofFunC g₂`. -/
structure ConeGood (γ : ℝ) (X : DistC) (g₁ g₂ : ℂ → ℝ) (μX : Measure ℂ) (c : ℝ) : Prop where
  good : GoodCirc X
  scale : HasScaleCircleAvgs X
  area : HasAreaLimitS γ X μX
  meas₁ : Measurable g₁
  meas₂ : Measurable g₂
  li₁ : LocallyIntegrable g₁ volume
  li₂ : LocallyIntegrable g₂ volume
  cont₁ : ContinuousOn g₁ {0}ᶜ
  cont₂ : ContinuousOn g₂ {0}ᶜ
  c_nonneg : 0 ≤ c
  growth : ∃ C ρ₁ : ℝ, 0 < ρ₁ ∧ ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ₁ →
    g₂ w - g₁ w ≤ c * -Real.log ‖w‖ + C
  tight : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s ≤ r₀ →
    ∫⁻ w in ball 0 r₀, ENNReal.ofReal (max ‖w‖ s ^ (-(γ * c))) ∂areaS γ X s ≤ ENNReal.ofReal ε

/-- the area measure of the cone-type field -/
def coneMeasure (γ : ℝ) (μX : Measure ℂ) (g₁ g₂ : ℂ → ℝ) : Measure ℂ :=
  (μX.restrict {0}ᶜ).withDensity fun z => ENNReal.ofReal (Real.exp (γ * (g₂ z - g₁ z)))

variable {γ : ℝ} {X : DistC} {g₁ g₂ : ℂ → ℝ} {μX : Measure ℂ} {c : ℝ}

/-- `areaS γ h s = e^{γ G_s} areaS γ X s` -/
theorem areaS_cone_eq (hc : ConeGood γ X g₁ g₂ μX c) {s : ℝ} (hs : 0 < s) :
    areaS γ (X - ofFunC g₁ + ofFunC g₂) s =
      (areaS γ X s).withDensity fun z => ENNReal.ofReal (Real.exp (γ * coneShift g₁ g₂ s z)) := by
  have hm : Measurable fun z => ENNReal.ofReal (Real.exp (γ * coneShift g₁ g₂ s z)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_coneShift hc.meas₁ hc.meas₂ s).const_mul γ))
  rw [show areaS γ (X - ofFunC g₁ + ofFunC g₂) s =
      volume.withDensity (densS γ (X - ofFunC g₁ + ofFunC g₂) s) from rfl,
    show areaS γ X s = volume.withDensity (densS γ X s) from rfl,
    ← withDensity_mul _ (measurable_densS γ X s) hm]
  refine withDensity_congr_ae ?_
  filter_upwards [hc.scale s hs, ae_norm_ne s] with z hz hne
  simp only [densS, Pi.mul_apply]
  rw [circleAvg_cone hc.li₁ hc.li₂ hc.cont₁ hc.cont₂ hs hne hz,
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hs.le _) (Real.exp_pos _).le)]
  congr 1
  rw [coneShift, show γ * (circleAvg X s z - Real.circleAverage g₁ z s +
      Real.circleAverage g₂ z s) = γ * circleAvg X s z +
      γ * (Real.circleAverage g₂ z s - Real.circleAverage g₁ z s) by ring, Real.exp_add]
  ring

/-- **`g_s → g` uniformly on compacts of the continuity set** (continuum version of MoTPort's
`ConeArea3.tendstoUniformlyOn_circleAverage`) -/
theorem tendstoUniformlyOn_circleAverage_nhdsGT {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContinuousOn g U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn (fun r z => Real.circleAverage g z r) g (𝓝[>] 0) K := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hu := hK.cthickening.uniformContinuousOn_of_continuous (hg.mono hsub)
  rw [Metric.uniformContinuousOn_iff] at hu
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨η, hη, hηu⟩ := hu (ε / 2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hη hδ)] with r hr z hz
  have hr0 : 0 < r := hr.1
  have habs : |r| = r := abs_of_pos hr0
  have hk1 : r < η := lt_of_lt_of_le hr.2 (min_le_left _ _)
  have hk2 : r < δ := lt_of_lt_of_le hr.2 (min_le_right _ _)
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

/-! ## The punctured limit -/

lemma isVagueLimitOn_punctured_of_hasAreaLimitS (hX : HasAreaLimitS γ X μX) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) :
    IsVagueLimitOn ({0}ᶜ) (fun n => areaS γ X (s n)) (μX.restrict {0}ᶜ) := by
  refine ⟨?_, fun K hK _ => ?_, fun f hf hfc hfU => ?_⟩
  · rw [Measure.restrict_apply (measurableSet_singleton (0 : ℂ)).compl.compl]
    simp
  · exact (Measure.restrict_apply_le _ K).trans_lt (hX.1 K hK)
  · have h := (hX.2 f hf hfc).comp hs
    have e : ∫ z, f z ∂(μX.restrict {0}ᶜ) = ∫ z, f z ∂μX := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
      have hz0 : z = 0 := by simpa using hz
      subst hz0
      exact image_eq_zero_of_notMem_tsupport fun h' => hfU h' rfl
    rw [e]
    exact h

/-- uniform convergence of the shifts on compacts off `0`, along a sequence of radii -/
lemma eventually_unif_coneShift (hc : ConeGood γ X g₁ g₂ μX c) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ {0}ᶜ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ z ∈ K, |coneShift g₁ g₂ (s n) z - (g₂ z - g₁ z)| < η := by
  have hU : IsOpen ({0}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h₁ := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_circleAverage_nhdsGT hU hc.cont₁ hK hKU) (η / 2) (by positivity)
  have h₂ := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_circleAverage_nhdsGT hU hc.cont₂ hK hKU) (η / 2) (by positivity)
  filter_upwards [hs.eventually h₁, hs.eventually h₂] with n hn₁ hn₂ z hz
  have a₁ := hn₁ z hz
  have a₂ := hn₂ z hz
  rw [Real.dist_eq] at a₁ a₂
  rw [coneShift]
  calc |Real.circleAverage g₂ z (s n) - Real.circleAverage g₁ z (s n) - (g₂ z - g₁ z)|
      ≤ |g₂ z - Real.circleAverage g₂ z (s n)| + |g₁ z - Real.circleAverage g₁ z (s n)| := by
        rw [abs_sub_comm (g₂ z), abs_sub_comm (g₁ z)]
        have := abs_sub (Real.circleAverage g₂ z (s n) - g₂ z)
          (Real.circleAverage g₁ z (s n) - g₁ z)
        calc _ = |(Real.circleAverage g₂ z (s n) - g₂ z) -
              (Real.circleAverage g₁ z (s n) - g₁ z)| := by ring_nf
          _ ≤ _ := this
    _ < η / 2 + η / 2 := add_lt_add a₂ a₁
    _ = η := by ring

/-- **the punctured limit along a sequence of radii** -/
theorem isVagueLimitOn_cone_punctured (hc : ConeGood γ X g₁ g₂ μX c) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) :
    IsVagueLimitOn ({0}ᶜ) (fun n => areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n))
      (coneMeasure γ μX g₁ g₂) := by
  set U : Set ℂ := {0}ᶜ with hUdef
  have hU : IsOpen U := isOpen_compl_singleton
  have hx := isVagueLimitOn_punctured_of_hasAreaLimitS hc.area hs
  set G : ℂ → ℝ := fun z => g₂ z - g₁ z with hGdef
  have hGm : Measurable G := hc.meas₂.sub hc.meas₁
  have hG : ContinuousOn G U := hc.cont₂.sub hc.cont₁
  have hρm : Measurable fun z => Real.exp (γ * G z) := Real.measurable_exp.comp (hGm.const_mul γ)
  refine ⟨withDensity_absolutelyContinuous _ _ hx.1, fun K hK hKU => ?_, fun f hf hfc hfU => ?_⟩
  · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hG.mono hKU)
    rw [coneMeasure, withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, ENNReal.ofReal (Real.exp (γ * G z)) ∂(μX.restrict U)
        ≤ ∫⁻ _ in K, ENNReal.ofReal (Real.exp (|γ| * M)) ∂(μX.restrict U) := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h1 := hM z hz
          rw [Real.norm_eq_abs] at h1
          calc γ * G z ≤ |γ * G z| := le_abs_self _
            _ = |γ| * |G z| := abs_mul _ _
            _ ≤ |γ| * M := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = ENNReal.ofReal (Real.exp (|γ| * M)) * (μX.restrict U) K := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hx.2.1 K hK hKU)
  set F : ℂ → ℝ := fun z => f z * Real.exp (γ * G z) with hF
  have hFc : Continuous F := by
    refine continuous_iff_continuousAt.2 fun z => ?_
    by_cases hz : z ∈ U
    · exact hf.continuousAt.mul (Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul (hG.continuousAt (hU.mem_nhds hz))))
    · have h0 : f =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hfU h)
      have h1 : (fun _ : ℂ => (0 : ℝ)) =ᶠ[𝓝 z] F :=
        Filter.Eventually.mono h0 fun w hw => by
          simp only [Pi.zero_apply] at hw
          simp [hF, hw]
      exact continuousAt_const.congr h1
  have hFs : tsupport F ⊆ tsupport f := tsupport_mul_subset_left
  have hFcs : HasCompactSupport F := hfc.mul_right
  set e : ℕ → ℂ → ℝ := fun n z => Real.exp (γ * (coneShift g₁ g₂ (s n) z - G z)) with he
  have hem : ∀ n, Measurable (e n) := fun n =>
    Real.measurable_exp.comp (((measurable_coneShift hc.meas₁ hc.meas₂ _).sub hGm).const_mul γ)
  have hK : IsCompact (tsupport f) := hfc
  have hunif : ∀ η > 0, ∀ᶠ n in atTop, ∀ z ∈ tsupport F, |e n z - 1| < η := by
    intro η hη
    set η' := min 1 (η / 4) / (|γ| + 1) with hη'
    have hη'0 : 0 < η' := by positivity
    filter_upwards [eventually_unif_coneShift hc hs hK hfU hη'0] with n hn z hz
    have h1 := hn z (hFs hz)
    have h2 : |γ * (coneShift g₁ g₂ (s n) z - G z)| < min 1 (η / 4) := by
      rw [abs_mul]
      calc |γ| * |coneShift g₁ g₂ (s n) z - G z|
          ≤ (|γ| + 1) * |coneShift g₁ g₂ (s n) z - G z| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
        _ < (|γ| + 1) * η' := mul_lt_mul_of_pos_left h1 (by positivity)
        _ = min 1 (η / 4) := by rw [hη']; field_simp
    have h3 := Real.abs_exp_sub_one_le (h2.le.trans (min_le_left _ _))
    have h4 : min 1 (η / 4) ≤ η / 4 := min_le_right _ _
    show |Real.exp (γ * (coneShift g₁ g₂ (s n) z - G z)) - 1| < η
    linarith
  have hlim := DG.tendsto_integral_mul_of_unif hx hem hFc hFcs (hFs.trans hfU) hunif
  have hval : ∫ z, f z ∂(coneMeasure γ μX g₁ g₂) = ∫ z, F z ∂(μX.restrict U) := by
    rw [coneMeasure, DG.integral_withDensity_ofReal _ hρm (fun z => (Real.exp_pos _).le)]
    simp only [hF, mul_comm, hUdef]
  rw [hval]
  refine hlim.congr' ?_
  filter_upwards [hs.eventually self_mem_nhdsWithin] with n hn
  have hn0 : 0 < s n := hn
  have hsm : Measurable fun z => Real.exp (γ * coneShift g₁ g₂ (s n) z) :=
    Real.measurable_exp.comp ((measurable_coneShift hc.meas₁ hc.meas₂ _).const_mul γ)
  rw [areaS_cone_eq hc hn0, DG.integral_withDensity_ofReal _ hsm (fun z => (Real.exp_pos _).le)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  have : Real.exp (γ * coneShift g₁ g₂ (s n) z) =
      Real.exp (γ * G z) * Real.exp (γ * (coneShift g₁ g₂ (s n) z - G z)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [hF, he, this]
  ring

/-! ## Near the cone point -/

/-- Jensen's bound for the shift on circles inside the singular disc -/
lemma coneShift_le_logBound (hc : ConeGood γ X g₁ g₂ μX c) {C ρ₁ : ℝ}
    (hgb : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ρ₁ → g₂ w - g₁ w ≤ c * -Real.log ‖w‖ + C) {s : ℝ}
    (hs : 0 < s) {z : ℂ} (hzs : ‖z‖ ≠ s) (hzρ : ‖z‖ + s < ρ₁) :
    coneShift g₁ g₂ s z ≤ c * -Real.log (max ‖z‖ s) + C := by
  have habs : |s| = s := abs_of_pos hs
  have hsph0 : sphere z s ⊆ {0}ᶜ := sphere_subset_compl_zero hzs
  have hsph : ∀ w ∈ sphere z |s|, w ≠ 0 ∧ ‖w‖ < ρ₁ := fun w hw => by
    rw [habs] at hw
    refine ⟨fun h0 => hsph0 hw h0, ?_⟩
    rw [mem_sphere, dist_eq_norm] at hw
    have := norm_add_le z (w - z)
    simp only [add_sub_cancel] at this
    linarith
  have hi₁ : CircleIntegrable g₁ z s :=
    (hc.cont₁.mono (by rw [habs]; exact hsph0)).circleIntegrable'
  have hi₂ : CircleIntegrable g₂ z s :=
    (hc.cont₂.mono (by rw [habs]; exact hsph0)).circleIntegrable'
  have hcs : ContinuousOn (fun w : ℂ => c * -Real.log ‖w‖ + C) (sphere z |s|) :=
    ((continuousOn_const.mul (Real.continuousOn_log.comp continuous_norm.continuousOn
      fun w hw => by simpa [norm_eq_zero] using (hsph w hw).1).neg).add continuousOn_const)
  rw [coneShift, ← Real.circleAverage_fun_sub hi₂ hi₁,
    ← MoTPort.ConeArea5.circleAverage_logBound c C z hs]
  exact Real.circleAverage_mono (hi₂.sub hi₁) hcs.circleIntegrable' fun w hw =>
    hgb w (hsph w hw).1 (hsph w hw).2

lemma exp_logBound_eq' {γ c C : ℝ} {m : ℝ} (hm : 0 < m) :
    Real.exp (γ * (c * -Real.log m + C)) = Real.exp (γ * C) * m ^ (-(γ * c)) := by
  rw [Real.rpow_def_of_pos hm, ← Real.exp_add]
  congr 1; ring

/-- **tightness at the cone point**, along a sequence of radii -/
theorem tight_cone (hγ : 0 < γ) (hc : ConeGood γ X g₁ g₂ μX c) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ᶠ n in atTop,
      areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) (ball 0 δ) ≤ ENNReal.ofReal ε := by
  obtain ⟨C, ρ₁, hρ₁, hgb⟩ := hc.growth
  obtain ⟨r₀, hr₀, hT⟩ := hc.tight (ε * Real.exp (-(γ * C))) (by positivity)
  set δ := min r₀ (ρ₁ / 2) with hδ
  have hδ0 : 0 < δ := lt_min hr₀ (by linarith)
  refine ⟨δ, hδ0, ?_⟩
  have hev : ∀ᶠ n in atTop, s n ∈ Ioo 0 δ :=
    hs.eventually (Ioo_mem_nhdsGT hδ0)
  filter_upwards [hev] with n hn
  have hn0 : 0 < s n := hn.1
  rw [areaS_cone_eq hc hn0, withDensity_apply _ measurableSet_ball]
  have hle : ∀ᵐ z ∂((areaS γ X (s n)).restrict (ball 0 δ)),
      ENNReal.ofReal (Real.exp (γ * coneShift g₁ g₂ (s n) z)) ≤
        ENNReal.ofReal (Real.exp (γ * C)) * ENNReal.ofReal (max ‖z‖ (s n) ^ (-(γ * c))) := by
    have hac : areaS γ X (s n) ≪ volume := withDensity_absolutelyContinuous _ _
    have h1 := hac.ae_le (ae_norm_ne (s n))
    filter_upwards [ae_restrict_of_ae h1, ae_restrict_mem measurableSet_ball] with z hz hzb
    have hzb' : ‖z‖ < δ := by simpa [mem_ball, dist_zero_right] using hzb
    have hzρ : ‖z‖ + s n < ρ₁ := by
      have : δ ≤ ρ₁ / 2 := min_le_right _ _
      linarith [hn.2]
    have hb := coneShift_le_logBound hc hgb hn0 hz hzρ
    have hm : 0 < max ‖z‖ (s n) := lt_max_of_lt_right hn0
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← exp_logBound_eq' hm]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hb hγ.le))
  refine (lintegral_mono_ae hle).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsub : ∫⁻ z in ball 0 δ, ENNReal.ofReal (max ‖z‖ (s n) ^ (-(γ * c))) ∂areaS γ X (s n) ≤
      ∫⁻ z in ball 0 r₀, ENNReal.ofReal (max ‖z‖ (s n) ^ (-(γ * c))) ∂areaS γ X (s n) :=
    lintegral_mono_set (ball_subset_ball (min_le_left _ _))
  calc ENNReal.ofReal (Real.exp (γ * C)) *
        ∫⁻ z in ball 0 δ, ENNReal.ofReal (max ‖z‖ (s n) ^ (-(γ * c))) ∂areaS γ X (s n)
      ≤ ENNReal.ofReal (Real.exp (γ * C)) * ENNReal.ofReal (ε * Real.exp (-(γ * C))) :=
        mul_le_mul' le_rfl (hsub.trans (hT (s n) hn0 (hn.2.le.trans (min_le_left _ _))))
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [mul_comm ε, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- eventual finiteness on compacts, along a sequence of radii -/
theorem fin_cone (hγ : 0 < γ) (hc : ConeGood γ X g₁ g₂ μX c) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) K < ⊤ := by
  obtain ⟨δ, hδ, hδev⟩ := tight_cone hγ hc hs 1 one_pos
  set K' := K \ ball 0 δ with hK'
  have hK'c : IsCompact K' := hK.diff isOpen_ball
  have hK'U : K' ⊆ {0}ᶜ := fun z hz h0 => by
    rw [mem_singleton_iff] at h0
    exact hz.2 (by rw [h0]; exact mem_ball_self hδ)
  obtain ⟨M, hM⟩ := hK'c.exists_bound_of_continuousOn ((hc.cont₂.sub hc.cont₁).mono hK'U)
  filter_upwards [hδev, eventually_unif_coneShift hc hs hK'c hK'U one_pos,
    hs.eventually self_mem_nhdsWithin] with n hn hun hn0
  have hn0' : 0 < s n := hn0
  have h1 : areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) K' < ⊤ := by
    rw [areaS_cone_eq hc hn0', withDensity_apply _ hK'c.measurableSet]
    calc ∫⁻ z in K', ENNReal.ofReal (Real.exp (γ * coneShift g₁ g₂ (s n) z)) ∂areaS γ X (s n)
        ≤ ∫⁻ _ in K', ENNReal.ofReal (Real.exp (γ * (M + 1))) ∂areaS γ X (s n) := by
          refine setLIntegral_mono measurable_const fun z hz => ?_
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left ?_ hγ.le))
          have a1 := hun z hz
          have a2 : |g₂ z - g₁ z| ≤ M := by
            have := hM z hz; simpa [Real.norm_eq_abs] using this
          linarith [(abs_lt.1 a1).2, le_abs_self (g₂ z - g₁ z)]
      _ = ENNReal.ofReal (Real.exp (γ * (M + 1))) * areaS γ X (s n) K' := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (areaS_lt_top_of_good hc.good hn0' hK'c)
  have hsub : K ⊆ ball 0 δ ∪ K' := fun z hz => by
    by_cases h : z ∈ ball 0 δ
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  calc areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) K
      ≤ areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) (ball 0 δ ∪ K') := measure_mono hsub
    _ ≤ areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) (ball 0 δ) +
        areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n) K' := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hn.trans_lt ENNReal.ofReal_lt_top, h1⟩

/-! ## The continuum area limit of the cone-type field -/

theorem isVagueLimitOn_cone_seq (hγ : 0 < γ) (hc : ConeGood γ X g₁ g₂ μX c) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝[>] 0)) :
    IsVagueLimitOn univ (fun n => areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n))
      (coneMeasure γ μX g₁ g₂) := by
  have hloc : IsVagueLimitOn (univ \ {0}) (fun n => areaS γ (X - ofFunC g₁ + ofFunC g₂) (s n))
      (coneMeasure γ μX g₁ g₂) := by
    rw [← compl_eq_univ_sdiff]
    exact isVagueLimitOn_cone_punctured hc hs
  exact AtomlessUncond.isVagueLimitOn_of_local_of_tight isOpen_univ (mem_univ 0) hloc
    (fun K hK _ => fin_cone hγ hc hs hK) (tight_cone hγ hc hs)

/-- **The continuum area limit of a cone-type field**: `areaS γ (X − g₁ + g₂) s →
coneMeasure γ μX g₁ g₂` vaguely on `ℂ` as `s → 0⁺`. -/
theorem hasAreaLimitS_cone (hγ : 0 < γ) (hc : ConeGood γ X g₁ g₂ μX c) :
    HasAreaLimitS γ (X - ofFunC g₁ + ofFunC g₂) (coneMeasure γ μX g₁ g₂) := by
  have hseq : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
      (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))
  refine ⟨fun K hK => (isVagueLimitOn_cone_seq hγ hc hseq).2.1 K hK (subset_univ _),
    fun f hf hfc => ?_⟩
  rw [tendsto_iff_seq_tendsto]
  intro s hs
  exact (isVagueLimitOn_cone_seq hγ hc hs).2.2 f hf hfc (subset_univ _)

end MatedCRTHarmonic.LQGCoord
