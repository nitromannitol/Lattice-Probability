/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPArea at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.WPOffsets
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.Transform
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D

/-!
# The whole-plane GFF: area approximations along all radii, on all of `ℂ`

For a whole-plane GFF `X` and `0 < γ < 2`, almost surely

* `ae_hasAreaLimitS_wp`: `areaS γ (X ω) s → lqgArea γ (X ω)` vaguely on `ℂ` as `s → 0⁺` (the
  continuum of radii; Sheffield–Wang arXiv:1605.06171 Thm 1.1 for the whole-plane GFF);
* `ae_hasScaleCircleAvgs_wp`: the circle averages are limits along every mollifier scale.

Proof of the first: the dyadic vague limit exists a.s. (MoTPort `ConeArea4.ae_areaGood_univ`,
Duplantier–Sheffield Prop. 1.1); for a countable family of bounded test functions
`1_{B̄(0,n+1)} d` (`d` in a countable dense subset of `C(ℂ, ℝ)`, compact-open topology), the
continuum limits exist a.s. (`ae_tendsto_wMass`, with `∫ g d(areaS s) = e^{γ X_δ(0)} wMass g s`);
a deterministic approximation argument (`hasAreaLimitS_of_dense`) passes to every continuous
compactly supported test function. Own elementary glue.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper MatedCRTHarmonic.CellScaling

/-! ## Integrals against the approximations -/

/-- the real density of `areaS γ h s` -/
def densR (γ : ℝ) (h : DistC) (s : ℝ) (z : ℂ) : ℝ :=
  s ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h s z)

lemma densR_nonneg (γ : ℝ) (h : DistC) {s : ℝ} (hs : 0 ≤ s) (z : ℂ) : 0 ≤ densR γ h s z :=
  mul_nonneg (Real.rpow_nonneg hs _) (Real.exp_pos _).le

lemma integral_areaS_eq (γ : ℝ) (h : DistC) {s : ℝ} (hs : 0 ≤ s) (g : ℂ → ℝ) :
    ∫ z, g z ∂areaS γ h s = ∫ z, densR γ h s z * g z := by
  rw [show areaS γ h s = volume.withDensity (densS γ h s) from rfl,
    integral_withDensity_eq_integral_toReal_smul (measurable_densS γ h s)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [smul_eq_mul]
  rw [show densS γ h s z = ENNReal.ofReal (densR γ h s z) from rfl,
    ENNReal.toReal_ofReal (densR_nonneg γ h hs z)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

omit [MeasurableSpace Ω] in
lemma integral_areaS_eq_wMass (γ δ : ℝ) {s : ℝ} (hs : 0 ≤ s) (g : ℂ → ℝ) (ω : Ω) :
    ∫ z, g z ∂areaS γ (X ω) s =
      Real.exp (γ * circleAvg (X ω) δ 0) * wMass γ X δ g s ω := by
  rw [integral_areaS_eq γ (X ω) hs, wMass, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [densR, wDens, cInc]
  rw [show γ * circleAvg (X ω) s z = γ * circleAvg (X ω) δ 0 +
    γ * (circleAvg (X ω) s z - circleAvg (X ω) δ 0) by ring, Real.exp_add]
  ring

/-- on the good event, the approximations are finite on compacts -/
lemma areaS_lt_top_of_good {γ : ℝ} {h : DistC} (hg : GoodCirc h) {s : ℝ} (hs : 0 < s)
    {K : Set ℂ} (hK : IsCompact K) : areaS γ h s K < ⊤ := by
  have h1 : ContinuousOn (fun z : ℂ => circleAvg h s z) K := by
    have := hg.comp (s := K) (continuous_const.prodMk continuous_id).continuousOn
      (fun z _ => (⟨hs, mem_univ _⟩ : (s, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)))
    exact this
  have hc : ContinuousOn (fun z => densR γ h s z) K := by
    unfold densR
    exact continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (h1.const_smul γ))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  rw [show areaS γ h s = volume.withDensity (densS γ h s) from rfl, withDensity_apply' _ K]
  calc ∫⁻ z in K, densS γ h s z ≤ ∫⁻ z in K, ENNReal.ofReal B := by
        refine setLIntegral_mono measurable_const (fun z hz => ?_)
        refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
        have := hB z hz
        rwa [Real.norm_eq_abs] at this
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

lemma integrable_areaS_of_good {γ : ℝ} {h : DistC} (hg : GoodCirc h) {s : ℝ} (hs : 0 < s)
    {K : Set ℂ} (hK : IsCompact K) {g : ℂ → ℝ} (hgm : AEStronglyMeasurable g (areaS γ h s))
    {C : ℝ} (hgC : ∀ z, |g z| ≤ C) (hg0 : ∀ z ∉ K, g z = 0) :
    Integrable g (areaS γ h s) := by
  have : IsFiniteMeasure ((areaS γ h s).restrict K) :=
    isFiniteMeasure_restrict.2 (areaS_lt_top_of_good hg hs hK).ne
  have hi : IntegrableOn g K (areaS γ h s) :=
    Integrable.of_bound hgm.restrict C (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hgC z)
  exact hi.integrable_of_forall_notMem_eq_zero hg0

/-! ## The deterministic approximation argument -/

/-- the window `B̄(0, n+1)` -/
def winS (n : ℕ) : Set ℂ := closedBall 0 ((n : ℝ) + 1)

/-- the window scale `4(n+1)` -/
def winδ (n : ℕ) : ℝ := 4 * ((n : ℝ) + 1)

lemma win_n (n : ℕ) : Win (winS n) (winδ n) where
  meas := measurableSet_closedBall
  pos := by unfold winδ; positivity
  sub := fun z hz => by
    simp only [winS, mem_closedBall, dist_zero_right] at hz
    unfold winδ; linarith

/-- the test function `1_{B̄(0,n+1)} d` -/
def winFun (n : ℕ) (d : C(ℂ, ℝ)) : ℂ → ℝ := (winS n).indicator d

lemma exists_winFun (n : ℕ) (d : C(ℂ, ℝ)) : ∃ M, WinFun (winS n) (winFun n d) M := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)).exists_bound_of_continuousOn
    d.continuous.continuousOn
  refine ⟨max B 0, ⟨d.continuous.measurable.indicator measurableSet_closedBall,
    fun z => ?_, fun z hz => indicator_of_notMem hz _⟩⟩
  by_cases hz : z ∈ winS n
  · rw [winFun, indicator_of_mem hz]
    have := hB z hz
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · rw [winFun, indicator_of_notMem hz, abs_zero]; exact le_max_right _ _

/-- **Approximation argument**: on the good event, the dyadic vague limit together with continuum
limits for the countable family `1_{B̄(0,n+1)} d`, `d ∈ D` (dense, containing `1`), gives the
continuum vague limit. -/
theorem hasAreaLimitS_of_dense {γ : ℝ} {h : DistC} (hg : GoodCirc h) {μ : Measure ℂ}
    (hμ : IsVagueLimitC (lqgAreaApprox γ h) μ) {D : Set C(ℂ, ℝ)} (hD : Dense D)
    (h1 : ContinuousMap.const ℂ (1 : ℝ) ∈ D)
    (hconv : ∀ n : ℕ, ∀ d ∈ D, ∃ ℓ, Tendsto (fun s => ∫ z, winFun n d z ∂areaS γ h s)
      (𝓝[>] 0) (𝓝 ℓ)) :
    HasAreaLimitS γ h μ := by
  refine ⟨hμ.1, fun f hf hfc => ?_⟩
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hfS : ∀ z ∉ winS n, f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport fun h' => hz
    (closedBall_subset_closedBall (by linarith) (hR h'))
  set b := winFun n (ContinuousMap.const ℂ (1 : ℝ)) with hb
  obtain ⟨ℓb, hℓb⟩ := hconv n _ h1
  have hKc : IsCompact (winS n) := isCompact_closedBall _ _
  -- the dyadic subsequence of the continuum limit
  have hdy : ∀ {g : ℂ → ℝ} {ℓ : ℝ}, Tendsto (fun s => ∫ z, g z ∂areaS γ h s) (𝓝[>] 0) (𝓝 ℓ) →
      Tendsto (fun k => ∫ z, g z ∂lqgAreaApprox γ h k) atTop (𝓝 ℓ) := fun ht =>
    ht.comp tendsto_dyadicScale
  have hℓb0 : 0 ≤ ℓb := by
    refine ge_of_tendsto hℓb ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [integral_areaS_eq γ h (le_of_lt hs)]
    refine integral_nonneg fun z => mul_nonneg (densR_nonneg γ h (le_of_lt hs) z) ?_
    simp only [winFun]
    exact indicator_nonneg (fun _ _ => zero_le_one) _
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη
  set η' := η / (4 * (ℓb + 1)) with hη'
  have hη'0 : 0 < η' := by positivity
  -- an approximating `d ∈ D`
  have hU : ∀ᶠ g in 𝓝 (⟨f, hf⟩ : C(ℂ, ℝ)), ∀ x ∈ winS n, dist (f x) (g x) < η' := by
    have ht := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      (tendsto_id (x := 𝓝 (⟨f, hf⟩ : C(ℂ, ℝ))))) _ hKc
    exact (Metric.tendstoUniformlyOn_iff.1 ht) η' hη'0
  obtain ⟨d, hdU, hdD⟩ := mem_closure_iff_nhds.1 (hD ⟨f, hf⟩) _ hU
  obtain ⟨ℓg, hℓg⟩ := hconv n d hdD
  set g := winFun n d with hgdef
  -- pointwise comparison
  have hfg : ∀ z, |f z - g z| ≤ η' * b z := by
    intro z
    by_cases hz : z ∈ winS n
    · simp only [hgdef, hb, winFun, indicator_of_mem hz, ContinuousMap.const_apply, mul_one]
      have := hdU z hz
      rw [Real.dist_eq] at this
      exact this.le
    · simp only [hgdef, hb, winFun, indicator_of_notMem hz, hfS z hz, sub_zero, abs_zero,
        mul_zero, le_refl]
  obtain ⟨Mg, hMg⟩ := exists_winFun n d
  obtain ⟨Mf, hMf⟩ := hf.bounded_above_of_compact_support hfc
  have hint : ∀ s : ℝ, 0 < s → ∀ {u : ℂ → ℝ} {C : ℝ}, Measurable u → (∀ z, |u z| ≤ C) →
      (∀ z ∉ winS n, u z = 0) → Integrable u (areaS γ h s) := fun s hs u C hu hC h0 =>
    integrable_areaS_of_good hg hs hKc hu.aestronglyMeasurable hC h0
  have hfb : ∀ z, |f z| ≤ Mf := fun z => by have := hMf z; rwa [Real.norm_eq_abs] at this
  have hbb : ∀ z, |b z| ≤ 1 := fun z => by
    simp only [hb, winFun]
    by_cases hz : z ∈ winS n
    · rw [indicator_of_mem hz]; simp
    · rw [indicator_of_notMem hz]; simp
  have hb0 : ∀ z ∉ winS n, b z = 0 := fun z hz => indicator_of_notMem hz _
  have hbm : Measurable b := measurable_const.indicator measurableSet_closedBall
  -- comparison of integrals against a measure for which all three are integrable
  have hcomp : ∀ ν : Measure ℂ, Integrable f ν → Integrable g ν → Integrable b ν →
      |∫ z, f z ∂ν - ∫ z, g z ∂ν| ≤ η' * ∫ z, b z ∂ν := by
    intro ν hfi hgi hbi
    rw [← integral_sub hfi hgi, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono (hfi.sub hgi).abs
      (hbi.const_mul η') fun z => hfg z)
  -- the dyadic limit of `∫ f`
  have hlimf : Tendsto (fun k => ∫ z, f z ∂lqgAreaApprox γ h k) atTop (𝓝 (∫ z, f z ∂μ)) :=
    hμ.2 f hf hfc
  have hpos : ∀ k, 0 < dyadicScale k := dyadicScale_pos
  have hk : ∀ k, |∫ z, f z ∂lqgAreaApprox γ h k - ∫ z, g z ∂lqgAreaApprox γ h k| ≤
      η' * ∫ z, b z ∂lqgAreaApprox γ h k := fun k =>
    hcomp _ (hint _ (hpos k) hf.measurable hfb hfS) (hint _ (hpos k) hMg.meas hMg.bdd hMg.zero)
      (hint _ (hpos k) hbm hbb hb0)
  have hlimit : |∫ z, f z ∂μ - ℓg| ≤ η' * ℓb := by
    have ht : Tendsto (fun k => |∫ z, f z ∂lqgAreaApprox γ h k - ∫ z, g z ∂lqgAreaApprox γ h k|
        - η' * ∫ z, b z ∂lqgAreaApprox γ h k) atTop (𝓝 (|∫ z, f z ∂μ - ℓg| - η' * ℓb)) :=
      ((hlimf.sub (hdy hℓg)).abs).sub ((hdy hℓb).const_mul η')
    have : |∫ z, f z ∂μ - ℓg| - η' * ℓb ≤ 0 := le_of_tendsto' ht fun k => by linarith [hk k]
    linarith
  -- the continuum statement
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), |∫ z, g z ∂areaS γ h s - ℓg| < η / 4 ∧
      |∫ z, b z ∂areaS γ h s - ℓb| < 1 := by
    refine (Metric.tendsto_nhds.1 hℓg (η / 4) (by positivity)).and
      (Metric.tendsto_nhds.1 hℓb 1 one_pos) |>.mono fun s hs => ?_
    rw [Real.dist_eq, Real.dist_eq] at hs
    exact hs
  obtain ⟨ρ, hρ, hρev⟩ := Metric.mem_nhdsWithin_iff.1 (hev.and self_mem_nhdsWithin)
  refine ⟨ρ, hρ, fun s hs hsd => ?_⟩
  obtain ⟨⟨h1s, h2s⟩, hs0⟩ := hρev ⟨Metric.mem_ball.2 hsd, hs⟩
  have hs0' : (0 : ℝ) < s := hs0
  have hcs := hcomp _ (hint _ hs0' hf.measurable hfb hfS) (hint _ hs0' hMg.meas hMg.bdd hMg.zero)
    (hint _ hs0' hbm hbb hb0)
  rw [Real.dist_eq]
  have hbs : ∫ z, b z ∂areaS γ h s ≤ ℓb + 1 := by linarith [(abs_lt.1 h2s).2]
  have e1 : η' * ∫ z, b z ∂areaS γ h s ≤ η / 4 := by
    calc η' * ∫ z, b z ∂areaS γ h s ≤ η' * (ℓb + 1) := mul_le_mul_of_nonneg_left hbs hη'0.le
      _ = η / 4 := by rw [hη']; field_simp
  have e2 : η' * ℓb ≤ η / 4 := by
    calc η' * ℓb ≤ η' * (ℓb + 1) := mul_le_mul_of_nonneg_left (by linarith) hη'0.le
      _ = η / 4 := by rw [hη']; field_simp
  have t1 := abs_sub_le (∫ z, f z ∂areaS γ h s) (∫ z, g z ∂areaS γ h s) (∫ z, f z ∂μ)
  have t2 := abs_sub_le (∫ z, g z ∂areaS γ h s) ℓg (∫ z, f z ∂μ)
  rw [abs_sub_comm ℓg] at t2
  linarith

/-! ## The whole-plane GFF -/

lemma radius_eq_dyadicScale (k : ℕ) : QuantumZipper.radius k = dyadicScale k := by
  simp [QuantumZipper.radius, dyadicScale, zpow_neg, zpow_natCast, inv_pow]

lemma areaApproxC_eq_lqgAreaApprox (γ : ℝ) (h : DistC) :
    MoTPort.areaApproxC γ h = lqgAreaApprox γ h := by
  funext k
  simp only [MoTPort.areaApproxC, lqgAreaApprox, radius_eq_dyadicScale]

/-- the dyadic vague limit of the whole-plane GFF exists a.s. (MoTPort `ae_areaGood_univ`) -/
theorem ae_exists_isVagueLimitC_wp [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitC (lqgAreaApprox γ (X ω)) μ := by
  filter_upwards [MoTPort.ConeArea4.ae_areaGood_univ hX hγ hγ2] with ω h
  obtain ⟨⟨μ, hμ⟩, -⟩ := h
  rw [areaApproxC_eq_lqgAreaApprox] at hμ
  exact ⟨μ, fun K hK => hμ.2.1 K hK (subset_univ K), fun f hf hfc => hμ.2.2 f hf hfc (subset_univ _)⟩

/-- **Continuum area limit of the whole-plane GFF** (Sheffield–Wang Thm 1.1): a.s.
`areaS γ (X ω) s → lqgArea γ (X ω)` vaguely on `ℂ` as `s → 0⁺`. -/
theorem ae_hasAreaLimitS_wp (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, HasAreaLimitS γ (X ω) (lqgArea γ (X ω)) := by
  have := hX.gaussian.isProbabilityMeasure
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense C(ℂ, ℝ)
  set D := insert (ContinuousMap.const ℂ (1 : ℝ)) D₀ with hD
  have hDc : D.Countable := hD₀c.insert _
  have : Countable D := hDc.to_subtype
  have hDd : Dense D := hD₀d.mono (subset_insert _ _)
  have hnd : ∀ n : ℕ, ∀ d : D, ∀ᵐ ω ∂P, ∃ ℓ, Tendsto
      (fun s => ∫ z, winFun n d z ∂areaS γ (X ω) s) (𝓝[>] 0) (𝓝 ℓ) := by
    intro n d
    obtain ⟨M, hM⟩ := exists_winFun n d
    obtain ⟨L, hL⟩ := exists_wMass_limit hX hγ hγ2 (win_n n) hM
    filter_upwards [ae_tendsto_wMass hX hγ hγ2 (win_n n) hM hL] with ω hω
    refine ⟨Real.exp (γ * circleAvg (X ω) (winδ n) 0) * L ω, ?_⟩
    refine (hω.const_mul _).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (integral_areaS_eq_wMass γ (winδ n) (le_of_lt hs) _ ω).symm
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ d : D, ∃ ℓ, Tendsto
      (fun s => ∫ z, winFun n d z ∂areaS γ (X ω) s) (𝓝[>] 0) (𝓝 ℓ) :=
    ae_all_iff.2 fun n => ae_all_iff.2 (hnd n)
  filter_upwards [hall, ae_exists_isVagueLimitC_wp hX hγ hγ2, ae_goodCirc hX] with ω hall hdy hg
  obtain ⟨μ, hμ⟩ := hdy
  rw [lqgArea_eq_of_isVagueLimitC hμ]
  exact hasAreaLimitS_of_dense hg hμ hDd (mem_insert _ _) fun n d hd => hall n ⟨d, hd⟩

/-- the whole-plane GFF has circle averages along every mollifier scale, a.s. -/
theorem ae_hasScaleCircleAvgs_wp (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, HasScaleCircleAvgs (X ω) := by
  filter_upwards [ae_tendsto_mollAvgS_circleAvg hX] with ω h ρ hρ
  exact Eventually.of_forall (h.2 ρ hρ)

/-- **The coordinate change for the whole-plane GFF**, simultaneously for all dilations,
translations and additive constants: almost surely, for every `r > 0`, `c`, `z` and every set
`A`, `lqgArea γ (X(r · + z) + Q log r + c) A = e^{γc} lqgArea γ X (r A + z)`. -/
theorem ae_lqgArea_affine_wp (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ (c : ℝ) (z : ℂ) (A : Set ℂ),
      lqgArea γ (addConst (affineComp r z (X ω)) (lqgQ γ * Real.log r + c)) A =
        ENNReal.ofReal (Real.exp (γ * c)) *
          lqgArea γ (X ω) ((fun w => (r : ℂ) * w + z) '' A) := by
  filter_upwards [ae_hasScaleCircleAvgs_wp hX, ae_hasAreaLimitS_wp hX hγ hγ2] with ω h1 h2
  intro r hr c z A
  exact lqgArea_affine_apply hγ.ne' h1 h2 hr z c A

end MatedCRTHarmonic.LQGCoord
