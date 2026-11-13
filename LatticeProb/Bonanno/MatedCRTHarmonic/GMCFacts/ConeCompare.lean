/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.ConeCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.ConeRadialPath
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.L27Bridge

/-!
# [18]'s reduction from the quantum cone to the whole-plane GFF: `AreaDominatesWholePlaneGFF`

**Target** (`GMSLemma27.AreaDominatesWholePlaneGFF M`, an obligation of the cell model): the sample space of the cell
model carries a whole-plane GFF circle-average process `H` (normalized by `h_1(0) = 0`) with LQG measure `μ̃` such that
a.s. `μ̃(A) ≤ μ_h(A)` for every Borel `A ⊆ 𝔻`. Source: [18]: "If `h` is a circle-average
embedding of an `α`-quantum cone, then `h|_𝔻` agrees in law with a whole-plane GFF normalized so that its circle
average over `∂𝔻` is 0 plus `−α log|·|`. If `h` is a whole-plane GFF, then `μ_{h−α log|·|}(A) ≥ μ_h(A)` for each Borel
set `A ⊂ 𝔻`."

**Construction** (the cone-to-whole-plane comparison, realized on the given sample space). For the cone field `h = lateral(X) + A(−log|·|)`
built from a whole-plane GFF `X` and independent Brownian motions `B, B'` (`A = coneRadial γ γ B B'`):
* `W` = the two-sided Brownian motion `B(t⁺) + B'((−t)⁺)` (continuous version), independent of `X`;
* `X̃ = lateral(X) + W(−log|·|)` is a whole-plane GFF normalized by `X̃_1(0) = 0` (`Replaced.lean`,
  `ReplacedArea.lean`); its LQG measure `μ̃` is the `IsLQGAreaOf` measure of a measurable circle-average process `H`;
* `h = X̃ + g` with `g = A(−log|·|) − W(−log|·|)`, and on `𝔻 ∖ {0}`, `g = γ(−log|·|) ≥ 0` because `A_t = B_t + γt`
  for `t ≥ 0`; by the density rule (ported MoT `ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC`, Ding–Gwynne
  arXiv:1807.01072: `dμ_{h+f} = e^{γ f} dμ_h`) and uniqueness of vague limits, `μ_h = e^{γ g} μ̃ ≥ μ̃` on
  `𝔻 ∖ {0}`; `μ̃({0}) = 0` (`NoAtom.lean`).

**Existence of the cone area** (`ConeAreaExists`): a.s. the
approximations `2^{-kγ²/2} e^{γ h_{2^{-k}}} dz` of the cone field converge vaguely, so that `lqgArea γ h` is their limit
(and not the junk value `0`). It is proved here (`coneAreaExists_holds`) from the decomposition `h = X̃ + g` and the
ported MoT cone-area lemmas, so `areaDominates_of_cone` has no named input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort MatedCRTHarmonic.CellScaling

/-- Almost surely the γ-LQG area approximations of the cone field `coneFieldOf γ X B B'` converge vaguely
on `ℂ` (the target "for `h = coneField X (coneRadial γ α B B')`: a.s. the vague limit exists", the cone-area construction; quantum cones
have a whole-plane area measure, Duplantier–Sheffield Prop 1.1, DMS §4). Proved below as `coneAreaExists_holds`. -/
def ConeAreaExists (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → DistC)
    (B B' : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∃ μ : Measure ℂ,
    IsVagueLimitC (lqgAreaApprox γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) μ

/-! ### Vague limits: conventions -/

lemma dyadicScale_eq_radius (k : ℕ) : dyadicScale k = QuantumZipper.radius k := by
  rw [dyadicScale, QuantumZipper.radius, zpow_neg, zpow_natCast, inv_pow]

lemma lqgAreaApprox_eq_areaApproxC (γ : ℝ) (h : DistC) (k : ℕ) :
    lqgAreaApprox γ h k = areaApproxC γ h k := by
  rw [lqgAreaApprox, areaApproxC, dyadicScale_eq_radius]

/-- A vague limit on `ℂ` restricts to every open set. -/
lemma isVagueLimitOn_restrict {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hK : ∀ K : Set ℂ, IsCompact K → μ K < ⊤)
    (ht : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 (∫ z, f z ∂μ))) :
    QuantumZipper.IsVagueLimitOn U μs (μ.restrict U) := by
  refine ⟨by rw [Measure.restrict_apply' hU.measurableSet, compl_inter_self, measure_empty],
    fun K hKc _ => (Measure.restrict_apply_le U K).trans_lt (hK K hKc), fun f hf hfs hfU => ?_⟩
  have e : ∫ z, f z ∂(μ.restrict U) = ∫ z, f z ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h => hz (hfU h)
  rw [e]
  exact ht f hf hfs

/-- Measures equal to a density `≥ 1` times another measure dominate it. -/
lemma le_withDensity_of_one_le {μ : Measure ℂ} {f : ℂ → ℝ≥0∞} {A : Set ℂ} (hA : MeasurableSet A)
    (hf : ∀ z ∈ A, 1 ≤ f z) : μ A ≤ μ.withDensity f A := by
  rw [withDensity_apply _ hA]
  calc μ A = ∫⁻ _z in A, 1 ∂μ := by rw [setLIntegral_const, one_mul]
    _ ≤ ∫⁻ z in A, f z ∂μ := setLIntegral_mono' hA hf

/-! ### Independence transfers to the continuous version -/

lemma indepFun_continuousMap_of_coe {β : Type*} [MeasurableSpace β] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → β} {W : Ω → C(ℝ, ℝ)}
    (h : IndepFun f (fun ω => (⇑(W ω) : ℝ → ℝ)) P) : IndepFun f W P := by
  have hσ : MeasurableSpace.comap W (inferInstance : MeasurableSpace C(ℝ, ℝ)) =
      MeasurableSpace.comap (fun ω => (⇑(W ω) : ℝ → ℝ)) MeasurableSpace.pi := by
    rw [continuousMap_measurableSpace_eq, MeasurableSpace.comap_comp]
    rfl
  unfold IndepFun Kernel.IndepFun at h ⊢
  rw [hσ]
  exact h

/-! ### The decomposition `h = X̃ + g` -/

/-- **The cone field is a whole-plane GFF plus `γ(−log|·|)` on `𝔻`**: on the sample space of the cone data there is a
whole-plane GFF `X̃` normalized by `X̃_1(0) = 0` such that a.s. `h = X̃ + g` with `g` measurable, locally integrable,
continuous off `0` and equal to `γ(−log|z|)` for `|z| ≤ 1` (the cone-to-whole-plane comparison; `[18]`). -/
theorem exists_cone_decomposition {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) (hγ2 : γ < 2) :
    ∃ Xt : Ω → DistC, IsNormalizedWPGFF Xt P ∧ ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
      coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω) = Xt ω + MoTPort.ofFunC g ∧
      Measurable g ∧ LocallyIntegrable g volume ∧ ContinuousOn g {z | z ≠ 0} ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖) := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  -- continuous versions and the two-sided Brownian motion `W`
  obtain ⟨Bc, hBcm, hBc0, hBcae⟩ := exists_continuousVersion_brownian hB
  obtain ⟨Bc', hBc'm, hBc'0, hBc'ae⟩ := exists_continuousVersion_brownian hB'
  set W : Ω → C(ℝ, ℝ) := fun ω => twoSided (Bc ω) (Bc' ω) with hW_def
  have hWm : Measurable W := measurable_twoSided.comp (hBcm.prodMk hBc'm)
  have hpath : (fun ω => (fun t => B t ω)) =ᵐ[P] fun ω => (fun t => Bc ω t) := by
    filter_upwards [hBcae] with ω hω
    funext t
    exact (hω t).symm
  have hpath' : (fun ω => (fun t => B' t ω)) =ᵐ[P] fun ω => (fun t => Bc' ω t) := by
    filter_upwards [hBc'ae] with ω hω
    funext t
    exact (hω t).symm
  have hBpre : IsPreBrownianReal (fun t ω => Bc ω t) P :=
    hB.toIsPreBrownianReal.congr fun t => by
      filter_upwards [hBcae] with ω hω
      exact (hω t).symm
  have hBpre' : IsPreBrownianReal (fun t ω => Bc' ω t) P :=
    hB'.toIsPreBrownianReal.congr fun t => by
      filter_upwards [hBc'ae] with ω hω
      exact (hω t).symm
  have hindBB : IndepFun (fun ω t => Bc ω t) (fun ω t => Bc' ω t) P := hind.2.congr hpath hpath'
  have hWg : IsGaussianProcess (fun t ω => W ω t) P :=
    twoSided_isGaussianProcess hBpre.isGaussianProcess hBpre'.isGaussianProcess hindBB
  have hW0 : ∀ t, ∫ ω, W ω t ∂P = 0 := fun t => by
    have e : (fun ω => W ω t) = fun ω => Bc ω t.toNNReal + Bc' ω (-t).toNNReal := by
      funext ω
      simp [hW_def, twoSided_apply, hBc0, hBc'0]
    rw [e, integral_add (hBpre.integrable_eval _) (hBpre'.integrable_eval _),
      hBpre.integral_eval, hBpre'.integral_eval, add_zero]
  have hWc : ∀ s t, cov[fun ω => W ω s, fun ω => W ω t; P] = radCov s t :=
    twoSided_covariance hBpre hBpre' hindBB hBc0 hBc'0
  have hWzero : ∀ ω, W ω 0 = 0 := fun ω => by simp [hW_def, twoSided_apply]
  -- `X` is independent of `W`
  have hindXW : IndepFun X W P := by
    have h1 : IndepFun X (fun ω => ((fun t => Bc ω t), (fun t => Bc' ω t))) P :=
      hind.1.congr (ae_eq_refl _) (by
        filter_upwards [hpath, hpath'] with ω h1 h2
        show ((fun t => B t ω), (fun t => B' t ω)) = ((fun t => Bc ω t), (fun t => Bc' ω t))
        rw [h1, h2])
    have hΦ : Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) =>
        fun t : ℝ => (p.1 t.toNNReal - p.1 0) + (p.2 (-t).toNNReal - p.2 0) :=
      have e1 : ∀ s : ℝ≥0, Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.1 s := fun s =>
        (measurable_pi_apply s).comp measurable_fst
      have e2 : ∀ s : ℝ≥0, Measurable fun p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) => p.2 s := fun s =>
        (measurable_pi_apply s).comp measurable_snd
      measurable_pi_iff.2 fun t => ((e1 _).sub (e1 _)).add ((e2 _).sub (e2 _))
    exact indepFun_continuousMap_of_coe (h1.comp measurable_id hΦ)
  -- the replaced field
  set Xt := replField X W
  have hXt : IsNormalizedWPGFF Xt P :=
    ⟨isWholePlaneGFF_replField hX hWm hWg hW0 hWc hindXW, ae_circleAvg_replField_one hX hWzero⟩
  refine ⟨Xt, hXt, ?_⟩
  filter_upwards [hBcae, hBc'ae, ae_goodDrift hB' (α := γ) (lqgQ_sub_pos hγ hγ2),
    QuantumZipper.BMLLN.ae_tendsto_div_atTop hB] with ω hω_B hω_B' hω_drift hω_lln
  set b : ℝ≥0 → ℝ := fun t => B t ω
  set b' : ℝ≥0 → ℝ := fun t => B' t ω
  have hbBc : b = ⇑(Bc ω) := funext fun t => (hω_B t).symm
  have hbc : Continuous b := by rw [hbBc]; exact (Bc ω).continuous
  have hb0 : b 0 = 0 := by rw [hbBc]; exact hBc0 ω
  set Ar := coneRadial γ γ b b' with hAr
  have hAc : Continuous Ar := continuous_coneRadial hbc hb0 hω_drift
  obtain ⟨C₀, hC₀⟩ := exists_abs_le_add_of_tendsto_div hbc hω_lln
  set C := max C₀ 0
  have hC0 : 0 ≤ C := le_max_right _ _
  have hbC : ∀ t : ℝ, 0 ≤ t → |b t.toNNReal| ≤ C + t := fun t ht => by
    have := hC₀ t.toNNReal
    rw [Real.coe_toNNReal t ht] at this
    linarith [le_max_left C₀ 0]
  have hAgr : ∀ t, 0 ≤ t → |Ar t| ≤ C + (1 + γ) * t := by
    intro t ht
    rw [hAr, coneRadial_of_nonneg γ γ b b' ht]
    calc |b t.toNNReal + γ * t| ≤ |b t.toNNReal| + |γ * t| := abs_add_le _ _
      _ ≤ C + t + γ * t := by
          rw [abs_of_nonneg (by positivity : 0 ≤ γ * t)]; linarith [hbC t ht]
      _ = C + (1 + γ) * t := by ring
  have hWt : ∀ t, 0 ≤ t → W ω t = b t.toNNReal := by
    intro t ht
    rw [hW_def, twoSided_apply, hBc0, hBc'0, Real.toNNReal_of_nonpos (neg_nonpos.2 ht), hBc'0, hbBc]
    ring
  have hWgr : ∀ t, 0 ≤ t → |W ω t| ≤ C + 1 * t := fun t ht => by
    rw [hWt t ht]; linarith [hbC t ht]
  have hAli := locallyIntegrable_radial_of_growth hAc hC0 (by linarith : (0 : ℝ) ≤ 1 + γ) hAgr
  have hWli := locallyIntegrable_radial_of_growth (W ω).continuous hC0 zero_le_one hWgr
  set g : ℂ → ℝ := fun z => Ar (-Real.log ‖z‖) - W ω (-Real.log ‖z‖)
  have hgli : LocallyIntegrable g volume := hAli.sub hWli
  have hlogm : Measurable fun z : ℂ => -Real.log ‖z‖ := (Real.measurable_log.comp measurable_norm).neg
  have hgm : Measurable g :=
    (hAc.measurable.comp hlogm).sub ((W ω).continuous.measurable.comp hlogm)
  have hlogc : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) {z | z ≠ 0} :=
    (Real.continuousOn_log.comp continuous_norm.continuousOn fun z hz => norm_ne_zero_iff.2 hz).neg
  have hgc : ContinuousOn g {z | z ≠ 0} :=
    (hAc.comp_continuousOn hlogc).sub ((W ω).continuous.comp_continuousOn hlogc)
  -- the cone field is the replaced field plus `g`
  have hdec : coneFieldOf γ (X ω) b b' = Xt ω + MoTPort.ofFunC g := by
    show CellScaling.lateralPart (X ω) + CellScaling.ofFunC (fun z => Ar (-Real.log ‖z‖)) =
      lateralPartC (X ω) + MoTPort.ofFunC (radialW (W ω)) + MoTPort.ofFunC g
    rw [add_assoc, MoTPort.ofFunC, MoTPort.ofFunC, ← Distribution.ofFun_add
      (by rw [TopologicalSpace.Opens.coe_top]; exact hWli.locallyIntegrableOn univ)
      (by simpa using hgli.locallyIntegrableOn univ)]
    congr 2
    funext z
    simp only [g, radialW, Pi.add_apply]
    ring
  -- on the closed unit disc, `g = γ(−log|z|) ≥ 0`
  have hg1 : ∀ z : ℂ, ‖z‖ ≤ 1 → g z = γ * (-Real.log ‖z‖) := by
    intro z hz
    have ht : 0 ≤ -Real.log ‖z‖ := neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) hz)
    simp only [g]
    rw [hAr, coneRadial_of_nonneg γ γ b b' ht, hWt _ ht]
    ring
  exact ⟨g, hdec, hgm, hgli, hgc, hg1⟩

/-! ### Existence of the cone's area measure -/

/-- **Existence of the γ-LQG area of the cone field** (the cone-area construction; DMS §4, Duplantier–Sheffield
Prop 1.1): almost surely the approximations of `coneFieldOf γ X B B'` converge vaguely on `ℂ`. From the decomposition
`h = X̃ + g`: off `0` by the density rule (ported MoT `ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC`), finiteness
(MoT `ConeArea4.eventually_lt_top_add_ofFunC`, `fin_of_away_of_tight`), and tightness at `0` from `g = γ(−log|·|)` on
`𝔻` and the weighted whole-plane tightness (MoT `ConeArea6.ae_tight_logFactor'`, `γ < Q`, `ConeArea5.tight_add_ofFunC`);
then MoT's localization `ConeArea2.isVagueLimitOn_univ_of_punctured`. -/
theorem coneAreaExists_holds {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) P) :
    ConeAreaExists γ P X B B' := by
  have hP : IsProbabilityMeasure P := hX.gaussian.isProbabilityMeasure
  obtain ⟨Xt, hXt, hdec⟩ := exists_cone_decomposition hγ hX hB hB' hind hγ2
  have hcQ : γ < QuantumZipper.Qc γ := by
    unfold QuantumZipper.Qc
    have : γ / 2 < 2 / γ := by rw [div_lt_div_iff₀ two_pos hγ]; nlinarith
    linarith
  filter_upwards [hdec, ConeArea3.ae_hasCircleAvgs hXt.1, ConeArea4.ae_areaGood_univ hXt.1 hγ hγ2,
    ConeArea6.ae_tight_logFactor' hγ hγ2 hcQ hXt.1] with ω ⟨g, hd, hgm, hgli, hgc, hg1⟩ hω_circ
    hω_good hω_tight
  have hgc' : ContinuousOn g (univ \ {0}) := hgc.mono fun z hz => hz.2
  -- (b1) off `0`
  have hU : IsOpen (univ \ {(0 : ℂ)}) := isOpen_univ.sdiff isClosed_singleton
  have hXtU : QuantumZipper.IsVagueLimitOn (univ \ {0}) (areaApproxC γ (Xt ω))
      ((qAreaC γ (Xt ω)).restrict (univ \ {0})) :=
    isVagueLimitOn_restrict hU (fun K hK => ConeArea.qAreaC_compact_lt_top γ _ hK)
      (fun f hf hfs => (ConeArea.isVagueLimitOn_qAreaC hω_good.1).2.2 f hf hfs (subset_univ _))
  have hb1 := ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC hU hXtU hω_circ hgm hgli hgc'
  -- (b3) tightness at `0`
  have hb3 := ConeArea5.tight_add_ofFunC (c := γ) (C := 0) hγ one_pos hω_circ hgli hgc'
    (fun w _ hw => by rw [hg1 w hw.le, add_zero]) hω_tight
  -- (b2) finiteness on compacts
  have hb2 : ∀ K, IsCompact K → ∀ᶠ k in atTop, areaApproxC γ (Xt ω + MoTPort.ofFunC g) k K < ⊤ :=
    fun K hK => ConeArea4.fin_of_away_of_tight
      (fun K' hK' h0 => ConeArea4.eventually_lt_top_add_ofFunC hω_circ hgli hgc'
        (fun K hK => hω_good.2 K hK (subset_univ K)) hK' h0)
      hb3 hK
  have hlim := ConeArea2.isVagueLimitOn_univ_of_punctured hb1 hb2 hb3
  refine ⟨_, fun K hK => hlim.2.1 K hK (subset_univ K), fun f hf hfs => ?_⟩
  rw [hd]
  simpa only [lqgAreaApprox_eq_areaApproxC] using hlim.2.2 f hf hfs (subset_univ _)

/-! ### The comparison -/

/-- **[18]'s reduction from the cone to the whole-plane GFF**, for any cell model whose area is,
almost surely, the γ-LQG area of the cone field built from a whole-plane GFF `X` and Brownian motions `B, B'` with the
independence of the circle-average embedding of the γ-quantum cone. -/
theorem areaDominates_of_cone {γ : ℝ} (M : GMSLemma27.CellModel γ) (hγ : 0 < γ) (hγ2 : γ < 2)
    {X : M.Ω → DistC} {B B' : ℝ≥0 → M.Ω → ℝ} (hX : IsWholePlaneGFF X M.P)
    (hB : IsBrownianReal B M.P) (hB' : IsBrownianReal B' M.P)
    (hind : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) M.P ∧
      IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) M.P)
    (harea : ∀ᵐ ω ∂M.P,
      M.area ω = lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) :
    GMSLemma27.AreaDominatesWholePlaneGFF M := by
  have hP : IsProbabilityMeasure M.P := hX.gaussian.isProbabilityMeasure
  obtain ⟨Xt, hXt, hdec⟩ := exists_cone_decomposition hγ hX hB hB' hind hγ2
  obtain ⟨H, hH, hHm, -, hμ⟩ := exists_isLQGAreaOf hXt hγ hγ2
  refine ⟨H, fun ω => qAreaC γ (Xt ω), hH, hμ, ?_⟩
  filter_upwards [harea, coneAreaExists_holds hγ hγ2 hX hB hB' hind, hdec,
    ConeArea3.ae_hasCircleAvgs hXt.1, ConeArea4.ae_areaGood_univ hXt.1 hγ hγ2,
    ae_measure_singleton_eq_zero hH hHm hμ (z₀ := 0) (by simp)]
    with ω hω_area hω_LC ⟨g, hd, hgm, hgli, hgc, hg1⟩ hω_circ hω_good hω_atom
  intro S hS hS1
  set b : ℝ≥0 → ℝ := fun t => B t ω
  set b' : ℝ≥0 → ℝ := fun t => B' t ω
  set U : Set ℂ := {z | z ≠ 0} ∩ ball 0 1
  have hU : IsOpen U := isOpen_ne.inter isOpen_ball
  -- vague limits on `U`
  have hXtU : QuantumZipper.IsVagueLimitOn U (areaApproxC γ (Xt ω)) ((qAreaC γ (Xt ω)).restrict U) :=
    isVagueLimitOn_restrict hU (fun K hK => ConeArea.qAreaC_compact_lt_top γ _ hK)
      (fun f hf hfs => (ConeArea.isVagueLimitOn_qAreaC hω_good.1).2.2 f hf hfs (subset_univ _))
  have hdens := ConeArea3.isVagueLimitOn_areaApproxC_add_ofFunC hU hXtU hω_circ hgm hgli
    (hgc.mono inter_subset_left)
  obtain ⟨μc, hμc⟩ := hω_LC
  have hμh : IsVagueLimitC (lqgAreaApprox γ (coneFieldOf γ (X ω) b b'))
      (lqgArea γ (coneFieldOf γ (X ω) b b')) := by
    have hx : ∃ μ, IsVagueLimitC (lqgAreaApprox γ (coneFieldOf γ (X ω) b b')) μ := ⟨μc, hμc⟩
    rw [lqgArea, dite_eq_left_of_eq_true (eq_true hx)]
    exact hx.choose_spec
  have hconeU : QuantumZipper.IsVagueLimitOn U (areaApproxC γ (Xt ω + MoTPort.ofFunC g))
      ((lqgArea γ (coneFieldOf γ (X ω) b b')).restrict U) := by
    rw [← hd]
    refine isVagueLimitOn_restrict hU hμh.1 fun f hf hfs => ?_
    simpa only [lqgAreaApprox_eq_areaApproxC] using hμh.2 f hf hfs
  have huniq := QuantumZipper.isVagueLimitOn_unique hU hconeU hdens
  -- conclusion
  rw [hω_area]
  set μh := lqgArea γ (coneFieldOf γ (X ω) b b')
  set μt := qAreaC γ (Xt ω)
  have hsub : S ⊆ (S ∩ U) ∪ {0} := fun z hz => by
    by_cases h0 : z = 0
    · exact Or.inr h0
    · exact Or.inl ⟨hz, h0, hS1 hz⟩
  have hone : ∀ z ∈ S, 1 ≤ ENNReal.ofReal (Real.exp (γ * g z)) := fun z hz => by
    rw [hg1 z (mem_ball_zero_iff.1 (hS1 hz)).le, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_exp ?_)
    have : 0 ≤ -Real.log ‖z‖ :=
      neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) (mem_ball_zero_iff.1 (hS1 hz)).le)
    have : 0 ≤ γ * -Real.log ‖z‖ := mul_nonneg hγ.le this
    exact mul_nonneg hγ.le this
  calc μt S ≤ μt (S ∩ U) + μt {0} := (measure_mono hsub).trans (measure_union_le _ _)
    _ = μt.restrict U S := by rw [hω_atom, add_zero, Measure.restrict_apply hS]
    _ ≤ (μt.restrict U).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * g z))) S :=
        le_withDensity_of_one_le hS hone
    _ = μh.restrict U S := by rw [huniq]
    _ ≤ μh S := Measure.restrict_apply_le U S

/-- **`AreaDominatesWholePlaneGFF` for the cone realization** (the `CellModel` built by
`CellScaling.ConeRealization.toCellModel`), with no further input. -/
theorem areaDominates_toCellModel {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)
    (hpar : AreaParametrization D) (hγ : 0 < γ) (hγ2 : γ < 2) :
    GMSLemma27.AreaDominatesWholePlaneGFF (D.toCellModel hpar) :=
  areaDominates_of_cone (D.toCellModel hpar) hγ hγ2 D.gff D.brownian D.brownian' D.indep
    (Eventually.of_forall fun _ => rfl)

end MatedCRTHarmonic.GMCFacts
