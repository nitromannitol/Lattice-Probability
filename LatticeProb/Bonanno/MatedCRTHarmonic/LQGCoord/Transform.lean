/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.Transform at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ScaleBump
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc4
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn

/-!
# The deterministic coordinate change of the LQG area

For a field `h` on `ℂ` define the
area approximation at an arbitrary radius `s > 0`,
`areaS γ h s = s^{γ²/2} e^{γ h_s(z)} dz` (so `lqgAreaApprox γ h k = areaS γ h 2^{-k}`).
Two deterministic properties of `h`:

* `HasScaleCircleAvgs h`: for every `ρ > 0` and a.e. `w`, the scale-`s` mollified circle averages
  converge to `circleAvg h ρ w` as `s → 0⁺` (continuum of scales);
* `HasAreaLimitS γ h μ`: `areaS γ h s → μ` vaguely as `s → 0⁺` (continuum of radii; QuantumZipper's
  `HasAreaLimit` along the offsets `a 2^{-k}`, `a ∈ [1,2]`, on all of `ℂ`).

**Main result** (`lqgArea_affine_eq`): if both hold, then for **every** `r > 0`, `z ∈ ℂ`, `c ∈ ℝ`,
`lqgArea γ (h(r · + z) + Q log r + c) = e^{γc} · (w ↦ (w − z)/r)_* μ`, and `lqgArea γ h = μ`; in
set form `lqgArea γ (…) A = e^{γc} lqgArea γ h (r A + z)` for every set `A`
(`lqgArea_affine_apply`). Proof: the circle averages of `h(r · + z) + C` at radius `2^{-k}` are
those of `h` at radius `r 2^{-k}` and centre `r w + z` (plus `C`) for a.e. `w`
(`ScaleBump.mollAvg_affineComp`), so by the change of variables `w ↦ r w + z` and
`γQ − γ²/2 − 2 = 0` the dyadic approximations of the new field are `e^{γc}` times the push-forwards
of `areaS γ h (r 2^{-k})`, which converge to `e^{γc} μ` by the continuum limit. This is the
coordinate change rule (Duplantier–Sheffield arXiv:0808.1560 Prop. 2.1 for fixed maps;
Sheffield–Wang arXiv:1605.06171 Thm 1.4 simultaneously for all maps), and the whole-plane analogue
of QuantumZipper's `GoodTransforms.qAreaMeasure_rescale` / `qAreaMeasure_translate`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling

/-! ## Definitions -/

/-- The area approximation at radius `s`: `s^{γ²/2} e^{γ h_s(z)} dz` on `ℂ`. -/
def areaS (γ : ℝ) (h : DistC) (s : ℝ) : Measure ℂ :=
  volume.withDensity fun z => ENNReal.ofReal (s ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h s z))
lemma lqgAreaApprox_eq_areaS (γ : ℝ) (h : DistC) (k : ℕ) :
    lqgAreaApprox γ h k = areaS γ h (dyadicScale k) := rfl

/-- **Circle averages along every mollifier scale**: for every `ρ > 0` and a.e. centre `w`, the
scale-`s` mollified circle averages converge to the circle average as `s → 0⁺`. -/
def HasScaleCircleAvgs (h : DistC) : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ∀ᵐ w : ℂ,
    Tendsto (fun s => mollAvgS h s w ρ) (𝓝[>] 0) (𝓝 (circleAvg h ρ w))

/-- **Continuum area limit**: `areaS γ h s → μ` vaguely on `ℂ` as `s → 0⁺`. -/
def HasAreaLimitS (γ : ℝ) (h : DistC) (μ : Measure ℂ) : Prop :=
  (∀ K : Set ℂ, IsCompact K → μ K < ⊤) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun s => ∫ z, f z ∂areaS γ h s) (𝓝[>] 0) (𝓝 (∫ z, f z ∂μ))

/-! ## Vague limits on `ℂ` -/

lemma isVagueLimitOn_univ_of_isVagueLimitC {μs : ℕ → Measure ℂ} {μ : Measure ℂ}
    (h : IsVagueLimitC μs μ) : QuantumZipper.IsVagueLimitOn univ μs μ :=
  ⟨by simp, fun K hK _ => h.1 K hK, fun f hf hfc _ => h.2 f hf hfc⟩

/-- vague limits on `ℂ` are unique (QuantumZipper `isVagueLimitOn_unique`) -/
theorem isVagueLimitC_unique {μs : ℕ → Measure ℂ} {μ μ' : Measure ℂ} (h : IsVagueLimitC μs μ)
    (h' : IsVagueLimitC μs μ') : μ = μ' :=
  QuantumZipper.isVagueLimitOn_unique isOpen_univ (isVagueLimitOn_univ_of_isVagueLimitC h)
    (isVagueLimitOn_univ_of_isVagueLimitC h')

/-- `lqgArea` is *the* vague limit whenever one exists -/
theorem lqgArea_eq_of_isVagueLimitC {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : IsVagueLimitC (lqgAreaApprox γ h) μ) : lqgArea γ h = μ := by
  have hx : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ := ⟨μ, hμ⟩
  rw [lqgArea, dite_eq_left_of_eq_true (eq_true hx)]
  exact isVagueLimitC_unique hx.choose_spec hμ

lemma dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := by unfold dyadicScale; positivity

lemma tendsto_dyadicScale : Tendsto dyadicScale atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun k => Set.mem_Ioi.2 (dyadicScale_pos k))
  have e : dyadicScale = fun k : ℕ => (2 : ℝ)⁻¹ ^ k := by
    funext k; simp [dyadicScale, zpow_neg, zpow_natCast]
  rw [e]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- the continuum limit gives the dyadic one: `lqgArea γ h = μ` -/
theorem lqgArea_eq_of_hasAreaLimitS {γ : ℝ} {h : DistC} {μ : Measure ℂ}
    (hμ : HasAreaLimitS γ h μ) : lqgArea γ h = μ :=
  lqgArea_eq_of_isVagueLimitC ⟨hμ.1, fun f hf hfc => (hμ.2 f hf hfc).comp tendsto_dyadicScale⟩

/-! ## Circle averages of the transformed field -/

lemma tendsto_mul_inv_two_pow {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n : ℕ => r * (2 : ℝ)⁻¹ ^ n) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity))
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)).const_mul r
  rwa [mul_zero] at this

/-- the circle averages of `h(r · + z) + C` at `(ρ, w)`, given convergence of the mollified circle
averages of `h` at `(rρ, rw + z)` along every scale -/
lemma circleAvg_addConst_affineComp_of_tendsto {h : DistC} {r ρ : ℝ} (hr : 0 < r) {z w : ℂ}
    (C : ℝ) (ht : Tendsto (fun s => mollAvgS h s ((r : ℂ) * w + z) (r * ρ)) (𝓝[>] 0)
      (𝓝 (circleAvg h (r * ρ) ((r : ℂ) * w + z)))) :
    circleAvg (addConst (affineComp r z h) C) ρ w = circleAvg h (r * ρ) ((r : ℂ) * w + z) + C := by
  apply circleAvg_eq_of_tendsto
  refine ((ht.comp (tendsto_mul_inv_two_pow hr)).add_const C).congr fun n => ?_
  simp only [Function.comp_apply]
  rw [mollAvg_addConst, mollAvg_affineComp h hr]

/-- the affine map `w ↦ r w + z` -/
abbrev affT {r : ℝ} (hr : 0 < r) (z : ℂ) : ℂ ≃ᵐ ℂ := DG.affineEquivC hr z
lemma affT_apply {r : ℝ} (hr : 0 < r) (z w : ℂ) : affT hr z w = (r : ℂ) * w + z := rfl

lemma quasiMeasurePreserving_affT {r : ℝ} (hr : 0 < r) (z : ℂ) :
    Measure.QuasiMeasurePreserving (affT hr z) volume volume := by
  refine ⟨(affT hr z).measurable, ?_⟩
  rw [show ⇑(affT hr z) = DG.affineC r z from rfl, DG.map_affineC_volume hr z]
  exact Measure.smul_absolutelyContinuous

/-- for a.e. `w`, the circle averages of the transformed field at radius `ρ` -/
lemma ae_circleAvg_addConst_affineComp {h : DistC} (h1 : HasScaleCircleAvgs h) {r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (z : ℂ) (C : ℝ) :
    ∀ᵐ w : ℂ, circleAvg (addConst (affineComp r z h) C) ρ w =
      circleAvg h (r * ρ) ((r : ℂ) * w + z) + C := by
  have hb := (quasiMeasurePreserving_affT hr z).ae (h1 (r * ρ) (mul_pos hr hρ))
  filter_upwards [hb] with w hw
  exact circleAvg_addConst_affineComp_of_tendsto hr C hw

/-! ## The approximations of the transformed field -/

lemma gamma_mul_lqgQ {γ : ℝ} (hγ : γ ≠ 0) : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
  unfold lqgQ; field_simp

/-- the density of `areaS γ h s` -/
def densS (γ : ℝ) (h : DistC) (s : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h s z))

lemma measurable_densS (γ : ℝ) (h : DistC) (s : ℝ) : Measurable (densS γ h s) := by
  unfold densS
  have h1 : Measurable fun z : ℂ => circleAvg h s z :=
    measurable_circleAvg.comp (f := fun z : ℂ => (h, s, z))
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (h1.const_mul γ)).const_mul _)

/-- change of variables for a density composed with `w ↦ δw + a` (copy of MoTPort
`ConeArea4D.map_withDensity_affineC`) -/
lemma map_withDensity_affineC' {δ : ℝ} (hδ : 0 < δ) (a : ℂ) {D : ℂ → ℝ≥0∞} (hD : Measurable D)
    (c : ℝ≥0∞) :
    (volume.withDensity fun w => c * D (DG.affineC δ a w)).map (DG.affineC δ a) =
      (ENNReal.ofReal (δ ^ 2)⁻¹ * c) • volume.withDensity D := by
  have hT : Measurable (DG.affineC δ a) := (DG.continuous_affineC _ _).measurable
  ext A hA
  rw [Measure.map_apply hT hA, withDensity_apply _ (hT hA), Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ hA, lintegral_const_mul c (f := fun w => D (DG.affineC δ a w)) (hD.comp hT),
    ← setLIntegral_map hA hD hT,
    DG.map_affineC_volume hδ a, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  ring

/-- **the dyadic approximations of the transformed field**, pushed forward by `w ↦ r w + z`, are
`e^{γc}` times the radius-`r 2^{-k}` approximations of `h` -/
theorem map_lqgAreaApprox_affine {γ : ℝ} (hγ : γ ≠ 0) {h : DistC} (h1 : HasScaleCircleAvgs h)
    {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) (k : ℕ) :
    (lqgAreaApprox γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) k).map (affT hr z) =
      ENNReal.ofReal (Real.exp (γ * c)) • areaS γ h (r * dyadicScale k) := by
  set ε := dyadicScale k
  have hε : 0 < ε := dyadicScale_pos k
  have hrε : 0 < r * ε := mul_pos hr hε
  have e1 : lqgAreaApprox γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) k =
      volume.withDensity fun w => ENNReal.ofReal (Real.exp (γ * c) * r ^ 2) *
        densS γ h (r * ε) (DG.affineC r z w) := by
    unfold lqgAreaApprox
    refine withDensity_congr_ae ?_
    filter_upwards [ae_circleAvg_addConst_affineComp h1 hr hε z (lqgQ γ * Real.log r + c)]
      with w hw
    rw [hw, densS, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    show ε ^ (γ ^ 2 / 2) * Real.exp (γ * (circleAvg h (r * ε) ((r : ℂ) * w + z) +
        (lqgQ γ * Real.log r + c))) = Real.exp (γ * c) * r ^ 2 *
      ((r * ε) ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h (r * ε) (DG.affineC r z w)))
    have hA : DG.affineC r z w = (r : ℂ) * w + z := rfl
    rw [hA, Real.mul_rpow hr.le hε.le]
    have hQ : Real.exp (γ * (lqgQ γ * Real.log r)) = r ^ (2 : ℝ) * r ^ (γ ^ 2 / 2) := by
      rw [← mul_assoc, gamma_mul_lqgQ hγ, ← Real.rpow_add hr, Real.rpow_def_of_pos hr]
      congr 1; ring
    have h2 : (r : ℝ) ^ 2 = r ^ (2 : ℝ) := by norm_cast
    rw [mul_add, mul_add, Real.exp_add, Real.exp_add, hQ, h2]
    ring
  rw [e1, show ⇑(affT hr z) = DG.affineC r z from rfl,
    LQGCoord.map_withDensity_affineC' hr z (measurable_densS γ h (r * ε))]
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end MatedCRTHarmonic.LQGCoord

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.CellScaling

/-! ## The coordinate change -/

lemma continuous_affT_symm {r : ℝ} (hr : 0 < r) (z : ℂ) : Continuous (affT hr z).symm := by
  show Continuous ((((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans
    (Homeomorph.addRight z)).toMeasurableEquiv).symm : ℂ → ℂ)
  rw [Homeomorph.toMeasurableEquiv_symm_coe]
  exact Homeomorph.continuous _

lemma continuous_affT {r : ℝ} (hr : 0 < r) (z : ℂ) : Continuous (affT hr z) := by
  show Continuous (DG.affineC r z)
  exact DG.continuous_affineC _ _

lemma tendsto_mul_dyadicScale {r : ℝ} (hr : 0 < r) :
    Tendsto (fun k => r * dyadicScale k) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (Eventually.of_forall fun k => Set.mem_Ioi.2 (mul_pos hr (dyadicScale_pos k)))
  have := (tendsto_nhdsWithin_iff.1 tendsto_dyadicScale).1.const_mul r
  rwa [mul_zero] at this

/-- **Deterministic coordinate change of the LQG area** (all dilations, translations and additive
constants at once): `lqgArea γ (h(r · + z) + Q log r + c) = e^{γc} (w ↦ (w − z)/r)_* μ`. -/
theorem lqgArea_affine_eq {γ : ℝ} (hγ : γ ≠ 0) {h : DistC} {μ : Measure ℂ}
    (h1 : HasScaleCircleAvgs h) (h2 : HasAreaLimitS γ h μ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ) :
    lqgArea γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) =
      ENNReal.ofReal (Real.exp (γ * c)) • μ.map (affT hr z).symm := by
  apply lqgArea_eq_of_isVagueLimitC
  set h' := addConst (affineComp r z h) (lqgQ γ * Real.log r + c)
  set T := affT hr z
  set e := ENNReal.ofReal (Real.exp (γ * c))
  have hmapk : ∀ k, lqgAreaApprox γ h' k = (e • areaS γ h (r * dyadicScale k)).map T.symm := by
    intro k
    rw [← map_lqgAreaApprox_affine hγ h1 hr z c k,
      Measure.map_map T.symm.measurable T.measurable, T.symm_comp_self, Measure.map_id]
  constructor
  · intro K hK
    rw [Measure.smul_apply, smul_eq_mul, MeasurableEquiv.map_apply,
      ← MeasurableEquiv.image_eq_preimage_symm]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h2.1 _ (hK.image (continuous_affT hr z)))
  · intro f hf hfc
    have hg : Continuous (f ∘ T.symm) := hf.comp (continuous_affT_symm hr z)
    have hgc : HasCompactSupport (f ∘ T.symm) := by
      have := hfc.comp_homeomorph ((Homeomorph.mulLeft₀ (r : ℂ) (by exact_mod_cast hr.ne')).trans
        (Homeomorph.addRight z)).symm
      simpa only [T, affT, DG.affineEquivC, Homeomorph.toMeasurableEquiv_symm_coe] using this
    have hlim := ((h2.2 _ hg hgc).comp (tendsto_mul_dyadicScale hr)).const_smul e.toReal
    have hval : ∀ k, ∫ w, f w ∂lqgAreaApprox γ h' k =
        e.toReal • ∫ w, (f ∘ T.symm) w ∂areaS γ h (r * dyadicScale k) := by
      intro k
      rw [hmapk k, integral_map_equiv, integral_smul_measure]
      rfl
    have hval' : ∫ w, f w ∂(e • μ.map T.symm) = e.toReal • ∫ w, (f ∘ T.symm) w ∂μ := by
      rw [integral_smul_measure, integral_map_equiv]
      rfl
    rw [hval']
    exact hlim.congr fun k => (hval k).symm

/-- **Set form of the coordinate change**: for every set `A`,
`lqgArea γ (h(r · + z) + Q log r + c) A = e^{γc} · lqgArea γ h (r A + z)`. -/
theorem lqgArea_affine_apply {γ : ℝ} (hγ : γ ≠ 0) {h : DistC} {μ : Measure ℂ}
    (h1 : HasScaleCircleAvgs h) (h2 : HasAreaLimitS γ h μ) {r : ℝ} (hr : 0 < r) (z : ℂ) (c : ℝ)
    (A : Set ℂ) :
    lqgArea γ (addConst (affineComp r z h) (lqgQ γ * Real.log r + c)) A =
      ENNReal.ofReal (Real.exp (γ * c)) * lqgArea γ h ((fun w => (r : ℂ) * w + z) '' A) := by
  rw [lqgArea_affine_eq hγ h1 h2 hr z c, lqgArea_eq_of_hasAreaLimitS h2, Measure.smul_apply,
    smul_eq_mul, MeasurableEquiv.map_apply, ← MeasurableEquiv.image_eq_preimage_symm]
  rfl

end MatedCRTHarmonic.LQGCoord
