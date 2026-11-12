/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4D at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4C
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc4
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Dilate
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.RTMeas2CGlue

/-!
# Whole-plane LQG area, part 4: scaling and gluing

**`ae_areaGood_univ`**: for every whole-plane GFF `X` and `0 < γ < 2`, a.s. the approximations
`areaApproxC γ X = 2^{-kγ²/2} e^{γ X_{2^{-k}}(z)} dz` converge vaguely on all of `ℂ` and are
eventually finite on every compact set (Duplantier–Sheffield arXiv:0808.1560 Prop. 1.1 for the
whole-plane GFF; DMS L321–337). **`ae_isVagueLimitOn_punctured`** is node (R1) of
the exact form used by `ConeArea3.ae_isVagueLimitOn_coneField_punctured_of`.

Proof: `Y = X(2^m · + a)` is again a whole-plane GFF (LM `IsWholePlaneGFF.affineComp`), so a.s.
its approximations are good on the window `U₀` (ConeArea4C); its circle averages are
`Y_{2^{-k-m}}(w) = X_{2^{-k}}(2^m w + a)` a.s. (LM `CircleAvg.ae_circleAvg_affineComp`,
`GM.affineComp_comp`, Fubini), so by the change of variables `z = 2^m w + a` (LM
`DG.map_affineC_volume`) `areaApproxC γ X k` is a constant multiple of the push-forward of
`areaApproxC γ Y (k+m)`, which gives goodness on `B(0, 2^m/20)`. The balls are glued by QZ
`R18.RTMeas.exists_isVagueLimitOn_of_winC`. Own elementary glue (DS use the same scaling
implicitly: "by translation and scaling invariance").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric

/-! ## Deterministic operations on `AreaGood` -/

lemma areaGood_shift {U : Set ℂ} {μs : ℕ → Measure ℂ} (h : AreaGood U μs) (m : ℕ) :
    AreaGood U (fun k => μs (k + m)) := by
  obtain ⟨⟨μ, h0, hK, hf⟩, hfin⟩ := h
  exact ⟨⟨μ, h0, hK, fun f a b c => (hf f a b c).comp (tendsto_add_atTop_nat m)⟩,
    fun K hK' hKU => (tendsto_add_atTop_nat m).eventually (hfin K hK' hKU)⟩

lemma areaGood_smul {U : Set ℂ} {μs : ℕ → Measure ℂ} (h : AreaGood U μs) {c : ℝ≥0∞}
    (hc : c ≠ ⊤) : AreaGood U (fun k => c • μs k) := by
  obtain ⟨⟨μ, hμ⟩, hfin⟩ := h
  refine ⟨⟨_, LocalRule.IsVagueLimitOn.const_smul hμ hc⟩, fun K hK hKU => ?_⟩
  filter_upwards [hfin K hK hKU] with k hk
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top hc.lt_top hk

lemma areaGood_mono {U V : Set ℂ} (hV : IsOpen V) (hVU : V ⊆ U) {μs : ℕ → Measure ℂ}
    (h : AreaGood U μs) : AreaGood V μs := by
  obtain ⟨⟨μ, h0, hK, hf⟩, hfin⟩ := h
  refine ⟨⟨μ.restrict V, ?_, fun K hK' hKV => ?_, fun f a b c => ?_⟩,
    fun K hK' hKV => hfin K hK' (hKV.trans hVU)⟩
  · rw [Measure.restrict_apply hV.measurableSet.compl, compl_inter_self, measure_empty]
  · exact (Measure.restrict_le_self K).trans_lt (hK K hK' (hKV.trans hVU))
  · have e : ∫ z, f z ∂(μ.restrict V) = ∫ z, f z ∂μ :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
        image_eq_zero_of_notMem_tsupport fun h' => hz (c h')
    rw [e]
    exact hf f a b (c.trans hVU)

lemma areaGood_map {U : Set ℂ} (hU : IsOpen U) {μs : ℕ → Measure ℂ} (h : AreaGood U μs)
    (T : ℂ ≃ₜ ℂ) : AreaGood (T '' U) (fun k => (μs k).map T) := by
  obtain ⟨⟨μ, h0, hK, hf⟩, hfin⟩ := h
  have hpre : T ⁻¹' (T '' U) = U := T.preimage_image U
  have hKpre : ∀ K, IsCompact K → K ⊆ T '' U → IsCompact (T ⁻¹' K) ∧ T ⁻¹' K ⊆ U :=
    fun K hK' hKU => ⟨T.isCompact_preimage.2 hK', (preimage_mono hKU).trans hpre.subset⟩
  refine ⟨⟨μ.map T, ?_, fun K hK' hKU => ?_, fun f a b c => ?_⟩, fun K hK' hKU => ?_⟩
  · rw [Measure.map_apply T.measurable (T.isOpenMap U hU).measurableSet.compl, preimage_compl,
      hpre, h0]
  · rw [Measure.map_apply T.measurable hK'.isClosed.measurableSet]
    exact hK _ (hKpre K hK' hKU).1 (hKpre K hK' hKU).2
  · have e : ∀ ν : Measure ℂ, ∫ z, f z ∂(ν.map T) = ∫ z, (f ∘ T) z ∂ν := fun ν =>
      integral_map T.measurable.aemeasurable a.aestronglyMeasurable
    simp only [e]
    refine hf _ (a.comp T.continuous) (b.comp_homeomorph T) ?_
    rw [tsupport_comp_eq_preimage]
    exact (preimage_mono c).trans hpre.subset
  · filter_upwards [hfin _ (hKpre K hK' hKU).1 (hKpre K hK' hKU).2] with k hk
    rwa [Measure.map_apply T.measurable hK'.isClosed.measurableSet]

/-- gluing the balls `B(0, 2^m/20)` -/
theorem areaGood_univ_of_balls {μs : ℕ → Measure ℂ}
    (h : ∀ m : ℕ, AreaGood (ball 0 ((2 : ℝ) ^ m / 20)) μs) : AreaGood univ μs := by
  have hsub : ∀ S : Set ℂ, Bornology.IsBounded S → ∃ m : ℕ, S ⊆ ball 0 ((2 : ℝ) ^ m / 20) := by
    intro S hS
    obtain ⟨R, hR⟩ := hS.subset_ball 0
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (20 * R) (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, hR.trans (ball_subset_ball (by linarith))⟩
  have hfin : ∀ K, IsCompact K → K ⊆ univ → ∀ᶠ k in atTop, μs k K < ⊤ := by
    intro K hK _
    obtain ⟨m, hm⟩ := hsub K hK.isBounded
    exact (h m).2 K hK hm
  refine ⟨R18.RTMeas.exists_isVagueLimitOn_of_winC isOpen_univ hfin fun n => ?_, hfin⟩
  have hb : Bornology.IsBounded (R18.RTMeas.winC univ n) := by
    unfold R18.RTMeas.winC; split_ifs
    · exact isBounded_ball
    · exact Bornology.isBounded_empty
  obtain ⟨m, hm⟩ := hsub _ hb
  exact (areaGood_mono (R18.RTMeas.isOpen_winC univ n) hm (h m)).1

/-! ## Scaling of the approximations -/

/-- the constant of the scaling identity -/
def scaleConst (γ : ℝ) (m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((2 : ℝ) ^ m) ^ 2)⁻¹ * ENNReal.ofReal (radius m ^ (γ ^ 2 / 2))

lemma scaleConst_ne_top (γ : ℝ) (m : ℕ) : scaleConst γ m ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

lemma scaleConst_ne_zero (γ : ℝ) (m : ℕ) : scaleConst γ m ≠ 0 := by
  unfold scaleConst
  refine mul_ne_zero ?_ ?_ <;> rw [Ne, ENNReal.ofReal_eq_zero, not_le]
  · positivity
  · have := QuantumZipper.radius_pos m; positivity

lemma radius_add (k m : ℕ) : radius (k + m) = radius k * radius m := by
  simp only [radius, pow_add]

lemma two_pow_mul_radius_add (k m : ℕ) : (2 : ℝ) ^ m * radius (k + m) = radius k := by
  rw [radius_add, radius, radius, inv_pow, inv_pow]
  field_simp

/-- change of variables for a density composed with `w ↦ δw + a` -/
lemma map_withDensity_affineC {δ : ℝ} (hδ : 0 < δ) (a : ℂ) {D : ℂ → ℝ≥0∞} (hD : Measurable D)
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

/-- **change of variables**: if `y_{2^{-k-m}}(w) = x_{2^{-k}}(2^m w + a)` for a.e. `w`, then the
push-forward of `areaApproxC γ y (k+m)` under `w ↦ 2^m w + a` is `scaleConst γ m` times
`areaApproxC γ x k` -/
theorem map_areaApproxC_scale {γ : ℝ} {x y : Field} {m k : ℕ} {a : ℂ}
    (h : ∀ᵐ w ∂(volume : Measure ℂ), circleAvg y (radius (k + m)) w =
      circleAvg x (radius k) (DG.affineC ((2 : ℝ) ^ m) a w)) :
    (areaApproxC γ y (k + m)).map (DG.affineC ((2 : ℝ) ^ m) a) =
      scaleConst γ m • areaApproxC γ x k := by
  have hD : Measurable fun z => ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg x (radius k) z)) := ENNReal.measurable_ofReal.comp
    ((measurable_densC γ k).comp (f := fun z : ℂ => (z, x)) (measurable_id.prodMk measurable_const))
  have e1 : areaApproxC γ y (k + m) =
      volume.withDensity fun w => ENNReal.ofReal (radius m ^ (γ ^ 2 / 2)) *
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
          Real.exp (γ * circleAvg x (radius k) (DG.affineC ((2 : ℝ) ^ m) a w))) := by
    unfold areaApproxC
    refine withDensity_congr_ae ?_
    filter_upwards [h] with w hw
    rw [hw, ← ENNReal.ofReal_mul (by have := QuantumZipper.radius_pos m; positivity),
      radius_add, Real.mul_rpow (QuantumZipper.radius_pos k).le (QuantumZipper.radius_pos m).le]
    congr 1
    ring
  rw [e1, map_withDensity_affineC (pow_pos two_pos m) a hD]
  rfl

/-- the circle averages of `X(2^m · + a)` -/
theorem ae_ae_circleAvg_scale {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    {X : Ω → Field} (hX : IsWholePlaneGFF X P) (m k : ℕ) (a : ℂ) :
    ∀ᵐ ω ∂P, ∀ᵐ w ∂(volume : Measure ℂ),
      circleAvg (affineComp ((2 : ℝ) ^ m) a (X ω)) (radius (k + m)) w =
        circleAvg (X ω) (radius k) (DG.affineC ((2 : ℝ) ^ m) a w) := by
  have hs : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hY := hX.affineComp hs a
  have hS : MeasurableSet {p : Ω × ℂ |
      circleAvg (affineComp ((2 : ℝ) ^ m) a (X p.1)) (radius (k + m)) p.2 =
        circleAvg (X p.1) (radius k) (DG.affineC ((2 : ℝ) ^ m) a p.2)} := by
    refine measurableSet_eq_fun ?_ ?_
    · exact measurable_circleAvg.comp (f := fun p : Ω × ℂ =>
        (affineComp ((2 : ℝ) ^ m) a (X p.1), radius (k + m), p.2))
        ((hY.measurable.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd))
    · exact measurable_circleAvg.comp (f := fun p : Ω × ℂ =>
        (X p.1, radius k, DG.affineC ((2 : ℝ) ^ m) a p.2))
        ((hX.measurable.comp measurable_fst).prodMk (measurable_const.prodMk
          ((DG.continuous_affineC _ _).measurable.comp measurable_snd)))
  rw [Measure.ae_ae_comm hS]
  refine ae_of_all _ fun w => ?_
  filter_upwards [CircleAvg.ae_circleAvg_affineComp hY (QuantumZipper.radius_pos (k + m)) w,
    CircleAvg.ae_circleAvg_affineComp hX (mul_pos hs (QuantumZipper.radius_pos (k + m)))
      ((((2 : ℝ) ^ m : ℝ) : ℂ) * w + a)] with ω h1 h2
  rw [← h1, GM.affineComp_comp (QuantumZipper.radius_pos (k + m)).ne' hs.ne', h2,
    two_pow_mul_radius_add]
  rfl

/-- the image of the window under `w ↦ 2^m w − 2^m c₀` contains `B(0, 2^m/20)` -/
lemma ball_subset_image_U₀ (m : ℕ) :
    ball (0 : ℂ) ((2 : ℝ) ^ m / 20) ⊆
      (Homeomorph.mulLeft₀ (((2 : ℝ) ^ m : ℝ) : ℂ) (by exact_mod_cast (pow_pos two_pos m).ne')
        |>.trans (Homeomorph.addRight (-((((2 : ℝ) ^ m : ℝ) : ℂ) * c₀)))) '' U₀ := by
  intro z hz
  have hs : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  have hs' : ((((2 : ℝ) ^ m : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨z / (((2 : ℝ) ^ m : ℝ) : ℂ) + c₀, ?_, ?_⟩
  · rw [U₀, mem_ball, dist_eq_norm, add_sub_cancel_right, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs, div_lt_iff₀ hs]
    rw [mem_ball, dist_zero_right] at hz
    linarith
  · simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, Homeomorph.coe_addRight]
    field_simp
    ring

/-- **goodness on `B(0, 2^m/20)`** for every whole-plane GFF -/
theorem ae_areaGood_ball {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (m : ℕ) :
    ∀ᵐ ω ∂P, AreaGood (ball 0 ((2 : ℝ) ^ m / 20)) (areaApproxC γ (X ω)) := by
  have hs : (0 : ℝ) < 2 ^ m := pow_pos two_pos m
  set a : ℂ := -((((2 : ℝ) ^ m : ℝ) : ℂ) * c₀)
  filter_upwards [ae_areaGood_U₀ (hX.affineComp hs a) hγ hγ2,
    ae_all_iff.2 fun k => ae_ae_circleAvg_scale hX m k a] with ω hy hxy
  set T : ℂ ≃ₜ ℂ := (Homeomorph.mulLeft₀ (((2 : ℝ) ^ m : ℝ) : ℂ)
    (by exact_mod_cast hs.ne')).trans (Homeomorph.addRight a)
  have h1 := areaGood_map isOpen_U₀ (areaGood_shift hy m) T
  have e : (fun k => (areaApproxC γ (affineComp ((2 : ℝ) ^ m) a (X ω)) (k + m)).map T) =
      fun k => scaleConst γ m • areaApproxC γ (X ω) k :=
    funext fun k => map_areaApproxC_scale (hxy k)
  rw [e] at h1
  have h2 := areaGood_smul h1 (ENNReal.inv_ne_top.2 (scaleConst_ne_zero γ m))
  simp only [smul_smul, ENNReal.inv_mul_cancel (scaleConst_ne_zero γ m) (scaleConst_ne_top γ m),
    one_smul] at h2
  exact areaGood_mono isOpen_ball (ball_subset_image_U₀ m) h2

/-- **(R1) on `ℂ`**: a.s. the whole-plane approximations converge vaguely on `ℂ` and are
eventually finite on compacts (DS Prop. 1.1 for the whole-plane GFF) -/
theorem ae_areaGood_univ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) : ∀ᵐ ω ∂P, AreaGood univ (areaApproxC γ (X ω)) := by
  filter_upwards [ae_all_iff.2 (ae_areaGood_ball hX hγ hγ2)] with ω h
  exact areaGood_univ_of_balls h

/-- **Almost-sure vague convergence away from the cone point** -/
theorem ae_isVagueLimitOn_punctured {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} (hX : IsWholePlaneGFF X P) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ μ, IsVagueLimitOn (univ \ {0}) (areaApproxC γ (X ω)) μ := by
  filter_upwards [ae_areaGood_univ hX hγ hγ2] with ω h
  rw [← compl_eq_univ_sdiff]
  exact (areaGood_mono isOpen_compl_singleton (subset_univ _) h).1

end ConeArea4
end MatedCRTHarmonic.MoTPort
