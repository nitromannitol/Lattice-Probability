/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3D105Sc4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Sc2
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3D105Mu
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Measure
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Measure.Prod
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseCont
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.Interval
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# D105 packet P7, part 2: deterministic vague-limit transfer under `y ↦ δy + c`

Deterministic core of DG Lemma 3.3 (3.6) (`lem-measure-scale`, DG:1014–1036) in the D105 form
(decisions/DEC-105.md §1 item 3–4, §3 N6): DG's proof is "the coordinate change formula
[DS Prop 2.1] … (this is also easy to see directly from the circle average … approximations of
the measures)" (DG:1033–1034) together with `dμ_{h+f} = e^{γf} dμ_h`. We follow the second
route: the approximations `D_j(z) dz` of `μ` and `D'_k(y) dy` of `μ'` satisfy
`D'_k(y) = a · D_{k+m}(Ty) · e^{−γ ψ_k(Ty)}` with `ψ_k → φ` locally uniformly, so
`T_*(w · D'_k dy) = e^{γ(φ − ψ_k)} D_{k+m} dz` on `T(U')`, and uniqueness of vague limits
(QuantumZipper `isVagueLimitOn_unique`) gives `μ|_{T(U')} = T_*(δ²/a · e^{γ φ∘T} μ')`.

* `tendsto_integral_mul_of_unif` — vague convergence survives a density factor `e_k → 1`
  uniformly on the support (no finiteness hypothesis on the approximations);
* `map_affineC_volume`, `setIntegral_comp_affineC` — Lebesgue change of variables;
* **`restrict_eq_map_withDensity_of_vague`** — the deterministic identity.

Own elementary glue (the paper says "easy to see directly", DG:1034).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

open QuantumZipper

/-- **vague convergence with a density factor `e_k → 1` uniformly on the support** -/
lemma tendsto_integral_mul_of_unif {U : Set ℂ} {A : ℕ → Measure ℂ} {μ : Measure ℂ}
    (hA : IsVagueLimitOn U A μ) {e : ℕ → ℂ → ℝ} (hem : ∀ k, Measurable (e k)) {f : ℂ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U)
    (hunif : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ tsupport f, |e k z - 1| < η) :
    Tendsto (fun k => ∫ z, f z * e k z ∂(A k)) atTop (𝓝 (∫ z, f z ∂μ)) := by
  have hf0 : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hB : Tendsto (fun k => ∫ z, f z ∂(A k)) atTop (𝓝 (∫ z, f z ∂μ)) := hA.2.2 f hf hfc hfU
  have hC : Tendsto (fun k => ∫ z, |f z| ∂(A k)) atTop (𝓝 (∫ z, |f z| ∂μ)) :=
    hA.2.2 _ hf.abs (hfc.comp_left abs_zero) ((tsupport_comp_subset abs_zero f).trans hfU)
  -- the key estimate `|a_k − b_k| ≤ η c_k`
  have key : ∀ η, 0 < η → η ≤ 1 / 2 → ∀ k, (∀ z ∈ tsupport f, |e k z - 1| < η) →
      |∫ z, f z * e k z ∂(A k) - ∫ z, f z ∂(A k)| ≤ η * ∫ z, |f z| ∂(A k) := by
    intro η hη hη2 k hk
    have hpt : ∀ z, |f z * e k z - f z| ≤ η * |f z| := fun z => by
      by_cases hz : z ∈ tsupport f
      · rw [show f z * e k z - f z = f z * (e k z - 1) by ring, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hk z hz).le (abs_nonneg _)
      · simp [hf0 z hz]
    have hmeas : AEStronglyMeasurable (fun z => f z * e k z) (A k) :=
      (hf.measurable.mul (hem k)).aestronglyMeasurable
    by_cases hi : Integrable (fun z => |f z|) (A k)
    · have hfi : Integrable f (A k) :=
        hi.mono' hf.aestronglyMeasurable (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs])
      have hfe : Integrable (fun z => f z * e k z) (A k) :=
        (hi.const_mul 2).mono' hmeas (Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          have := hpt z
          have h1 := abs_sub_abs_le_abs_sub (f z * e k z) (f z)
          have h2 : η * |f z| ≤ |f z| := by nlinarith [abs_nonneg (f z)]
          linarith)
      rw [← integral_sub hfe hfi, ← integral_const_mul]
      exact (norm_integral_le_of_norm_le (hi.const_mul η)
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hpt z))
    · have h1 : ¬ Integrable f (A k) := fun h => hi h.abs
      have h2 : ¬ Integrable (fun z => f z * e k z) (A k) := fun h => by
        refine hi ((h.norm.const_mul 2).mono' hf.abs.aestronglyMeasurable
          (Eventually.of_forall fun z => ?_))
        rw [Real.norm_eq_abs, abs_abs, Real.norm_eq_abs]
        have := hpt z
        have h3 := abs_sub_abs_le_abs_sub (f z) (f z * e k z)
        rw [abs_sub_comm] at h3
        nlinarith [abs_nonneg (f z), abs_nonneg (f z * e k z)]
      rw [integral_undef h1, integral_undef h2, integral_undef hi]
      simp
  have hD : Tendsto (fun k => ∫ z, f z * e k z ∂(A k) - ∫ z, f z ∂(A k)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set L := ∫ z, |f z| ∂μ + 1 with hL
    have hL1 : 0 < L := by
      have : 0 ≤ ∫ z, |f z| ∂μ := integral_nonneg fun z => abs_nonneg _
      linarith
    set η := min (1 / 2) (ε / (2 * L)) with hηd
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    filter_upwards [hunif η hη, hC.eventually (gt_mem_nhds (show ∫ z, |f z| ∂μ < L by linarith))]
      with k hk hc
    rw [Real.dist_eq, sub_zero]
    have hc0 : 0 ≤ ∫ z, |f z| ∂(A k) := integral_nonneg fun z => abs_nonneg _
    calc _ ≤ η * ∫ z, |f z| ∂(A k) := key η hη (min_le_left _ _) k hk
      _ ≤ (ε / (2 * L)) * L := mul_le_mul (min_le_right _ _) hc.le hc0 (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  have := hD.add hB
  rw [zero_add] at this
  exact this.congr fun k => by ring

/-- Lebesgue measure under `y ↦ δy + c`: `T_* Leb = δ⁻² Leb` -/
lemma map_affineC_volume {δ : ℝ} (hδ : 0 < δ) (c : ℂ) :
    Measure.map (affineC δ c) volume = ENNReal.ofReal (δ ^ 2)⁻¹ • (volume : Measure ℂ) := by
  have e : affineC δ c = (fun y : ℂ => y + c) ∘ fun y : ℂ => δ • y := by
    funext y; simp only [affineC, Function.comp, Complex.real_smul]
  rw [e, ← Measure.map_map (measurable_add_const c) (measurable_const_smul δ),
    Measure.map_addHaar_smul volume hδ.ne', Measure.map_smul,
    map_add_right_eq_self, Complex.finrank_real_complex,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (δ ^ 2)⁻¹)]
  exact (measurable_add_const c).aemeasurable

/-- change of variables on `U'`: `∫_{U'} F(δy + c) dy = δ⁻² ∫_{T(U')} F` -/
lemma setIntegral_comp_affineC {δ : ℝ} (hδ : 0 < δ) (c : ℂ) (U' : Set ℂ) (F : ℂ → ℝ) :
    ∫ y in U', F (affineC δ c y) = (δ ^ 2)⁻¹ * ∫ x in affineC δ c '' U', F x := by
  set T := affineEquivC hδ c
  have hpre : affineC δ c ⁻¹' (affineC δ c '' U') = U' :=
    preimage_image_eq _ T.injective
  have h1 : (volume.restrict U').map (affineC δ c) =
      (ENNReal.ofReal (δ ^ 2)⁻¹ • volume).restrict (affineC δ c '' U') := by
    rw [← map_affineC_volume hδ c, ← coe_affineEquivC hδ c, T.restrict_map,
      coe_affineEquivC, hpre]
  have h2 := T.measurableEmbedding.integral_map (μ := volume.restrict U') F
  rw [coe_affineEquivC, h1, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), smul_eq_mul] at h2
  exact h2.symm

/-- integrals against a real density -/
lemma integral_withDensity_ofReal (ν : Measure ℂ) {D : ℂ → ℝ} (hD : Measurable D)
    (hD0 : ∀ y, 0 ≤ D y) (g : ℂ → ℝ) :
    ∫ y, g y ∂(ν.withDensity fun y => ENNReal.ofReal (D y)) = ∫ y, D y * g y ∂ν := by
  rw [integral_withDensity_eq_integral_toReal_smul hD.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (hD0 y), smul_eq_mul]

/-- integrals against `T_*(w ν)` -/
lemma integral_map_withDensity_affineC {δ : ℝ} (hδ : 0 < δ) (c : ℂ) (ν : Measure ℂ)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y) (f : ℂ → ℝ) :
    ∫ x, f x ∂((ν.withDensity fun y => ENNReal.ofReal (w y)).map (affineC δ c)) =
      ∫ y, w y * f (affineC δ c y) ∂ν := by
  rw [← coe_affineEquivC hδ c, (affineEquivC hδ c).measurableEmbedding.integral_map,
    coe_affineEquivC, integral_withDensity_ofReal ν hw hw0]

/-- **deterministic core of DG (3.6) at dyadic scale**: if `D_j dz → μ` vaguely on `U`,
`D'_k dy → μ'` vaguely on `U'`, `T(U') ⊆ U` for `T y = δy + c`, and on `U'`
`D'_k(y) = a · D_{k+m}(Ty) · e^{−γ ψ_k(Ty)}` with `ψ_k → φ` uniformly on compacts of `T(U')`
(`φ` continuous), then `μ|_{T(U')} = T_*(δ²/a · e^{γ φ∘T} μ')`. -/
theorem restrict_eq_map_withDensity_of_vague {U U' : Set ℂ} (hU' : IsOpen U') {δ : ℝ}
    (hδ : 0 < δ) {c : ℂ} (hTU : affineC δ c '' U' ⊆ U) {a γ : ℝ} (ha : 0 < a) {m : ℕ}
    {D D' : ℕ → ℂ → ℝ} (hDm : ∀ j, Measurable (D j)) (hD0 : ∀ j z, 0 ≤ D j z)
    (hD'm : ∀ k, Measurable (D' k)) (hD'0 : ∀ k y, 0 ≤ D' k y)
    {ψ : ℕ → ℂ → ℝ} (hψm : ∀ k, Measurable (ψ k)) {φ : ℂ → ℝ} (hφ : Continuous φ)
    (hunif : ∀ C, IsCompact C → C ⊆ affineC δ c '' U' → TendstoUniformlyOn ψ φ atTop C)
    (hrel : ∀ k, ∀ y ∈ U', D' k y =
      a * D (k + m) (affineC δ c y) * Real.exp (-(γ * ψ k (affineC δ c y))))
    {μ μ' : Measure ℂ}
    (hν : IsVagueLimitOn U
      (fun j => (volume.restrict U).withDensity fun z => ENNReal.ofReal (D j z)) μ)
    (hν' : IsVagueLimitOn U'
      (fun k => (volume.restrict U').withDensity fun y => ENNReal.ofReal (D' k y)) μ') :
    μ.restrict (affineC δ c '' U') =
      (μ'.withDensity fun y => ENNReal.ofReal (δ ^ 2 / a * Real.exp (γ * φ (affineC δ c y)))).map
        (affineC δ c) := by
  have hT : Continuous (affineC δ c) := continuous_affineC δ c
  have hV : IsOpen (affineC δ c '' U') := by
    have := (affineHomeoC hδ c).isOpenMap U' hU'; rwa [coe_affineHomeoC] at this
  have hVm := hV.measurableSet
  have hpre : affineC δ c ⁻¹' (affineC δ c '' U') = U' :=
    preimage_image_eq _ (affineEquivC hδ c).injective
  have hcpt : ∀ C, IsCompact C → IsCompact (affineC δ c ⁻¹' C) := fun C hC => by
    have := (affineHomeoC hδ c).isCompact_preimage.2 hC; rwa [coe_affineHomeoC] at this
  set w : ℂ → ℝ := fun y => δ ^ 2 / a * Real.exp (γ * φ (affineC δ c y)) with hwdef
  have hwc : Continuous w :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hφ.comp hT)))
  have hw0 : ∀ y, 0 ≤ w y := fun y => by positivity
  set ν' : ℕ → Measure ℂ :=
    fun k => (volume.restrict U').withDensity fun y => ENNReal.ofReal (D' k y)
  set ρ : ℕ → Measure ℂ :=
    fun k => ((ν' k).withDensity fun y => ENNReal.ofReal (w y)).map (affineC δ c) with hρ
  have hρint : ∀ k (f : ℂ → ℝ), ∫ x, f x ∂(ρ k) = ∫ y, w y * f (affineC δ c y) ∂(ν' k) :=
    fun k f => integral_map_withDensity_affineC hδ c _ hwc.measurable hw0 f
  have hpull : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      tsupport f ⊆ affineC δ c '' U' →
      Continuous (fun y => w y * f (affineC δ c y)) ∧
        HasCompactSupport (fun y => w y * f (affineC δ c y)) ∧
          tsupport (fun y => w y * f (affineC δ c y)) ⊆ U' := by
    intro f hf hfc hfV
    have hsub : tsupport (fun y => w y * f (affineC δ c y)) ⊆ affineC δ c ⁻¹' tsupport f :=
      closure_minimal (fun y hy => subset_tsupport f (fun h => hy (by simp [h])))
        ((isClosed_tsupport f).preimage hT)
    exact ⟨hwc.mul (hf.comp hT), (hcpt _ hfc).of_isClosed_subset (isClosed_tsupport _) hsub,
      hsub.trans (by rw [← hpre]; exact preimage_mono hfV)⟩
  -- the limit `T_*(w μ')`
  have h2 : IsVagueLimitOn (affineC δ c '' U') ρ
      ((μ'.withDensity fun y => ENNReal.ofReal (w y)).map (affineC δ c)) := by
    refine ⟨?_, fun C hC hCV => ?_, fun f hf hfc hfV => ?_⟩
    · rw [Measure.map_apply hT.measurable hVm.compl, preimage_compl, hpre]
      exact withDensity_absolutelyContinuous _ _ hν'.1
    · rw [Measure.map_apply hT.measurable hC.measurableSet,
        withDensity_apply _ (hC.measurableSet.preimage hT.measurable)]
      obtain ⟨M, hM⟩ := (hcpt C hC).exists_bound_of_continuousOn hwc.continuousOn
      calc ∫⁻ y in affineC δ c ⁻¹' C, ENNReal.ofReal (w y) ∂μ'
          ≤ ∫⁻ y in affineC δ c ⁻¹' C, ENNReal.ofReal M ∂μ' :=
            setLIntegral_mono measurable_const fun y hy => ENNReal.ofReal_le_ofReal
              ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM y hy))
        _ = ENNReal.ofReal M * μ' (affineC δ c ⁻¹' C) := setLIntegral_const _ _
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (hν'.2.1 _ (hcpt C hC) (by rw [← hpre]; exact preimage_mono hCV))
    · obtain ⟨g1, g2, g3⟩ := hpull f hf hfc hfV
      rw [integral_map_withDensity_affineC hδ c _ hwc.measurable hw0]
      exact (hν'.2.2 _ g1 g2 g3).congr fun k => (hρint k f).symm
  -- the limit `μ|_{T(U')}`
  have h1 : IsVagueLimitOn (affineC δ c '' U') ρ (μ.restrict (affineC δ c '' U')) := by
    refine ⟨?_, fun C hC hCV => ?_, fun f hf hfc hfV => ?_⟩
    · rw [Measure.restrict_apply hVm.compl, compl_inter_self, measure_empty]
    · exact (Measure.restrict_apply_le _ _).trans_lt (hν.2.1 C hC (hCV.trans hTU))
    · have hf0 : ∀ x, x ∉ affineC δ c '' U' → f x = 0 := fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hfV h))
      set e : ℕ → ℂ → ℝ := fun k z => Real.exp (γ * -(ψ k z - φ z)) with hedef
      have hem : ∀ k, Measurable (e k) := fun k =>
        Real.measurable_exp.comp (measurable_const.mul ((hψm k).sub hφ.measurable).neg)
      have hunif' : ∀ η > 0, ∀ᶠ k in atTop, ∀ z ∈ tsupport f, |e k z - 1| < η := by
        intro η hη
        have hd : TendstoUniformlyOn (fun k z => ψ k z - φ z) (fun _ => 0) atTop (tsupport f) := by
          have h := hunif _ hfc hfV
          rw [Metric.tendstoUniformlyOn_iff] at h ⊢
          intro ε hε
          filter_upwards [h ε hε] with k hk z hz
          have := hk z hz
          rw [Real.dist_eq] at this ⊢
          rwa [zero_sub, abs_neg, abs_sub_comm]
        have he := Metric.tendstoUniformlyOn_iff.1
          (tendstoUniformlyOn_exp_neg γ hfc continuous_const hd) η hη
        filter_upwards [he] with k hk z hz
        have := hk z hz
        rwa [neg_zero, mul_zero, Real.exp_zero, Real.dist_eq, abs_sub_comm] at this
      have hνm : IsVagueLimitOn U (fun k => (volume.restrict U).withDensity
          fun z => ENNReal.ofReal (D (k + m) z)) μ :=
        ⟨hν.1, hν.2.1, fun g a b c => (hν.2.2 g a b c).comp (tendsto_add_atTop_nat m)⟩
      have hlim := tendsto_integral_mul_of_unif hνm hem hf hfc (hfV.trans hTU) hunif'
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero hf0]
      refine hlim.congr fun k => ?_
      set G : ℂ → ℝ := fun x => D (k + m) x * (f x * e k x) with hG
      have hG0 : ∀ x, x ∉ affineC δ c '' U' → G x = 0 := fun x hx => by simp [hG, hf0 x hx]
      rw [hρint, integral_withDensity_ofReal _ (hD'm k) (hD'0 k),
        integral_withDensity_ofReal _ (hDm (k + m)) (hD0 (k + m)),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hG0 x (fun h => hx (hTU h))),
        ← setIntegral_eq_integral_of_forall_compl_eq_zero hG0]
      have hpt : ∀ y ∈ U', D' k y * (w y * f (affineC δ c y)) = δ ^ 2 * G (affineC δ c y) := by
        intro y hy
        have hE : Real.exp (γ * -(ψ k (affineC δ c y) - φ (affineC δ c y))) =
            Real.exp (-(γ * ψ k (affineC δ c y))) * Real.exp (γ * φ (affineC δ c y)) := by
          rw [← Real.exp_add]; ring_nf
        simp only [hG, hedef, hwdef, hrel k y hy, hE]
        field_simp
      rw [setIntegral_congr_fun hU'.measurableSet hpt, integral_const_mul,
        setIntegral_comp_affineC hδ c U' G]
      field_simp
  exact isVagueLimitOn_unique hV h1 h2

end DG
end LQGMetric
