/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea5B at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea5

/-!
# Cone area, part 11: growth of the cone shift at the origin

For the cone field `coneField (lateralPartC X) A Q = X + g`, `g = coneShift A Q R`
(ConeArea3B), with `s = −log|w|`:

  `g(w) = Q s + A_s − R(|w|) = α s + b_s − X_1(0) − β_s`

where `b` is the Brownian motion of the cone process (DMS Def. 4.10 with Def. 4.5, `Q t + A_t =
b_t + α t` for `t ≥ 0`, `conePath_of_nonneg`) and `β_s = X_{e^{-s}}(0) − X_1(0)` is the circle
average Brownian motion of the whole-plane GFF (Duplantier–Sheffield arXiv:0808.1560 Prop. 3.3;
LM `CircleAvg.isPreBrownianReal_circleAvg`). By the law of large numbers for Brownian motion
(QZ `BMLLN.ae_tendsto_div_atTop`) both are `o(s)`, so

  **`ae_coneShift_le`**: a.s., for every `η > 0` there is `C` with `g(w) ≤ (α+η)(−log|w|) + C`
  on the punctured unit disc,

for every version `R` of the radial part continuous on `(0,∞)` (all such versions agree:
`eqOn_of_ae_norm`). This gives the comparison needed for the cone area measure.

* `exists_radFt_version`: on an event of full measure the measurable dyadic version `radFt`
  (ConeArea4E) equals LM's continuous version of the circle averages at the centre `0` (copied
  from the proof of `ConeArea4.ae_radial_version`);
* `isBrownianReal_radBM`: `t ↦ radFt X (e^{-t})` is a standard Brownian motion.

Own elementary glue around the cited facts.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea5

open QuantumZipper LQGMetric ConeArea4

/-- continuous radial profiles that agree at a.e. point of the plane agree on `(0,∞)` -/
lemma eqOn_of_ae_norm {f g : ℝ → ℝ} (hf : ContinuousOn f (Ioi 0)) (hg : ContinuousOn g (Ioi 0))
    (h : ∀ᵐ z ∂(volume : Measure ℂ), f ‖z‖ = g ‖z‖) : ∀ r, 0 < r → f r = g r := by
  intro r hr
  by_contra hne
  have hcont : ContinuousAt (fun s => f s - g s) r :=
    ((hf.sub hg) r hr).continuousAt (Ioi_mem_nhds hr)
  have hev : ∀ᶠ s in 𝓝 r, f s - g s ≠ 0 := hcont.eventually_ne (sub_ne_zero.2 hne)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set V : Set ℂ := (fun z : ℂ => ‖z‖) ⁻¹' ball r ε with hV
  have hVo : IsOpen V := isOpen_ball.preimage continuous_norm
  have hVne : V.Nonempty := ⟨(r : ℂ), by
    simp only [hV, mem_preimage, Complex.norm_of_nonneg hr.le, mem_ball, dist_self]; exact hε⟩
  have hpos := hVo.measure_pos (volume : Measure ℂ) hVne
  have hnull : volume {z : ℂ | ¬ f ‖z‖ = g ‖z‖} = 0 := ae_iff.1 h
  refine hpos.ne' (measure_mono_null (fun z hz => ?_) hnull)
  exact fun e => hball hz (sub_eq_zero.2 e)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Field}

/-- the measurable version `radFt` agrees a.s. with LM's continuous version of the circle
averages at `0` (copied from the proof of `ConeArea4.ae_radial_version`) -/
theorem exists_radFt_version [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    ∃ H : ℝ → ℂ → Ω → ℝ, (∀ ω, ContinuousOn (fun p : ℝ × ℂ => H p.1 p.2 ω) (Ioi 0 ×ˢ univ)) ∧
      (∀ r, 0 < r → ∀ z, (fun ω => H r z ω) =ᵐ[P]
        fun ω => circleAvg (X ω) r z - circleAvg (X ω) 1 0) ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → radFt X (r, ω) = H r 0 ω := by
  obtain ⟨H, hHc, hHae⟩ := CircleAvg.exists_continuous_version_circleAvg hX
  refine ⟨H, hHc, hHae, ?_⟩
  have hG : ∀ᵐ ω ∂P, ∀ n j : ℕ,
      H (((j : ℝ) + 1) / 2 ^ n) 0 ω = radG X (((j : ℝ) + 1) / 2 ^ n) ω := by
    simp only [ae_all_iff]
    intro n j
    exact hHae _ (by positivity) 0
  filter_upwards [hG] with ω hω r hr
  have hlim : Tendsto (fun n => H (dyUp n r) 0 ω) atTop (𝓝 (H r 0 ω)) := by
    have hc := ((hHc ω) (r, 0) ⟨hr, mem_univ _⟩).tendsto
    have ht : Tendsto (fun n : ℕ => ((dyUp n r, (0 : ℂ)) : ℝ × ℂ)) atTop
        (𝓝[Ioi 0 ×ˢ univ] (r, 0)) :=
      tendsto_nhdsWithin_iff.2 ⟨(tendsto_dyUp hr.le).prodMk_nhds tendsto_const_nhds,
        Eventually.of_forall fun n =>
          (show ((dyUp n r, (0 : ℂ)) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) from
            ⟨dyUp_pos n r, mem_univ _⟩)⟩
    exact hc.comp ht
  have e : (fun n => radG X (dyUp n r) ω) = fun n => H (dyUp n r) 0 ω :=
    funext fun n => (hω n _).symm
  show limUnder atTop (fun n => radG X (dyUp n r) ω) = _
  rw [e]
  exact hlim.limUnder_eq

/-- a.s. `radFt X (|z|) = X_{|z|}(0) − X_1(0)` at a.e. point `z` (Fubini, as in ConeArea4E) -/
theorem ae_ae_radFt_eq [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ), radFt X (‖z‖, ω) = radG X ‖z‖ ω := by
  obtain ⟨H, -, hHae, hEv⟩ := exists_radFt_version hX
  have hg := measurable_radG hX.measurable
  have hFt := measurable_radFt hX.measurable
  have hS : MeasurableSet {p : Ω × ℂ | radFt X (‖p.2‖, p.1) = radG X ‖p.2‖ p.1} :=
    measurableSet_eq_fun
      (hFt.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
      (hg.comp (f := fun p : Ω × ℂ => (‖p.2‖, p.1))
        ((measurable_norm.comp measurable_snd).prodMk measurable_fst))
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  rw [Measure.ae_ae_comm hS]
  filter_upwards [hne] with z hz
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  filter_upwards [hEv, hHae ‖z‖ hz' 0] with ω hω h1
  rw [hω _ hz', h1]; rfl

/-- the radial Brownian motion `t ↦ X_{e^{-t}}(0) − X_1(0)`, read through `radFt` -/
def radBM (X : Ω → Field) (t : ℝ≥0) (ω : Ω) : ℝ := radFt X (Real.exp (-(t : ℝ)), ω)

/-- **`t ↦ X_{e^{-t}}(0) − X_1(0)` is a standard Brownian motion** (DS Prop. 3.3) -/
theorem isBrownianReal_radBM [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) :
    IsBrownianReal (radBM X) P := by
  obtain ⟨H, hHc, hHae, hEv⟩ := exists_radFt_version hX
  obtain ⟨B₀, hpre, -, hB₀⟩ := CircleAvg.isPreBrownianReal_circleAvg hX 0
  refine ⟨hpre.congr fun t => ?_, ?_⟩
  · filter_upwards [hB₀ t, hHae _ (Real.exp_pos (-(t : ℝ))) 0, hEv] with ω h1 h2 h3
    rw [h1]
    show _ = radFt X (Real.exp (-(t : ℝ)), ω)
    rw [h3 _ (Real.exp_pos _), h2]
  · filter_upwards [hEv] with ω hω
    have e : (fun t : ℝ≥0 => radBM X t ω) = fun t : ℝ≥0 => H (Real.exp (-(t : ℝ))) 0 ω :=
      funext fun t => hω _ (Real.exp_pos _)
    rw [e]
    have hc : Continuous fun t : ℝ≥0 => ((Real.exp (-(t : ℝ)), (0 : ℂ)) : ℝ × ℂ) :=
      (Real.continuous_exp.comp NNReal.continuous_coe.neg).prodMk continuous_const
    exact (hHc ω).comp_continuous hc fun t => ⟨Real.exp_pos _, mem_univ _⟩

/-- `|f t| ≤ η (M + t)` from `f t / t → 0` (scaled form of `ConeArea4.exists_abs_le_add`) -/
lemma exists_abs_le_eta {f : ℝ≥0 → ℝ} (hc : Continuous f)
    (hl : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * f t) atTop (𝓝 0)) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, ∀ t : ℝ≥0, |f t| ≤ η * (M + t) := by
  have hl' : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * (η⁻¹ * f t)) atTop (𝓝 0) := by
    have := hl.const_mul η⁻¹
    rw [mul_zero] at this
    exact this.congr fun t => by ring
  obtain ⟨M, -, hM⟩ := exists_abs_le_add (f := fun t => η⁻¹ * f t)
    (continuous_const.mul hc) hl'
  refine ⟨M, fun t => ?_⟩
  have h : |η⁻¹ * f t| ≤ M + t := hM t
  rw [abs_mul, abs_inv, abs_of_pos hη, inv_mul_le_iff₀ hη] at h
  exact h

/-- **growth of the cone shift at `0`**: a.s., for every version `R` of the radial part continuous
on `(0,∞)` and every `η > 0`, `coneShift A Q R (w) ≤ (α + η)(−log|w|) + C` on the punctured unit
disc -/
theorem ae_coneShift_le [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hX : IsWholePlaneGFF X P) (hA : IsConeProcess α Q A P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ → ℝ, ContinuousOn R (Ioi 0) →
      (radialFun (X ω) =ᵐ[volume] fun z => R ‖z‖) → ∀ η : ℝ, 0 < η → ∃ C : ℝ,
        ∀ w : ℂ, w ≠ 0 → ‖w‖ < 1 →
          ConeArea3.coneShift (fun t => A t ω) Q R w ≤ (α + η) * -Real.log ‖w‖ + C := by
  obtain ⟨H, hHc, -, hEv⟩ := exists_radFt_version hX
  have hBM := isBrownianReal_radBM hX
  obtain ⟨b, b', hb, -, -, hAe⟩ := hA
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [hEv, ae_ae_radFt_eq hX, BMLLN.ae_tendsto_div_atTop hBM,
    BMLLN.ae_tendsto_div_atTop hb, hb.cont, hBM.cont] with ω hω hFω hl1 hl2 hc2 hc1
  intro R hRc hRe η hη
  set c₀ := circleAvg (X ω) 1 0 with hc₀
  have hHc' : ContinuousOn (fun r => H r 0 ω) (Ioi 0) :=
    (hHc ω).comp (continuous_id.prodMk continuous_const).continuousOn
      fun r hr => ⟨hr, mem_univ _⟩
  have hid : ∀ r, 0 < r → R r - c₀ = H r 0 ω := by
    refine eqOn_of_ae_norm (hRc.sub continuousOn_const) hHc' ?_
    filter_upwards [hRe, hFω, hne] with z h1 h2 h3
    have hz : 0 < ‖z‖ := norm_pos_iff.2 h3
    rw [← h1, ← hω _ hz, h2]
    simp only [radialFun, radG, hc₀]
  obtain ⟨M₁, hM₁⟩ := exists_abs_le_eta hc1 hl1 (half_pos hη)
  obtain ⟨M₂, hM₂⟩ := exists_abs_le_eta hc2 hl2 (half_pos hη)
  refine ⟨η / 2 * M₁ + η / 2 * M₂ + |c₀|, fun w hw0 hw1 => ?_⟩
  have hpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
  set s := -Real.log ‖w‖ with hs
  have hs0 : 0 ≤ s := neg_nonneg.2 (Real.log_nonpos hpos.le hw1.le)
  have hR : R ‖w‖ = c₀ + radBM X s.toNNReal ω := by
    have h := hid ‖w‖ hpos
    have hex : Real.exp (-((s.toNNReal : ℝ≥0) : ℝ)) = ‖w‖ := by
      rw [Real.coe_toNNReal _ hs0, hs, neg_neg, Real.exp_log hpos]
    simp only [radBM, hex, hω _ hpos]
    linarith
  have hA' : A s ω = b s.toNNReal ω + (α - Q) * s := by
    rw [hAe ω, conePath_of_nonneg _ _ _ _ hs0]
  have h1 := hM₁ s.toNNReal
  have h2 := hM₂ s.toNNReal
  rw [Real.coe_toNNReal _ hs0] at h1 h2
  have h1' := (abs_le.1 h1).1
  have h2' := (abs_le.1 h2).2
  have h3 := neg_abs_le c₀
  simp only [ConeArea3.coneShift]
  rw [← hs, hA', hR]
  nlinarith
