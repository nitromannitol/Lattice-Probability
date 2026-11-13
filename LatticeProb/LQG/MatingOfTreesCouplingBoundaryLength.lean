import LatticeProb.LQG.MatingOfTreesCouplingLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.Radial

/-!
# The boundary-length clause of a mating-of-trees coupling depends only on its law

The boundary-length clause of a mating-of-trees coupling asks for a measurable functional `BL` of
the quantum cone field and the curve which almost surely returns the boundary-length pair `bm`,
and which, for every level `b₀ > 0`, maps the field and the curve rescaled at the cone scale
`R_{b₀}` to the Brownian rescaling `b₀^{-1/2} bm(b₀ ·)` of the boundary-length pair.

On the measurable set `radGood` of pairs of paths whose cone radial path is continuous, the cone
field, the cone scale and the rescaled field and curve are measurable functions of the data. The
cone Brownian motions of a coupling lie in `radGood` almost surely for `0 < γ < 2` (the drifted
Brownian motion `B'_t + (Q - γ) t` has a bounded zero set), so the clause transfers, with the same
functional `BL`, to every measurable random element of the data space with the law of a coupling.

* `MeasureTheory.ae_eq_comp_of_map_eq_of_eqOn`: an almost sure identity `f ∘ V = g ∘ V` passes to
  a random element with the law of `V` when `f` and `g` agree with measurable maps on a measurable
  set of full law-measure.
* `measurable_addConst_comp`, `measurable_coneRescaleField_uncurry`,
  `measurable_coneRescaleCurve_uncurry`, `measurable_brownRescale`: joint measurability of the
  rescalings.
* `CouplingData.coneScaleOf`, `CouplingData.coneScale_eq_coneScaleOf`: on `radGood` the cone scale
  is the exponential of the last level of the radial path, a measurable function of the data.
* `IsCouplingData.ae_radGood`, `IsCouplingData.boundaryLength_of_map_eq`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace MeasureTheory

variable {Ω Ω' 𝒱 E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace 𝒱]
  [MeasurableSpace E] [MeasurableEq E] {P : Measure Ω} {P' : Measure Ω'} {V : Ω → 𝒱}
  {V' : Ω' → 𝒱}

/-- An almost sure identity `f ∘ V = g ∘ V` passes to a random element `V'` with the law of `V`
when `f` and `g` agree with measurable maps `f₀` and `g₀` on a measurable set `T` which contains
`V` almost surely. -/
theorem ae_eq_comp_of_map_eq_of_eqOn (hV : Measurable V) (hV' : Measurable V')
    (hlaw : P'.map V' = P.map V) {T : Set 𝒱} (hT : MeasurableSet T) (hTae : ∀ᵐ ω ∂P, V ω ∈ T)
    {f g f₀ g₀ : 𝒱 → E} (hf₀ : Measurable f₀) (hg₀ : Measurable g₀) (hf : EqOn f f₀ T)
    (hg : EqOn g g₀ T) (h : ∀ᵐ ω ∂P, f (V ω) = g (V ω)) : ∀ᵐ ω ∂P', f (V' ω) = g (V' ω) := by
  have hS : MeasurableSet (T ∩ {v | f₀ v = g₀ v}) := hT.inter (measurableSet_eq_fun hf₀ hg₀)
  have h' : ∀ᵐ ω ∂P, V ω ∈ T ∩ {v | f₀ v = g₀ v} := by
    filter_upwards [hTae, h] with ω hω hfg
    exact ⟨hω, show f₀ (V ω) = g₀ (V ω) by rw [← hf hω, ← hg hω]; exact hfg⟩
  filter_upwards [ae_comp_of_map_eq hV hV' hlaw hS h'] with ω hω
  rw [hf hω.1, hg hω.1]
  exact hω.2

end MeasureTheory

namespace MatedCRTHarmonic

namespace MatedCRT

/-- Adding a measurable constant to a measurable random distribution is measurable. -/
theorem measurable_addConst_comp {α : Type*} [MeasurableSpace α] {Ψ : α → LQGMetric.DistC}
    {x : α → ℝ} (hΨ : Measurable Ψ) (hx : Measurable x) :
    Measurable fun a => LQGMetric.addConst (Ψ a) (x a) := by
  refine LQGMetric.GFFInv.measurable_distC_iff.2 fun φ => ?_
  simp only [LQGMetric.GFFInv.addConst_apply]
  exact (LQGMetric.GFFInv.measurable_distC_iff.1 hΨ φ).add (hx.const_mul _)

/-- The rescaled cone field `(R, h) ↦ h(R ·) + Q log R - γ⁻¹ log b₀` is jointly measurable. -/
theorem measurable_coneRescaleField_uncurry (γ b₀ : ℝ) :
    Measurable fun p : ℝ × Field => coneRescaleField γ p.1 b₀ p.2 := by
  unfold coneRescaleField
  exact measurable_addConst_comp MoTPort.ConeMeas.measurable_affineComp_joint
    ((measurable_const.mul (Real.measurable_log.comp measurable_fst)).sub measurable_const)

/-- The rescaled curve `(R, c) ↦ R⁻¹ c(b₀ ·)` is jointly measurable. -/
theorem measurable_coneRescaleCurve_uncurry (b₀ : ℝ) :
    Measurable fun p : ℝ × C(ℝ, ℂ) => coneRescaleCurve p.1 b₀ p.2 := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  simp only [coneRescaleCurve, ContinuousMap.coe_mk]
  exact (Complex.measurable_ofReal.comp measurable_fst.inv).mul
    ((continuous_eval_const (b₀ * t)).measurable.comp measurable_snd)

/-- The Brownian rescaling `ω ↦ b₀^{-1/2} ω(b₀ ·)` of a path in `ℝ²` is measurable. -/
theorem measurable_brownRescale (b₀ : ℝ) : Measurable (brownRescale b₀) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  simp only [brownRescale, ContinuousMap.coe_mk]
  exact (continuous_eval_const (F := Path2) (b₀ * t)).measurable.const_smul (b₀ ^ (-(1 / 2 : ℝ)))

namespace CouplingData

/-- The cone scale `R_{b₀}` read off the data: the exponential of the last level
`γ⁻¹ log b₀` of the radial path of the cone (the radial path is `ConeScaling.radMap`, which is
`0` off `radGood`). -/
def coneScaleOf (γ b₀ : ℝ) (v : CouplingData) : ℝ :=
  Real.exp (ConeScaling.lastLevel (lqgQ γ) (γ⁻¹ * Real.log b₀) (ConeScaling.radMap γ γ (v.B, v.B')))

theorem measurable_coneScaleOf (γ b₀ : ℝ) : Measurable (coneScaleOf γ b₀) :=
  Real.measurable_exp.comp ((ConeScaling.measurable_lastLevel _ _).comp
    ((ConeScaling.measurable_radMap γ γ).comp (measurable_B.prodMk measurable_B')))

/-- On `radGood` the cone scale of the paths of the data is `coneScaleOf`. -/
theorem coneScale_eq_coneScaleOf {γ : ℝ} {v : CouplingData}
    (hv : (v.B, v.B') ∈ ConeScaling.radGood γ γ) (b₀ : ℝ) :
    coneScale γ γ v.B v.B' b₀ = coneScaleOf γ b₀ v := by
  classical
  exact ConeScaling.coneScale_eq_exp_lastLevel γ b₀ fun t => by
    simp only [ConeScaling.radMap_apply, hv, ↓reduceIte]

end CouplingData

variable {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  {γ : ℝ} {V : Ω → CouplingData} {V' : Ω' → CouplingData}

open CouplingData

/-- For `0 < γ < 2` the cone Brownian motions of a coupling almost surely lie in `radGood`: both
start at `0` and the drifted path `B'_t + (Q - γ) t` has a bounded zero set. -/
theorem IsCouplingData.ae_radGood (hC : IsCouplingData γ P V) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ((V ω).B, (V ω).B') ∈ ConeScaling.radGood γ γ := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  filter_upwards [hCP.bm_B.eval_zero_ae_eq_zero, hCP.bm_B'.eval_zero_ae_eq_zero,
    CellScaling.ae_goodDrift hCP.bm_B' (CellScaling.lqgQ_sub_pos hγ hγ2)] with ω h1 h2 hdrift
  exact ⟨h1, h2, hdrift.bddAbove_zeroSet⟩

/-- **The boundary-length clause depends only on the law.** If the cone Brownian motions of a
coupling lie in `radGood` almost surely, then every measurable random element of the data space
with the law of the coupling satisfies the boundary-length clause, with the same functional
`BL`. -/
theorem IsCouplingData.boundaryLength_of_map_eq (hC : IsCouplingData γ P V) (hV : Measurable V)
    (hV' : Measurable V') (hlaw : P'.map V' = P.map V)
    (hrad : ∀ᵐ ω ∂P, ((V ω).B, (V ω).B') ∈ ConeScaling.radGood γ γ) :
    ∃ BL : Field × C(ℝ, ℂ) → Path2, Measurable BL ∧
      (∀ᵐ ω ∂P', (V' ω).bm = BL (coneField (V' ω).X
        (coneRadial γ γ (fun u => (V' ω).B u) (fun u => (V' ω).B' u)), (V' ω).η)) ∧
      ∀ b₀ : ℝ, 0 < b₀ → ∀ᵐ ω ∂P',
        BL (coneRescaleField γ (coneScale γ γ (fun u => (V' ω).B u) (fun u => (V' ω).B' u) b₀) b₀
              (coneField (V' ω).X (coneRadial γ γ (fun u => (V' ω).B u) (fun u => (V' ω).B' u))),
            coneRescaleCurve (coneScale γ γ (fun u => (V' ω).B u) (fun u => (V' ω).B' u) b₀) b₀
              (V' ω).η) =
          brownRescale b₀ (V' ω).bm := by
  have hCP := (show IsMatingOfTreesCoupling _ _ _ _ _ _ _ _ _ _ _ _ _ _ from hC)
  obtain ⟨BL, hBL, h1, h2⟩ := hCP.boundaryLength
  have hT : MeasurableSet {v : CouplingData | (v.B, v.B') ∈ ConeScaling.radGood γ γ} :=
    (ConeScaling.measurableSet_radGood γ γ).preimage (measurable_B.prodMk measurable_B')
  have hfield : ∀ v : CouplingData, (v.B, v.B') ∈ ConeScaling.radGood γ γ →
      coneField v.X (coneRadial γ γ v.B v.B') = (coneTriple γ v).1 :=
    fun v hv => (coneTriple_fst_of_mem hv).symm
  have hF : Measurable fun v : CouplingData => (coneTriple γ v).1 :=
    measurable_fst.comp (measurable_coneTriple γ)
  refine ⟨BL, hBL, ?_, fun b₀ hb₀ => ?_⟩
  · refine ae_eq_comp_of_map_eq_of_eqOn (f := fun v => v.bm)
      (g := fun v => BL (coneField v.X (coneRadial γ γ v.B v.B'), v.η))
      (g₀ := fun v => BL ((coneTriple γ v).1, v.η)) hV hV' hlaw hT hrad
      measurable_bm (hBL.comp (hF.prodMk measurable_η)) (fun _ _ => rfl) (fun v hv => ?_) h1
    simp only [hfield v hv]
  · have hS := measurable_coneScaleOf γ b₀
    refine ae_eq_comp_of_map_eq_of_eqOn
      (f := fun v => BL (coneRescaleField γ (coneScale γ γ v.B v.B' b₀) b₀
        (coneField v.X (coneRadial γ γ v.B v.B')), coneRescaleCurve (coneScale γ γ v.B v.B' b₀) b₀ v.η))
      (f₀ := fun v => BL (coneRescaleField γ (coneScaleOf γ b₀ v) b₀ (coneTriple γ v).1,
        coneRescaleCurve (coneScaleOf γ b₀ v) b₀ v.η))
      (g := fun v => brownRescale b₀ v.bm) hV hV' hlaw hT hrad
      (hBL.comp (((measurable_coneRescaleField_uncurry γ b₀).comp (hS.prodMk hF)).prodMk
        ((measurable_coneRescaleCurve_uncurry b₀).comp (hS.prodMk measurable_η))))
      ((measurable_brownRescale b₀).comp measurable_bm) (fun v hv => ?_) (fun _ _ => rfl)
      (h2 b₀ hb₀)
    simp only [coneScale_eq_coneScaleOf hv b₀, hfield v hv]

end MatedCRT

end MatedCRTHarmonic

end
