/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCIdent4LGD at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent4Dy
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCIdent3Wn
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeasQ

/-!
# Law transfer of the LGD event (P2-GMCID4, D85, handoff/P2-GMCID3.md "T2 consumers")

* `aemeasurable_qAreaMeasureOn_ball_circ`: under the circle law `circLaw P X`, the ball masses
  of the LQG measure of the canonical field `circExt v` are a.e.-measurable. This is the argument
  of `DZZ.aemeasurable_qAreaMeasureOn_ball'` (LGDMeasQ.lean) for the field `circExt` on
  `(CircIdx → ℝ, circLaw P X)`: it uses only measurability of the field (`measurable_circExt`) and
  the a.s. vague limit (`ae_isVagueLimitOn_circExt`).
* `nullMeasurableSet_lgdEvent_circ`: the LGD event `log D_δ(u,v) / log δ⁻¹ → χ` of
  `IsLGDExponent` is null-measurable for `circLaw P X` (reduction to dyadic `δ`,
  `tendsto_lgdRatio_iff_dyadic`, then `measurableSet_tendsto` for measurable versions).
* **`ae_lgdEvent_iff_wn`**: the LGD event holds a.s. for a zero-boundary GFF `X` iff it holds
  a.s. for the white-noise field (`GMCIdent3.ae_iff_wn`).
* **`isLGDExponent_iff_wn`**: hence `IsLGDExponent γ χ` iff the LGD event holds a.s. for the
  white-noise field, for all `u ≠ v` in `𝕍` (given one zero-boundary GFF).
* `map_qArea_eq_wn`, `map_qArea_ball_eq_wn`: laws of functionals of `M_γ` (e.g. ball masses)
  agree for a zero-boundary GFF and for the white-noise field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped ENNReal

namespace LQGMetric
namespace GMCIdent4

open WhiteNoise GMCIdent3

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} {X : Ω → Measure ℂ → ℝ} {W : WNSpace → Ω' → ℝ}

/-- **a.e.-measurability of ball masses under the circle law** (port of
`DZZ.aemeasurable_qAreaMeasureOn_ball'`) -/
theorem aemeasurable_qAreaMeasureOn_ball_circ [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (c : ℂ)
    (r : ℝ) :
    AEMeasurable (fun v => qAreaMeasureOn γ (circExt v) openSquare (Metric.ball c r))
      (circLaw P X) := by
  set U : Set ℂ := Metric.ball c r ∩ openSquare with hU
  have hUo : IsOpen U := Metric.isOpen_ball.inter isOpen_openSquare'
  have hUb : Bornology.IsBounded U := Metric.isBounded_ball.subset inter_subset_left
  have hUc : Uᶜ.Nonempty := ⟨0, fun h => by
    have := h.2; simp [openSquare] at this⟩
  have hUU : U ⊆ openSquare := inter_subset_right
  let F : (CircIdx → ℝ) → ℝ≥0∞ := fun v =>
    ⨆ n, ENNReal.ofReal (Prop16Area.Meas.Psi γ circExt (fun _ z => LQGMeas.openBump U n z) v)
  have hF : Measurable F := Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (Prop16Area.Meas.measurable_Psi γ measurable_circExt
      ((LQGMeas.continuous_openBump U n).measurable.comp measurable_snd))
  refine hF.aemeasurable.congr ?_
  filter_upwards [ae_isVagueLimitOn_circExt hX hγ hγ2] with v hm
  set μ := qAreaMeasureOn γ (circExt v) openSquare
  have hts : ∀ n, tsupport (LQGMeas.openBump U n) ⊆ openSquare := fun n =>
    (LQGMeas.tsupport_openBump_subset U n).trans hUU
  have ePsi : ∀ n, Prop16Area.Meas.Psi γ circExt (fun _ z => LQGMeas.openBump U n z) v =
      ∫ z, LQGMeas.openBump U n z ∂μ := fun n =>
    (hm.2.2 _ (LQGMeas.continuous_openBump U n) (LQGMeas.hasCompactSupport_openBump hUb n)
      (hts n)).limUnder_eq
  have eL : ∀ n, ENNReal.ofReal (∫ z, LQGMeas.openBump U n z ∂μ) =
      ∫⁻ z, ENNReal.ofReal (LQGMeas.openBump U n z) ∂μ := fun n =>
    ofReal_integral_eq_lintegral_ofReal
      (GoodSample.integrable_of_tsupport hm.2.1 (LQGMeas.continuous_openBump U n)
        (LQGMeas.hasCompactSupport_openBump hUb n) (hts n))
      (ae_of_all _ (LQGMeas.openBump_nonneg U n))
  simp only [F, ePsi, eL]
  rw [← LQGMeas.measure_open_eq_iSup μ hUo hUc, hU,
    measure_inter_conull (qAreaMeasureOn_openSquare_compl γ (circExt v))]

/-- the LGD event of `IsLGDExponent` along dyadic scales -/
lemma lgdEvent_iff_dyadic (μ : Measure ℂ) (u v : ℂ) (χ : ℝ) :
    Tendsto (fun δ : ℝ => Real.log (lgdDZZ μ δ u v).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) ↔
      Tendsto (fun n : ℕ => Real.log (lgdDZZ μ ((2 : ℝ)⁻¹ ^ n) u v).toNat /
        Real.log ((2 : ℝ)⁻¹ ^ n)⁻¹) atTop (𝓝 χ) :=
  tendsto_lgdRatio_iff_dyadic (g := fun δ => lgdDZZ μ δ u v)
    (fun _ _ hδ hle => lgdDZZ_antitone μ hδ.le hle u v) (fun δ => one_le_lgdDZZ μ δ u v) χ

/-- **null-measurability of the LGD event under the circle law** -/
theorem nullMeasurableSet_lgdEvent_circ [IsProbabilityMeasure P]
    (hX : IsZeroBoundaryGFFOn openSquare X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (χ : ℝ)
    (u v : ℂ) :
    NullMeasurableSet {w | Tendsto (fun δ : ℝ => Real.log
        (lgdDZZ (qAreaMeasureOn γ (circExt w) openSquare) δ u v).toNat / Real.log δ⁻¹)
        (𝓝[>] 0) (𝓝 χ)} (circLaw P X) := by
  set φ : ℕ → (CircIdx → ℝ) → ℝ := fun n w =>
    Real.log (lgdDZZ (qAreaMeasureOn γ (circExt w) openSquare) ((2 : ℝ)⁻¹ ^ n) u v).toNat /
      Real.log ((2 : ℝ)⁻¹ ^ n)⁻¹
  have e : {w | Tendsto (fun δ : ℝ => Real.log
      (lgdDZZ (qAreaMeasureOn γ (circExt w) openSquare) δ u v).toNat / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ)} = {w | Tendsto (fun n => φ n w) atTop (𝓝 χ)} :=
    Set.ext fun w => lgdEvent_iff_dyadic _ u v χ
  rw [e]
  have hφ : ∀ n, AEMeasurable (φ n) (circLaw P X) := fun n =>
    (DZZ.aemeasurable_log_lgdDZZ (fun c r => aemeasurable_qAreaMeasureOn_ball_circ hX hγ hγ2 c r)
      _ u v).div_const _
  have hS : MeasurableSet {w | Tendsto (fun n => (hφ n).mk (φ n) w) atTop (𝓝 χ)} :=
    measurableSet_tendsto (𝓝 χ) fun n => (hφ n).measurable_mk
  refine hS.nullMeasurableSet.congr ?_
  filter_upwards [ae_all_iff.2 fun n => (hφ n).ae_eq_mk] with w hw
  have : (fun n => (hφ n).mk (φ n) w) = fun n => φ n w := funext fun n => (hw n).symm
  change Tendsto (fun n => (hφ n).mk (φ n) w) atTop (𝓝 χ) = Tendsto (fun n => φ n w) atTop (𝓝 χ)
  rw [this]

/-- **law transfer of the LGD event**: it holds a.s. for a zero-boundary GFF on `𝕍` iff it holds
a.s. for the white-noise field -/
theorem ae_lgdEvent_iff_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (χ : ℝ) (u v : ℂ) :
    (∀ᵐ ω ∂P, Tendsto (fun δ : ℝ => Real.log
        (lgdDZZ (qAreaMeasureOn γ (X ω) openSquare) δ u v).toNat / Real.log δ⁻¹)
        (𝓝[>] 0) (𝓝 χ)) ↔
      ∀ᵐ ω ∂P', Tendsto (fun δ : ℝ => Real.log
        (lgdDZZ (qAreaMeasureOn γ (wnField W ω) openSquare) δ u v).toNat / Real.log δ⁻¹)
        (𝓝[>] 0) (𝓝 χ) :=
  ae_iff_wn hX hW γ (Q := fun μ => Tendsto (fun δ : ℝ => Real.log (lgdDZZ μ δ u v).toNat /
    Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)) (nullMeasurableSet_lgdEvent_circ hX hγ hγ2 χ u v)

/-- **`IsLGDExponent` through the white-noise field**: given one zero-boundary GFF on `𝕍`,
`χ` is the LGD exponent iff the LGD event holds a.s. for the white-noise field -/
theorem isLGDExponent_iff_wn {Ω₀ : Type} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {X₀ : Ω₀ → Measure ℂ → ℝ} (hX₀ : IsZeroBoundaryGFFOn openSquare X₀ P₀)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (χ : ℝ) :
    IsLGDExponent γ χ ↔ ∀ u ∈ openSquare, ∀ v ∈ openSquare, u ≠ v → ∀ᵐ ω ∂P',
      Tendsto (fun δ : ℝ => Real.log
        (lgdDZZ (qAreaMeasureOn γ (wnField W ω) openSquare) δ u v).toNat / Real.log δ⁻¹)
        (𝓝[>] 0) (𝓝 χ) := by
  constructor
  · intro h u hu v hv huv
    exact (ae_lgdEvent_iff_wn hX₀ hW hγ hγ2 χ u v).1 (h P₀ X₀ hX₀ u hu v hv huv)
  · intro h Ω _ P _ X hX u hu v hv huv
    exact (ae_lgdEvent_iff_wn hX hW hγ hγ2 χ u v).2 (h u hu v hv huv)

/-- **law transfer of functionals of `M_γ`**: for `F` a.e.-measurable along the circle law, the
law of `F(M_γ)` is the same for a zero-boundary GFF and for the white-noise field -/
theorem map_qArea_eq_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) (γ : ℝ) {β : Type*} [MeasurableSpace β] {F : Measure ℂ → β}
    (hF : AEMeasurable (fun w => F (qAreaMeasureOn γ (circExt w) openSquare)) (circLaw P X)) :
    P.map (fun ω => F (qAreaMeasureOn γ (X ω) openSquare)) =
      P'.map (fun ω => F (qAreaMeasureOn γ (wnField W ω) openSquare)) := by
  set G : (CircIdx → ℝ) → β := fun w => F (qAreaMeasureOn γ (circExt w) openSquare)
  have hm : Measurable fun ω => circVec (X ω) := measurable_circVec.comp (measurable_field hX)
  have hν := map_circVec_eq hX hW
  have e1 : (fun ω => F (qAreaMeasureOn γ (X ω) openSquare)) = G ∘ fun ω => circVec (X ω) :=
    funext fun ω => by simp only [G, Function.comp_apply, qAreaMeasureOn_circExt]
  have e2 : (fun ω => F (qAreaMeasureOn γ (wnField W ω) openSquare)) = G ∘ wnCircVec W := rfl
  have hF' : AEMeasurable G (P'.map (wnCircVec W)) := by rw [← hν]; exact hF
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable hF hm.aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable hF' (measurable_wnCircVec hW).aemeasurable, hν]

/-- the ball masses of `M_γ` have the same law for a zero-boundary GFF and the white-noise
field -/
theorem map_qArea_ball_eq_wn [IsProbabilityMeasure P] (hX : IsZeroBoundaryGFFOn openSquare X P)
    (hW : IsWhiteNoise P' W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (c : ℂ) (r : ℝ) :
    P.map (fun ω => qAreaMeasureOn γ (X ω) openSquare (Metric.ball c r)) =
      P'.map (fun ω => qAreaMeasureOn γ (wnField W ω) openSquare (Metric.ball c r)) :=
  map_qArea_eq_wn hX hW γ (F := fun μ => μ (Metric.ball c r))
    (aemeasurable_qAreaMeasureOn_ball_circ hX hγ hγ2 c r)

end GMCIdent4
end LQGMetric
