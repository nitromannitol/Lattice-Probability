/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RGauss at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RInputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4GoodMax
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RSum

 








set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 
theorem laneA4R_conditional_phi_truncated_upper_of_indep
    {Ω : Type*} {m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (hm₂ : m₂ ≤ mΩ) (K : ℕ) (b : ℤ × ℤ) (ξ β : ℝ)
    (hInd : Indep (MeasurableSpace.comap (phiMN W P 0 K (T20.dyCenter K b))
      (inferInstance : MeasurableSpace ℝ)) m₂ P) :
    let X : Ω → ℝ := fun ω => phiMN W P 0 K (T20.dyCenter K b) ω
    let E : Set Ω := {ω | X ω ≤ β * ((K : ℝ) * Real.log 2)}
    ∀ᵐ ω ∂P,
      (∫⁻ x, ENNReal.ofReal (E.indicator (fun y => Real.exp (ξ * X y)) x)
        ∂(condExpKernel P m₂ ω)) ≤
      ENNReal.ofReal (Real.exp ((ξ * min ξ β - (min ξ β) ^ 2 / 2) * ((K : ℝ) * Real.log 2))) := by
  intro X E
  let f : Ω → ℝ := E.indicator (fun y => Real.exp (ξ * X y))
  have hXm : Measurable X := (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  have hE : @MeasurableSet Ω mΩ E := measurableSet_le hXm measurable_const
  obtain ⟨v, hv, hLaw⟩ := hasLaw_phiMN hW K (T20.dyCenter K b)
  have hIntExp : Integrable (fun ω => Real.exp (ξ * X ω)) P :=
    hLaw.integrable_comp (f := fun x => Real.exp (ξ * x)) (integrable_exp_mul_gaussianReal ξ)
  have hInt : Integrable f P := hIntExp.integrableOn.integrable_indicator hE
  let mφ : MeasurableSpace Ω := MeasurableSpace.comap X (inferInstance : MeasurableSpace ℝ)
  have hXφ : @Measurable Ω ℝ mφ _ X := comap_measurable X
  have hEφ : @MeasurableSet Ω mφ E := measurableSet_le hXφ measurable_const
  have hf : StronglyMeasurable[mφ] f :=
    ((hXφ.const_mul ξ).exp.stronglyMeasurable).indicator hEφ
  letI : MeasurableSpace Ω := mΩ
  have hcond := laneC_conditional_lintegral_eq_of_indep P hXm.comap_le hm₂ hf hInd hInt (by
    intro ω
    by_cases hω : ω ∈ E <;> simp [f, hω, Real.exp_nonneg])
  have hgauss := laneA4_coarse_phi_truncated_upper hW K (T20.dyCenter K b) ξ β
  filter_upwards [hcond] with ω hc
  change (∫⁻ x, ENNReal.ofReal (f x) ∂(condExpKernel P m₂ ω)) ≤ _
  rw [hc]
  have hrewrite : (∫⁻ x, ENNReal.ofReal (f x) ∂P) =
      ∫⁻ x in E, ENNReal.ofReal (Real.exp (ξ * X x)) ∂P := by
    rw [← lintegral_indicator hE]
    congr 1
    funext x
    by_cases hx : x ∈ E <;> simp [f, hx]
  rw [hrewrite]
  simpa only [X, E, hv] using hgauss

 
theorem laneA4R_good_conditional_gaussian_le_of_indep
    {Ω : Type*} {m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (hm₂ : m₂ ≤ mΩ) (K : ℕ) (b : ℤ × ℤ) (ξ β : ℝ)
    (hInd : Indep (MeasurableSpace.comap (phiMN W P 0 K (T20.dyCenter K b))
      (inferInstance : MeasurableSpace ℝ)) m₂ P)
    (F E : Set Ω) (Y : Ω → ℝ≥0∞) (c : ℝ≥0∞)
    (hhit : F ∩ E ⊆ {ω | phiMN W P 0 K (T20.dyCenter K b) ω ≤ β * ((K : ℝ) * Real.log 2)})
    (hregular : ∀ ω ∈ E, Y ω ≤ c * ENNReal.ofReal
      (Real.exp (ξ * phiMN W P 0 K (T20.dyCenter K b) ω))) :
    ∀ᵐ ω ∂P,
      (∫⁻ x, (F ∩ E).indicator Y x ∂(condExpKernel P m₂ ω)) ≤
      c * ENNReal.ofReal (Real.exp ((ξ * min ξ β - (min ξ β) ^ 2 / 2) *
          ((K : ℝ) * Real.log 2))) := by
  let Φ : Ω → ℝ := fun ω => phiMN W P 0 K (T20.dyCenter K b) ω
  let H : Set Ω := {ω | Φ ω ≤ β * ((K : ℝ) * Real.log 2)}
  let X : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (ξ * Φ ω))
  have hΦm : Measurable Φ := (isPhiVersion_phiMN hW (Nat.zero_le K)).meas _
  have hHm : MeasurableSet H := measurableSet_le hΦm measurable_const
  have hXm : Measurable X :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hΦm))
  have hmain (ω : Ω) : (∫⁻ x, (F ∩ E).indicator Y x ∂(condExpKernel P m₂ ω)) ≤
      c * (∫⁻ x, H.indicator X x ∂(condExpKernel P m₂ ω)) :=
    laneA4_good_conditional_integral_le _ F E H X Y c hHm hXm hhit hregular
  have hgauss := laneA4R_conditional_phi_truncated_upper_of_indep P W hW hm₂ K b ξ β hInd
  filter_upwards [hgauss] with ω hg
  have hsame : (fun x => H.indicator X x) =
      (fun x => ENNReal.ofReal (H.indicator (fun y => Real.exp (ξ * Φ y)) x)) := by
    funext x
    by_cases hx : x ∈ H <;> simp [H, X, hx]
  have hgauss' : (∫⁻ x, H.indicator X x ∂(condExpKernel P m₂ ω)) ≤
      ENNReal.ofReal (Real.exp ((ξ * min ξ β - (min ξ β) ^ 2 / 2) * ((K : ℝ) * Real.log 2))) := by
    rw [hsame]
    simpa only [H, Φ] using hg
  exact (hmain ω).trans (mul_le_mul_of_nonneg_left hgauss' bot_le)

 
theorem laneA4R_indep_point_fineStar.{u}
    (hInd : LaneFineStarIndepCoarse.{u}) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams) {K n : ℕ} (hKn : K ≤ n)
    (b : ℤ × ℤ) :
    Indep (MeasurableSpace.comap (phiMN W P 0 K (T20.dyCenter K b))
      (inferInstance : MeasurableSpace ℝ)) (laneFineStar Q W P K n) P := by
  apply indep_of_indep_of_le_left (hInd P W hW Q K n hKn)
  refine le_trans ?_ le_sup_left
  exact ((measurable_pi_apply (T20.dyCenter K b)).comp
    (comap_measurable (fun ω x => phiMN W P 0 K x ω))).comap_le

end SupercriticalLQGUniqueness.B2.DG20Conc
