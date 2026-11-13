/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cO.Lemma49Canonical at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Phase
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalMoments

/-!
# [18] Lemma 4.9 in the canonical consumer form

The Proposition 4.8 consumes Lemma 4.9 as the record `GMS4.Canonical.Lemma49ConditionalMoments D hγ q ζ ρ`:
`(4.24)` for every `p ≥ 1` and `(4.25)` for every `p ∈ (1, 4/γ²)`, for the literal real masked observables of the
reference 0-cone (event `Canon.referenceLocalEvent`, including the IG phase `U`), conditionally on the *physical*
circle-average pair `GMS4.Canonical.circleObservation = (h₀,r(z), hIG₀,r(z) + U)` (a measurable version), with
integrability and constants uniform in the centre `z ∈ B_ρ(0)` and the mesh `ε ∈ (0, ε_*]`.

`L43O.lemma49ConditionalMoments_of_locality` constructs that record from the phase-aware 0-cone theorems of
`Lemma49Phase` (conditional on the finer triple `(h₀,r(z), (hIG₀,r(z), U))`), for `ρ ∈ (0,1)` and `0 < 4ζ < q`
(as in [18] (4.21)). Its only further inputs are the two named Lemma 4.3 locality statements
`ZeroConeRescaledLocality` (for the masked `DA` and the masked `u_*`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric LQGMetric.Blueprint MatedCRTHarmonic.MatedCRT
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.L43O

attribute [local instance] Classical.propDecidable

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The canonical local event (4.22) lies in the diameter event. -/
theorem canonical_localEvent_subset_diamEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) :
    GMS4.Canonical.localEvent D hγ ε q ζ z ⊆ diamEvent η₀ ε q z :=
  fun _ hω => hω.1

/-- The real `p`th power of the masked area ratio is dominated by the `ℝ≥0∞` diameter-masked area ratio. -/
theorem ofReal_areaMomentVariable_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ p : ℝ} (hp : 0 < p) (z : ℂ) (ω : Ω) :
    ENNReal.ofReal (GMS4.Canonical.areaMomentVariable D hγ ε q ζ p z ω) ≤
      (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.areaRatio ε (η₀ ω) z) ω ^ p := by
  by_cases hω : ω ∈ GMS4.Canonical.localEvent D hγ ε q ζ z
  · have hD : ω ∈ diamEvent η₀ ε q z := canonical_localEvent_subset_diamEvent D hγ ε q ζ z hω
    have hx : GMS4.Canonical.maskedAreaRatio D hγ ε q ζ z ω =
        (GMS4b.areaRatio ε (η₀ ω) z).toReal := by
      simp only [GMS4.Canonical.maskedAreaRatio, Set.indicator_of_mem hω]
      rfl
    have hx0 : 0 ≤ (GMS4b.areaRatio ε (η₀ ω) z).toReal := ENNReal.toReal_nonneg
    rw [GMS4.Canonical.areaMomentVariable, hx, max_eq_right hx0,
      ← ENNReal.ofReal_rpow_of_nonneg hx0 hp.le, Set.indicator_of_mem hD]
    exact ENNReal.rpow_le_rpow ENNReal.ofReal_toReal_le hp.le
  · have hx : GMS4.Canonical.maskedAreaRatio D hγ ε q ζ z ω = 0 := by
      simp only [GMS4.Canonical.maskedAreaRatio, Set.indicator_of_notMem hω]
    rw [GMS4.Canonical.areaMomentVariable, hx, max_self, Real.zero_rpow hp.ne', ENNReal.ofReal_zero]
    exact bot_le

/-- The real `p`th power of the masked density is dominated by the `ℝ≥0∞` diameter-masked density. -/
theorem ofReal_densityMomentVariable_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ p : ℝ} (hp : 0 < p) (z : ℂ) (ω : Ω) :
    ENNReal.ofReal (GMS4.Canonical.densityMomentVariable D hγ ε q ζ p z ω) ≤
      (diamEvent η₀ ε q z).indicator (fun ω => GMS4b.uStar ε (η₀ ω) z) ω ^ p := by
  by_cases hω : ω ∈ GMS4.Canonical.localEvent D hγ ε q ζ z
  · have hD : ω ∈ diamEvent η₀ ε q z := canonical_localEvent_subset_diamEvent D hγ ε q ζ z hω
    have hx : GMS4.Canonical.maskedUStar D hγ ε q ζ z ω = GMS4F.realUStar ε (η₀ ω) z := by
      simp only [GMS4.Canonical.maskedUStar, Set.indicator_of_mem hω]
      rfl
    have hx0 : 0 ≤ GMS4F.realUStar ε (η₀ ω) z := GMS4F.realUStar_nonneg ε (η₀ ω) z
    rw [GMS4.Canonical.densityMomentVariable, hx, max_eq_right hx0,
      ← ENNReal.ofReal_rpow_of_nonneg hx0 hp.le, Set.indicator_of_mem hD]
    exact ENNReal.rpow_le_rpow (GMS4F.ofReal_realUStar_le_geometric _ _ _) hp.le
  · have hx : GMS4.Canonical.maskedUStar D hγ ε q ζ z ω = 0 := by
      simp only [GMS4.Canonical.maskedUStar, Set.indicator_of_notMem hω]
    rw [GMS4.Canonical.densityMomentVariable, hx, max_self, Real.zero_rpow hp.ne',
      ENNReal.ofReal_zero]
    exact bot_le

/-- The physical observation's preimages are almost surely the triple's preimages of the summed set. -/
theorem circleObservation_preimage_ae_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε q ζ : ℝ) (z : ℂ) (A' : Set (ℝ × ℝ)) :
    (GMS4.Canonical.circleObservation D hγ ε q ζ z ⁻¹' A' : Set Ω) =ᵐ[P]
      (circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹'
        {x : ℝ × (ℝ × ℝ) | (x.1, x.2.1 + x.2.2) ∈ A'} : Set Ω) := by
  filter_upwards [GMS4.Canonical.ae_circleObservation_eq_actual D hγ ε q ζ z] with ω hω
  show (ω ∈ GMS4.Canonical.circleObservation D hγ ε q ζ z ⁻¹' A') =
    (ω ∈ circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹'
      {x : ℝ × (ℝ × ℝ) | (x.1, x.2.1 + x.2.2) ∈ A'})
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, hω]
  rfl

/-- **From the phase-aware set bound to the canonical conditional bound.** -/
theorem canonical_condExp_le_of_triple
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {ε q ζ : ℝ} {z : ℂ} {f : Ω → ℝ} {Ye : Ω → ℝ≥0∞}
    (hf0 : ∀ ω, 0 ≤ f ω) (hfm : AEMeasurable f P) (hfY : ∀ ω, ENNReal.ofReal (f ω) ≤ Ye ω)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ A : Set (ℝ × (ℝ × ℝ)), MeasurableSet A →
      ∫⁻ ω in circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A, Ye ω ∂P ≤
        C * P (circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z ⁻¹' A)) :
    Integrable f P ∧ ∀ᵐ ω ∂P,
      P[f | MeasurableSpace.comap (GMS4.Canonical.circleObservation D hγ ε q ζ z) inferInstance] ω ≤
        C.toReal := by
  have := D.isProbabilityMeasure
  set T := circleTriple γ X₀ hIG₀ B₀ B₀' U (averageRadius q ζ ε) z with hTdef
  have hsetle : ∀ A : Set (ℝ × (ℝ × ℝ)), MeasurableSet A →
      ∫⁻ ω in T ⁻¹' A, ENNReal.ofReal (f ω) ∂P ≤ C * P (T ⁻¹' A) := fun A hA =>
    (lintegral_mono fun ω => hfY ω).trans (hbound A hA)
  have hint : Integrable f P := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    have h1 := hsetle univ MeasurableSet.univ
    rw [preimage_univ, Measure.restrict_univ, measure_univ, mul_one] at h1
    refine lt_of_le_of_lt (le_of_eq ?_) (h1.trans_lt hC)
    refine lintegral_congr fun ω => ?_
    rw [Real.enorm_eq_ofReal (hf0 ω)]
  refine ⟨hint, ?_⟩
  refine condExp_le_of_setIntegral_le (GMS4.Canonical.measurable_circleObservation D hγ ε q ζ z)
    hint fun A' hA' => ?_
  set A : Set (ℝ × (ℝ × ℝ)) := {x | (x.1, x.2.1 + x.2.2) ∈ A'} with hAdef
  have hAm : MeasurableSet A :=
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).add
      (measurable_snd.comp measurable_snd))) hA'
  have hae := circleObservation_preimage_ae_eq D hγ ε q ζ z A' (U := U) (X₀ := X₀)
    (B₀ := B₀) (B₀' := B₀')
  rw [setIntegral_congr_set hae, measure_congr hae]
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hf0 ω)
    hfm.aestronglyMeasurable.restrict]
  have hfin : C * P (T ⁻¹' A) ≠ ⊤ := ENNReal.mul_ne_top hC.ne (measure_ne_top _ _)
  calc (∫⁻ ω in T ⁻¹' A, ENNReal.ofReal (f ω) ∂P).toReal
      ≤ (C * P (T ⁻¹' A)).toReal := ENNReal.toReal_mono hfin (hsetle A hAm)
    _ = C.toReal * (P (T ⁻¹' A)).toReal := ENNReal.toReal_mul

/-- **[18] Lemma 4.9 in the canonical form**, from the two named Lemma 4.3 locality inputs. -/
def lemma49ConditionalMoments_of_locality
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (hlocDA : ZeroConeRescaledLocality D (maskedLocDA (1 / 2)) fieldRegion excursionRegion)
    (hlocU : ZeroConeRescaledLocality D (maskedLocUStar (1 / 2)) fieldRegion excursionRegion)
    {q ζ ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hζ : 0 < ζ) (hζq : 4 * ζ < q) :
    GMS4.Canonical.Lemma49ConditionalMoments D hγ q ζ ρ where
  epsilonStar := epsStar ρ q ζ
  epsilonStar_pos := (epsStar_mem hρ).1
  epsilonStar_le_one := (epsStar_mem hρ).2.le
  area := by
    intro p hp
    obtain ⟨C, hCtop, hC⟩ := (lemma49_zeroCone_DA_phase D hγ hlocDA hρ hζ hζq).2 p hp
    refine ⟨C.toReal, ENNReal.toReal_nonneg, fun ε hε z hz => ?_⟩
    have hp0 : 0 < p := by linarith
    have hfm : AEMeasurable (GMS4.Canonical.areaMomentVariable D hγ ε q ζ p z) P :=
      (aemeasurable_const.max (GMS4.Canonical.aemeasurable_maskedAreaRatio D hγ hε.1.le q ζ z)).pow_const p
    exact canonical_condExp_le_of_triple D hγ
      (fun ω => Real.rpow_nonneg (le_max_left _ _) p) hfm
      (ofReal_areaMomentVariable_le D hγ hp0 z) hCtop (hC z hz ε hε)
  density := by
    intro p hp hpK
    obtain ⟨C, hCtop, hC⟩ := (lemma49_zeroCone_uStar_phase D hγ hlocU hρ hζ hζq).2 p hp.le hpK
    refine ⟨C.toReal, ENNReal.toReal_nonneg, fun ε hε z hz => ?_⟩
    have hp0 : 0 < p := by linarith
    have hfm : AEMeasurable (GMS4.Canonical.densityMomentVariable D hγ ε q ζ p z) P :=
      (aemeasurable_const.max (GMS4.Canonical.aemeasurable_maskedUStar D hγ hε.1.le q ζ z)).pow_const p
    exact canonical_condExp_le_of_triple D hγ
      (fun ω => Real.rpow_nonneg (le_max_left _ _) p) hfm
      (ofReal_densityMomentVariable_le D hγ hp0 z) hCtop (hC z hz ε hε)

end Bundle

end MatedCRTHarmonic.L43O
