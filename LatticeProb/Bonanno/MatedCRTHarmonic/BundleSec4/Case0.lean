/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.Case0 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Prop210Source
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210IntegralBridge
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Statement

/-!
# Case 0 of [18] §4.6 in the lower-integral carrier

The canonical Proposition 4.8 statement shows that the source estimate
(`GMS4.Canonical.prop48_canonical_of_lemma49_gmcReconstruction`) bounds the failure of a **Bochner** integral of the
**real** `u_*` (`toReal` of the geometric value). Where `f·u_*` is not integrable (Bochner integral `0`) or `u_* = ⊤`, a
sample is never "bad" — weaker than [18] on such samples. The consumers of Case 0 (towards `Prop410At`)
work with the extended `u_*` and lower integrals (`BundleSec4.Prop410Bad`). This file provides the conversion:

* `lintegral_bad_le_of_integral_bad` — generic: a Bochner failure bound for a real density `u ≥ 0` gives the
  lower-integral failure bound for an extended density `ū`, up to the probability of the exceptional set where
  `f·u` is not integrable on `D` or `ofReal ∘ u ≠ ū` on a non-null subset of `D`;
* `Prop48ZeroConeLintegral P η₀` — [18] Proposition 4.8 for the 0-cone in the lower-integral carrier (failure event
  `BundleSec4.Prop410Bad η₀ ε domain f A (ε^α ‖f‖)`, source tolerance `ε^α ‖f‖_∞` of (4.1));
* `prop48ZeroConeLintegral_of_bochner` — the Case 0 adapter: the Bochner-form conclusion (for any real density
  `u ε ω z ≥ 0`) plus a polynomial bound on the exceptional set (integrability on `D` and a.e. identification
  `ofReal (u ε ω z) = GMS4b.uStar ε (η₀ ω) z`; e.g. via the good event of Prop 4.5 and `GMS4F.ofReal_realUStar_eq_geometric`)
  give `Prop48ZeroConeLintegral P η₀`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- The pointwise step: on a sample where `f·u` is integrable on `D` and `ofReal ∘ u = ū` a.e. on `D`, the Bochner
good event implies the lower-integral good event. -/
theorem bundle_lintegral_good_of_integral_good {D : Set ℂ} (hD : MeasurableSet D) {f : ℂ → ℝ}
    (hf : ∀ z ∈ D, 0 ≤ f z) (hIntf : IntegrableOn f D) {u : ℂ → ℝ} (hu : ∀ z ∈ D, 0 ≤ u z)
    {ū : ℂ → ℝ≥0∞} {A tol : ℝ} (hA : 0 ≤ A) (htol : 0 ≤ tol)
    (hInt : IntegrableOn (fun z => f z * u z) D)
    (hEq : ∀ᵐ z ∂volume.restrict D, ENNReal.ofReal (u z) = ū z)
    (hgood : (∫ z in D, f z * u z) ≤ A * (∫ z in D, f z) + tol) :
    (∫⁻ z in D, ENNReal.ofReal (f z) * ū z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol := by
  have hreal := GMS4F.lintegral_bound_of_real_integral_bound D hD f u hf hu hInt hIntf hA htol le_rfl hgood
  have heq : (∫⁻ z in D, ENNReal.ofReal (f z) * ū z) =
      ∫⁻ z in D, ENNReal.ofReal (f z) * ENNReal.ofReal (u z) := by
    apply lintegral_congr_ae
    filter_upwards [hEq] with z hz
    rw [hz]
  rw [heq]
  exact hreal

/-- **Bochner failure ⇒ lower-integral failure, up to the exceptional set.** -/
theorem lintegral_bad_le_of_integral_bad {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {D : Set ℂ} (hD : MeasurableSet D) {f : ℂ → ℝ} (hf : ∀ z ∈ D, 0 ≤ f z)
    (hIntf : IntegrableOn f D)
    {u : Ω → ℂ → ℝ} (hu : ∀ ω, ∀ z ∈ D, 0 ≤ u ω z) (ū : Ω → ℂ → ℝ≥0∞)
    {A tol : ℝ} (hA : 0 ≤ A) (htol : 0 ≤ tol) {δ δ' : ℝ≥0∞}
    (h : P {ω | A * (∫ z in D, f z) + tol < ∫ z in D, f z * u ω z} ≤ δ)
    (hexc : P {ω | ¬ (IntegrableOn (fun z => f z * u ω z) D ∧
      ∀ᵐ z ∂volume.restrict D, ENNReal.ofReal (u ω z) = ū ω z)} ≤ δ') :
    P {ω | ¬ ((∫⁻ z in D, ENNReal.ofReal (f z) * ū ω z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol)} ≤ δ + δ' := by
  let Bb : Set Ω := {ω | A * (∫ z in D, f z) + tol < ∫ z in D, f z * u ω z}
  let E : Set Ω := {ω | ¬ (IntegrableOn (fun z => f z * u ω z) D ∧
      ∀ᵐ z ∂volume.restrict D, ENNReal.ofReal (u ω z) = ū ω z)}
  let Bl : Set Ω := {ω | ¬ ((∫⁻ z in D, ENNReal.ofReal (f z) * ū ω z) ≤
      ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal tol)}
  have hsub : Bl ⊆ Bb ∪ E := by
    intro ω hbad
    by_cases hω : IntegrableOn (fun z => f z * u ω z) D ∧
        ∀ᵐ z ∂volume.restrict D, ENNReal.ofReal (u ω z) = ū ω z
    · left
      show A * (∫ z in D, f z) + tol < ∫ z in D, f z * u ω z
      by_contra hgood
      exact hbad (bundle_lintegral_good_of_integral_good hD hf hIntf (hu ω) hA htol hω.1 hω.2
        (not_lt.mp hgood))
    · exact Or.inr hω
  have h1 : P Bl ≤ P Bb + P E := (measure_mono hsub).trans (measure_union_le _ _)
  exact h1.trans (add_le_add h hexc)

/-- The test-function norm of [18] (4.1) is nonnegative for bounded tests. -/
theorem bundle_prop48TestSupNorm_nonneg {ρ : ℝ} {f : ℂ → ℝ}
    (hb : ∃ B : ℝ, ∀ z ∈ Metric.ball 0 ρ, |f z| ≤ B) : 0 ≤ GMS4.prop48TestSupNorm ρ f :=
  le_csSup (GMS4.prop48TestSupNorm_bddAbove hb) (Set.mem_insert 0 _)

/-- An admissible [18] (4.1) test is integrable on its domain (bounded, measurable on `B_ρ(0)`, finite area). -/
theorem bundle_integrableOn_prop48Test {ρ : ℝ} {domain : Set ℂ} {f : ℂ → ℝ}
    (hadm : GMS4.Prop48TestPairAdmissible ρ domain f) : IntegrableOn f domain := by
  obtain ⟨B, hB⟩ := hadm.test_bounded
  have hball : MeasurableSet (Metric.ball (0 : ℂ) ρ) := measurableSet_ball
  have hmeas : AEMeasurable f (volume.restrict (Metric.ball (0 : ℂ) ρ)) :=
    (aemeasurable_restrict_iff_comap_subtype hball).2 hadm.test_measurable.aemeasurable
  have hmeasD : AEStronglyMeasurable f (volume.restrict domain) :=
    (hmeas.mono_set hadm.domain_subset_ball).aestronglyMeasurable
  have hfin : volume domain < ⊤ :=
    (measure_mono hadm.domain_subset_ball).trans_lt measure_ball_lt_top
  refine ⟨hmeasD, HasFiniteIntegral.restrict_of_bounded (C := B) hfin ?_⟩
  filter_upwards [ae_restrict_mem hadm.domain_borel] with z hz
  simpa [Real.norm_eq_abs] using hB z (hadm.domain_subset_ball hz)

/-- **[18] Proposition 4.8 for the 0-cone curve `η₀`, lower-integral carrier**: exponent before `ρ`; for each
`ρ ∈ (0,1)` a mean bound `A > 0` and rate `C`; for every mesh `ε ∈ (0,1)` and admissible test pair, the failure of
`∫⁻_D f u_*^ε ≤ A ∫⁻_D f + ε^α ‖f‖_∞` (extended `u_*^ε = GMS4b.uStar ε (η₀ ω)`) has probability `≤ C ε^α`. -/
def Prop48ZeroConeLintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (η₀ : Ω → C(ℝ, ℂ)) : Prop :=
  ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (domain : Set ℂ) (f : ℂ → ℝ),
      GMS4.Prop48TestPairAdmissible ρ domain f →
        P (Prop410Bad η₀ ε domain f A (ε ^ α * GMS4.prop48TestSupNorm ρ f)) ≤
          ENNReal.ofReal (C * ε ^ α)

/-- **The Case 0 adapter.** the Bochner-form Proposition 4.8 (for a real density `u ε ω z ≥ 0`,
e.g. `GMS4.Canonical.uStar ε η₀`) and a polynomial bound on the exceptional set (non-integrability of `f·u` on the
domain, or failure of `ofReal (u ε ω z) = GMS4b.uStar ε (η₀ ω) z` for a.e. `z` in the domain) give the lower-integral
form `Prop48ZeroConeLintegral P η₀`, with exponent `min α α'` and constant `C + C'`. -/
theorem prop48ZeroConeLintegral_of_bochner {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {η₀ : Ω → C(ℝ, ℂ)} (u : ℝ → Ω → ℂ → ℝ) (hu : ∀ ε ω z, 0 ≤ u ε ω z)
    (h48 : ∃ α : ℝ, 0 < α ∧ ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (domain : Set ℂ) (f : ℂ → ℝ),
        GMS4.Prop48TestPairAdmissible ρ domain f →
          P {ω | A * (∫ z in domain, f z) + ε ^ α * GMS4.prop48TestSupNorm ρ f <
            ∫ z in domain, f z * u ε ω z} ≤ ENNReal.ofReal (C * ε ^ α))
    (hexc : ∃ α' : ℝ, 0 < α' ∧ ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ ε : ℝ, ε ∈ Ioo (0 : ℝ) 1 → ∀ (domain : Set ℂ) (f : ℂ → ℝ),
        GMS4.Prop48TestPairAdmissible ρ domain f →
          P {ω | ¬ (IntegrableOn (fun z => f z * u ε ω z) domain ∧
            ∀ᵐ z ∂volume.restrict domain,
              ENNReal.ofReal (u ε ω z) = GMS4b.uStar ε (η₀ ω) z)} ≤ ENNReal.ofReal (C' * ε ^ α')) :
    Prop48ZeroConeLintegral P η₀ := by
  obtain ⟨α, hα, h48⟩ := h48
  obtain ⟨α', hα', hexc⟩ := hexc
  refine ⟨min α α', lt_min hα hα', fun ρ hρ => ?_⟩
  obtain ⟨A, hA, C, hC, hbound⟩ := h48 ρ hρ
  obtain ⟨C', hC', hexcρ⟩ := hexc ρ hρ
  refine ⟨A, hA, C + C', by positivity, fun ε hε domain f hadm => ?_⟩
  have hε0 := hε.1
  have hε1 := hε.2
  have hpowα : ε ^ α ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_left _ _)
  have hpowα' : ε ^ α' ≤ ε ^ min α α' :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (min_le_right _ _)
  have hN : 0 ≤ GMS4.prop48TestSupNorm ρ f := bundle_prop48TestSupNorm_nonneg hadm.test_bounded
  have htol : 0 ≤ ε ^ α * GMS4.prop48TestSupNorm ρ f :=
    mul_nonneg (Real.rpow_nonneg hε0.le _) hN
  -- the lower-integral failure at tolerance `ε^α ‖f‖` (Bochner bound at exponent `α`)
  have hbad := lintegral_bad_le_of_integral_bad (P := P) hadm.domain_borel
    (fun z hz => hadm.test_nonnegative z (hadm.domain_subset_ball hz)) (bundle_integrableOn_prop48Test hadm)
    (fun ω z _ => hu ε ω z) (fun ω z => GMS4b.uStar ε (η₀ ω) z) hA.le htol
    (hbound ε hε domain f hadm) (hexcρ ε hε domain f hadm)
  -- enlarge the tolerance from `ε^α ‖f‖` to `ε^{min α α'} ‖f‖`
  have hsub : Prop410Bad η₀ ε domain f A (ε ^ min α α' * GMS4.prop48TestSupNorm ρ f) ⊆
      {ω | ¬ ((∫⁻ z in domain, ENNReal.ofReal (f z) * GMS4b.uStar ε (η₀ ω) z) ≤
        ENNReal.ofReal A * (∫⁻ z in domain, ENNReal.ofReal (f z)) +
          ENNReal.ofReal (ε ^ α * GMS4.prop48TestSupNorm ρ f))} := by
    intro ω hω hgood
    apply hω
    exact hgood.trans (add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpowα hN)))
  calc
    P (Prop410Bad η₀ ε domain f A (ε ^ min α α' * GMS4.prop48TestSupNorm ρ f)) ≤
        ENNReal.ofReal (C * ε ^ α) + ENNReal.ofReal (C' * ε ^ α') :=
      (measure_mono hsub).trans hbad
    _ ≤ ENNReal.ofReal (C * ε ^ min α α') + ENNReal.ofReal (C' * ε ^ min α α') :=
      add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpowα hC))
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpowα' hC'))
    _ = ENNReal.ofReal ((C + C') * ε ^ min α α') := by
      rw [← ENNReal.ofReal_add (mul_nonneg hC (Real.rpow_nonneg hε0.le _))
        (mul_nonneg hC' (Real.rpow_nonneg hε0.le _)), add_mul]

end MatedCRTHarmonic.BundleSec4
