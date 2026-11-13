/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TPhase at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.Transfer

/-!
# Local comparison with the common imaginary-geometry phase

The observable required for Lemma 4.3 is the field pair together with the
uniform additive phase. An independent phase of the same law does not change
The density or its moment.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- Restricted LQG field, restricted normalized IG field, and IG phase. -/
abbrev L46TLocalFieldPhase (V : TopologicalSpace.Opens ℂ) : Type :=
  GMS4c.LocalFieldPair V × ℝ

def l46tLocalFieldPhase {Ω : Type*} (V : TopologicalSpace.Opens ℂ)
    (h hIG : Ω → DistC) (u : Ω → ℝ) (ω : Ω) : L46TLocalFieldPhase V :=
  (GMS4c.localFieldPair V h hIG ω, u ω)

/-- Formula (4.16) for the actual three-coordinate local observation. -/
structure L46TPhaseLawComparison {Ωγ Ω₀ : Type*}
    [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    (V : TopologicalSpace.Opens ℂ)
    (Pγ : Measure Ωγ) (P₀ : Measure Ω₀)
    (hγ hIGγ : Ωγ → DistC) (uγ : Ωγ → ℝ)
    (h₀ hIG₀ : Ω₀ → DistC) (u₀ : Ω₀ → ℝ)
    (p q : ℝ) where
  gamma_measurable : AEMeasurable (l46tLocalFieldPhase V hγ hIGγ uγ) Pγ
  target_measurable : AEMeasurable (l46tLocalFieldPhase V h₀ hIG₀ u₀) P₀
  density : L46TLocalFieldPhase V → ℝ≥0∞
  density_measurable : Measurable density
  law_eq : P₀.map (l46tLocalFieldPhase V h₀ hIG₀ u₀) =
    (Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ)).withDensity density
  moment_finite :
    ∫⁻ x, density x ^ p ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ)) < ⊤
  conjugate : p.HolderConjugate q

/-- Append an independent, identically distributed phase to an existing
field-pair density without changing its finite moment. -/
def l46t_phaseComparison_of_independent
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    [IsProbabilityMeasure Pγ] [IsProbabilityMeasure P₀]
    {hγ hIGγ : Ωγ → DistC} {h₀ hIG₀ : Ω₀ → DistC}
    {p q : ℝ} (hcmp : GMS4c.LocalFieldLawComparison V Pγ P₀ hγ hIGγ h₀ hIG₀ p q)
    {uγ : Ωγ → ℝ} {u₀ : Ω₀ → ℝ}
    (humγ : AEMeasurable uγ Pγ) (hum₀ : AEMeasurable u₀ P₀)
    (hphase : Pγ.map uγ = P₀.map u₀)
    (hindγ : IndepFun (GMS4c.localFieldPair V hγ hIGγ) uγ Pγ)
    (hind₀ : IndepFun (GMS4c.localFieldPair V h₀ hIG₀) u₀ P₀) :
    L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q := by
  let Aγ := GMS4c.localFieldPair V hγ hIGγ
  let A₀ := GMS4c.localFieldPair V h₀ hIG₀
  have hbase : Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ) =
      (Pγ.map Aγ).prod (Pγ.map uγ) :=
    (indepFun_iff_map_prod_eq_prod_map_map hcmp.gamma_measurable.aemeasurable
      humγ).1 hindγ
  have htarget : P₀.map (l46tLocalFieldPhase V h₀ hIG₀ u₀) =
      (P₀.map A₀).prod (P₀.map u₀) :=
    (indepFun_iff_map_prod_eq_prod_map_map hcmp.target_measurable.aemeasurable
      hum₀).1 hind₀
  have hprob : IsProbabilityMeasure (Pγ.map uγ) :=
    (Measure.isProbabilityMeasure_map_iff humγ).2 inferInstance
  let _ : IsProbabilityMeasure (Pγ.map uγ) := hprob
  refine ⟨hcmp.gamma_measurable.aemeasurable.prodMk humγ,
    hcmp.target_measurable.aemeasurable.prodMk hum₀,
    (fun x => hcmp.density x.1), hcmp.density_measurable.comp measurable_fst,
    ?_, ?_, hcmp.conjugate⟩
  · calc
      P₀.map (l46tLocalFieldPhase V h₀ hIG₀ u₀) =
          (P₀.map A₀).prod (P₀.map u₀) := htarget
      _ = ((Pγ.map Aγ).withDensity hcmp.density).prod (Pγ.map uγ) := by
        rw [hcmp.law_eq, hphase]
      _ = ((Pγ.map Aγ).prod (Pγ.map uγ)).withDensity (fun x => hcmp.density x.1) :=
        prod_withDensity_left hcmp.density_measurable
      _ = (Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ)).withDensity
          (fun x => hcmp.density x.1) := by rw [hbase]
  · rw [hbase]
    calc
      (∫⁻ x : L46TLocalFieldPhase V, hcmp.density x.1 ^ p
          ∂((Pγ.map Aγ).prod (Pγ.map uγ))) =
          ∫⁻ x, (∫⁻ _y : ℝ, hcmp.density x ^ p ∂(Pγ.map uγ)) ∂(Pγ.map Aγ) := by
            rw [lintegral_prod]
            exact (hcmp.density_measurable.comp measurable_fst).pow_const p |>.aemeasurable
      _ = ∫⁻ x, hcmp.density x ^ p ∂(Pγ.map Aγ) := by simp
      _ < ⊤ := hcmp.moment_finite

/-- Hölder's inequality for an event read from the three-coordinate local
observation. -/
theorem l46t_phase_badEvent_le_holder
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → DistC} {u₀ : Ω₀ → ℝ}
    {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q)
    {A : Set (L46TLocalFieldPhase V)} (hA : MeasurableSet A) :
    P₀ ((l46tLocalFieldPhase V h₀ hIG₀ u₀) ⁻¹' A) ≤
      (∫⁻ x, hcmp.density x ^ p
        ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) *
        (Pγ ((l46tLocalFieldPhase V hγ hIGγ uγ) ⁻¹' A)) ^ (1 / q) := by
  rw [← Measure.map_apply_of_aemeasurable hcmp.target_measurable hA,
    ← Measure.map_apply_of_aemeasurable hcmp.gamma_measurable hA, hcmp.law_eq]
  exact GMS4.withDensity_event_le_holder
    (Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ)) hcmp.density
    hcmp.density_measurable.aemeasurable hA hcmp.conjugate

/-- Its finite Hölder constant, at the comparison's actual conjugate. -/
theorem l46t_phase_holder_constant_finite
    {Ωγ Ω₀ : Type*} [MeasurableSpace Ωγ] [MeasurableSpace Ω₀]
    {V : TopologicalSpace.Opens ℂ}
    {Pγ : Measure Ωγ} {P₀ : Measure Ω₀}
    {hγ hIGγ : Ωγ → DistC} {uγ : Ωγ → ℝ}
    {h₀ hIG₀ : Ω₀ → DistC} {u₀ : Ω₀ → ℝ}
    {p q : ℝ}
    (hcmp : L46TPhaseLawComparison V Pγ P₀ hγ hIGγ uγ h₀ hIG₀ u₀ p q) :
    (∫⁻ x, hcmp.density x ^ p
      ∂(Pγ.map (l46tLocalFieldPhase V hγ hIGγ uγ))) ^ (1 / p) < ⊤ := by
  exact ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr hcmp.conjugate.pos.le) hcmp.moment_finite.ne

end MatedCRTHarmonic.GMS4b
