/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCM.BundleComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCM.BundleIG

/-!
# Cone-coordinate (4.16) for the frozen bundle's cone and IG field

This is the exact `GMS4c.LocalFieldLawComparison` orientation needed for the
Hölder transfer, on a compact observation region of the punctured unit disk.
The target is a unit-circle-normalized whole-plane GFF on the same sample
space and the same independent IG field.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Set TopologicalSpace LQGMetric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMSCM

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The cone-coordinate [18] (4.16) comparison for the bundle's γ-cone on a
local region away from its root:
the normalized whole-plane GFF and the same IG field have an `L²` density
relative to the cone and IG law. -/
theorem IsMatingOfTreesCoupling.exists_localFieldLawComparison
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : Opens ℂ) (hK : IsCompact (closure (V : Set ℂ)))
    (hV : closure (V : Set ℂ) ⊆ Metric.ball (0 : ℂ) 1 \ {0}) :
    ∃ (hγm Xt : Ω → DistC),
      Measurable hγm ∧
      (fun ω => coneField (X ω)
        (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))) =ᵐ[P] hγm ∧
      IsNormalizedWPGFF Xt P ∧
      Nonempty (GMS4c.LocalFieldLawComparison V P P
        hγm hIG₀ Xt hIG₀ 2 2) := by
  let : IsProbabilityMeasure P := hC.isProbabilityMeasure
  let raw : Ω → DistC := fun ω => coneField (X ω)
    (coneRadial γ γ (fun t => B t ω) (fun t => B' t ω))
  have hraw : AEMeasurable raw P :=
    aemeasurable_coneFieldOf hC.gff hC.bm_B hC.bm_B' hC.indep_cone.2
  let hγm : Ω → DistC := hraw.mk raw
  have hγmeas : Measurable hγm := hraw.measurable_mk
  have hγae : raw =ᵐ[P] hγm := hraw.ae_eq_mk
  obtain ⟨Xt, φ, hXt, hφavg, hlocal⟩ :=
    exists_cone_local_shift hγ hC.gff hC.bm_B hC.bm_B' hC.indep_cone V hK hV
  have hIGm : Measurable hIG₀ := hC.igField.1.1.measurable
  have hindRaw : IndepFun raw hIG₀ P :=
    IsMatingOfTreesCoupling.indepFun_coneField_hIG hC hγ
  have hindγ : IndepFun hγm hIG₀ P :=
    hindRaw.congr hγae (ae_eq_refl _)
  let Hγ : Ω → DistOn V := fun ω => restrictTo V (hγm ω)
  let H₀ : Ω → DistOn V := fun ω => restrictTo V (Xt ω)
  let Hφ : Ω → DistOn V := fun ω => restrictTo V (addFun (Xt ω) (testCont φ))
  let K : Ω → DistOn V := fun ω => restrictTo V (hIG₀ ω)
  have hHγ : Measurable Hγ := (measurable_restrictTo V).comp hγmeas
  have hH₀ : Measurable H₀ := (measurable_restrictTo V).comp hXt.1.measurable
  have hHφ : Measurable Hφ :=
    (measurable_restrictTo V).comp
      ((measurable_addFun_left (testCont φ)).comp hXt.1.measurable)
  have hKm : Measurable K := (measurable_restrictTo V).comp hIGm
  have hlocalm : Hγ =ᵐ[P] Hφ := by
    filter_upwards [hγae, hlocal] with ω h1 h2
    exact (congrArg (restrictTo V) h1).symm.trans h2
  have hLawH : P.map Hγ = P.map Hφ := Measure.map_congr hlocalm
  have hindHγ : IndepFun Hγ K P :=
    hindγ.comp (measurable_restrictTo V) (measurable_restrictTo V)
  have hindHφ : IndepFun Hφ K P :=
    hindHγ.congr hlocalm (ae_eq_refl _)
  let T : DistOn V := restrictTo V (ofCont (testCont φ))
  have hrel : ∀ ω, Hφ ω = H₀ ω + T := by
    intro ω
    rfl
  have hsub : Measurable (fun z : DistOn V => z - T) :=
    measurable_distOn_iff.2 fun ψ => (measurable_distOn_apply ψ).sub_const (T ψ)
  have hindH₀ : IndepFun H₀ K P := by
    have hi := hindHφ.comp hsub measurable_id
    refine hi.congr (ae_of_all _ fun ω => ?_) (ae_eq_refl _)
    simp [hrel ω]
  obtain ⟨M, hMm, hLaw, hM2⟩ :=
    normalized_shift_restriction_comparison_reverse hXt φ hφavg V
  have hKprob : IsProbabilityMeasure (P.map K) :=
    (Measure.isProbabilityMeasure_map_iff hKm.aemeasurable).2 inferInstance
  let : IsProbabilityMeasure (P.map K) := hKprob
  have hgamma : P.map (GMS4c.localFieldPair V hγm hIG₀) =
      (P.map Hγ).prod (P.map K) :=
    (indepFun_iff_map_prod_eq_prod_map_map hHγ.aemeasurable hKm.aemeasurable).1 hindHγ
  have htarget : P.map (GMS4c.localFieldPair V Xt hIG₀) =
      (P.map H₀).prod (P.map K) :=
    (indepFun_iff_map_prod_eq_prod_map_map hH₀.aemeasurable hKm.aemeasurable).1 hindH₀
  refine ⟨hγm, Xt, hγmeas, hγae, hXt,
    ⟨⟨GMS4c.measurable_localFieldPair V hγmeas hIGm,
      GMS4c.measurable_localFieldPair V hXt.1.measurable hIGm,
      (fun x => M x.1), hMm.comp measurable_fst, ?_, ?_,
      Real.HolderConjugate.two_two⟩⟩⟩
  · calc
      P.map (GMS4c.localFieldPair V Xt hIG₀) =
          (P.map H₀).prod (P.map K) := htarget
      _ = ((P.map Hφ).withDensity M).prod (P.map K) := by rw [hLaw]
      _ = ((P.map Hγ).withDensity M).prod (P.map K) := by rw [hLawH]
      _ = ((P.map Hγ).prod (P.map K)).withDensity (fun x => M x.1) :=
        prod_withDensity_left hMm
      _ = (P.map (GMS4c.localFieldPair V hγm hIG₀)).withDensity
          (fun x => M x.1) := by rw [hgamma]
  · rw [hgamma]
    calc
      (∫⁻ x : DistOn V × DistOn V, M x.1 ^ (2 : ℝ)
          ∂((P.map Hγ).prod (P.map K))) =
          ∫⁻ x, (∫⁻ _y, M x ^ (2 : ℝ) ∂(P.map K)) ∂(P.map Hγ) := by
            rw [lintegral_prod]
            exact (hMm.comp measurable_fst).pow_const (2 : ℝ) |>.aemeasurable
      _ = ∫⁻ x, M x ^ (2 : ℝ) ∂(P.map Hγ) := by simp
      _ = ∫⁻ x, M x ^ (2 : ℝ) ∂(P.map Hφ) := by rw [hLawH]
      _ < ⊤ := hM2

end MatedCRTHarmonic.GMSCM
