/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.ZeroConeBridge at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.Representations
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48ZeroIG

/-!
# Case 0 on the 0-cone feeds Cases 1–2

Source: [18] and the last paragraph of §4.5
: the restrictions to `𝔻` of a 0-quantum cone and of a whole-plane GFF normalized
by `h_1(0) = 0` agree in law, which (with Lemma 4.3) transfers the local estimates between them.

The Proposition 4.8 proof proved the field/IG-input form of this on the frozen coupling
(`GMS4.prop48_zeroCone_disk_IGdata_law_eq_wholePlaneGFF`). Here it is extended by the
Lebesgue-time SLE `ηL` (a.s. the bundle's measurable function of `(hIG₀, U)`, `igMap`):
`map_restrictData_zeroConeData_eq` — for every open `V ⊆ 𝔻`, the restricted 0-cone data
`(h₀^{cone}|_V, ((hIG₀, U), ηL))` and the restricted whole-plane data `(h₀|_V, ((hIG₀, U), ηL))`
have the same law. Consequently a Case 0 bound proved for the 0-cone local event (the route)
is the Case 0 input of `case1_rooted_event_le`, `case2_local_event_le`,
`case2ConditionalDataLaw_local_le` (`case2_local_event_le_of_zeroCone`, …).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

/-- The 0-quantum-cone data `(h₀^{cone}, ((hIG₀, U), ηL))` of the coupling. -/
def zeroConeData {Ω : Type} (γ : ℝ) (X₀ hIG₀ : Ω → MatedCRT.Field) (B₀ B₀' : ℝ≥0 → Ω → ℝ)
    (U : Ω → ℝ) (ηL : Ω → C(ℝ, ℂ)) (ω : Ω) : WPData :=
  (coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω)),
    wpAux hIG₀ U ηL ω)

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **Restricted 0-cone data = restricted whole-plane data in law** on every open `V ⊆ 𝔻`, jointly
with the full IG coordinates `(hIG₀, U)` and the SLE `ηL`. -/
theorem map_restrictData_zeroConeData_eq
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV : V ≤ Blueprint.ballO 0 1) :
    P.map (fun ω => restrictData V (zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω)) =
      P.map (fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨Φ, hΦ, -, hηL, -⟩ := D.igMap
  have hind : IndepFun (wpField X₀) (fun ω => (hIG₀ ω, U ω)) P :=
    (indepFun_wpField_wpAux D).comp measurable_id measurable_fst
  have hdisk := GMS4.prop48_zeroCone_disk_IGdata_law_eq_wholePlaneGFF D hγ
    (isNormalizedWPGFF_wpField D) hind
  let F : DistOn (Blueprint.ballO (0 : ℂ) 1) × (DistC × ℝ) → DistOn V × AuxData :=
    fun x => (MoTPort.IG.GFFAbsCont.resOn V (Blueprint.ballO 0 1) x.1, (x.2, Φ (igInput x.2)))
  have hF : Measurable F :=
    ((MoTPort.IG.GFFAbsCont.measurable_resOn V (Blueprint.ballO 0 1)).comp measurable_fst).prodMk
      (measurable_snd.prodMk (hΦ.comp (measurable_igInput.comp measurable_snd)))
  have hU : AEMeasurable U P := Canon.aemeasurable_phase D hγ
  have hIG : AEMeasurable (fun ω => (hIG₀ ω, U ω)) P :=
    D.igField.1.1.measurable.aemeasurable.prodMk hU
  have hm₀ : AEMeasurable (fun ω => (restrictTo (Blueprint.ballO 0 1) (coneField (X₀ ω)
      (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))), (hIG₀ ω, U ω))) P :=
    ((measurable_restrictTo (Blueprint.ballO 0 1)).comp_aemeasurable
      (GMS4.aemeasurable_prop48ZeroConeField D)).prodMk hIG
  have hm₁ : AEMeasurable (fun ω => (restrictTo (Blueprint.ballO 0 1) (wpField X₀ ω), (hIG₀ ω, U ω))) P :=
    ((measurable_restrictTo (Blueprint.ballO 0 1)).comp (measurable_wpField D)).aemeasurable.prodMk hIG
  have he₀ : (fun ω => restrictData V (zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω)) =ᵐ[P]
      F ∘ (fun ω => (restrictTo (Blueprint.ballO 0 1) (coneField (X₀ ω)
        (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))), (hIG₀ ω, U ω))) := by
    filter_upwards [hηL] with ω hω
    have hω' : Φ (igInput (hIG₀ ω, U ω)) = ηL ω := hω.symm
    simp only [Function.comp_apply, F, restrictData, zeroConeData, wpAux,
      MoTPort.IG.GFFAbsCont.resOn_restrictTo hV, hω']
  have he₁ : (fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) =ᵐ[P]
      F ∘ (fun ω => (restrictTo (Blueprint.ballO 0 1) (wpField X₀ ω), (hIG₀ ω, U ω))) := by
    filter_upwards [hηL] with ω hω
    have hω' : Φ (igInput (hIG₀ ω, U ω)) = ηL ω := hω.symm
    simp only [Function.comp_apply, F, restrictData, wpData, wpAux,
      MoTPort.IG.GFFAbsCont.resOn_restrictTo hV, hω']
  rw [Measure.map_congr he₀, Measure.map_congr he₁,
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm₀,
    ← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm₁]
  exact congrArg (Measure.map F) hdisk

/-- A local event has the same probability for the 0-cone data as for the whole-plane data. -/
theorem measure_restrictData_zeroConeData_preimage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : Opens ℂ) (hV : V ≤ Blueprint.ballO 0 1)
    {G : Set (DistOn V × AuxData)} (hG : MeasurableSet G) :
    P ((fun ω => restrictData V (zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω)) ⁻¹' G) =
      P ((fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) ⁻¹' G) := by
  have h₀ : AEMeasurable (fun ω => restrictData V (zeroConeData γ X₀ hIG₀ B₀ B₀' U ηL ω)) P :=
    (measurable_restrictData V).comp_aemeasurable
      ((GMS4.aemeasurable_prop48ZeroConeField D).prodMk (aemeasurable_wpAux D hγ))
  have h₁ : AEMeasurable (fun ω => restrictData V (wpData X₀ hIG₀ U ηL ω)) P :=
    (measurable_restrictData V).comp_aemeasurable (aemeasurable_wpData D hγ)
  rw [← Measure.map_apply_of_aemeasurable h₀ hG, ← Measure.map_apply_of_aemeasurable h₁ hG,
    map_restrictData_zeroConeData_eq D hγ V hV]

end Coupling

end MatedCRTHarmonic.GMSCase1
