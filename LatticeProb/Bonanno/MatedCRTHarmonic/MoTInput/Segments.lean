/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.Segments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.SLEInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping

/-!
# Transfer of the bundle's segment-ball estimate to the cell-model interface

The bundle states the estimate for the Lebesgue-parametrized curve. Its increasing order
reparameterization preserves the collection of curve segments, so the estimate transfers to
the LQG-area-parametrized curve used by the cell-model interface.

Re-based onto the frozen surface v3 : `cellModelOfCoupling` takes
`hγ : γ ∈ Ioo 0 2` (see `MoTInput/CellModel.lean`), so the statements below carry it too; the proofs
are unchanged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Topology Asymptotics
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic
open MatedCRTHarmonic.MatedCRT

private theorem image_reparam_Icc {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t)) (a b : ℝ) :
    η '' Icc a b = ηL '' Icc (φ a) (φ b) := by
  rw [show (η : ℝ → ℂ) = (ηL : ℝ → ℂ) ∘ φ from funext hη, Set.image_comp, φ.image_Icc]

private theorem segmentBallEvent_of_bundle
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {ω : Ω} {φ : ℝ ≃o ℝ}
    (hη : ∀ t, η ω t = ηL ω (φ t))
    {R r ε : ℝ}
    (hsource : SegmentsContainBalls (ηL ω) R r ε) :
    GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε ω := by
  change ∀ δ ∈ Ioc (0 : ℝ) ε, ∀ a b : ℝ, a < b → η ω '' Icc a b ⊆ ball 0 R →
    δ ^ (1 - r) ≤ diam (η ω '' Icc a b) →
      ∃ w : ℂ, ∃ t : ℝ, δ ≤ t ∧ ball w t ⊆ η ω '' Icc a b
  intro δ hδε a b hab hball hdiam
  have himage := image_reparam_Icc hη a b
  have hballL : ηL ω '' Icc (φ a) (φ b) ⊆ ball 0 R := by
    rw [← himage]
    simpa [GMSLemma27.CellModel.cell, cellModelOfCoupling] using hball
  have hdiamL : δ ^ (1 - r) ≤ diam (ηL ω '' Icc (φ a) (φ b)) := by
    simpa only [← himage] using hdiam
  obtain ⟨w, hw⟩ := hsource δ hδε (φ a) (φ b) (φ.strictMono hab) (by
    exact hballL) hdiamL
  refine ⟨w, δ, le_rfl, ?_⟩
  rw [himage]
  exact hw

private theorem probability_segmentBallEvent_le
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    {R r ε : ℝ} :
    P (GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε)ᶜ ≤
      P {ω | ¬ SegmentsContainBalls (ηL ω) R r ε} := by
  apply measure_mono_ae
  filter_upwards [D.areaParam] with ω harea
  rcases harea with ⟨⟨φ, _, hη⟩, _⟩
  intro hbad hsource
  exact hbad (segmentBallEvent_of_bundle D hγ hη hsource)

/-- The bundle's superpolynomial segment-ball estimate, expressed in the little-o form. -/
theorem segmentsContainBalls_of_coupling
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    GMSLemma27.SegmentsContainBalls (cellModelOfCoupling D hγ) := by
  intro r hr R hR s
  obtain ⟨N, hsN⟩ := exists_nat_gt s
  obtain ⟨C, hC⟩ := D.segmentsContainBalls R hR r hr N
  have hdecay : 0 < (N : ℝ) - s := sub_pos.mpr hsN
  have hlim := GMSLemma27.tendsto_rpow_nhdsGT_zero hdecay
  have hlim' : Tendsto (fun ε : ℝ => max C 0 * ε ^ ((N : ℝ) - s))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hlim0 : Tendsto (fun ε : ℝ => ε ^ ((N : ℝ) - s))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := hlim.mono_right nhdsWithin_le_nhds
    simpa only [mul_zero] using hlim0.const_mul (max C 0)
  have hlittle :
      (fun ε : ℝ => (P (GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε)ᶜ).toReal) =o[𝓝[>] (0 : ℝ)]
        (fun ε => ε ^ s) := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hsmall := hlim'.eventually (gt_mem_nhds hc)
    filter_upwards [hsmall, self_mem_nhdsWithin, Ioo_mem_nhdsGT one_pos] with ε hsmall hε hεlt
    have hεpos : 0 < ε := hε
    have hprob := probability_segmentBallEvent_le D hγ (R := R) (r := r) (ε := ε)
    have hbound := hC ε hεlt
    have hpow : 0 ≤ ε ^ N := pow_nonneg hεpos.le N
    have hCpow : 0 ≤ max C 0 * ε ^ N := mul_nonneg (le_max_right _ _) hpow
    have hCmono : C * ε ^ N ≤ max C 0 * ε ^ N :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hpow
    have hprob' : P (GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε)ᶜ ≤
        ENNReal.ofReal (max C 0 * ε ^ N) :=
      hprob.trans (hbound.trans (ENNReal.ofReal_le_ofReal hCmono))
    have hreal : (P (GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε)ᶜ).toReal ≤
        max C 0 * ε ^ N :=
      ENNReal.toReal_le_of_le_ofReal hCpow hprob'
    have hrpow : ε ^ (N : ℝ) = ε ^ s * ε ^ ((N : ℝ) - s) := by
      calc
        ε ^ (N : ℝ) = ε ^ (s + ((N : ℝ) - s)) := by congr 1 <;> ring
        _ = ε ^ s * ε ^ ((N : ℝ) - s) := Real.rpow_add hεpos _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (ENNReal.toReal_nonneg)]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hεpos.le s)]
    calc
      (P (GMSLemma27.segmentBallEvent (cellModelOfCoupling D hγ) R r ε)ᶜ).toReal ≤
          max C 0 * ε ^ N := hreal
      _ = ε ^ s * (max C 0 * ε ^ ((N : ℝ) - s)) := by
        rw [← Real.rpow_natCast ε N, hrpow]
        ring
      _ ≤ c * ε ^ s := by
        simpa only [mul_comm c (ε ^ s)] using
          mul_le_mul_of_nonneg_left (le_of_lt hsmall) (Real.rpow_nonneg hεpos.le s)
  exact hlittle

end MatedCRTHarmonic.MoTInput
