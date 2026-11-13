/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.LawExtensionality at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.GFFLaw

/-!
# Extensionality of normalized distribution laws from mean-zero pairings

Mean-zero test pairings determine a distribution only modulo an additive constant. This file
uses the existing `LQGMetric.GFFLaw.sigma0` and `LQGMetric.GFFLaw.recenter` factorization to
upgrade equality of their joint laws to equality of laws on `DistC`, when both laws are supported
on the zero set of the same additive-equivariant normalization.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.GFFInv

/-- A measurable function of a distribution's mean-zero pairings has the same pushforward under
two measures whose complete mean-zero pairing laws agree. -/
theorem map_eq_of_map_ev0_eq {μ ν : Measure DistC} {β : Type*} [MeasurableSpace β]
    {F : DistC → β} (hF : Measurable[GFFLaw.sigma0] F)
    (hpair : μ.map GFFLaw.ev0 = ν.map GFFLaw.ev0) : μ.map F = ν.map F := by
  have hle : GFFLaw.sigma0 ≤ (inferInstance : MeasurableSpace DistC) := by
    rw [GFFLaw.sigma0, ← measurable_iff_comap_le]
    exact measurable_pi_iff.2 fun φ => measurable_pair φ.1
  have hFm : Measurable F := hF.mono hle le_rfl
  have hev : Measurable GFFLaw.ev0 :=
    measurable_pi_iff.2 fun φ => measurable_pair φ.1
  ext S hS
  obtain ⟨T, hT, hTS⟩ := hF hS
  rw [Measure.map_apply hFm hS, Measure.map_apply hFm hS]
  have hpre : F ⁻¹' S = GFFLaw.ev0 ⁻¹' T := hTS.symm
  rw [hpre, ← Measure.map_apply hev hT, ← Measure.map_apply hev hT, hpair]

end MatedCRTHarmonic.ConeLemmaA10

