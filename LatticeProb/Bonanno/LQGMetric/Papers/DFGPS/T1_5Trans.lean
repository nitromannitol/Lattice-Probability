/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5Trans at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgAffine
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Theorem 1.5, Step 1: moving the centre of an event (law transfer without measurability)

DFGPS (arXiv:1905.00380, "T"), proof of Theorem 1.5, Step 1 (T:1662–1670) applies Proposition 3.1
"and a union bound over all `z ∈ (𝕣𝕊) ∩ (δ𝕣ℤ²)`": Prop 3.1 is stated at the centre `0`, and is
used at the centres `z` through the translation invariance of the law of `h` (`h(· + z) - h_1(z)`
is again a normalized whole-plane GFF) with constants not depending on `z`.

`DFGPS.Prop3_1` gives its constants for each realization `(Ω, P, h)` separately. We work on the
canonical space `Ω = DistC` with `P = μ` the law of a normalized whole-plane GFF and `h = id`; the
translation `T_z g = g(· + z) - g_1(z)` preserves `μ` (`map_affine_sub_circleAvg`), so for every
set `S` (measurable or not) `μ (T_z⁻¹ S) ≤ μ S` (`Measure.le_map_apply`). Hence the constants of
Prop 3.1 for `(DistC, μ, id)` bound the probabilities of the translated events for all `z` at
once, with no measurability of the events needed.
-/

noncomputable section

open MeasureTheory Set

namespace LQGMetric.DFGPS

/-- the recentred translate `T_z g = g(· + z) - g_1(z)` -/
def transField (z : ℂ) (g : DistC) : DistC := addConst (affineComp 1 z g) (-circleAvg g 1 z)

lemma measurable_transField {μ : Measure DistC} (hμ : IsWholePlaneGFF id μ) (z : ℂ) :
    Measurable (transField z) :=
  ((hμ.affineComp one_pos z).addConst (measurable_circleAvg_left 1 z).neg).measurable

/-- `T_z` preserves the law of a normalized whole-plane GFF -/
lemma map_transField {μ : Measure DistC} (hμ : IsNormalizedWPGFF id μ) (z : ℂ) :
    μ.map (transField z) = μ := by
  have := CircleAvg.map_affine_sub_circleAvg (P := μ) (h := id) hμ one_pos z
  rw [Measure.map_id] at this
  exact this

/-- **Law transfer for arbitrary sets**: `μ (T_z⁻¹ S) ≤ μ S` for every `S ⊆ DistC`. -/
theorem measure_preimage_transField_le {μ : Measure DistC} (hμ : IsNormalizedWPGFF id μ)
    (z : ℂ) (S : Set DistC) : μ (transField z ⁻¹' S) ≤ μ S := by
  have h := Measure.le_map_apply (μ := μ) (measurable_transField hμ.1 z).aemeasurable S
  rwa [map_transField hμ z] at h

end LQGMetric.DFGPS
