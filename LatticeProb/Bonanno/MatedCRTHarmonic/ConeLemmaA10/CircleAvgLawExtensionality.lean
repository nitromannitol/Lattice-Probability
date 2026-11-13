/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeLemmaA10.CircleAvgLawExtensionality at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.ConeLemmaA10.LawExtensionality
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGauss
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Extensionality for circle-average-normalized distributions

The unit-circle average is a junk-valued limit, so its additive-constant law is only valid when
the defining mollified averages converge. This adapter uses that law only on the a.e. support of
the measures, where convergence is included explicitly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace MatedCRTHarmonic.ConeLemmaA10

open LQGMetric LQGMetric.GFFInv

/-- Equality of all mean-zero pairing laws determines a measure on `DistC` if the measure is
supported on fields whose unit-circle average is zero and whose defining mollified averages
converge. Convergence is the support condition that makes the circle average equivariant under
adding constants; no global equivariance assumption is made for arbitrary distributions. -/
theorem measure_eq_of_map_ev0_eq_of_circleAvg_zero
    {μ ν : Measure DistC} {ρ : TestC} (hρ : ∫ x, ρ x = 1)
    (hpair : μ.map GFFLaw.ev0 = ν.map GFFLaw.ev0)
    (hμ : ∀ᵐ g ∂μ,
      (∃ a, Tendsto (fun n => CircleAvg.mollAvg g n 0 1) atTop (𝓝 a)) ∧
        circleAvg g 1 0 = 0)
    (hν : ∀ᵐ g ∂ν,
      (∃ a, Tendsto (fun n => CircleAvg.mollAvg g n 0 1) atTop (𝓝 a)) ∧
        circleAvg g 1 0 = 0) : μ = ν := by
  let N : DistC → ℝ := fun g => circleAvg g 1 0
  let K : DistC → DistC := fun g => addConst g (-(N g))
  let F : DistC → DistC := K ∘ GFFLaw.recenter ρ
  have hNm : Measurable N := by
    simpa [N] using measurable_circleAvg_left 1 0
  have hK : Measurable K := measurable_distC_iff.2 fun φ => by
    simp only [K, addConst_apply]
    exact (measurable_pair φ).add (hNm.neg.const_mul _)
  have hF : Measurable[GFFLaw.sigma0] F :=
    hK.comp (GFFLaw.measurable_recenter_sigma0 hρ)
  have hkey : ∀ᵐ g ∂μ, F g = addConst g (-(N g)) := by
    filter_upwards [hμ] with g hg
    obtain ⟨a, ha⟩ := hg.1
    have hshift : N (GFFLaw.recenter ρ g) = N g - g ρ := by
      change circleAvg (addConst g (-(g ρ))) 1 0 = circleAvg g 1 0 - g ρ
      rw [CircleAvg.circleAvg_addConst_of_tendsto ha (-(g ρ))]
      ring
    change addConst (addConst g (-(g ρ)))
      (-(N (GFFLaw.recenter ρ g))) = addConst g (-(N g))
    rw [hshift, GFFLaw.addConst_addConst]
    congr 1
    ring
  have hkeyν : ∀ᵐ g ∂ν, F g = addConst g (-(N g)) := by
    filter_upwards [hν] with g hg
    obtain ⟨a, ha⟩ := hg.1
    have hshift : N (GFFLaw.recenter ρ g) = N g - g ρ := by
      change circleAvg (addConst g (-(g ρ))) 1 0 = circleAvg g 1 0 - g ρ
      rw [CircleAvg.circleAvg_addConst_of_tendsto ha (-(g ρ))]
      ring
    change addConst (addConst g (-(g ρ)))
      (-(N (GFFLaw.recenter ρ g))) = addConst g (-(N g))
    rw [hshift, GFFLaw.addConst_addConst]
    congr 1
    ring
  have hfix : ∀ g, N g = 0 → addConst g (-(N g)) = g := by
    intro g hg
    rw [hg, neg_zero, GFFLaw.addConst_zero']
  have hμmap : μ.map F = μ := by
    calc
      μ.map F = μ.map id := Measure.map_congr (by
        filter_upwards [hμ, hkey] with g hg hfg
        rw [hfg]
        exact hfix g hg.2)
      _ = μ := Measure.map_id
  have hνmap : ν.map F = ν := by
    calc
      ν.map F = ν.map id := Measure.map_congr (by
        filter_upwards [hν, hkeyν] with g hg hfg
        rw [hfg]
        exact hfix g hg.2)
      _ = ν := Measure.map_id
  calc
    μ = μ.map F := hμmap.symm
    _ = ν.map F := map_eq_of_map_ev0_eq hF hpair
    _ = ν := hνmap

end MatedCRTHarmonic.ConeLemmaA10

