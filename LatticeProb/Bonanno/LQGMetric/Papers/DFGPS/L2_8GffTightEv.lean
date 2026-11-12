/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffTightEv at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofTight

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Tightness transfer with domination on events of probability close to one (DFGPS L2.8, (a1))

DFGPS T:883–891 compares `D^ε_h` with `D^ε_{h̊}` through the localized metrics; the comparison
holds only for `ε` below a random threshold `ε₀(ω)`. Hence, for `ε < ε₁` with deterministic
`ε₁`, the domination `B_ε ≤ K · A_ε` holds on the event `{ε₀ ≥ ε₁}`, whose probability is close to
one for small `ε₁`. This file extends `isTightMeasureSet_of_le_mul` (`L2_8ProofTight.lean`) to
this situation (own elementary argument; the paper does not discuss it):

* `isTightMeasureSet_of_approx` : a family dominated, up to `η`, on compact complements by a
  tight family, for every `η > 0`, is tight;
* `isTightMeasureSet_of_le_mul_ev` : tightness transfer with domination `B_i ≤ M · A_i` on
  events `E_i` (arbitrary sets, depending on `i`) with `P(E_iᶜ) ≤ η` (one constant `M` per `η`).
  Per-`ε` probability bounds therefore suffice: no simultaneity in `ε` is needed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

/-- **Tightness by approximation.** -/
theorem isTightMeasureSet_of_approx {𝓧 : Type*} [TopologicalSpace 𝓧] [MeasurableSpace 𝓧]
    {S : Set (Measure 𝓧)}
    (h : ∀ η : ℝ≥0∞, 0 < η → ∃ T : Set (Measure 𝓧), IsTightMeasureSet T ∧
      ∀ μ ∈ S, ∃ ν ∈ T, ∀ K : Set 𝓧, IsCompact K → μ Kᶜ ≤ ν Kᶜ + η) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (ENNReal.half_pos hε.ne')
  obtain ⟨K, hK, hKT⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hT) (ε / 2)
      (ENNReal.half_pos hε.ne')
  refine ⟨K, hK, fun μ hμ => ?_⟩
  obtain ⟨ν, hν, hle⟩ := hST μ hμ
  calc μ Kᶜ ≤ ν Kᶜ + ε / 2 := hle K hK
    _ ≤ ε / 2 + ε / 2 := by gcongr; exact hKT ν hν
    _ = ε := ENNReal.add_halves ε

end LQGMetric.DFGPS
