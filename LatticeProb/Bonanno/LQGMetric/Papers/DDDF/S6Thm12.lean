/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm11Wire
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA

/-!
# DDDF Theorem 1 (2) on `D = (−1,2)²`, `δ ∈ (0,1/2)`: tightness (task P2-DDDF6e, packet O9)

DDDF = arXiv:1904.08021, `tightness.tex` l. 160–161 (Theorem 1 (2)) and l. 1497–1498 ("the
second assertion of Theorem 1 is a corollary of" Prop 29): on the coupling of Prop 29 at time
`t = δ` (`DDDFProp29Sq`, `D = (−1,2)²`, `U = (−1/2,3/2)²`), `‖φ_{√δ} − p_{δ/2} * h‖_U ≤ x` off
an event of probability `≤ C e^{-cx²}`, so the metric of `p_{δ/2} * h` is at most `e^{ξx}` times
that of `φ_{√δ}` (`sqMetricC_le_of_abs_sub_le`), whose laws are tight by Theorem 1 (1); the laws
are transported between probability spaces by `map_pathC_heat_eq`, `map_pathC_phiVer_eq`.
The tightness transfer through the modulus criterion (`modulus_of_tight`,
`map_mod_le_of_le_on`) is an own elementary argument (Billingsley Thm 7.3).
Only `δ ∈ (0,1/2)` is covered (Prop 29's range; `δ ∈ [1/2,1)` is D-DDDF-13).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS

local notation "SQ" => C(closedUnitSquare × closedUnitSquare, ℝ)

/-- the modulus event `{d | ∃ z w, |z − w| ≤ η, d(z,w) > ζ}` -/
def modBad (η ζ : ℝ) : Set SQ := {d | ¬ ∀ z w : closedUnitSquare, dist z w ≤ η → d (z, w) ≤ ζ}

lemma measurableSet_modBad (η ζ : ℝ) : MeasurableSet (modBad η ζ) :=
  (isClosed_modulusSet _ η ζ).isOpen_compl.measurableSet

/-- a tight family of laws of functions vanishing on the diagonal has a uniform modulus -/
theorem modulus_of_tight {S : Set (Measure SQ)} (hS : IsTightMeasureSet S)
    (hdiag : ∀ μ ∈ S, μ {d | ¬ ∀ x, d (x, x) = 0} = 0) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ η > 0, ∀ μ ∈ S, μ (modBad η ζ) ≤ ENNReal.ofReal ζ := by
  obtain ⟨K, hK, hKμ⟩ := (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1 hS)
    (ENNReal.ofReal ζ) (by simpa using hζ)
  obtain ⟨η, hη, hmod⟩ := exists_modulus_of_isCompact hK hζ
  refine ⟨η, hη, fun μ hμ => ?_⟩
  have hsub : modBad η ζ ⊆ Kᶜ ∪ {d | ¬ ∀ x, d (x, x) = 0} := by
    intro d hd
    by_contra hc
    simp only [mem_union, mem_compl_iff, not_or, not_not, mem_ofPred_eq] at hc
    refine hd fun z w hzw => ?_
    have h1 := hmod d hc.1 (z, w) (z, z) (by
      rw [Prod.dist_eq, dist_self, dist_comm]; exact max_le hη.le hzw)
    have h2 := hc.2 z
    rw [h2, sub_zero] at h1
    exact (le_abs_self _).trans h1
  calc μ (modBad η ζ) ≤ μ Kᶜ + μ {d | ¬ ∀ x, d (x, x) = 0} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal ζ + 0 := add_le_add (hKμ μ hμ) (hdiag μ hμ).le
    _ = _ := add_zero _

/-- domination on an event transfers the modulus event -/
theorem map_mod_le_of_le_on {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A B : Ω → SQ}
    (hA : Measurable A) (hB : Measurable B) {E : Set Ω} {M : ℝ} (hM : 0 < M)
    (hE : ∀ ω ∈ E, ∀ p, A ω p ≤ M * B ω p) (η ζ : ℝ) :
    (P.map A) (modBad η ζ) ≤ (P.map B) (modBad η (ζ / M)) + P Eᶜ := by
  rw [Measure.map_apply hA (measurableSet_modBad η ζ),
    Measure.map_apply hB (measurableSet_modBad η (ζ / M))]
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  by_cases hωE : ω ∈ E
  · left
    simp only [mem_preimage, modBad, mem_ofPred_eq, not_forall, not_le] at hω ⊢
    obtain ⟨z, w, hzw, hlt⟩ := hω
    refine ⟨z, w, hzw, ?_⟩
    rw [div_lt_iff₀ hM, mul_comm]
    exact hlt.trans_le (hE ω hωE (z, w))
  · exact Or.inr hωE

end S6Thm
end DDDF
end LQGMetric
