import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D114U1
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112M4

/-! # Mean-zero pairings observed in a random dyadic hull -/

set_option autoImplicit false

open MeasureTheory MeasurableSpace Set
open LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A supported mean-zero pairing, gated by inclusion of its support in the
interior hull, is measurable from the hull and its local field observation. -/
theorem measurable_hull_gated_pairing {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ) (θ : TestC)
    (hθ : ∫ z, θ z = 0) :
    Measurable[hullSigma0 h A n] (fun ω =>
      ({ω | tsupport (θ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))} : Set Ω).indicator
        (fun ω => h ω θ) ω) := by
  classical
  intro B hB
  let T : Set ℂ → Set Ω := fun S =>
    if tsupport (θ : ℂ → ℝ) ⊆ interior S then {ω | h ω θ ∈ B}
    else if (0 : ℝ) ∈ B then univ else ∅
  have hT : ∀ S, MeasurableSet[fieldSigma0On h (interior S)] (T S) := by
    intro S
    dsimp [T]
    split_ifs with hS hzero
    · exact (measurable_pair_fieldSigma0On h θ hθ hS) hB
    · exact @MeasurableSet.univ Ω (fieldSigma0On h (interior S))
    · exact @MeasurableSet.empty Ω (fieldSigma0On h (interior S))
  have heq : (fun ω =>
      ({ω | tsupport (θ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω))} : Set Ω).indicator
        (fun ω => h ω θ) ω) ⁻¹' B =
      ⋃ S ∈ conf36HullShapes n, {ω | dyadicHull n (A ω) = S} ∩ T S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨_, conf36_hull_mem_shapes (Or.inl (hA ω)) n, rfl, ?_⟩
      by_cases hs : tsupport (θ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) <;>
        simpa [T, Set.indicator_apply, hs] using hx
    · rintro ⟨S, hS, heq, hx⟩
      subst S
      by_cases hs : tsupport (θ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) <;>
        simpa [T, Set.indicator_apply, hs] using hx
  rw [heq]
  apply MeasurableSet.biUnion (conf36HullShapes_countable n)
  intro S hS
  exact (le_sup_right : _ ≤ hullSigma0 h A n) _
    (measurableSet_generateFrom ⟨S, T S, hT S, rfl⟩)

end LatticeProb.LQG
