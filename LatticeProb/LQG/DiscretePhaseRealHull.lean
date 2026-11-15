import LatticeProb.LQG.LocalHullFieldPhase
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A

/-! # Local discrete phase observations and real field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory MeasurableSpace Set
open LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The locally gated phase is observable from the real field on a bounded
random dyadic hull. -/
theorem measurable_localHullFieldPhase_real {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (ψ : TestC) {p : ℝ} (hp : 0 < p) :
    Measurable[hullSigma h A n] (localHullFieldPhase h A n ψ hp) := by
  classical
  intro B hB
  let T : Set ℂ → Set Ω := fun S =>
    if tsupport (ψ : ℂ → ℝ) ⊆ interior S then
      {ω | toIcoMod hp 0 (h ω ψ) ∈ B}
    else if (0 : ℝ) ∈ B then univ else ∅
  have hT : ∀ S, MeasurableSet[fieldSigma h (toOpens (interior S) isOpen_interior)] (T S) := by
    intro S
    dsimp [T]
    split_ifs with hS hzero
    · exact ((measurable_toIcoMod_zero hp).comp (LQGMetric.GM.measurable_pair_fieldSigma h ψ hS)) hB
    · exact @MeasurableSet.univ Ω (fieldSigma h (toOpens (interior S) isOpen_interior))
    · exact @MeasurableSet.empty Ω (fieldSigma h (toOpens (interior S) isOpen_interior))
  have heq : (localHullFieldPhase h A n ψ hp) ⁻¹' B =
      ⋃ S ∈ conf36HullShapes n, {ω | dyadicHull n (A ω) = S} ∩ T S := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_ofPred_eq]
    constructor
    · intro hx
      refine ⟨_, conf36_hull_mem_shapes (Or.inl (hA ω)) n, rfl, ?_⟩
      by_cases hs : tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) <;>
        simpa [T, localHullFieldPhase, Set.indicator_apply, hs] using hx
    · rintro ⟨S, hS, heq, hx⟩
      subst S
      by_cases hs : tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) <;>
        simpa [T, localHullFieldPhase, Set.indicator_apply, hs] using hx
  rw [heq]
  apply MeasurableSet.biUnion (conf36HullShapes_countable n)
  intro S hS
  exact (le_sup_right : _ ≤ hullSigma h A n) _
    (measurableSet_generateFrom ⟨S, T S, hT S, rfl⟩)

/-- A local discrete-period field observation is contained in the corresponding
real field observation. -/
theorem localHullFieldSigma_le_hullSigma {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω)) (n : ℕ)
    (ψ : TestC) {p : ℝ} (hp : 0 < p) :
    localHullFieldSigma h A n ψ hp ≤ hullSigma h A n := by
  let : MeasurableSpace Ω := hullSigma h A n
  exact sup_le (hullSigma0_le_hullSigma h A n)
    (measurable_localHullFieldPhase_real h A hA n ψ hp).comap_le

/-- The intersection over scales of the joined local phase observations is
contained in the real-field local sigma algebra. -/
theorem iInf_iSup_localHullFieldSigma_le_localSigma {Ω : Type} (h : Ω → DistC)
    (A : Ω → Set ℂ) (hA : ∀ ω, Bornology.IsBounded (A ω))
    (ψ : ℕ → ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    (⨅ n, ⨆ k, localHullFieldSigma h A n (ψ n k) hp) ≤ localSigma h A := by
  unfold localSigma
  exact iInf_mono fun n => iSup_le fun k =>
    localHullFieldSigma_le_hullSigma h A hA n (ψ n k) hp

end LatticeProb.LQG
