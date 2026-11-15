import LatticeProb.LQG.CompactFieldGerm

/-! # Field germs on deterministic sets -/

set_option autoImplicit false

open Set
open LQGMetric LQGMetric.Blueprint

namespace LatticeProb.LQG

/-- The observation of a deterministic set generates the trivial sigma algebra. -/
theorem setSigma_const {Ω : Type} (K : Set ℂ) :
    setSigma (fun _ : Ω => K) = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  apply MeasurableSpace.generateFrom_le
  rintro E ⟨U, _, rfl⟩
  by_cases h : (K ∩ U).Nonempty
  · simp [h]
  · simp [h]

/-- At a deterministic set, a hull observation is the field observation on its interior. -/
theorem hullSigma0_const {Ω : Type} (h : Ω → DistC) (K : Set ℂ) (n : ℕ) :
    hullSigma0 h (fun _ => K) n = fieldSigma0On h (interior (dyadicHull n K)) := by
  classical
  unfold hullSigma0
  rw [setSigma_const, bot_sup_eq]
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro E ⟨S, F, hF, rfl⟩
    by_cases heq : dyadicHull n K = S
    · subst S
      simpa using hF
    · simp [heq]
  · intro F hF
    apply MeasurableSpace.measurableSet_generateFrom
    refine ⟨dyadicHull n K, F, hF, ?_⟩
    simp

/-- For a deterministic compact set, the dyadic local germ equals the thickening germ. -/
theorem localSigma0_const_eq_fieldSigmaClosed0 {Ω : Type} (h : Ω → DistC)
    {K : Set ℂ} (hK : IsCompact K) :
    localSigma0 h (fun _ => K) = fieldSigmaClosed0 h K := by
  unfold localSigma0
  simp_rw [hullSigma0_const]
  exact (fieldSigmaClosed0_eq_iInf_dyadicHull h hK).symm

end LatticeProb.LQG
