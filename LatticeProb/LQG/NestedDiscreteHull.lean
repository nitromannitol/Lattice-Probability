import LatticeProb.LQG.LocalHullFieldPhase
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39J5a

/-! # Nested discrete-period field observations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.CONF
open LQGMetric.LocalEvent

namespace LatticeProb.LQG

/-- Discrete-period field observations decrease as the dyadic hull shrinks. -/
theorem localHullFieldSigma_succ_le {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (n : ℕ) (ψ : TestC) {p : ℝ} (hp : 0 < p) :
    localHullFieldSigma h A (n + 1) ψ hp ≤ localHullFieldSigma h A n ψ hp := by
  apply sup_le ((t39j_hullSigma0_succ_le h hclosed n).trans le_sup_left)
  apply Measurable.comap_le
  let : MeasurableSpace Ω := localHullFieldSigma h A n ψ hp
  let E : Set Ω := {ω | tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull (n + 1) (A ω))}
  have hE : MeasurableSet E :=
    ((t39j_hullSigma0_succ_le h hclosed n).trans
      (le_sup_left : hullSigma0 h A n ≤ localHullFieldSigma h A n ψ hp)) _
      (measurableSet_subset_interior_dyadicHull h A hbounded (n + 1) _)
  have hphase : Measurable (localHullFieldPhase h A n ψ hp) :=
    (comap_measurable _).mono le_sup_right le_rfl
  have heq : localHullFieldPhase h A (n + 1) ψ hp =
      E.indicator (localHullFieldPhase h A n ψ hp) := by
    funext ω
    by_cases hω : tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull (n + 1) (A ω))
    · have hcoarse : tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (A ω)) :=
        hω.trans (interior_mono (hull_succ_subset n (A ω)))
      simp [localHullFieldPhase, E, hω, hcoarse]
    · simp [localHullFieldPhase, E, hω]
  rw [heq]
  exact hphase.indicator hE

/-- The joined observations from a fixed family of anchors decrease with scale. -/
theorem antitone_iSup_localHullFieldSigma {Ω : Type} (h : Ω → DistC) (A : Ω → Set ℂ)
    (hclosed : ∀ ω, IsClosed (A ω)) (hbounded : ∀ ω, Bornology.IsBounded (A ω))
    (ψ : ℕ → TestC) {p : ℝ} (hp : 0 < p) :
    Antitone (fun n => ⨆ k, localHullFieldSigma h A n (ψ k) hp) := by
  apply antitone_nat_of_succ_le
  intro n
  exact iSup_le fun k => (localHullFieldSigma_succ_le h A hclosed hbounded n (ψ k) hp).trans
    (le_iSup (fun j => localHullFieldSigma h A n (ψ j) hp) k)

end LatticeProb.LQG
