import Mathlib
import LatticeProb.Prob.StopFunctional
import LatticeProb.Prob.UpcrossMeasurable

/-!
# First hits are stopping functionals

For a stopping functional `Ψ` and a level `a`, the first hit of `a` after the random time `Ψ` is
again a stopping functional (`LatticeProb.IsStopFun.hitFrom`).  In particular the first zero
`τ₀ = hitFrom 0 0` and the end `d₁` of the first up-crossing interval are stopping functionals,
hence stopping times of any filtration to which a continuous process is adapted.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

lemma stopAt_coe_of_le {s t : ℝ≥0} (w : C(ℝ≥0, ℝ)) (h : s ≤ t) :
    stopAt (t : ℝ≥0∞) w s = w s := by
  rw [stopAt_coe, min_eq_left h]

/-- The first hit of `a` after a stopping functional is a stopping functional. -/
theorem IsStopFun.hitFrom (a : ℝ) {Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΨ : IsStopFun Ψ) :
    IsStopFun (fun w => hitFrom a (Ψ w) (w : ℝ≥0 → ℝ)) := by
  intro w t
  constructor
  · intro h
    replace h : LatticeProb.hitFrom a (Ψ w) (w : ℝ≥0 → ℝ) ≤ t := h
    have hΨt : Ψ w ≤ t := le_hitFrom.trans h
    have hΨeq := (hΨ w t).1 hΨt
    show LatticeProb.hitFrom a (Ψ (stopAt (t : ℝ≥0∞) w)) (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ) =
      LatticeProb.hitFrom a (Ψ w) (w : ℝ≥0 → ℝ)
    rw [hΨeq]
    have hne : LatticeProb.hitFrom a (Ψ w) (w : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h
    obtain ⟨s0, hs0, hrs0, hws0, hmin⟩ := exists_hitFrom_eq w.continuous hne
    have hs0t : s0 ≤ t := by rw [hs0] at h; exact_mod_cast h
    rw [hs0]
    apply le_antisymm
    · exact hitFrom_le hrs0 (by show stopAt (t : ℝ≥0∞) w s0 = a
                                rw [stopAt_coe_of_le w hs0t]; exact hws0)
    · refine le_iInf₂ fun s hs => ?_
      have hs' : stopAt (t : ℝ≥0∞) w s = a := hs.2
      by_cases hst : s ≤ t
      · rw [stopAt_coe_of_le w hst] at hs'
        exact_mod_cast hmin s hs.1 hs'
      · exact_mod_cast hs0t.trans (not_le.1 hst).le
  · intro h
    replace h : LatticeProb.hitFrom a (Ψ (stopAt (t : ℝ≥0∞) w)) (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ)
      ≤ t := h
    have hΨ'w : Ψ (stopAt (t : ℝ≥0∞) w) ≤ t :=
      (le_hitFrom (r := Ψ (stopAt (t : ℝ≥0∞) w)) (a := a)
        (w := (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ))).trans h
    have hΨt : Ψ w ≤ t := (hΨ w t).2 hΨ'w
    have hΨeq := (hΨ w t).1 hΨt
    have h' : LatticeProb.hitFrom a (Ψ w) (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ) ≤ t := by
      have : LatticeProb.hitFrom a (Ψ (stopAt (t : ℝ≥0∞) w)) (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ) ≤ t := h
      rwa [hΨeq] at this
    have hne : LatticeProb.hitFrom a (Ψ w) (stopAt (t : ℝ≥0∞) w : ℝ≥0 → ℝ) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top h'
    obtain ⟨s0, hs0, hrs0, hws0, -⟩ := exists_hitFrom_eq (stopAt (t : ℝ≥0∞) w).continuous hne
    have hs0t : s0 ≤ t := by rw [hs0] at h'; exact_mod_cast h'
    have hws : w s0 = a := by
      have : stopAt (t : ℝ≥0∞) w s0 = a := hws0
      rwa [stopAt_coe_of_le w hs0t] at this
    exact (hitFrom_le hrs0 hws).trans (by exact_mod_cast hs0t)

/-- The first hit of `a` is a stopping functional. -/
theorem isStopFun_hitFrom_zero (a : ℝ) :
    IsStopFun (fun w : C(ℝ≥0, ℝ) => hitFrom a 0 (w : ℝ≥0 → ℝ)) :=
  (isStopFun_zero).hitFrom a

/-- The end `d₁` of the first up-crossing interval is a stopping functional. -/
theorem isStopFun_upcrossEnd₁ (c : ℝ) :
    IsStopFun (fun w : C(ℝ≥0, ℝ) => upcrossEnd₁ c (w : ℝ≥0 → ℝ)) :=
  (isStopFun_hitFrom_zero 0).hitFrom c

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first zero time of an adapted process with continuous paths is a stopping time. -/
theorem isStoppingTime_hitFrom_zero {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hXad : StronglyAdapted 𝔽 X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (a : ℝ) :
    IsStoppingTime 𝔽 fun ω => hitFrom a 0 (fun t => X t ω) :=
  isStoppingTime_of_isStopFun hXad hXc (measurable_hitFrom measurable_const a)
    (isStopFun_hitFrom_zero a)

/-- The end `d₁` of the first up-crossing interval of an adapted process with continuous paths is
a stopping time. -/
theorem isStoppingTime_upcrossEnd₁ {𝔽 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {X : ℝ≥0 → Ω → ℝ} (hXad : StronglyAdapted 𝔽 X) (hXc : ∀ ω, Continuous fun t => X t ω)
    (c : ℝ) :
    IsStoppingTime 𝔽 fun ω => upcrossEnd₁ c (fun t => X t ω) :=
  isStoppingTime_of_isStopFun hXad hXc (measurable_upcrossEnd₁ c) (isStopFun_upcrossEnd₁ c)

end LatticeProb
