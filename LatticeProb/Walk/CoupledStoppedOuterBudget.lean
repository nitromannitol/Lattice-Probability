import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianActiveTransfer
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteProbability

/-! # Coupled stopping and outer-endpoint failure -/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

/-- If stopping puts the Brownian pasted endpoint outside a set, then the
joint failure of walk stopping or outer exit is bounded by the Brownian active
tail and the probability of an unmatched excursion pair. -/
theorem coupled_stopping_outer_failure_le {d n : ℕ} {V : Type*}
    (pos : V → Euc d) (m : ℕ → ℕ) (E : ∀ i, Fin (m i) → Set (Euc d))
    (a : ℝ) (P : TimePartition n) (Q : Set (Euc d))
    (ρ : Measure ((ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d))))
    (hendpoint : ∀ᵐ x ∂ρ, (x.2 n).1 = true → pastedBrownianCurve P x.2 1 ∉ Q) :
    ρ {x | (x.1 n).1 = false ∨ pastedBrownianCurve P x.2 1 ∈ Q} ≤
      ρ.snd (sequenceActive n) +
        ρ {x | ∃ i ≤ n, (x.1 i, x.2 i) ∉ goodExcursionPair pos (E i) a} := by
  let A := {x : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) | (x.2 n).1 = false}
  let F := {x : (ℕ → Bool × ClockedWalkExcursion d) ×
      (ℕ → Bool × C(unitInterval, Euc d)) |
        ∃ i ≤ n, (x.1 i, x.2 i) ∉ goodExcursionPair pos (E i) a}
  have hsub : ∀ᵐ x ∂ρ,
      x ∈ {x | (x.1 n).1 = false ∨ pastedBrownianCurve P x.2 1 ∈ Q} → x ∈ A ∪ F := by
    filter_upwards [hendpoint] with x hx hbad
    by_cases hb : (x.2 n).1 = false
    · exact Or.inl hb
    · have hbt : (x.2 n).1 = true := Bool.eq_true_of_not_eq_false hb
      have hout := hx hbt
      have hw : (x.1 n).1 = false := hbad.resolve_right hout
      right
      by_contra hF
      have hg : (x.1 n, x.2 n) ∈ goodExcursionPair pos (E n) a := by
        by_contra hng
        exact hF ⟨n, le_rfl, hng⟩
      have hflags := goodExcursionPair_flags pos (E n) a hg
      rw [hw, hbt] at hflags
      cases hflags
  calc
    _ ≤ ρ (A ∪ F) := measure_mono_ae hsub
    _ ≤ ρ A + ρ F := measure_union_le _ _
    _ = _ := by
      change ρ (Prod.snd ⁻¹' sequenceActive n) + ρ F = _
      rw [Measure.snd_apply (measurableSet_sequenceActive n)]

end LatticeProb
end
