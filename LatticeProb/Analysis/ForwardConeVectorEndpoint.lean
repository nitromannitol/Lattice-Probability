import LatticeProb.Analysis.ConeVectorMembership

/-!
# Endpoint of a forward cone vector

Continuity identifies an equal-endpoint barrier at the first strict exit.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace LatticeProb

/-- If either coordinate eventually drops, the first exit of a forward cone
vector is an equal-endpoint barrier for at least one coordinate. -/
theorem forwardConeVector_closed_barrier {X Y : ℝ → ℝ} {a s : ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hdrop : ∃ t > s, X t < X s ∨ Y t < Y s)
    (hvec : (a, s) ∈ forwardConeVectors X Y) :
    (X a = X s ∧ ∀ t ∈ Icc s a, X s ≤ X t) ∨
    (Y a = Y s ∧ ∀ t ∈ Icc s a, Y s ≤ Y t) := by
  rcases hvec with ⟨ha, hs, _, hbar⟩
  let A : Set ℝ := {t | s < t ∧ (X t < X s ∨ Y t < Y s)}
  have hne : A.Nonempty := hdrop
  have hlower : BddBelow A := ⟨s, fun _ ht => ht.1.le⟩
  have hclosed : IsClosed ({t : ℝ | X t ≤ X s} ∪ {t : ℝ | Y t ≤ Y s}) :=
    (isClosed_le hX continuous_const).union (isClosed_le hY continuous_const)
  have hsubset : A ⊆ {t : ℝ | X t ≤ X s} ∪ {t : ℝ | Y t ≤ Y s} := by
    intro t ht
    rcases ht.2 with hx | hy
    · exact Or.inl hx.le
    · exact Or.inr hy.le
  have hmem := (closure_minimal hsubset hclosed) (csInf_mem_closure hne hlower)
  change X (sInf A) ≤ X s ∨ Y (sInf A) ≤ Y s at hmem
  change a = sInf A at ha
  change s < sInf A at hs
  change ∀ t ∈ Icc s (sInf A), X s ≤ X t ∧ Y s ≤ Y t at hbar
  rw [← ha] at hmem hs hbar
  have hends := hbar a ⟨hs.le, le_rfl⟩
  rcases hmem with hx | hy
  · exact Or.inl ⟨le_antisymm hx hends.1, fun t ht => (hbar t ht).1⟩
  · exact Or.inr ⟨le_antisymm hy hends.2, fun t ht => (hbar t ht).2⟩

end LatticeProb
