import LatticeProb.Analysis.ConeJointExitBarriers

/-!
# Endpoint of a joint backward exit

For continuous coordinates with earlier strict drops, one coordinate has equal
values at the joint backward exit and terminal time, and a closed barrier.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace LatticeProb

private theorem jointBackwardExit_endpoint_of_barrier {X Y : ℝ → ℝ} {s : ℝ}
    (hX : Continuous X)
    (hx : ∃ r < s, X r < X s) (hy : ∃ r < s, Y r < Y s)
    (hbar : ∀ t ∈ Ioc (coneJointExitBackward X Y s) s, X s ≤ X t) :
    X (coneJointExitBackward X Y s) = X s ∧
      ∀ t ∈ Icc (coneJointExitBackward X Y s) s, X s ≤ X t := by
  let A : Set ℝ := {t | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
    (∃ r ∈ Icc t s, Y r < Y s)}
  let B : Set ℝ := {r | r < s ∧ X r < X s}
  let a := coneJointExitBackward X Y s
  have ha : a = sSup A := rfl
  obtain ⟨x, hxs, hxX⟩ := hx
  obtain ⟨y, hys, hyY⟩ := hy
  have hAne : A.Nonempty := ⟨min x y, lt_of_le_of_lt (min_le_left x y) hxs,
    ⟨x, ⟨min_le_left x y, hxs.le⟩, hxX⟩,
    ⟨y, ⟨min_le_right x y, hys.le⟩, hyY⟩⟩
  have hAupper : BddAbove A := ⟨s, fun _ ht => ht.1.le⟩
  have hBne : B.Nonempty := ⟨x, hxs, hxX⟩
  have hBupper : BddAbove B := ⟨s, fun _ ht => ht.1.le⟩
  have has : a ≤ s := by
    rw [ha]
    exact csSup_le hAne (fun _ ht => ht.1.le)
  have hab : a ≤ sSup B := by
    rw [ha]
    apply csSup_le hAne
    intro t ht
    obtain ⟨r, hr, hxr⟩ := ht.2.1
    have hrs : r < s := lt_of_le_of_ne hr.2 (by
      intro h
      subst r
      exact lt_irrefl _ hxr)
    exact hr.1.trans (le_csSup hBupper ⟨hrs, hxr⟩)
  have hba : sSup B ≤ a := by
    apply csSup_le hBne
    intro r hr
    by_contra h
    have hlt : a < r := lt_of_not_ge h
    exact (not_lt_of_ge (hbar r ⟨hlt, hr.1.le⟩)) hr.2
  have hval : X a ≤ X s := by
    have hcl : closure B ⊆ {r | X r ≤ X s} :=
      closure_minimal (fun _ hr => hr.2.le) (isClosed_le hX continuous_const)
    have hb := hcl (csSup_mem_closure hBne hBupper)
    change X (sSup B) ≤ X s at hb
    rw [le_antisymm hba hab] at hb
    exact hb
  have hclosed : ∀ t ∈ Icc a s, X s ≤ X t := by
    by_cases h : a = s
    · intro t ht
      have ht' : t = s := le_antisymm ht.2 (h ▸ ht.1)
      subst t
      exact le_rfl
    · have hsub : Ioc a s ⊆ {t | X s ≤ X t} := hbar
      have hc := closure_minimal hsub (isClosed_le continuous_const hX)
      rw [closure_Ioc h] at hc
      exact hc
  exact ⟨le_antisymm hval (hclosed a ⟨le_rfl, has⟩), hclosed⟩

/-- A continuous pair with earlier strict drops has an equal-endpoint closed
barrier in at least one coordinate. -/
theorem jointBackwardExit_closed_barrier {X Y : ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hx : ∃ r < s, X r < X s) (hy : ∃ r < s, Y r < Y s) :
    (X (coneJointExitBackward X Y s) = X s ∧
      ∀ t ∈ Icc (coneJointExitBackward X Y s) s, X s ≤ X t) ∨
    (Y (coneJointExitBackward X Y s) = Y s ∧
      ∀ t ∈ Icc (coneJointExitBackward X Y s) s, Y s ≤ Y t) := by
  rcases jointBackwardExit_one_coordinate_barrier X Y s with h | h
  · exact Or.inl (jointBackwardExit_endpoint_of_barrier hX hx hy h)
  · have hswap : coneJointExitBackward Y X s = coneJointExitBackward X Y s := by
      simp only [coneJointExitBackward, and_comm]
    apply Or.inr
    rw [← hswap] at h ⊢
    exact jointBackwardExit_endpoint_of_barrier hY hy hx h

end LatticeProb
