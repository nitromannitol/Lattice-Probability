import LatticeProb.Analysis.ConeVectorMembership

/-! # Backward cone exits under increasing time changes -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An increasing change of time transports the last strict drop in either
coordinate, provided such a drop exists. Vertical shifts are immaterial. -/
theorem coneFirstExitBackward_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d s : ℝ)
    (hne : ∃ t < e s, X t < X (e s) ∨ Y t < Y (e s)) :
    coneFirstExitBackward (fun t => X (e t) - c) (fun t => Y (e t) - d) s =
      e.symm (coneFirstExitBackward X Y (e s)) := by
  let A : Set ℝ := {t | t < e s ∧ (X t < X (e s) ∨ Y t < Y (e s))}
  have hA : A.Nonempty := hne
  have hbound : BddAbove A := ⟨e s, fun _ ht => ht.1.le⟩
  have hset : {t : ℝ | t < s ∧
      (X (e t) - c < X (e s) - c ∨ Y (e t) - d < Y (e s) - d)} =
      e.symm '' A := by
    ext t
    constructor
    · intro ht
      refine ⟨e t, ?_, e.symm_apply_apply t⟩
      exact ⟨e.strictMono ht.1, by simpa only [sub_lt_sub_iff_right] using ht.2⟩
    · rintro ⟨u, hu, rfl⟩
      have hu' : e.symm u < s := by
        apply e.lt_iff_lt.mp
        simpa only [e.apply_symm_apply] using hu.1
      exact ⟨hu', by simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hu.2⟩
  unfold coneFirstExitBackward
  rw [hset]
  exact (e.symm.map_csSup' hA hbound).symm

/-- An increasing change of time transports the joint backward exit when both
coordinates have made a strict drop before the reference time. -/
theorem coneJointExitBackward_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d s : ℝ)
    (hne : ∃ t < e s, (∃ r ∈ Icc t (e s), X r < X (e s)) ∧
      (∃ r ∈ Icc t (e s), Y r < Y (e s))) :
    coneJointExitBackward (fun t => X (e t) - c) (fun t => Y (e t) - d) s =
      e.symm (coneJointExitBackward X Y (e s)) := by
  let A : Set ℝ := {t | t < e s ∧ (∃ r ∈ Icc t (e s), X r < X (e s)) ∧
    (∃ r ∈ Icc t (e s), Y r < Y (e s))}
  have hA : A.Nonempty := hne
  have hbound : BddAbove A := ⟨e s, fun _ ht => ht.1.le⟩
  have hset : {t : ℝ | t < s ∧
      (∃ r ∈ Icc t s, X (e r) - c < X (e s) - c) ∧
      (∃ r ∈ Icc t s, Y (e r) - d < Y (e s) - d)} = e.symm '' A := by
    ext t
    constructor
    · rintro ⟨ht, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩
      refine ⟨e t, ⟨e.strictMono ht, ⟨e x, ⟨e.monotone hx.1, e.monotone hx.2⟩, ?_⟩,
        ⟨e y, ⟨e.monotone hy.1, e.monotone hy.2⟩, ?_⟩⟩, e.symm_apply_apply t⟩
      · simpa only [sub_lt_sub_iff_right] using hx'
      · simpa only [sub_lt_sub_iff_right] using hy'
    · rintro ⟨u, ⟨hu, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩, rfl⟩
      refine ⟨?_, ⟨e.symm x, ⟨e.symm.monotone hx.1, ?_⟩, ?_⟩,
        ⟨e.symm y, ⟨e.symm.monotone hy.1, ?_⟩, ?_⟩⟩
      · simpa only [e.symm_apply_apply] using e.symm.strictMono hu
      · simpa only [e.symm_apply_apply] using e.symm.monotone hx.2
      · simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hx'
      · simpa only [e.symm_apply_apply] using e.symm.monotone hy.2
      · simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hy'
  unfold coneJointExitBackward
  rw [hset]
  exact (e.symm.map_csSup' hA hbound).symm

/-- Backward cone-vector membership is preserved by an increasing change of
 time and vertical shifts, provided both coordinates have previously dropped. -/
theorem mem_backwardConeVectors_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d a s : ℝ)
    (hne : ∃ t < e s, (∃ r ∈ Icc t (e s), X r < X (e s)) ∧
      (∃ r ∈ Icc t (e s), Y r < Y (e s))) :
    (a, s) ∈ backwardConeVectors (fun t => X (e t) - c) (fun t => Y (e t) - d) ↔
      (e a, e s) ∈ backwardConeVectors X Y := by
  have hfirst : ∃ t < e s, X t < X (e s) ∨ Y t < Y (e s) := by
    obtain ⟨t, ht, ⟨x, hx, hx'⟩, hy⟩ := hne
    have hxs : x < e s := by
      by_contra h
      have heq : x = e s := le_antisymm hx.2 (le_of_not_gt h)
      rw [heq] at hx'
      exact (lt_irrefl _) hx'
    exact ⟨x, hxs, Or.inl hx'⟩
  have hf := coneFirstExitBackward_timeChange X Y e c d s hfirst
  have hj := coneJointExitBackward_timeChange X Y e c d s hne
  have hbar : (∀ t ∈ Icc (e.symm (coneFirstExitBackward X Y (e s))) s,
        X (e s) - c ≤ X (e t) - c ∧ Y (e s) - d ≤ Y (e t) - d) ↔
      ∀ t ∈ Icc (coneFirstExitBackward X Y (e s)) (e s),
        X (e s) ≤ X t ∧ Y (e s) ≤ Y t := by
    constructor
    · intro h t ht
      have ht' : e.symm t ∈ Icc (e.symm (coneFirstExitBackward X Y (e s))) s :=
        ⟨e.symm.monotone ht.1, by simpa only [e.symm_apply_apply] using e.symm.monotone ht.2⟩
      simpa only [e.apply_symm_apply, sub_le_sub_iff_right] using h (e.symm t) ht'
    · intro h t ht
      have ht' : e t ∈ Icc (coneFirstExitBackward X Y (e s)) (e s) :=
        ⟨by simpa only [e.apply_symm_apply] using e.monotone ht.1, e.monotone ht.2⟩
      simpa only [sub_le_sub_iff_right] using h (e t) ht'
  change (a = coneJointExitBackward _ _ s ∧
      coneJointExitBackward _ _ s < coneFirstExitBackward _ _ s ∧
      coneFirstExitBackward _ _ s < s ∧ _) ↔
    (e a = coneJointExitBackward X Y (e s) ∧
      coneJointExitBackward X Y (e s) < coneFirstExitBackward X Y (e s) ∧
      coneFirstExitBackward X Y (e s) < e s ∧ _)
  rw [hf, hj, hbar]
  constructor
  · rintro ⟨ha, h1, h2, hb⟩
    refine ⟨?_, ?_, ?_, hb⟩
    · simpa only [e.apply_symm_apply] using congrArg e ha
    · simpa only [e.apply_symm_apply] using e.strictMono h1
    · simpa only [e.apply_symm_apply] using e.strictMono h2
  · rintro ⟨ha, h1, h2, hb⟩
    refine ⟨?_, ?_, ?_, hb⟩
    · simpa only [e.symm_apply_apply] using congrArg e.symm ha
    · exact e.symm.strictMono h1
    · simpa only [e.symm_apply_apply] using e.symm.strictMono h2

end LatticeProb
