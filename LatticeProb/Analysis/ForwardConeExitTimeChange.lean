import LatticeProb.Analysis.ConeVectorMembership

/-! # Forward cone exits under increasing time changes -/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- An increasing change of time transports the first strict drop in either
coordinate, provided such a drop exists. Vertical shifts are immaterial. -/
theorem coneFirstExit_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d s : ℝ)
    (hne : ∃ t > e s, X t < X (e s) ∨ Y t < Y (e s)) :
    coneFirstExit (fun t => X (e t) - c) (fun t => Y (e t) - d) s =
      e.symm (coneFirstExit X Y (e s)) := by
  let A : Set ℝ := {t | e s < t ∧ (X t < X (e s) ∨ Y t < Y (e s))}
  have hA : A.Nonempty := hne
  have hbound : BddBelow A := ⟨e s, fun _ ht => ht.1.le⟩
  have hset : {t : ℝ | s < t ∧
      (X (e t) - c < X (e s) - c ∨ Y (e t) - d < Y (e s) - d)} =
      e.symm '' A := by
    ext t
    constructor
    · intro ht
      refine ⟨e t, ?_, e.symm_apply_apply t⟩
      exact ⟨e.strictMono ht.1, by simpa only [sub_lt_sub_iff_right] using ht.2⟩
    · rintro ⟨u, hu, rfl⟩
      have hu' : s < e.symm u := by
        apply e.lt_iff_lt.mp
        simpa only [e.apply_symm_apply] using hu.1
      exact ⟨hu', by simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hu.2⟩
  unfold coneFirstExit
  rw [hset]
  exact (e.symm.map_csInf' hA hbound).symm

/-- An increasing change of time transports the joint forward exit when both
coordinates have made a strict drop after the reference time. -/
theorem coneJointExit_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d s : ℝ)
    (hne : ∃ t > e s, (∃ r ∈ Icc (e s) t, X r < X (e s)) ∧
      (∃ r ∈ Icc (e s) t, Y r < Y (e s))) :
    coneJointExit (fun t => X (e t) - c) (fun t => Y (e t) - d) s =
      e.symm (coneJointExit X Y (e s)) := by
  let A : Set ℝ := {t | e s < t ∧ (∃ r ∈ Icc (e s) t, X r < X (e s)) ∧
    (∃ r ∈ Icc (e s) t, Y r < Y (e s))}
  have hA : A.Nonempty := hne
  have hbound : BddBelow A := ⟨e s, fun _ ht => ht.1.le⟩
  have hset : {t : ℝ | s < t ∧
      (∃ r ∈ Icc s t, X (e r) - c < X (e s) - c) ∧
      (∃ r ∈ Icc s t, Y (e r) - d < Y (e s) - d)} = e.symm '' A := by
    ext t
    constructor
    · rintro ⟨ht, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩
      refine ⟨e t, ⟨e.strictMono ht, ⟨e x, ⟨e.monotone hx.1, e.monotone hx.2⟩, ?_⟩,
        ⟨e y, ⟨e.monotone hy.1, e.monotone hy.2⟩, ?_⟩⟩, e.symm_apply_apply t⟩
      · simpa only [sub_lt_sub_iff_right] using hx'
      · simpa only [sub_lt_sub_iff_right] using hy'
    · rintro ⟨u, ⟨hu, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩, rfl⟩
      refine ⟨?_, ⟨e.symm x, ⟨?_, e.symm.monotone hx.2⟩, ?_⟩,
        ⟨e.symm y, ⟨?_, e.symm.monotone hy.2⟩, ?_⟩⟩
      · simpa only [e.symm_apply_apply] using e.symm.strictMono hu
      · simpa only [e.symm_apply_apply] using e.symm.monotone hx.1
      · simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hx'
      · simpa only [e.symm_apply_apply] using e.symm.monotone hy.1
      · simpa only [e.apply_symm_apply, sub_lt_sub_iff_right] using hy'
  unfold coneJointExit
  rw [hset]
  exact (e.symm.map_csInf' hA hbound).symm

/-- Forward cone-vector membership is preserved by an increasing change of
 time and vertical shifts, provided both coordinates subsequently drop. -/
theorem mem_forwardConeVectors_timeChange (X Y : ℝ → ℝ) (e : ℝ ≃o ℝ)
    (c d a s : ℝ)
    (hne : ∃ t > e s, (∃ r ∈ Icc (e s) t, X r < X (e s)) ∧
      (∃ r ∈ Icc (e s) t, Y r < Y (e s))) :
    (a, s) ∈ forwardConeVectors (fun t => X (e t) - c) (fun t => Y (e t) - d) ↔
      (e a, e s) ∈ forwardConeVectors X Y := by
  have hfirst : ∃ t > e s, X t < X (e s) ∨ Y t < Y (e s) := by
    obtain ⟨t, ht, ⟨x, hx, hx'⟩, hy⟩ := hne
    have hxs : e s < x := by
      by_contra h
      have heq : x = e s := le_antisymm (le_of_not_gt h) hx.1
      rw [heq] at hx'
      exact (lt_irrefl _) hx'
    exact ⟨x, hxs, Or.inl hx'⟩
  have hf := coneFirstExit_timeChange X Y e c d s hfirst
  have hj := coneJointExit_timeChange X Y e c d s hne
  have hbar : (∀ t ∈ Icc s (e.symm (coneFirstExit X Y (e s))),
        X (e s) - c ≤ X (e t) - c ∧ Y (e s) - d ≤ Y (e t) - d) ↔
      ∀ t ∈ Icc (e s) (coneFirstExit X Y (e s)),
        X (e s) ≤ X t ∧ Y (e s) ≤ Y t := by
    constructor
    · intro h t ht
      have ht' : e.symm t ∈ Icc s (e.symm (coneFirstExit X Y (e s))) :=
        ⟨by simpa only [e.symm_apply_apply] using e.symm.monotone ht.1, e.symm.monotone ht.2⟩
      simpa only [e.apply_symm_apply, sub_le_sub_iff_right] using h (e.symm t) ht'
    · intro h t ht
      have ht' : e t ∈ Icc (e s) (coneFirstExit X Y (e s)) :=
        ⟨e.monotone ht.1, by simpa only [e.apply_symm_apply] using e.monotone ht.2⟩
      simpa only [sub_le_sub_iff_right] using h (e t) ht'
  change (a = coneFirstExit _ _ s ∧ s < coneFirstExit _ _ s ∧
      coneFirstExit _ _ s < coneJointExit _ _ s ∧ _) ↔
    (e a = coneFirstExit X Y (e s) ∧ e s < coneFirstExit X Y (e s) ∧
      coneFirstExit X Y (e s) < coneJointExit X Y (e s) ∧ _)
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
    · simpa only [e.symm_apply_apply] using e.symm.strictMono h1
    · exact e.symm.strictMono h2

end LatticeProb
