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

end LatticeProb
