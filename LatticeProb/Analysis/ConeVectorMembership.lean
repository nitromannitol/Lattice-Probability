import LatticeProb.Analysis.BackwardConeExcursion

/-!
# Cone vectors from strict excursions

Two distinct strict excursions with a common endpoint determine a two-coordinate
cone vector. The vector records the earlier exit and the cone time; the later
exit is the unrecorded terminal time.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- The first time after `s` when either coordinate drops below its value at `s`. -/
noncomputable def coneFirstExit (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf {t : ℝ | s < t ∧ (X t < X s ∨ Y t < Y s)}

/-- The first time after `s` by which both coordinates have dropped. -/
noncomputable def coneJointExit (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  sInf {t : ℝ | s < t ∧ (∃ r ∈ Icc s t, X r < X s) ∧
    (∃ r ∈ Icc s t, Y r < Y s)}

/-- The last time before `s` when either coordinate is below its value at `s`. -/
noncomputable def coneFirstExitBackward (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  sSup {t : ℝ | t < s ∧ (X t < X s ∨ Y t < Y s)}

/-- The last time before `s` by which both coordinates have dropped backwards. -/
noncomputable def coneJointExitBackward (X Y : ℝ → ℝ) (s : ℝ) : ℝ :=
  sSup {t : ℝ | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
    (∃ r ∈ Icc t s, Y r < Y s)}

/-- Forward cone vectors: the first coordinate is the earlier exit and the
second is the cone time. The later exit is strictly beyond the earlier exit. -/
noncomputable def forwardConeVectors (X Y : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 = coneFirstExit X Y p.2 ∧
    p.2 < coneFirstExit X Y p.2 ∧
    coneFirstExit X Y p.2 < coneJointExit X Y p.2 ∧
    ∀ t ∈ Icc p.2 (coneFirstExit X Y p.2), X p.2 ≤ X t ∧ Y p.2 ≤ Y t}

/-- Backward cone vectors: the first coordinate is the earlier exit and the
second is the cone time. The later exit is strictly beyond the earlier exit. -/
noncomputable def backwardConeVectors (X Y : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 = coneJointExitBackward X Y p.2 ∧
    coneJointExitBackward X Y p.2 < coneFirstExitBackward X Y p.2 ∧
    coneFirstExitBackward X Y p.2 < p.2 ∧
    ∀ t ∈ Icc (coneFirstExitBackward X Y p.2) p.2, X p.2 ≤ X t ∧ Y p.2 ≤ Y t}

/-- Two distinct forward excursions yield a cone vector, and their endpoints
are its first and joint exit times in some order. -/
theorem forwardConeVector_of_excursions {X Y : ℝ → ℝ} {s a b : ℝ}
    (hsa : s < a) (hXa : X s = X a)
    (hX : ∀ t ∈ Ioo s a, X s < X t) (hXmin : ¬ IsLocalMin X a)
    (hsb : s < b) (hYb : Y s = Y b)
    (hY : ∀ t ∈ Ioo s b, Y s < Y t) (hYmin : ¬ IsLocalMin Y b)
    (hne : a ≠ b) :
    (coneFirstExit X Y s, s) ∈ forwardConeVectors X Y ∧
      ((a = coneFirstExit X Y s ∧ b = coneJointExit X Y s) ∨
       (a = coneJointExit X Y s ∧ b = coneFirstExit X Y s)) := by
  have h := cone_excursion_exit_times hsa hXa hX hXmin hsb hYb hY hYmin
  change s < coneFirstExit X Y s ∧
    (∀ t ∈ Icc s (coneFirstExit X Y s), X s ≤ X t ∧ Y s ≤ Y t) ∧
    (a ≠ b → coneFirstExit X Y s < coneJointExit X Y s) ∧
    ((a = coneFirstExit X Y s ∧ b = coneJointExit X Y s) ∨
     (a = coneJointExit X Y s ∧ b = coneFirstExit X Y s)) at h
  exact ⟨⟨rfl, h.1, h.2.2.1 hne, h.2.1⟩, h.2.2.2⟩

/-- Two distinct backward excursions yield a cone vector, and their endpoints
are its first and joint backward exit times in some order. -/
theorem backwardConeVector_of_excursions {X Y : ℝ → ℝ} {s a b : ℝ}
    (has : a < s) (hXa : X a = X s)
    (hX : ∀ t ∈ Ioo a s, X a < X t) (hXmin : ¬ IsLocalMin X a)
    (hbs : b < s) (hYb : Y b = Y s)
    (hY : ∀ t ∈ Ioo b s, Y b < Y t) (hYmin : ¬ IsLocalMin Y b)
    (hne : a ≠ b) :
    (coneJointExitBackward X Y s, s) ∈ backwardConeVectors X Y ∧
      ((a = coneFirstExitBackward X Y s ∧ b = coneJointExitBackward X Y s) ∨
       (a = coneJointExitBackward X Y s ∧ b = coneFirstExitBackward X Y s)) := by
  have h := backward_cone_excursion_exit_times has hXa hX hXmin hbs hYb hY hYmin hne
  change coneFirstExitBackward X Y s < s ∧
    (∀ t ∈ Icc (coneFirstExitBackward X Y s) s, X s ≤ X t ∧ Y s ≤ Y t) ∧
    coneJointExitBackward X Y s < coneFirstExitBackward X Y s ∧
    ((a = coneFirstExitBackward X Y s ∧ b = coneJointExitBackward X Y s) ∨
     (a = coneJointExitBackward X Y s ∧ b = coneFirstExitBackward X Y s)) at h
  exact ⟨⟨rfl, h.2.2.1, h.1, h.2.1⟩, h.2.2.2⟩

end LatticeProb
