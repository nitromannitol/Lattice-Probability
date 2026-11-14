import LatticeProb.Analysis.ConeExcursionEndpoints
import LatticeProb.Analysis.ConeExitReversal

/-!
# Backward cone excursions

Strict excursions ending at a common time determine a backward cone interval
and identify the two backward exit times.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Two strict excursions ending at the same time give a backward cone
interval. The first and joint backward exit times are the two excursion
endpoints, provided those endpoints are not local minima. -/
theorem backward_cone_excursion_exit_times {X Y : ℝ → ℝ} {s a b : ℝ}
    (has : a < s) (hXa : X a = X s)
    (hX : ∀ t ∈ Ioo a s, X a < X t) (hXmin : ¬ IsLocalMin X a)
    (hbs : b < s) (hYb : Y b = Y s)
    (hY : ∀ t ∈ Ioo b s, Y b < Y t) (hYmin : ¬ IsLocalMin Y b)
    (hne : a ≠ b) :
    let v := sSup {t : ℝ | t < s ∧ (X t < X s ∨ Y t < Y s)}
    let u := sSup {t : ℝ | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
      (∃ r ∈ Icc t s, Y r < Y s)}
    v < s ∧ (∀ t ∈ Icc v s, X s ≤ X t ∧ Y s ≤ Y t) ∧
      u < v ∧ ((a = v ∧ b = u) ∨ (a = u ∧ b = v)) := by
  have hXmin' : ¬ IsLocalMin (fun t => X (-t)) (-a) := by
    intro h
    apply hXmin
    have hc := h.comp_continuous (g := fun t : ℝ => -t) (b := a)
      (by fun_prop)
    simpa only [Function.comp_def, neg_neg] using hc
  have hYmin' : ¬ IsLocalMin (fun t => Y (-t)) (-b) := by
    intro h
    apply hYmin
    have hc := h.comp_continuous (g := fun t : ℝ => -t) (b := b)
      (by fun_prop)
    simpa only [Function.comp_def, neg_neg] using hc
  have hX' : ∀ t ∈ Ioo (-s) (-a), X s < X (-t) := by
    intro t ht
    rw [← hXa]
    apply hX (-t)
    constructor <;> linarith [ht.1, ht.2]
  have hY' : ∀ t ∈ Ioo (-s) (-b), Y s < Y (-t) := by
    intro t ht
    rw [← hYb]
    apply hY (-t)
    constructor <;> linarith [ht.1, ht.2]
  have h := cone_excursion_exit_times (X := fun t => X (-t)) (Y := fun t => Y (-t))
    (s := -s) (a := -a) (b := -b)
    (by linarith) (by simpa using hXa.symm) (by simpa only [neg_neg] using hX') hXmin'
    (by linarith) (by simpa using hYb.symm) (by simpa only [neg_neg] using hY') hYmin'
  dsimp only at h ⊢
  simp only [neg_neg] at h
  rw [firstEitherDrop_rev, jointDrop_rev] at h
  rcases h with ⟨hv, hint, hlt, heq⟩
  have hne' : -a ≠ -b := by simpa using hne
  refine ⟨by linarith, ?_, by have := hlt hne'; linarith, ?_⟩
  · intro t ht
    have hh := hint (-t) (by constructor <;> linarith [ht.1, ht.2])
    simpa only [neg_neg] using hh
  · rcases heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith

end LatticeProb
