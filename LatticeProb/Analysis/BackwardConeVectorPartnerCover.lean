import LatticeProb.Analysis.ConeVectorMembership

/-!
# Cone vectors covering backward excursion partners

The endpoints of two distinct backward excursions are encoded by cone vectors
of the original and time-reversed paths.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- Each partner of two strict backward excursions is encoded by a backward
vector or by a forward vector of the time-reversed paths. -/
theorem backward_excursion_partners_mem_coneVectors {X Y : ℝ → ℝ} {s a b : ℝ}
    (has : a < s) (hXa : X a = X s)
    (hX : ∀ t ∈ Ioo a s, X a < X t) (hXmin : ¬ IsLocalMin X a)
    (hbs : b < s) (hYb : Y b = Y s)
    (hY : ∀ t ∈ Ioo b s, Y b < Y t) (hYmin : ¬ IsLocalMin Y b)
    (hne : a ≠ b) :
    ((a, s) ∈ backwardConeVectors X Y ∨
      (-a, -s) ∈ forwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) ∧
    ((b, s) ∈ backwardConeVectors X Y ∨
      (-b, -s) ∈ forwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) := by
  have hXmin' : ¬ IsLocalMin (fun t => X (-t)) (-a) := by
    intro h
    apply hXmin
    have hc := h.comp_continuous (g := fun t : ℝ => -t) (b := a) (by fun_prop)
    simpa only [Function.comp_def, neg_neg] using hc
  have hYmin' : ¬ IsLocalMin (fun t => Y (-t)) (-b) := by
    intro h
    apply hYmin
    have hc := h.comp_continuous (g := fun t : ℝ => -t) (b := b) (by fun_prop)
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
  have hb := backwardConeVector_of_excursions has hXa hX hXmin hbs hYb hY hYmin hne
  have hf := forwardConeVector_of_excursions (X := fun t => X (-t))
    (Y := fun t => Y (-t)) (s := -s) (a := -a) (b := -b)
    (by linarith) (by simpa using hXa.symm) (by simpa only [neg_neg] using hX') hXmin'
    (by linarith) (by simpa using hYb.symm) (by simpa only [neg_neg] using hY') hYmin'
    (by simpa using hne)
  have hblt := hb.1.2.1
  have hflt := hf.1.2.2.1
  rcases hb.2 with ⟨ha, hb'⟩ | ⟨ha, hb'⟩ <;>
    rcases hf.2 with ⟨hra, hrb⟩ | ⟨hra, hrb⟩
  · exact ⟨Or.inr (hra ▸ hf.1), Or.inl (hb' ▸ hb.1)⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨Or.inl (ha ▸ hb.1), Or.inr (hrb ▸ hf.1)⟩

end LatticeProb
