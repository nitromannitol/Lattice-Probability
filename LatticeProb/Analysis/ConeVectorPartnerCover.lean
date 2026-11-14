import LatticeProb.Analysis.ConeVectorMembership

/-!
# Cone vectors covering excursion partners

Both endpoints of two distinct excursions from a common time are encoded by
cone vectors of the original and time-reversed paths.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace LatticeProb

/-- For two strict excursions from a common apex, each partner is encoded
by a forward vector or by a backward vector of the time-reversed paths. -/
theorem forward_excursion_partners_mem_coneVectors {X Y : ℝ → ℝ} {s a b : ℝ}
    (hsa : s < a) (hXa : X s = X a)
    (hX : ∀ t ∈ Ioo s a, X s < X t) (hXmin : ¬ IsLocalMin X a)
    (hsb : s < b) (hYb : Y s = Y b)
    (hY : ∀ t ∈ Ioo s b, Y s < Y t) (hYmin : ¬ IsLocalMin Y b)
    (hne : a ≠ b) :
    ((a, s) ∈ forwardConeVectors X Y ∨
      (-a, -s) ∈ backwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) ∧
    ((b, s) ∈ forwardConeVectors X Y ∨
      (-b, -s) ∈ backwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) := by
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
  have hX' : ∀ t ∈ Ioo (-a) (-s), X a < X (-t) := by
    intro t ht
    rw [← hXa]
    apply hX (-t)
    constructor <;> linarith [ht.1, ht.2]
  have hY' : ∀ t ∈ Ioo (-b) (-s), Y b < Y (-t) := by
    intro t ht
    rw [← hYb]
    apply hY (-t)
    constructor <;> linarith [ht.1, ht.2]
  have hf := forwardConeVector_of_excursions hsa hXa hX hXmin hsb hYb hY hYmin hne
  have hr := backwardConeVector_of_excursions (X := fun t => X (-t))
    (Y := fun t => Y (-t)) (s := -s) (a := -a) (b := -b)
    (by linarith) (by simpa using hXa.symm) (by simpa only [neg_neg] using hX') hXmin'
    (by linarith) (by simpa using hYb.symm) (by simpa only [neg_neg] using hY') hYmin'
    (by simpa using hne)
  have hflt := hf.1.2.2.1
  have hrlt := hr.1.2.1
  rcases hf.2 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hr.2 with ⟨hra, hrb⟩ | ⟨hra, hrb⟩
  · exact ⟨Or.inl (ha ▸ hf.1), Or.inr (hrb ▸ hr.1)⟩
  · exfalso; linarith
  · exfalso; linarith
  · exact ⟨Or.inr (hra ▸ hr.1), Or.inl (hb ▸ hf.1)⟩

end LatticeProb
