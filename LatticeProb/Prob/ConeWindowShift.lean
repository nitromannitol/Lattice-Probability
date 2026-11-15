import LatticeProb.Prob.ConeWindowGeometry

/-! # Translation of cone-window witnesses -/

set_option autoImplicit false

open Set

namespace LatticeProb

private theorem coneWindowWitness_shift_forward
    (z z' : C(ℝ, ℝ) × C(ℝ, ℝ)) (l r x t d c₁ c₂ : ℝ)
    (h₁ : ∀ s, z'.1 (s + d) = z.1 s + c₁)
    (h₂ : ∀ s, z'.2 (s + d) = z.2 s + c₂)
    (h : ((z, x), t) ∈ coneWindowWitness l r) :
    ((z', x + d), t + d) ∈ coneWindowWitness (l + d) (r + d) := by
  rw [mem_coneWindowWitness_iff_least_start] at h ⊢
  rcases h with ⟨hlx, hxt, htr, a, hla, hax, ha⟩
  let S : Set ℝ := {s | s ≤ t ∧ ∀ v ∈ Icc s t,
    z.1 t ≤ z.1 v ∧ z.2 t ≤ z.2 v}
  let S' : Set ℝ := {s | s ≤ t + d ∧ ∀ v ∈ Icc s (t + d),
    z'.1 (t + d) ≤ z'.1 v ∧ z'.2 (t + d) ≤ z'.2 v}
  have hs (s : ℝ) : s ∈ S ↔ s + d ∈ S' := by
    constructor
    · rintro ⟨hst, hm⟩
      refine ⟨by linarith, ?_⟩
      intro v hv
      have hv' : v - d ∈ Icc s t := ⟨by linarith [hv.1], by linarith [hv.2]⟩
      have hm' := hm (v - d) hv'
      have h₁v := h₁ (v - d)
      have h₂v := h₂ (v - d)
      rw [sub_add_cancel] at h₁v h₂v
      rw [h₁ t, h₂ t, h₁v, h₂v]
      exact ⟨by linarith [hm'.1], by linarith [hm'.2]⟩
    · rintro ⟨hst, hm⟩
      refine ⟨by linarith, ?_⟩
      intro v hv
      have hv' : v + d ∈ Icc (s + d) (t + d) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
      have hm' := hm (v + d) hv'
      rw [h₁ t, h₂ t, h₁ v, h₂ v] at hm'
      exact ⟨by linarith [hm'.1], by linarith [hm'.2]⟩
  refine ⟨by linarith, by linarith, by linarith, a + d, by linarith, by linarith, ?_⟩
  change IsLeast S' (a + d)
  refine ⟨(hs a).mp ha.1, ?_⟩
  intro s hmem
  have hm : s - d ∈ S := (hs (s - d)).mpr (by simpa only [sub_add_cancel] using hmem)
  have := ha.2 hm
  linarith

/-- Simultaneous translation in time and separate vertical translations preserve
cone-window witnesses, including irrational time shifts. -/
theorem mem_coneWindowWitness_shift_iff
    (z z' : C(ℝ, ℝ) × C(ℝ, ℝ)) (l r x t d c₁ c₂ : ℝ)
    (h₁ : ∀ s, z'.1 (s + d) = z.1 s + c₁)
    (h₂ : ∀ s, z'.2 (s + d) = z.2 s + c₂) :
    ((z', x + d), t + d) ∈ coneWindowWitness (l + d) (r + d) ↔
      ((z, x), t) ∈ coneWindowWitness l r := by
  constructor
  · intro h
    have h₁' : ∀ s, z.1 (s + -d) = z'.1 s + -c₁ := by
      intro s
      have h := h₁ (s - d)
      rw [sub_add_cancel] at h
      simp only [← sub_eq_add_neg]
      linarith
    have h₂' : ∀ s, z.2 (s + -d) = z'.2 s + -c₂ := by
      intro s
      have h := h₂ (s - d)
      rw [sub_add_cancel] at h
      simp only [← sub_eq_add_neg]
      linarith
    have h' := coneWindowWitness_shift_forward z' z (l + d) (r + d) (x + d)
      (t + d) (-d) (-c₁) (-c₂) h₁' h₂' h
    simpa only [add_neg_cancel_right] using h'
  · exact coneWindowWitness_shift_forward z z' l r x t d c₁ c₂ h₁ h₂

/-- The projected coverage event has the same translation covariance. -/
theorem mem_coneWindowCoverage_shift_iff
    (z z' : C(ℝ, ℝ) × C(ℝ, ℝ)) (l r x d c₁ c₂ : ℝ)
    (h₁ : ∀ s, z'.1 (s + d) = z.1 s + c₁)
    (h₂ : ∀ s, z'.2 (s + d) = z.2 s + c₂) :
    (z', x + d) ∈ Prod.fst '' coneWindowWitness (l + d) (r + d) ↔
      (z, x) ∈ Prod.fst '' coneWindowWitness l r := by
  constructor
  · rintro ⟨⟨⟨w, y⟩, t⟩, ht, heq⟩
    have hw : w = z' := congrArg Prod.fst heq
    have hy : y = x + d := congrArg Prod.snd heq
    subst w
    subst y
    refine ⟨((z, x), t - d), ?_, rfl⟩
    apply (mem_coneWindowWitness_shift_iff z z' l r x (t - d) d c₁ c₂ h₁ h₂).mp
    simpa only [sub_add_cancel] using ht
  · rintro ⟨⟨⟨w, y⟩, t⟩, ht, heq⟩
    have hw : w = z := congrArg Prod.fst heq
    have hy : y = x := congrArg Prod.snd heq
    subst w
    subst y
    exact ⟨((z', x + d), t + d),
      (mem_coneWindowWitness_shift_iff z z' l r x t d c₁ c₂ h₁ h₂).mpr ht, rfl⟩

end LatticeProb
