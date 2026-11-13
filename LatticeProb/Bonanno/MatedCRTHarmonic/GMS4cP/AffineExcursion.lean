/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.AffineExcursion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.ExcursionCoverage

/-!
# Excursion segments under an affine change of space and time

Source: the frozen `MatedCRT.excursionSegment`, `entryBefore`, `exitAfter`, `firstHit` and the
affine re-rooting `MatedCRT.affineReroot` of the coordinate-change clause (IG1).

For a continuous surjective transient curve `c`, a bounded open `U`, `z ∈ ℂ`, `s > 0`, any time shift `τ`, and the
curve `c'(t) = s⁻¹ (c(τ + s² t) − z)`, the excursion of `c'` into `U' = {v | z + s v ∈ U}` through `p` is the
affine image of the excursion of `c` into `U` through `z + s p`:
`excursionSegment c' U' p u = s⁻¹ (excursionSegment c U (z + s p) (s² u) − z)` (`excursionSegment_affine`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.GMS4c

variable {c c' : C(ℝ, ℂ)} {U : Set ℂ} {z : ℂ} {s τ : ℝ}

/-- The affine relation between the two curves, solved for `c`. -/
theorem affine_inv (hs : 0 < s) (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z)) (t : ℝ) :
    z + (s : ℂ) * c' t = c (τ + s ^ 2 * t) := by
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  rw [hc', ← mul_assoc, mul_inv_cancel₀ hs', one_mul]
  ring

theorem mem_affine_iff (hs : 0 < s) (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z))
    (t : ℝ) : c' t ∈ {v : ℂ | z + (s : ℂ) * v ∈ U} ↔ c (τ + s ^ 2 * t) ∈ U := by
  simp only [mem_ofPred_eq, affine_inv hs hc' t]

theorem time_affine_inv (hs : 0 < s) (t : ℝ) : τ + s ^ 2 * ((t - τ) / s ^ 2) = t := by
  have : s ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- First hitting times under the affine change. -/
theorem firstHit_affine (hsurj : Function.Surjective c)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hs : 0 < s)
    (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z)) (p : ℂ) :
    firstHit c' p = (firstHit c (z + s * p) - τ) / s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  set T := firstHit c (z + s * p)
  have hT : c T = z + s * p := GMS4b.hitTime_spec c.continuous htr (hsurj _)
  have hleast : IsLeast {t : ℝ | c' t = p} ((T - τ) / s ^ 2) := by
    constructor
    · have h := affine_inv hs hc' ((T - τ) / s ^ 2)
      rw [time_affine_inv hs, hT] at h
      have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
      exact mul_left_cancel₀ hs' (add_left_cancel h)
    · intro t ht
      have h := affine_inv hs hc' t
      rw [show c' t = p from ht] at h
      have hle := firstHit_le_visit htr h.symm
      rw [div_le_iff₀ hs2]
      linarith
  exact hleast.csInf_eq

/-- Entrance times under the affine change. -/
theorem entryBefore_affine (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hs : 0 < s)
    (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z)) {p : ℂ} (hp : z + s * p ∈ U) :
    entryBefore c' {v : ℂ | z + (s : ℂ) * v ∈ U} p =
      (entryBefore c U (z + s * p) - τ) / s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  obtain ⟨hex, hT⟩ := isExcursion_entry_exit hU hUb hsurj htr hp
  set e := entryBefore c U (z + s * p)
  set T := firstHit c (z + s * p)
  have hfh := firstHit_affine hsurj htr hs hc' p
  have hgreat : IsGreatest {t : ℝ | t ≤ firstHit c' p ∧
      c' t ∉ {v : ℂ | z + (s : ℂ) * v ∈ U}} ((e - τ) / s ^ 2) := by
    constructor
    · refine ⟨?_, ?_⟩
      · rw [hfh]
        exact div_le_div_of_nonneg_right (by linarith [hT.1]) hs2.le
      · rw [mem_affine_iff hs hc', time_affine_inv hs]
        exact hex.left
    · rintro t ⟨ht, hnot⟩
      rw [mem_affine_iff hs hc'] at hnot
      rw [hfh, le_div_iff₀ hs2] at ht
      rw [le_div_iff₀ hs2]
      by_contra hlt
      push Not at hlt
      exact hnot (hex.inside _ ⟨by linarith, by linarith [hT.2]⟩)
  exact hgreat.csSup_eq

/-- Exit times under the affine change. -/
theorem exitAfter_affine (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hs : 0 < s)
    (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z)) {p : ℂ} (hp : z + s * p ∈ U) :
    exitAfter c' {v : ℂ | z + (s : ℂ) * v ∈ U} p =
      (exitAfter c U (z + s * p) - τ) / s ^ 2 := by
  have hs2 : 0 < s ^ 2 := by positivity
  obtain ⟨hex, hT⟩ := isExcursion_entry_exit hU hUb hsurj htr hp
  set x := exitAfter c U (z + s * p)
  have hfh := firstHit_affine hsurj htr hs hc' p
  have hleast : IsLeast {t : ℝ | firstHit c' p ≤ t ∧
      c' t ∉ {v : ℂ | z + (s : ℂ) * v ∈ U}} ((x - τ) / s ^ 2) := by
    constructor
    · refine ⟨?_, ?_⟩
      · rw [hfh]
        exact div_le_div_of_nonneg_right (by linarith [hT.2]) hs2.le
      · rw [mem_affine_iff hs hc', time_affine_inv hs]
        exact hex.right
    · rintro t ⟨ht, hnot⟩
      rw [mem_affine_iff hs hc'] at hnot
      rw [hfh, div_le_iff₀ hs2] at ht
      rw [div_le_iff₀ hs2]
      by_contra hlt
      push Not at hlt
      exact hnot (hex.inside _ ⟨by linarith [hT.1], by linarith⟩)
  exact hleast.csInf_eq

/-- **Excursion segments under the affine change.** -/
theorem excursionSegment_affine (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hs : 0 < s)
    (hc' : ∀ t, c' t = (s : ℂ)⁻¹ * (c (τ + s ^ 2 * t) - z)) {p : ℂ} (hp : z + s * p ∈ U)
    (u : ℝ) :
    excursionSegment c' {v : ℂ | z + (s : ℂ) * v ∈ U} p u =
      (s : ℂ)⁻¹ * (excursionSegment c U (z + s * p) (s ^ 2 * u) - z) := by
  have hs2 : 0 < s ^ 2 := by positivity
  rw [excursionSegment, excursionSegment, entryBefore_affine hU hUb hsurj htr hs hc' hp,
    exitAfter_affine hU hUb hsurj htr hs hc' hp, hc']
  congr 2
  set e := entryBefore c U (z + s * p)
  set x := exitAfter c U (z + s * p)
  have hdiv : (x - τ) / s ^ 2 - (e - τ) / s ^ 2 = (x - e) / s ^ 2 := by ring
  rw [hdiv, mul_add, mul_max_of_nonneg _ _ hs2.le, mul_min_of_nonneg _ _ hs2.le, mul_zero,
    mul_div_cancel₀ _ hs2.ne', mul_div_cancel₀ _ hs2.ne']
  ring_nf

/-- The re-rooted curve of the coordinate-change clause at rotation `0`. -/
theorem affineReroot_zero_apply (z : ℂ) (s : ℝ) (c : C(ℝ, ℂ)) (t : ℝ) :
    affineReroot z s 0 c t = (s : ℂ)⁻¹ * (c (firstHit c z + s ^ 2 * t) - z) := by
  simp [affineReroot]

/-- The inverse form used for reconstruction: the excursion of `c` through `z + s p` is read from the
excursion of the re-rooted curve through `p`. -/
theorem excursionSegment_of_affineReroot (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hsurj : Function.Surjective c) (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hs : 0 < s)
    {p : ℂ} (hp : z + s * p ∈ U) (u : ℝ) :
    (s : ℂ) * excursionSegment (affineReroot z s 0 c) {v : ℂ | z + (s : ℂ) * v ∈ U} p
        (u / s ^ 2) + z = excursionSegment c U (z + s * p) u := by
  have hs2 : 0 < s ^ 2 := by positivity
  have hs' : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs.ne'
  rw [excursionSegment_affine hU hUb hsurj htr hs (affineReroot_zero_apply z s c) hp,
    mul_div_cancel₀ _ hs2.ne', ← mul_assoc, mul_inv_cancel₀ hs', one_mul]
  ring

end MatedCRTHarmonic.GMS4cP
