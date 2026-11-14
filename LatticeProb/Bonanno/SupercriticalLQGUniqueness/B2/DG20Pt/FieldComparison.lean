/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6Path

 




set_option autoImplicit false
noncomputable section

open LQGMetric.DDDF
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem crossLenIn_add_const (ξ : ℝ) (f : ℂ → ℝ) (c : ℝ) (U A B : Set ℂ) :
    crossLenIn ξ (fun x => f x + c) U A B =
      ENNReal.ofReal (Real.exp (ξ * c)) * crossLenIn ξ f U A B := by
  have h0 : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  simp only [crossLenIn, LQGMetric.DFGPS.lfppLen_add_const,
    ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]

 



theorem crossLenIn_compare_center (ξ : ℝ) (f g : ℂ → ℝ) (c δ : ℝ)
    (U A B : Set ℂ) (h : ∀ x ∈ U, |g x - c| ≤ δ) :
    crossLenIn ξ (fun x => f x + g x) U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * δ)) *
          (ENNReal.ofReal (Real.exp (ξ * c)) * crossLenIn ξ f U A B) ∧
      ENNReal.ofReal (Real.exp (ξ * c)) * crossLenIn ξ f U A B ≤
        ENNReal.ofReal (Real.exp (|ξ| * δ)) *
          crossLenIn ξ (fun x => f x + g x) U A B := by
  have hfg : ∀ x ∈ U, |(f x + g x) - (f x + c)| ≤ δ := by
    intro x hx
    simpa only [add_sub_add_left_eq_sub] using h x hx
  have hgf : ∀ x ∈ U, |(f x + c) - (f x + g x)| ≤ δ := by
    intro x hx
    rw [abs_sub_comm]
    exact hfg x hx
  constructor
  · simpa only [crossLenIn_add_const] using
      (crossLenIn_le_of_abs_sub_le (ξ := ξ) (f := fun x => f x + g x)
        (g := fun x => f x + c) (U := U) (A := A) (B := B) hfg)
  · simpa only [crossLenIn_add_const] using
      (crossLenIn_le_of_abs_sub_le (ξ := ξ) (f := fun x => f x + c)
        (g := fun x => f x + g x) (U := U) (A := A) (B := B) hgf)

 



theorem crossLenIn_mono_domain (ξ : ℝ) (f : ℂ → ℝ)
    {U' U A B : Set ℂ} (hU : U' ⊆ U) :
    crossLenIn ξ f U A B ≤ crossLenIn ξ f U' A B := by
  apply le_crossLenIn
  intro P hP
  apply crossLenIn_le_lfppLen
  obtain ⟨z, hz, w, hw, hpath, hinside⟩ := hP
  exact ⟨z, hz, w, hw, hpath, fun t ht => hU (hinside t ht)⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
