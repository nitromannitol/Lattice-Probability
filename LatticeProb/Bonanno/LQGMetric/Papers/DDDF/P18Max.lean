/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Max at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Rigid
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax

/-!
# DDDF Prop 2 on the rectangle `R_{3,1}` (for DDDF Prop 18, Step 2) (task P2-DDDF16)

DDDF (arXiv:1904.08021, `tightness.tex` l. 915–919, proof of Prop 18, Step 2) bound
`P(max_{R_{3,1}} φ_{0,m} ≥ Cm + s√m)` "by taking `a = C + s m^{-1/2}` in Proposition 2", which is
stated on `[0,1]²` (`prop2_tail`). We cover `R_{3,1} = [0,3] × [0,1]` by the three unit squares
`j + [0,1]²`, `j = 0, 1, 2`, and use that `x ↦ φ_{0,m}(x + j)` is the field `φ_{0,m}` of the
translated white noise `W ∘ T_j` (`phi_motion`, `isWhiteNoise_isometry`, P18Rigid.lean), so
`prop2_tail` applies to it verbatim; a union bound gives the factor `3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma exists_shift_mem_ferniqueBox {z : ℂ} (hz : z ∈ (rectAB 3 1).toSet) :
    ∃ j : Fin 3, z - ((j : ℕ) : ℂ) ∈ ferniqueBox 0 1 := by
  simp only [MarkedRect.toSet, rectAB, Complex.mem_reProdIm, mem_Icc, zero_add] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  simp only [ferniqueBox, Complex.mem_reProdIm, mem_Icc, Complex.sub_re, Complex.sub_im,
    Complex.natCast_re, Complex.natCast_im, Complex.zero_re, Complex.zero_im, zero_add, sub_zero]
  by_cases a1 : z.re ≤ 1
  · exact ⟨0, by simp only [Fin.val_zero, Nat.cast_zero, sub_zero]; exact ⟨⟨h1, a1⟩, h3, h4⟩⟩
  by_cases a2 : z.re ≤ 2
  · exact ⟨1, by simp only [Fin.val_one, Nat.cast_one]; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩⟩
  · exact ⟨2, by simp only [Fin.val_two, Nat.cast_ofNat]; exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩⟩

/-- **DDDF Prop 2 (2.10) on `R_{3,1}`**: with the constant `C` of `prop2_tail`,
`P(α(m + C√m) ≤ max_{R_{3,1}} |φ_{0,m}|) ≤ 3 C 4^m e^{-α² m / log 4}`. -/
theorem prop2_tail_R31 : ∃ C : ℝ, 0 < C ∧
    ∀ {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W → ∀ (m : ℕ) (α : ℝ), 0 < α →
    P.real {ω | α * (m + C * Real.sqrt m) ≤ ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ≤
      3 * (C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4)) := by
  obtain ⟨C, hC, h2⟩ := prop2_tail
  refine ⟨C, hC, fun {W} hW m α hα => ?_⟩
  have := hW.isProbabilityMeasure
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le m)
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ m := by positivity
  set Y : Fin 3 → ℂ → Ω → ℝ := fun j x ω => phiMN W P 0 m (x + ((j : ℕ) : ℂ)) ω with hYdef
  have hYc : ∀ j ω, Continuous fun x => Y j x ω := fun j ω =>
    (hφ.cont ω).comp (continuous_id.add continuous_const)
  have hbound : ∀ j : Fin 3, P.real {ω | α * (m + C * Real.sqrt m) ≤
      ⨆ z : ferniqueBox 0 1, |Y j z ω|} ≤ C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4) := by
    intro j
    have hV := isWhiteNoise_isometry hW (motionL2 1 ((j : ℕ) : ℂ))
    refine h2 hV m (Y j) (fun x => ?_) (hYc j) α hα
    have e := hφ.ae_eq (x + ((j : ℕ) : ℂ))
    have e2 := phi_motion W ha ((2 : ℝ)⁻¹ ^ 0) 1 x ((j : ℕ) : ℂ)
    simp only [Circle.coe_one, one_mul] at e2
    rw [e2] at e
    simpa [inv_pow] using e
  have hsub : {ω | α * (m + C * Real.sqrt m) ≤
      ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω|} ⊆
      ⋃ j : Fin 3, {ω | α * (m + C * Real.sqrt m) ≤ ⨆ z : ferniqueBox 0 1, |Y j z ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_iUnion] at hω ⊢
    by_contra hcon
    push Not at hcon
    have hbdd : ∀ j : Fin 3, BddAbove (range fun z : ferniqueBox 0 1 => |Y j z ω|) := by
      intro j
      have := (isCompact_ferniqueBox 0 1).bddAbove_image
        (continuous_abs.comp (hYc j ω)).continuousOn
      rwa [image_eq_range] at this
    have hne : Nonempty (rectAB 3 1).toSet :=
      ⟨⟨0, by simp [MarkedRect.toSet, rectAB, Complex.mem_reProdIm]⟩⟩
    have hle : ⨆ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω| <
        α * (m + C * Real.sqrt m) := by
      have hM : ∀ z : (rectAB 3 1).toSet, |phiMN W P 0 m z ω| ≤
          (Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty
            (fun j => ⨆ z : ferniqueBox 0 1, |Y j z ω|) := by
        intro z
        obtain ⟨j, hj⟩ := exists_shift_mem_ferniqueBox z.2
        have h1 : |phiMN W P 0 m z ω| = |Y j ((z : ℂ) - ((j : ℕ) : ℂ)) ω| := by
          simp only [hYdef, sub_add_cancel]
        rw [h1]
        exact (le_ciSup (hbdd j) (⟨_, hj⟩ : ferniqueBox 0 1)).trans (Finset.le_sup' (fun j => ⨆ z : ferniqueBox 0 1, |Y j z ω|) (Finset.mem_univ j))
      refine (ciSup_le hM).trans_lt ?_
      rw [Finset.sup'_lt_iff]
      exact fun j _ => hcon j
    exact absurd hω (not_le.2 hle)
  calc _ ≤ P.real (⋃ j : Fin 3, {ω | α * (m + C * Real.sqrt m) ≤
        ⨆ z : ferniqueBox 0 1, |Y j z ω|}) := measureReal_mono hsub
    _ ≤ ∑ j : Fin 3, P.real {ω | α * (m + C * Real.sqrt m) ≤
        ⨆ z : ferniqueBox 0 1, |Y j z ω|} := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin 3, C * 4 ^ m * Real.exp (-α ^ 2 * m / Real.log 4) :=
        Finset.sum_le_sum fun j _ => hbound j
    _ = _ := by simp

end DDDF
end LQGMetric
