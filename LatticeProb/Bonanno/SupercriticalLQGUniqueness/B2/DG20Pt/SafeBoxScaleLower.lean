/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxScaleLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.SafeBoxScale

 




set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem exists_scaled_finite_box_cross_lower
    (U : TopologicalSpace.Opens ℂ) (K₁ K₂ : Set ℂ)
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hK₁U : K₁ ⊆ U) (hdisj : Disjoint K₁ K₂) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : Finset ℂ,
      ∀ ξ : ℝ, ∀ g : ℂ → ℝ, ∀ r : ℝ, 0 < r →
        let D : ℂ → ℂ := fun z => (r : ℂ) * z
        (⨅ c ∈ F, scaledBoxCrossMin ξ g c ρ r) ≤
          crossLenIn ξ g (D '' U) (D '' K₁) (D '' K₂) := by
  obtain ⟨ρ, hρ, F, hbase⟩ :=
    exists_finite_box_cross_lower U K₁ K₂ hK₁ hK₂ hK₁U hdisj
  refine ⟨ρ, hρ, F, ?_⟩
  intro ξ g r hr
  dsimp
  let D : ℂ → ℂ := fun z => (r : ℂ) * z
  have hm0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr).ne'
  have hmtop : ENNReal.ofReal r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmain := hbase ξ (fun x => g (D x))
  calc
    (⨅ c ∈ F, scaledBoxCrossMin ξ g c ρ r) =
        ENNReal.ofReal r * (⨅ c ∈ F, boxCrossMin ξ (fun x => g (D x)) c ρ) := by
      simp only [scaledBoxCrossMin_eq_mul ξ g _ ρ r hr,
        ENNReal.mul_iInf_of_ne hm0 hmtop, D]
    _ ≤ ENNReal.ofReal r * crossLenIn ξ (fun x => g (D x)) U K₁ K₂ := by
      gcongr
    _ = crossLenIn ξ g (D '' U) (D '' K₁) (D '' K₂) := by
      simpa only [D] using (crossLenIn_image_mul ξ g U K₁ K₂ hr).symm

end SupercriticalLQGUniqueness.B2.DG20Pt
