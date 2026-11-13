/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5ScaleSeparation at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5AnnulusNonempty

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 

theorem dgff_annulus_radii_separated_scales
    (n k l : ℕ) (hkl : k < l) (hl : l ≤ n) :
    dgffOuterRadius (n - l) < dgffInnerRadius (n - k) := by
  have hsmall := dgffOuterRadius_lt_box (n - l)
  have hexp : 2 ^ (n - l) ≤ 2 ^ ((n - k) - 1) := by
    apply Nat.pow_le_pow_right (by omega)
    omega
  unfold dgffInnerRadius
  omega

 
theorem no_radius_in_distinct_annuli
    (n k l r : ℕ) (hkl : k < l) (hl : l ≤ n)
    (hk : dgffInnerRadius (n - k) < r ∧
      r ≤ dgffOuterRadius (n - k))
    (hlr : dgffInnerRadius (n - l) < r ∧
      r ≤ dgffOuterRadius (n - l)) : False := by
  have hsep := dgff_annulus_radii_separated_scales n k l hkl hl
  omega

end SupercriticalLQGUniqueness.B2.QPos
