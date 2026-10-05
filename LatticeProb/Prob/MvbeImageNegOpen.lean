import Mathlib
import LatticeProb.Prob.MvbeRegularClass
import LatticeProb.Prob.MvbeSmoothing
import LatticeProb.Prob.MvbeImageClass

/-!
# The image class preserves the openness of `{ρ < 0}`

`MvbeNegOpen C` (the extra hypothesis of Lemma 2.1, see `MvbeSmoothing.lean`) is stable under the
linear-image construction of `MvbeImageClass.lean`, so Lemma 2.1 applies to the image classes that
the bootstrapping argument uses.
-/

namespace LatticeProb

variable {m : ℕ} {κ : ℝ}

/-- The image class `imageCLE C T` satisfies `MvbeNegOpen` when `C` does. -/
theorem MvbeRegularClass.imageCLE_negOpen [NeZero m] (C : MvbeRegularClass m κ)
    (T : EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m)) (hneg : MvbeNegOpen C) :
    MvbeNegOpen (C.imageCLE T) := by
  intro B hB
  have hB' : T.symm '' B ∈ C.cls := (mvbe_mem_imageCls_iff C T B).mp hB
  have hopen : IsOpen {y | C.rho (T.symm '' B) y < 0} := hneg _ hB'
  have hc : 0 < mvbeInvNorm T := mvbeInvNorm_pos T
  have : {x | (C.imageCLE T).rho B x < 0}
      = (fun x => T.symm x) ⁻¹' {y | C.rho (T.symm '' B) y < 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    show C.rho (T.symm '' B) (T.symm x) / mvbeInvNorm T < 0 ↔ _
    exact (div_lt_iff₀ hc).trans (by rw [zero_mul])
  rw [this]
  exact hopen.preimage T.symm.continuous

/-- The matrix image class satisfies `MvbeNegOpen` when `C` does. -/
theorem MvbeRegularClass.image_negOpen [NeZero m] (C : MvbeRegularClass m κ)
    (L : Matrix (Fin m) (Fin m) ℝ) (hL : IsUnit L.det) (hneg : MvbeNegOpen C) :
    MvbeNegOpen (C.image L hL) :=
  C.imageCLE_negOpen _ hneg

end LatticeProb
