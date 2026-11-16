import LatticeProb.External.GilbargTrudinger
import LatticeProb.Analysis.Elliptic.HolderLocalPatch
import LatticeProb.Analysis.Elliptic.HolderPatchAssembly

/-!
# Assembly of Hölder extensions

The global extension follows from boundary patches and their finite assembly.
-/

namespace LatticeProb.Elliptic.HolderExtension.Internal

open scoped ENNReal

noncomputable section

/-- A local extension with uniform control and support in a prescribed neighborhood. -/
def HasLocalPatch {d : ℕ} (σ : ℝ) (U U' : Set (Fin d → ℝ)) (p : Fin d → ℝ) : Prop :=
  ∃ V W : Set (Fin d → ℝ), IsOpen V ∧ IsOpen W ∧ p ∈ V ∧ closure V ⊆ W ∧
    closure W ⊆ U' ∧ ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
      ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
      ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
        tsupport v ⊆ W ∧ Set.EqOn v u (V ∩ U) ∧
        c2HolderNorm σ Set.univ v ≤ ENNReal.ofReal C * c2HolderNorm σ U u

/-- Boundary patch construction and assembly imply the global extension statement. -/
theorem holder_extension_of_local_patches
    (boundary_local_patch : ∀ {d : ℕ} {σ : ℝ}, 0 < σ → σ < 1 →
      ∀ {U U' : Set (Fin d → ℝ)}, IsC2HolderDomain σ U → IsOpen U' →
        closure U ⊆ U' → ∀ {p : Fin d → ℝ}, p ∈ frontier U → HasLocalPatch σ U U' p)
    (assemble_local_patches : ∀ {d : ℕ} {σ : ℝ}, 0 < σ → σ < 1 →
      ∀ {U U' : Set (Fin d → ℝ)}, IsOpen U → Bornology.IsBounded U → IsOpen U' →
        closure U ⊆ U' → (∀ p ∈ frontier U, HasLocalPatch σ U U' p) →
        ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin d → ℝ) → ℝ,
          ContDiffOn ℝ 2 u U → c2HolderNorm σ U u < ⊤ →
          ∃ v : (Fin d → ℝ) → ℝ, ContDiff ℝ 2 v ∧ HasCompactSupport v ∧
            tsupport v ⊆ U' ∧ Set.EqOn v u U ∧
            c2HolderNorm σ U' v ≤ ENNReal.ofReal C * c2HolderNorm σ U u) :
    External.GilbargTrudingerHolderExtension := by
  intro d hd σ hσ hσ' U hU U' hU' hsub
  exact assemble_local_patches hσ hσ' hU.1 hU.2.2.1 hU' hsub
    (fun _ hp => boundary_local_patch hσ hσ' hU hU' hsub hp)

end
end LatticeProb.Elliptic.HolderExtension.Internal

namespace LatticeProb.Elliptic.HolderExtension

/-- Gilbarg–Trudinger's Hölder extension theorem. -/
theorem gilbargTrudingerHolderExtension_holds : External.GilbargTrudingerHolderExtension := by
  apply Internal.holder_extension_of_local_patches
  · intro d σ hσ hσ' U U' hU hU' hsub p hp
    exact boundary_local_patch hσ hσ' hU hU' hsub hp
  · intro d σ hσ hσ' U U' hU hbounded hU' hsub hpatch
    exact assemble_local_patches hσ hσ' hU hbounded hU' hsub hpatch

end LatticeProb.Elliptic.HolderExtension
