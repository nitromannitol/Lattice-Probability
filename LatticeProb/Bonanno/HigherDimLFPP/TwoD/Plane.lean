/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.TwoD.Plane at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Frozen.LfppDistance
import LatticeProb.Bonanno.LQGDimension.Statement.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# The plane `ℝ² ≃ ℂ` and the two LFPP path classes (packet P-X10, target T4, deterministic part)

Source: `source/higher-dimensional-lfpp-limit.pdf`, (1.2) in `d = 2` and the planar convention of
ref. [5] (`LQGDimension`); planning audit HA5, Details D12, Claim 4 ("`LQGDimension.lfppDistance ξ
(h ε ·)` and `lfppDistD 2 ξ (H ε)` use the same paths under the isometry `toC/ofC`").

* `cToR2 : ℂ ≃ₗᵢ[ℝ] Rd 2`, `z ↦ (Re z, Im z)`: the coordinates in the orthonormal basis `1, i`
  (`Complex.orthonormalBasisOneI.repr`); `cToR2 1 = e₁ 2`, and `cToR2` maps `LQGDimension.U` onto
  the frozen `cube 2` (`mem_cube_iff`).
* Admissible paths correspond (`isAdmissiblePath_cToR2_symm_comp`, `isAdmissiblePath_cToR2_comp`):
  `γ ↦ cToR2.symm ∘ γ` is a bijection between the frozen admissible paths in `ℝ²` (from `0` to `e₁`
  in `(-2,2)²`) and `LQGDimension`'s admissible paths in `ℂ` (from `0` to `1` in `U`), and it
  preserves `|γ'|` (`deriv_cToR2_symm_comp`), hence LFPP lengths.
* `lqg_lfppDistance_eq`: `LQGDimension.lfppDistance ξ ψ = lfppDistance 2 ξ (ψ ∘ cToR2.symm)` for
  every field `ψ : ℂ → ℝ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP

/-! ### The isometry `ℂ ≃ ℝ²` -/

/-- The linear isometry `ℂ ≃ ℝ²`, `z ↦ (Re z, Im z)` (coordinates in the orthonormal basis
`1, i`). -/
def cToR2 : ℂ ≃ₗᵢ[ℝ] Rd 2 := Complex.orthonormalBasisOneI.repr

theorem cToR2_apply_zero (z : ℂ) : cToR2 z 0 = z.re := by
  show (Complex.orthonormalBasisOneI.repr z).ofLp 0 = z.re
  rw [Complex.orthonormalBasisOneI_repr_apply]
  rfl

theorem cToR2_apply_one (z : ℂ) : cToR2 z 1 = z.im := by
  show (Complex.orthonormalBasisOneI.repr z).ofLp 1 = z.im
  rw [Complex.orthonormalBasisOneI_repr_apply]
  rfl

theorem cToR2_symm_re (x : Rd 2) : (cToR2.symm x).re = x 0 := by
  show (Complex.orthonormalBasisOneI.repr.symm x).re = x.ofLp 0
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

theorem cToR2_symm_im (x : Rd 2) : (cToR2.symm x).im = x 1 := by
  show (Complex.orthonormalBasisOneI.repr.symm x).im = x.ofLp 1
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

/-- `1 ↦ e₁`. -/
theorem cToR2_one : cToR2 1 = e₁ 2 := by
  refine PiLp.ext fun i => ?_
  fin_cases i
  · show cToR2 1 0 = (e₁ 2).ofLp 0
    rw [cToR2_apply_zero]
    simp [e₁]
  · show cToR2 1 1 = (e₁ 2).ofLp 1
    rw [cToR2_apply_one]
    simp [e₁]

theorem cToR2_symm_e₁ : cToR2.symm (e₁ 2) = 1 := by
  rw [← cToR2_one, LinearIsometryEquiv.symm_apply_apply]

theorem norm_cToR2_sub (z w : ℂ) : ‖cToR2 z - cToR2 w‖ = ‖z - w‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]

theorem norm_cToR2_symm_sub (x y : Rd 2) : ‖cToR2.symm x - cToR2.symm y‖ = ‖x - y‖ := by
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- `cToR2` as a measurable equivalence. -/
def cToR2Meas : ℂ ≃ᵐ Rd 2 := cToR2.toHomeomorph.toMeasurableEquiv

theorem coe_cToR2Meas : (cToR2Meas : ℂ → Rd 2) = cToR2 := rfl

/-! ### Admissible paths -/

/-- `cToR2.symm` maps the frozen `cube 2 = (-2,2)²` onto `LQGDimension.U`. -/
theorem mem_lqgU_iff (x : Rd 2) : cToR2.symm x ∈ LQGDimension.U ↔ x ∈ cube 2 := by
  simp only [LQGDimension.U, cube, mem_ofPred_eq, cToR2_symm_re, cToR2_symm_im, Fin.forall_fin_two]

theorem mem_cube_iff (z : ℂ) : cToR2 z ∈ cube 2 ↔ z ∈ LQGDimension.U := by
  rw [← mem_lqgU_iff, LinearIsometryEquiv.symm_apply_apply]

/-- Derivatives commute with a linear isometry (at every point, differentiable or not). -/
theorem TwoD.deriv_linearIsometryEquiv_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) (γ : ℝ → E) (t : ℝ) :
    deriv (fun s => e (γ s)) t = e (deriv γ t) := by
  rw [← fderiv_apply_one_eq_deriv, ← fderiv_apply_one_eq_deriv]
  have h : (fun s => e (γ s)) = e ∘ γ := rfl
  rw [h, LinearIsometryEquiv.comp_fderiv]
  rfl

theorem deriv_cToR2_symm_comp (γ : ℝ → Rd 2) (t : ℝ) :
    deriv (fun s => cToR2.symm (γ s)) t = cToR2.symm (deriv γ t) :=
  TwoD.deriv_linearIsometryEquiv_comp cToR2.symm γ t

/-- Frozen admissible paths in `ℝ²` give `LQGDimension`'s admissible paths in `ℂ`. -/
theorem isAdmissiblePath_cToR2_symm_comp {γ : ℝ → Rd 2} (hγ : IsAdmissiblePath 2 γ) :
    LQGDimension.IsAdmissiblePath fun t => cToR2.symm (γ t) where
  source := by simp only [hγ.source, map_zero]
  target := by rw [hγ.target, cToR2_symm_e₁]
  mapsTo := fun t ht => (mem_lqgU_iff _).2 (hγ.mapsTo ht)
  continuousOn := cToR2.symm.continuous.comp_continuousOn hγ.continuousOn
  piecewise_contDiff := by
    obtain ⟨k, t, hmono, h0, h1, hc⟩ := hγ.piecewise_contDiff
    exact ⟨k, t, hmono, h0, h1, fun i => cToR2.symm.contDiff.comp_contDiffOn (hc i)⟩

/-- `LQGDimension`'s admissible paths in `ℂ` give frozen admissible paths in `ℝ²`. -/
theorem isAdmissiblePath_cToR2_comp {γ : ℝ → ℂ} (hγ : LQGDimension.IsAdmissiblePath γ) :
    IsAdmissiblePath 2 fun t => cToR2 (γ t) where
  source := by simp only [hγ.source, map_zero]
  target := by rw [hγ.target, cToR2_one]
  mapsTo := fun t ht => (mem_cube_iff _).2 (hγ.mapsTo ht)
  continuousOn := cToR2.continuous.comp_continuousOn hγ.continuousOn
  piecewise_contDiff := by
    obtain ⟨k, t, hmono, h0, h1, hc⟩ := hγ.piecewise_contDiff
    exact ⟨k, t, hmono, h0, h1, fun i => cToR2.contDiff.comp_contDiffOn (hc i)⟩

/-- LFPP lengths agree under the isometry. -/
theorem lqg_lfppLength_cToR2_symm_comp (ξ : ℝ) (ψ : ℂ → ℝ) (γ : ℝ → Rd 2) :
    LQGDimension.lfppLength ξ ψ (fun t => cToR2.symm (γ t)) =
      lfppLength ξ (fun x => ψ (cToR2.symm x)) γ := by
  unfold LQGDimension.lfppLength lfppLength
  congr 1
  funext t
  rw [deriv_cToR2_symm_comp, LinearIsometryEquiv.norm_map]

/-- The bijection between the two classes of admissible paths. -/
def admissiblePathEquiv :
    {γ : ℝ → Rd 2 // IsAdmissiblePath 2 γ} ≃ {γ : ℝ → ℂ // LQGDimension.IsAdmissiblePath γ} where
  toFun γ := ⟨fun t => cToR2.symm (γ.1 t), isAdmissiblePath_cToR2_symm_comp γ.2⟩
  invFun γ := ⟨fun t => cToR2 (γ.1 t), isAdmissiblePath_cToR2_comp γ.2⟩
  left_inv γ := by
    apply Subtype.ext
    funext t
    exact LinearIsometryEquiv.apply_symm_apply cToR2 _
  right_inv γ := by
    apply Subtype.ext
    funext t
    exact LinearIsometryEquiv.symm_apply_apply cToR2 _

/-- **The two LFPP distances agree** (HA5 D12, Claim 4, deterministic part): for every field
`ψ : ℂ → ℝ`, `LQGDimension.lfppDistance ξ ψ = lfppDistance 2 ξ (ψ ∘ cToR2.symm)`. -/
theorem lqg_lfppDistance_eq (ξ : ℝ) (ψ : ℂ → ℝ) :
    LQGDimension.lfppDistance ξ ψ = lfppDistance 2 ξ (fun x => ψ (cToR2.symm x)) := by
  unfold LQGDimension.lfppDistance lfppDistance
  rw [← admissiblePathEquiv.iInf_comp]
  congr 1
  funext γ
  exact lqg_lfppLength_cToR2_symm_comp ξ ψ γ.1

end HigherDimLFPP
