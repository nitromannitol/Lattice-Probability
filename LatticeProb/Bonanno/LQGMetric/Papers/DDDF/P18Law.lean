/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P18Law at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Rigid

/-!
# Rigid-motion invariance of the law of `φ_{m,n}` (for DDDF Prop 18, Steps 1 and 3)
(task P2-DDDF16c)

DDDF (arXiv:1904.08021, `tightness.tex` l. 900–927) use that the law of the field is invariant
under translations and rotations (the four rectangles around a block, the blocks of a
percolation grid). `map_phiMN_motion`: the law of `x ↦ φ_{m,n}(u x + c)` (`|u| = 1`) is the law of
`φ_{m,n}`; same proof as `map_psiMN_motion` (P18Rigid.lean), via `map_ker_eq` and
`phiKernelL2_motion`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- law of `φ_{m,n}` invariant under the rigid motion `x ↦ u x + c`, `|u| = 1` -/
theorem map_phiMN_motion {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {m n : ℕ} (hmn : m ≤ n)
    (u : Circle) (c : ℂ) :
    P.map (fun ω => (fun x => phiMN W P m n ((u : ℂ) * x + c) ω)) =
      P.map (fun ω => (phiMN W P m n · ω)) := by
  have hφ := isPhiVersion_phiMN hW hmn
  have ha : (0 : ℝ) < (2 : ℝ)⁻¹ ^ n := by positivity
  refine (map_ker_eq hW (phiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ m)) (motionL2 u c)
    (Y := phiMN W P m n) (Y₂ := fun x => phiMN W P m n ((u : ℂ) * x + c)) hφ.meas
    (fun x => hφ.meas _) (fun x => hφ.ae_eq x) (fun x => ?_)).symm
  refine (hφ.ae_eq ((u : ℂ) * x + c)).trans (Filter.Eventually.of_forall fun ω => ?_)
  simp only [phi, phiKernelL2_motion ha]

/-- crossing lengths of a domain moved by `x ↦ u x + c`, `|u| = 1` (generalizes
`crossLenIn_image_add`; same proof via `crossLenIn_image_le`) -/
theorem crossLenIn_image_motion (ξ : ℝ) (g : ℂ → ℝ) (K A B : Set ℂ) (u : Circle) (c : ℂ) :
    crossLenIn ξ g ((fun x => (u : ℂ) * x + c) '' K) ((fun x => (u : ℂ) * x + c) '' A)
        ((fun x => (u : ℂ) * x + c) '' B) =
      crossLenIn ξ (fun x => g ((u : ℂ) * x + c)) K A B := by
  have hd : ∀ (v : Circle) (c' : ℂ) (x : ℂ), ‖deriv (fun x => (v : ℂ) * x + c') x‖ ≤ 1 := by
    intro v c' x
    have h : HasDerivAt (fun x => (v : ℂ) * x + c') (v : ℂ) x := by
      simpa using ((hasDerivAt_id x).const_mul (v : ℂ)).add_const c'
    rw [h.deriv, Circle.norm_coe]
  have hD : ∀ (v : Circle) (c' : ℂ), DifferentiableOn ℂ (fun x => (v : ℂ) * x + c') univ :=
    fun v c' => by fun_prop
  set F : ℂ → ℂ := fun x => (u : ℂ) * x + c with hF
  set G : ℂ → ℂ := fun x => ((u⁻¹ : Circle) : ℂ) * x + -(((u⁻¹ : Circle) : ℂ) * c) with hG
  have hu := Circle.coe_ne_zero u
  have hGF : ∀ x, G (F x) = x := fun x => by
    simp only [F, G, Circle.coe_inv]; field_simp; ring
  have hFG : ∀ x, F (G x) = x := fun x => by
    simp only [F, G, Circle.coe_inv]; field_simp; ring
  refine le_antisymm ?_ ?_
  · have h := crossLenIn_image_le (ξ := ξ) (g := g) (K := K) (A := A) (B := B) isOpen_univ
      (subset_univ _) (hD u c) one_pos (fun x _ => hd u c x)
    rw [ENNReal.ofReal_one, one_mul] at h
    exact h
  · have h := crossLenIn_image_le (ξ := ξ) (g := fun x => g (F x)) (K := F '' K) (A := F '' A)
      (B := F '' B) (F := G) isOpen_univ (subset_univ _) (hD u⁻¹ (-(((u⁻¹ : Circle) : ℂ) * c)))
      one_pos (fun x _ => hd u⁻¹ (-(((u⁻¹ : Circle) : ℂ) * c)) x)
    have e : ∀ S : Set ℂ, G '' (F '' S) = S := fun S => by
      rw [image_image]; simp only [hGF, image_id']
    have e2 : (fun x => g (F x)) ∘ G = g := funext fun x => by
      simp only [Function.comp_apply, hFG]
    rw [e, e, e, e2, ENNReal.ofReal_one, one_mul] at h
    exact h

/-- **Law of crossing lengths of `φ_{m,n}` invariant under rigid motions**: for compact `K`,
the crossing length of `φ_{m,n}` between `uA + c` and `uB + c` in `uK + c` has the law of the
crossing length between `A` and `B` in `K`. -/
theorem measure_crossLenIn_phiMN_motion {ξ : ℝ} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {m n : ℕ} (hmn : m ≤ n) (u : Circle) (c : ℂ) {K A B : Set ℂ} (hK : IsCompact K)
    {S : Set ℝ≥0∞} (hS : MeasurableSet S) :
    P {ω | crossLenIn ξ (fun x => phiMN W P m n x ω) ((fun x => (u : ℂ) * x + c) '' K)
        ((fun x => (u : ℂ) * x + c) '' A) ((fun x => (u : ℂ) * x + c) '' B) ∈ S} =
      P {ω | crossLenIn ξ (fun x => phiMN W P m n x ω) K A B ∈ S} := by
  have hφ := isPhiVersion_phiMN hW hmn
  simp_rw [crossLenIn_image_motion]
  exact measure_crossLenIn_eq hK (Y := fun x ω => phiMN W P m n ((u : ℂ) * x + c) ω)
    (Y₂ := phiMN W P m n)
    (fun ω => (hφ.cont ω).comp ((continuous_const.mul continuous_id).add continuous_const))
    (fun x => hφ.meas _) hφ.cont hφ.meas (map_phiMN_motion hW hmn u c) hS

end DDDF
end LQGMetric
