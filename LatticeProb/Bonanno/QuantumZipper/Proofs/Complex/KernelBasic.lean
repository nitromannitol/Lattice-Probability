/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.KernelBasic at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KoebeDistortion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsCayley
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Order

/-!
# Carathéodory kernel convergence: definition and basic tools (EXT-CA KT1, D7)

* `KernelConvergesTo G D w₀`: Pommerenke's kernel convergence `G n → D` with respect to `w₀`,
  conditions (i)–(ii) of Pommerenke, *Boundary Behaviour of Conformal Maps* (1992), §1.4, p. 13.
* `infDist_compl_le_schwarzPick`: for `F` injective holomorphic on `𝔻` and `z ∈ 𝔻`,
  `dist (F z, ∂F(𝔻)) ≤ (1 − |z|²) |F'(z)|` (the upper half of Pommerenke, *loc. cit.*,
  Cor. 1.4, p. 9, used in the proof of Thm 1.8, p. 14). Proof: Schwarz's lemma for
  `φ_z ∘ F⁻¹` on the disk `D(F z, dist)`, with `φ_z` the disk automorphism `z ↦ 0`
  (`Koebe.radius_mul_norm_deriv_le_of_ball_subset_image`).
* `eqOn_of_image_eq_of_deriv_pos`: uniqueness of the normalized Riemann map
  (`f(0) = g(0)`, `f'(0), g'(0) > 0`, same image), via `exists_rotation_of_bijOn_ball`
  (Ahlfors, *Complex Analysis*, 3rd ed., Ch. 6 §1.1, p. 230, uniqueness part).
-/

noncomputable section

open Set Metric Filter Topology Complex
open scoped ComplexConjugate ComplexOrder

namespace QuantumZipper.CA.Kernel

theorem hasDerivAt_diskMobius_self {a : ℂ} (ha : ‖a‖ < 1) :
    HasDerivAt (diskMobius a) (1 / (1 - ((‖a‖ ^ 2 : ℝ) : ℂ))) a := by
  have hden : (1 : ℂ) - conj a * a ≠ 0 := diskMobius_denom_ne_zero ha ha.le
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 a := (hasDerivAt_id a).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - conj a * w) (-conj a) a := by
    simpa using ((hasDerivAt_id a).const_mul (conj a)).const_sub 1
  have h : HasDerivAt (fun w : ℂ => (w - a) / (1 - conj a * w))
      ((1 * (1 - conj a * a) - (a - a) * -conj a) / (1 - conj a * a) ^ 2) a := h1.div h2 hden
  have hca : conj a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; rfl
  have he : (1 : ℂ) / (1 - ((‖a‖ ^ 2 : ℝ) : ℂ)) =
      (1 * (1 - conj a * a) - (a - a) * -conj a) / (1 - conj a * a) ^ 2 := by
    rw [← hca]
    field_simp
    ring
  rw [he]
  exact h

/-- Koebe's estimate, upper half, Schwarz–Pick form (Pommerenke, Cor. 1.4, p. 9):
`dist (F z, ℂ \ F(𝔻)) ≤ (1 − |z|²) |F'(z)|`. -/
theorem infDist_compl_le_schwarzPick {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1))
    (hinj : InjOn F (ball 0 1)) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    infDist (F z) (F '' ball 0 1)ᶜ ≤ (1 - ‖z‖ ^ 2) * ‖deriv F z‖ := by
  set R := infDist (F z) (F '' ball 0 1)ᶜ with hRdef
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hq : 0 < 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  rcases le_or_gt R 0 with hR | hR
  · exact hR.trans (by positivity)
  have hsub : ball (F z) R ⊆ F '' ball 0 1 := by
    intro w hw
    rw [mem_ball, dist_comm] at hw
    by_contra h
    exact notMem_of_dist_lt_infDist hw h
  have hψ : DifferentiableOn ℂ (diskMobius z) (ball 0 1) :=
    (differentiableOn_diskMobius hz1).mono ball_subset_closedBall
  have hmaps : MapsTo (diskMobius z) (ball 0 1) (closedBall (diskMobius z z) 1) := by
    intro w hw
    rw [diskMobius_self]
    exact ball_subset_closedBall (diskMobius_mem_ball hz1 hw)
  have key := Koebe.radius_mul_norm_deriv_le_of_ball_subset_image isOpen_ball hd hinj hz hψ
    hmaps hR hsub
  rw [(hasDerivAt_diskMobius_self hz1).deriv] at key
  have hc : (1 : ℂ) - ((‖z‖ ^ 2 : ℝ) : ℂ) = ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hq.le, one_mul,
    mul_one_div, div_le_iff₀ hq] at key
  linarith

end QuantumZipper.CA.Kernel
