/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Zipper.SWCoreN2Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.SWCoreN2Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-N2 (2): uniform smallness of scale-indexed Gaussian families (boxes + Borel–Cantelli)

Assembly of `SWCoreN2Chain`: `swcn2_ae_eventually_small` (statement in the docstring of
`SWCoreN2Chain`). Sheffield–Wang, arXiv:1605.06171, Lemma 3.5 and the Borel–Cantelli step after
(3.23), p. 16. Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Real

namespace QuantumZipper
namespace SWCore

open RegUnif

theorem swcn2_rad_rpow_inv (x : ℝ) (k : ℕ) : (radius k ^ x)⁻¹ = ((2 : ℝ) ^ x) ^ k := by
  unfold radius
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast, Real.inv_rpow (by norm_num), inv_pow, inv_inv]

theorem swcn2_radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Fixed

variable {d : ℕ} (Z : ℕ → (Fin d → ℝ) → Ω → ℝ) {D : Set (Fin d → ℝ)}

/-- The grid box of index `g` at side `s`. -/
def swcn2Box (D : Set (Fin d → ℝ)) (s : ℝ) (g : Fin d → ℤ) : Set (Fin d → ℝ) :=
  {θ | θ ∈ D ∧ ∀ i, |θ i - s * g i| ≤ s / 2}

theorem swcn2_box_diam {s : ℝ} (hs : 0 ≤ s) {g : Fin d → ℤ} {θ θ' : Fin d → ℝ}
    (hθ : θ ∈ swcn2Box D s g) (hθ' : θ' ∈ swcn2Box D s g) : ‖θ - θ'‖ ≤ s := by
  refine (pi_norm_le_iff_of_nonneg hs).2 fun i => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  have h1 := hθ.2 i
  have h2 := hθ'.2 i
  calc |θ i - θ' i| = |(θ i - s * g i) - (θ' i - s * g i)| := by ring_nf
    _ ≤ |θ i - s * g i| + |θ' i - s * g i| := abs_sub _ _
    _ ≤ s := by linarith

theorem swcn2_mem_box {s : ℝ} (hs : 0 < s) {θ : Fin d → ℝ} (hθ : θ ∈ D) :
    θ ∈ swcn2Box D s (fun i => round (θ i / s)) := by
  refine ⟨hθ, fun i => ?_⟩
  have h := abs_sub_round (θ i / s)
  have e : θ i - s * (round (θ i / s) : ℝ) = s * (θ i / s - round (θ i / s)) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hs]
  nlinarith

theorem swcn2_round_mem {s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) {θ : Fin d → ℝ} (hθR : ‖θ‖ ≤ R) :
    (fun i => round (θ i / s)) ∈ Fintype.piFinset fun _ : Fin d =>
      Finset.Icc (-((⌈R / s⌉₊ + 1 : ℕ) : ℤ)) ((⌈R / s⌉₊ + 1 : ℕ) : ℤ) := by
  rw [Fintype.mem_piFinset]
  intro i
  rw [Finset.mem_Icc]
  have hi : |θ i| ≤ R := by
    have := norm_le_pi_norm θ i
    rw [Real.norm_eq_abs] at this; linarith
  have hr := abs_sub_round (θ i / s)
  have hxs : |θ i / s| ≤ R / s := by
    rw [abs_div, abs_of_pos hs]; exact div_le_div_of_nonneg_right hi hs.le
  have hceil : R / s ≤ (⌈R / s⌉₊ : ℝ) := Nat.le_ceil _
  have hb : |(round (θ i / s) : ℝ)| ≤ (⌈R / s⌉₊ : ℝ) + 1 := by
    have : |(round (θ i / s) : ℝ)| ≤ |θ i / s| + |θ i / s - round (θ i / s)| := by
      have := abs_sub_abs_le_abs_sub (round (θ i / s) : ℝ) (θ i / s)
      rw [abs_sub_comm (round (θ i / s) : ℝ)] at this
      linarith
    linarith
  rw [abs_le] at hb
  constructor
  · have : (-(((⌈R / s⌉₊ + 1 : ℕ) : ℤ)) : ℝ) ≤ (round (θ i / s) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  · have : (round (θ i / s) : ℝ) ≤ (((⌈R / s⌉₊ + 1 : ℕ) : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this

theorem swcn2_rpow_facts {r : ℝ} (hr : 0 < r) (β : ℝ) :
    (r ^ 2) ^ (β / 2) = (r ^ (β / 2)) ^ 2 ∧ r ^ β = (r ^ (β / 2)) ^ 2 := by
  have h1 : (r ^ (β / 2)) ^ 2 = r ^ β := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring
  refine ⟨?_, h1.symm⟩
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]; congr 1; push_cast; ring

/-- Variance of a negated difference. -/
theorem swcn2_var_neg_sub {Z₁ Z₂ : Ω → ℝ} :
    Var[fun ω => -Z₁ ω - -Z₂ ω; P] = Var[fun ω => Z₁ ω - Z₂ ω; P] := by
  have e : (fun ω => -Z₁ ω - -Z₂ ω) = fun ω => -(Z₁ ω - Z₂ ω) := by funext ω; ring
  rw [e, variance_fun_neg]

end Fixed

end SWCore
end QuantumZipper
