/-
White-noise evaluation as a linear isometry into `L²`.

A covariance identity `∫ W f · W g = ∫ f · g` makes `f ↦ W f`, read in `L²(P)`, an
isometry of `L²(μ)` into `L²(P)`; linearity follows from the covariance identity by
polarization.  This is the form in which a bounded linear map commutes with a Bochner
integral, which is what a stochastic Fubini for white noise needs.
-/
import LatticeProb.Prob.L2JointVersion

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- A covariance identity makes white-noise evaluation a linear isometry into `L²`. -/
noncomputable def whiteNoiseLinearIsometry (μ : Measure X) (P : Measure Ω)
    (W : (X → ℝ) → Ω → ℝ) (hm : ∀ f, MemLp (W f) 2 P)
    (hc : ∀ f g, MemLp f 2 μ → MemLp g 2 μ →
      (∫ ω, W f ω * W g ω ∂P) = ∫ x, f x * g x ∂μ) :
    Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 P := by
  let Jf : Lp ℝ 2 μ → Lp ℝ 2 P := fun f => (hm (fun x => f x)).toLp (W (fun x => f x))
  have hinner : ∀ f g : Lp ℝ 2 μ, inner ℝ (Jf f) (Jf g) = inner ℝ f g :=
    fun f g => inner_toLp_eq_of_covariance P (fun a : Lp ℝ 2 μ => W (fun x => a x))
      (fun a => hm (fun x => a x))
      (fun a b => by
        rw [hc _ _ (Lp.memLp a) (Lp.memLp b), L2.inner_def]
        simp only [RCLike.inner_apply, conj_trivial]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun _ => mul_comm _ _) f g
  have hadd : ∀ f g : Lp ℝ 2 μ, Jf (f + g) = Jf f + Jf g := by
    intro f g
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, hinner]
    ring
  have hsmul : ∀ (c : ℝ) (f : Lp ℝ 2 μ), Jf (c • f) = c • Jf f := by
    intro c f
    apply sub_eq_zero.mp
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hinner]
    ring
  exact LinearMap.isometryOfInner
    { toFun := Jf, map_add' := hadd, map_smul' := hsmul } hinner


end LatticeProb
