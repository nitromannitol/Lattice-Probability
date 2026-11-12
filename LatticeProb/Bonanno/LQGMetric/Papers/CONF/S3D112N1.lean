/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D112N1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L35B9
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryVar
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Sup1

/-!
# `CONFHarmLowZB`, part 1: the unit-scale bound for `h − X` (task P2-CONFHLZ)

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF), Lemma 3.3, Step 2
(C:1217–1234), with the harmonic bound of C:1169–1172 ("since `𝔥^U` is continuous away from
`∂U` … by translation and scale invariance of the law of `h` modulo additive constant").

`hlz_unit`: for a bounded open `V`, a compact `K ⊆ V` and `β > 0` there is `A` such that, for
every normalized whole-plane GFF `h` and every measurable `X` whose restriction to `V` is a
zero-boundary GFF on `V` (no joint law, no independence), every harmonic representative `g` of
`(h − X)|_V` has `P[∃ x ∈ K, |g(x)| > A] ≤ β`.

Proof: the argument of Ding–Gwynne Lemma 2.2 (2.4) as formalized in `dg_tail_unif` (S3L35B7):
mean value property against radial bumps `ψ_y` (`pair_radBump_of_harmonic`,
`abs_sub_le_integral_of_harmonic`), `|g| ≤ κ₀ (∫_S |h(ψ_y − ψ_c)| + m |h(ψ_c)| + ∫_S |X(ψ_y)|)`
on `K`, and Gaussian exponential moments of the three pieces. Here the zero-boundary pairings are
bounded directly, `Var X(ψ_y) = ‖ψ_y‖²_{H⁻¹(V)} ≤ ‖ψ_y‖²_{H⁻¹(square)}` (domain monotonicity
`zeroGFFTestCov_self_mono` and the square bound `DDDF.S6Sup.zbVar_self_le`), instead of through
the independence `G ⫫ h̊` used in DG. Own routine adaptation of DG's argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric InnerProductSpace TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM LM MarkovNorm MarkovGauss MarkovZB DG DG.L22 QuantumZipper HeatSq

/-- an explicit tail level for `2 e^{−A²/(4B)} ≤ β` -/
theorem hlz_tail_level {B β : ℝ} (hB : 0 < B) (hβ : 0 < β) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ A, A₀ ≤ A → 2 * Real.exp (-(1 / (4 * B)) * A ^ 2) ≤ β := by
  refine ⟨max 1 (4 * B * Real.log (2 / β)), by positivity, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := (le_max_left _ _).trans hA
  have hA2 : 4 * B * Real.log (2 / β) ≤ A := (le_max_right _ _).trans hA
  have hAA : A ≤ A ^ 2 := by nlinarith
  have hlog : Real.log (2 / β) ≤ (1 / (4 * B)) * A ^ 2 := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    nlinarith
  have : Real.exp (-(1 / (4 * B)) * A ^ 2) ≤ β / 2 := by
    calc Real.exp (-(1 / (4 * B)) * A ^ 2) ≤ Real.exp (-Real.log (2 / β)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = β / 2 := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  linarith

/-- the zero-boundary variance of a radial bump is bounded uniformly in its centre -/
theorem hlz_zbVar_bound {V : Opens ℂ} (hVb : Bornology.IsBounded (V : Set ℂ)) {δ : ℝ}
    (hδ : 0 < δ) : ∃ vX : ℝ, ∀ (y : ℂ) (hB : closedBall y δ ⊆ V),
      zeroGFFTestCov V (bumpOn hδ hB) (bumpOn hδ hB) ≤ vX := by
  obtain ⟨R₀, hR₀⟩ := hVb.subset_ball (0 : ℂ)
  set R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hVsq : (V : Set ℂ) ⊆ sqOpen (-R) (2 * R) := fun x hx => by
    have h1 : ‖x‖ < R := by
      have := hR₀ hx; rw [mem_ball, dist_zero_right] at this
      exact lt_of_lt_of_le this (le_max_left _ _)
    have hre := Complex.abs_re_le_norm x
    have him := Complex.abs_im_le_norm x
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith [abs_lt.1 (lt_of_le_of_lt hre h1), abs_lt.1 (lt_of_le_of_lt him h1)]
  set C := expNegInvGlue (δ ^ 2)
  refine ⟨2 * (2 * R) ^ 2 / Real.pi * ((∫ x, radProf δ x) * (4 * C)), fun y hB => ?_⟩
  have hB' : closedBall y δ ⊆ (sqOpens (-R) (2 * R) : Set ℂ) := hB.trans hVsq
  have hmono := zeroGFFTestCov_self_mono (U := V) (U' := sqOpens (-R) (2 * R)) hVsq
    (zbAdmissible_of_isBounded hVb) (zbAdmissible_of_isBounded (isBounded_sqOpen _ _))
    (bumpOn hδ hB) (bumpOn hδ hB') rfl
  have hvan : ∀ x ∉ sqOpen (-R) (2 * R), (radBump δ hδ.le y : ℂ → ℝ) x = 0 := by
    intro x hx
    have hx' : x ∉ closedBall y δ := fun h => hx (hB' h)
    rw [mem_closedBall, dist_eq_norm, not_le] at hx'
    rw [radBump_apply]; exact radProf_eq_zero hδ.le hx'.le
  set ρ : BddOn (sqOpen (-R) (2 * R)) := ⟨radBump δ hδ.le y,
    (radBump δ hδ.le y).continuous.measurable, ⟨C, fun x => by
      rw [radBump_apply, abs_of_nonneg (radProf_nonneg _ _)]; exact radProf_le δ _⟩, hvan⟩
  have hsq := DDDF.S6Sup.zbVar_self_le (a := -R) (by positivity : 0 < 2 * R) ρ (C := C)
    (fun x => by
      show |(radBump δ hδ.le y : ℂ → ℝ) x| ≤ C
      rw [radBump_apply, abs_of_nonneg (radProf_nonneg _ _)]; exact radProf_le δ _)
  have hint : ∫ x, |ρ.1 x| * (4 * C) = (∫ x, radProf δ x) * (4 * C) := by
    show ∫ x, |(radBump δ hδ.le y : ℂ → ℝ) x| * (4 * C) = _
    simp_rw [radBump_apply, abs_of_nonneg (radProf_nonneg _ _)]
    rw [integral_mul_const]
    congr 1
    exact integral_sub_right_eq_self (fun x => radProf δ x) y
  rw [hint] at hsq
  exact hmono.trans hsq

end LQGMetric.CONF
