import LatticeProb.Analysis.Sobolev.BandLimitedCmNet

/-!
# The uniform Lipschitz (k = 1 Bernstein) bound for the band-limited family

The Arzelà–Ascoli net form `exists_finite_supNet_of_uniformLip`
(`RellichCmNetReduction.lean:43`) needs, besides the uniform `C^m` bound landed in
`BandLimitedCmNet.lean` (`exists_uniform_iteratedFDeriv_le`, and its multi-index evaluation form
`exists_uniform_iteratedFDeriv_apply_le`), a **uniform Lipschitz bound** on the band-limited
family: a single `C` with `dist (f x) (f y) ≤ C * dist x y` for every member `f = P_Λ φ` of the
`H^s` unit ball.

This file supplies it.  The transfer from the `k = 1` iterated-derivative bound to the distance is
the mean-value inequality `‖g y - g x‖ ≤ ‖fderiv g‖ ‖y - x‖`
(`Convex.norm_image_sub_le_of_norm_fderiv_le`) together with
`norm_iteratedFDeriv_one : ‖iteratedFDeriv ℝ 1 g x‖ = ‖fderiv ℝ g x‖`; the `k = 1` bound itself is
the `m = 1` instance of `exists_uniform_iteratedFDeriv_le`.

The remaining piece for the net half is the compact carrier / support–mollification repair: the
band-limited functions are not compactly supported, so Arzelà–Ascoli still needs either a compact
carrier or the support repair to place the centres in `IsTestFn D`.  The mapping of this
`ℂ`-valued family into `BoundedContinuousFunction α ℝ` is also not done here.
-/

open MeasureTheory
open scoped ENNReal

namespace LatticeProb.Sobolev

/-- **The mean-value Lipschitz transfer.**  If the `k = 1` iterated derivative of `g` is bounded by
`C`, then `g` is `C`-Lipschitz: `dist (g x) (g y) ≤ C * dist x y`. -/
theorem lipschitz_of_norm_iteratedFDeriv_one_le {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space d → F} {C : ℝ}
    (hg : ContDiff ℝ 1 g) (h : ∀ x, ‖iteratedFDeriv ℝ 1 g x‖ ≤ C) :
    ∀ x y, dist (g x) (g y) ≤ C * dist x y := by
  intro x y
  have hdiff : ∀ z ∈ (Set.univ : Set (Space d)), DifferentiableAt ℝ g z :=
    fun z _ => (hg.differentiable one_ne_zero).differentiableAt
  have hb : ∀ z ∈ (Set.univ : Set (Space d)), ‖fderiv ℝ g z‖ ≤ C := by
    intro z _
    rw [← norm_iteratedFDeriv_one g]
    exact h z
  have hle := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hb convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  calc dist (g x) (g y) = ‖g y - g x‖ := dist_eq_norm' _ _
    _ ≤ C * ‖y - x‖ := hle
    _ = C * dist x y := by rw [dist_eq_norm']

/-- **The uniform Lipschitz (k = 1 Bernstein) bound for the band-limited family.**  For `Λ > 0`
and `s ≥ 0` there is a single `C > 0` such that every truncation `P_Λ φ` of an `H^s`-unit test
function is `C`-Lipschitz.  This is the `k = 1` case of the band-limited Bernstein bound, in the
form `exists_finite_supNet_of_uniformLip` consumes. -/
theorem exists_uniform_lipschitz_bandTrunc {d : ℕ} (Λ : ℝ) (hΛ : 0 < Λ) {s : ℝ} (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : Space d → ℝ) (hcont : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hcs : HasCompactSupport φ) (x y : Space d),
      sobolevNormSq d s φ ≤ 1 →
        dist (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) x)
          (bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs) y)
          ≤ C * dist x y := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_iteratedFDeriv_le (d := d) Λ hΛ hs 1
  refine ⟨C, hC, fun φ hcont hcs x y hφ => ?_⟩
  refine lipschitz_of_norm_iteratedFDeriv_one_le
    ((bandTrunc d Λ hΛ.ne' (realToComplexSchwartz d φ hcont hcs)).smooth 1)
    (fun z => ?_) x y
  exact hbound φ hcont hcs z hφ 1 le_rfl

end LatticeProb.Sobolev

