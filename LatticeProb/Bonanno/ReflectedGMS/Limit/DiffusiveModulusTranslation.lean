/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.DiffusiveModulusTranslation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.TwoClockScalingLimitReduction

/-!
# The rescaled window modulus tail, translated back to the unrescaled path law

`ReflectedGMS/Limit/TwoClockScalingLimitReduction.lean` reduces
`InterpolatedTwoClockReduction.TwoClockScalingLimit` to four inputs, two of which are
`RescaledWindowModulusTail` — a uniform modulus-of-continuity tail for the *diffusively
rescaled* path laws `diffusivelyRescaledPathLaw μ ε`, uniformly over the small scales.
Stated that way the input mentions `BouRabeeGwynne.scaledBrownianPath` and a
`ProbabilityMeasure.map`, neither of which the martingale lane of this development ever
produces: every estimate there is about the law of the interpolation itself.

This file removes that mismatch.  Because the rescaling `f ↦ ε • f (ε⁻² ·)` is an exact
change of variables, an oscillation of the rescaled path by more than `c` across a time
lag `< d` inside the window `[0, m]` is *the same event* as an oscillation of the
original path by more than `c / ε` across a time lag `< ε⁻² d` inside the window
`[0, ε⁻² m]`.  So `RescaledWindowModulusTail μ T` follows from a family of window
moduli of `μ` alone, at the diffusively dilated window, lag and threshold.

Nothing here is a tightness estimate: `rescaledWindowModulusTail_of_diffusive_window_tails`
is an implication whose hypothesis is exactly as open as its conclusion.  What it buys is
that a producer can now work entirely with the interpolation law `μ` — no rescaling map,
no pushforward — which is the form in which `Limit/InterpolatedPathTightness`,
`Limit/UniformGridOscillation` and `Limit/GridModulusBracket` state their estimates.

## Main results

* `windowModulusFailure` — oscillation failure on an arbitrary `ℝ≥0` window, the
  parametrised form of `MartingaleLimit.halfLineModulusFailure`.
* `isOpen_halfLineModulusFailure`, `measurableSet_halfLineModulusFailure` — the failure
  set is open, hence Borel, so the pushforward can be computed on it.
* `scaledBrownianPath_preimage_halfLineModulusFailure_subset` — the change of variables.
* `rescaledWindowModulusTail_of_diffusive_window_tails` — the translation.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.DiffusiveModulusTranslation

open StatementIngredients
open ReflectedGMS.MartingaleLimit
open ReflectedGMS.TwoClockScalingLimitReduction

/-! ## The window modulus failure set -/

section Window

variable {E : Type*} [MetricSpace E] [ProperSpace E]

/-- Paths whose oscillation over a pair of times in the window `[0, b]` at distance less
than `δ` exceeds `a`.  This is `MartingaleLimit.halfLineModulusFailure` with the window
endpoint allowed to be an arbitrary nonnegative real rather than a natural number. -/
def windowModulusFailure (b : ℝ≥0) (a δ : ℝ) : Set C(ℝ≥0, E) :=
  {f | ∃ s ≤ b, ∃ t ≤ b, dist s t < δ ∧ a < dist (f s) (f t)}

/-- The window modulus failure set is open: evaluation at a fixed time is continuous on
the compact-open path space, and the set is a union of the open sets on which one fixed
pair of evaluations is far apart. -/
theorem isOpen_halfLineModulusFailure (m : ℕ) (c d : ℝ) :
    IsOpen (halfLineModulusFailure (E := E) m c d) := by
  rw [isOpen_iff_forall_mem_open]
  intro f hf
  simp only [halfLineModulusFailure, Set.mem_setOf_eq] at hf
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hf
  refine ⟨{g : C(ℝ≥0, E) | c < dist (g s) (g t)}, ?_, ?_, hlt⟩
  · intro g hg
    exact ⟨s, hs, t, ht, hst, hg⟩
  · exact isOpen_lt continuous_const
      ((continuous_eval_const s).dist (continuous_eval_const t))

theorem measurableSet_halfLineModulusFailure (m : ℕ) (c d : ℝ) :
    MeasurableSet (halfLineModulusFailure (E := E) m c d) :=
  (isOpen_halfLineModulusFailure m c d).measurableSet

end Window

/-! ## The change of variables -/

/-- **The diffusive rescaling turns a window oscillation into a dilated window
oscillation.**  A path whose rescaling `ε • f (ε⁻² ·)` oscillates by more than `c` across
a lag `< d` inside `[0, m]` itself oscillates by more than `c / ε` across a lag
`< ε⁻² d` inside `[0, ε⁻² m]`. -/
theorem scaledBrownianPath_preimage_halfLineModulusFailure_subset
    {ε : ℝ≥0} (hε : 0 < ε) (m : ℕ) (c d : ℝ) :
    BouRabeeGwynne.scaledBrownianPath ε⁻¹ ⁻¹'
        (halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m c d) ⊆
      windowModulusFailure (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ)) (((ε : ℝ))⁻¹ ^ 2 * d) := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hsqpos : (0 : ℝ) < ((ε : ℝ))⁻¹ ^ 2 := pow_pos (inv_pos.mpr hεR) 2
  have hsqnn : (0 : ℝ) ≤ ((ε : ℝ))⁻¹ ^ 2 := hsqpos.le
  have hmono : ∀ u : ℝ≥0, u ≤ (m : ℝ≥0) → ε⁻¹ ^ 2 * u ≤ ε⁻¹ ^ 2 * (m : ℝ≥0) := by
    intro u hu
    have huR : (u : ℝ) ≤ (m : ℝ) := by exact_mod_cast hu
    have hcoe : ((ε⁻¹ ^ 2 * u : ℝ≥0) : ℝ) ≤ ((ε⁻¹ ^ 2 * (m : ℝ≥0) : ℝ≥0) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left huR hsqnn
    exact_mod_cast hcoe
  have hdistEq : ∀ u v : ℝ≥0,
      dist (ε⁻¹ ^ 2 * u) (ε⁻¹ ^ 2 * v) = ((ε : ℝ))⁻¹ ^ 2 * dist u v := by
    intro u v
    rw [NNReal.dist_eq, NNReal.dist_eq]
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg hsqnn]
  intro f hf
  simp only [Set.mem_preimage, halfLineModulusFailure, Set.mem_setOf_eq] at hf
  obtain ⟨s, hs, t, ht, hst, hlt⟩ := hf
  rw [StatementIngredients.scaledBrownianPath_inv_apply ε hε f s,
    StatementIngredients.scaledBrownianPath_inv_apply ε hε f t, dist_smul₀,
    Real.norm_eq_abs, abs_of_nonneg ε.coe_nonneg] at hlt
  refine ⟨ε⁻¹ ^ 2 * s, hmono s hs, ε⁻¹ ^ 2 * t, hmono t ht, ?_, ?_⟩
  · rw [hdistEq s t]
    exact mul_lt_mul_of_pos_left hst hsqpos
  · rw [div_lt_iff₀ hεR]
    calc c < (ε : ℝ) * dist (f (ε⁻¹ ^ 2 * s)) (f (ε⁻¹ ^ 2 * t)) := hlt
      _ = dist (f (ε⁻¹ ^ 2 * s)) (f (ε⁻¹ ^ 2 * t)) * (ε : ℝ) := mul_comm _ _

/-! ## The translated input -/

/-- **`RescaledWindowModulusTail` from window moduli of the unrescaled law.**

CONDITIONAL on `h`; this proves no tightness estimate.  Its content is that the input
`RescaledWindowModulusTail μ T` of
`ReflectedGMS.TwoClockScalingLimitReduction.twoClockScalingLimit_of_window_modulus_of_finiteDimensional`
never has to be stated about a pushforward: it suffices to bound, for the interpolation
law `μ` itself and uniformly over the scales `ε ∈ T`, the probability that the path
oscillates by more than `c / ε` across a time lag `< ε⁻² d` inside the window
`[0, ε⁻² m]`.  That is the manuscript's diffusive tightness estimate, verbatim. -/
theorem rescaledWindowModulusTail_of_diffusive_window_tails
    (μ : ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) (T : Set ℝ≥0)
    (hT0 : ∀ ε ∈ T, 0 < ε)
    (h : ∀ (m : ℕ) (c : ℝ), 0 < c → ∀ η : ℝ≥0∞, 0 < η → ∃ d : ℝ, 0 < d ∧ ∀ ε ∈ T,
      (μ : Measure (BouRabeeGwynne.BrownianPath 2))
        (windowModulusFailure (E := BouRabeeGwynne.Euc 2)
          (ε⁻¹ ^ 2 * (m : ℝ≥0)) (c / (ε : ℝ)) (((ε : ℝ))⁻¹ ^ 2 * d)) ≤ η) :
    RescaledWindowModulusTail μ T := by
  intro m c hc η hη
  obtain ⟨d, hd, hdT⟩ := h m c hc η hη
  refine ⟨d, hd, fun ε hε => ?_⟩
  have hcoe : ((diffusivelyRescaledPathLaw μ ε :
      ProbabilityMeasure (BouRabeeGwynne.BrownianPath 2)) :
      Measure (BouRabeeGwynne.BrownianPath 2))
      = (μ : Measure (BouRabeeGwynne.BrownianPath 2)).map
          (BouRabeeGwynne.scaledBrownianPath ε⁻¹) := rfl
  rw [hcoe, Measure.map_apply (BouRabeeGwynne.measurable_scaledBrownianPath (d := 2) ε⁻¹)
    (measurableSet_halfLineModulusFailure (E := BouRabeeGwynne.Euc 2) m c d)]
  exact le_trans
    (measure_mono
      (scaledBrownianPath_preimage_halfLineModulusFailure_subset (hT0 ε hε) m c d))
    (hdT ε hε)

end ReflectedGMS.DiffusiveModulusTranslation
