/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexDynkinSquareCompensation at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1TrajectoryOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1SemigroupTimeIntegral
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1SquareDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedIntegrableTrajectoryConditional
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventSquareGenerator
import Mathlib.Probability.Martingale.Basic
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinOccupationPairing

/-!
# Square compensation for the vertex Dynkin martingale

The square Dynkin formula is combined with the conditional occupation pairing.
The bounded drift terms cancel by the deterministic square identity for an
interval-integral primitive.  This proves only the resolvent-potential
martingale with the ordinary-edge occupation candidate; it does not identify
the full Fukushima bracket or exclude additional boundary contributions.
-/

-- Merged from `ReflectedGMS/Forms/PrimitiveSquareIdentity.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_PrimitiveSquareIdentity

/-!
# Square increments of an interval-integral primitive

This file records the deterministic calculus identity used when assembling
square brackets.  Only interval integrability of the integrand is needed.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

/-- If `A(r) = ∫ u in a..r, f u`, then the increment of `A²` on `[s,t]`
is twice the integral of `A f`.  No continuity assumption on `f` is used. -/
theorem intervalIntegral_sq_sub_sq_eq_two_mul_integral
    {f : ℝ → ℝ} {a s t : ℝ}
    (hf : IntervalIntegrable f volume a t) (has : a ≤ s) (hst : s ≤ t) :
    (∫ u in a..t, f u) ^ 2 - (∫ u in a..s, f u) ^ 2 =
      2 * ∫ r in s..t, (∫ u in a..r, f u) * f r := by
  let A : ℝ → ℝ := fun r ↦ ∫ u in a..r, f u
  have hat : a ≤ t := has.trans hst
  have hsub : uIcc s t ⊆ uIcc a t := by
    rw [uIcc_of_le hst, uIcc_of_le hat]
    exact Icc_subset_Icc has le_rfl
  have hA : AbsolutelyContinuousOnInterval A s t :=
    (hf.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp [hat])).mono hsub
  have hderiv : ∀ᵐ r, r ∈ uIcc s t → deriv A r = f r := by
    filter_upwards [hf.ae_hasDerivAt_integral] with r hr hrs
    exact (hr (hsub hrs) a (by simp [hat])).deriv
  have hparts := hA.integral_deriv_mul_eq_sub hA
  calc
    A t ^ 2 - A s ^ 2 = A t * A t - A s * A s := by ring
    _ = ∫ r in s..t, deriv A r * A r + A r * deriv A r := hparts.symm
    _ = ∫ r in s..t, 2 * (A r * f r) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderiv] with r hr hrs
      rw [hr (uIoc_subset_uIcc hrs)]
      ring
    _ = 2 * ∫ r in s..t, A r * f r := by rw [intervalIntegral.integral_const_mul]

end ReflectedGMS

end Merged_PrimitiveSquareIdentity

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem boundedStateOccupationVersion_sub_ae
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (f : Option V → ℝ) {C : ℝ} (hf : ∀ q, |f q| ≤ C) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦ boundedStateOccupationVersion PF f t ω -
      boundedStateOccupationVersion PF f s ω) =ᵐ[PF.P z]
      fun ω ↦ ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        f (PF.X r.toNNReal ω) := by
  filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
      h f hf z, ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hocc hreg
  let H : ℝ → ℝ := fun r ↦ f (PF.X r.toNNReal ω)
  have hHmeas : Measurable H := by
    rw [show H = fun r : ℝ ↦ f (dyadicLimit PF.X r.toNNReal ω) by
      funext r
      dsimp only [H]
      rw [dyadicLimit_eq_of_rightRegular hreg]]
    exact (measurable_of_countable f).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have hC : 0 ≤ C := (abs_nonneg (f none)).trans (hf none)
  have hHint (a b : ℝ) : IntervalIntegrable H volume a b := by
    constructor
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [H, Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X r.toNNReal ω)
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [H, Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X r.toNNReal ω)
  rw [hocc.1 t, hocc.1 s]
  change (∫ r : ℝ in Icc 0 (t : ℝ), H r) -
      (∫ r : ℝ in Icc 0 (s : ℝ), H r) =
    ∫ r : ℝ in Icc (s : ℝ) (t : ℝ), H r
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le t.coe_nonneg,
    ← intervalIntegral.integral_of_le s.coe_nonneg,
    ← intervalIntegral.integral_of_le (by exact_mod_cast hst)]
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hHint 0 (s : ℝ)) (hHint (s : ℝ) (t : ℝ))
  linarith

theorem boundedStateOccupationVersion_sq_sub_sq_ae
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (f : Option V → ℝ) {C : ℝ} (hf : ∀ q, |f q| ≤ C) (z : V)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦ (boundedStateOccupationVersion PF f t ω) ^ 2 -
      (boundedStateOccupationVersion PF f s ω) ^ 2) =ᵐ[PF.P z]
      fun ω ↦ 2 * ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        boundedStateOccupationVersion PF f r.toNNReal ω *
          f (PF.X r.toNNReal ω) := by
  filter_upwards [boundedStateOccupationVersion_ae_eq_all_and_continuous
      h f hf z, ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1] with ω hocc hreg
  let H : ℝ → ℝ := fun r ↦ f (PF.X r.toNNReal ω)
  have hHmeas : Measurable H := by
    rw [show H = fun r : ℝ ↦ f (dyadicLimit PF.X r.toNNReal ω) by
      funext r
      dsimp only [H]
      rw [dyadicLimit_eq_of_rightRegular hreg]]
    exact (measurable_of_countable f).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have hC : 0 ≤ C := (abs_nonneg (f none)).trans (hf none)
  have hHint : IntervalIntegrable H volume 0 (t : ℝ) := by
    constructor
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [H, Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X r.toNNReal ω)
    · apply (integrableOn_const (C := C) measure_Ioc_lt_top.ne).mono'
      · exact hHmeas.aestronglyMeasurable
      · filter_upwards [] with r
        simpa [H, Real.norm_eq_abs, abs_of_nonneg hC] using hf (PF.X r.toNNReal ω)
  have hsq := intervalIntegral_sq_sub_sq_eq_two_mul_integral
    hHint s.coe_nonneg (by exact_mod_cast hst)
  rw [hocc.1 t, hocc.1 s]
  change (∫ r : ℝ in Icc 0 (t : ℝ), H r) ^ 2 -
      (∫ r : ℝ in Icc 0 (s : ℝ), H r) ^ 2 =
    2 * ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
      boundedStateOccupationVersion PF f r.toNNReal ω * H r
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le t.coe_nonneg,
    ← intervalIntegral.integral_of_le s.coe_nonneg]
  rw [hsq]
  congr 1
  rw [intervalIntegral.integral_of_le (by exact_mod_cast hst),
    integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r hr
  have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.1.le
  dsimp
  rw [hocc.1 r.toNNReal]
  rw [Real.coe_toNNReal r hr0, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hr0]

/-- Generic final assembly for a square-compensation argument.  If `N` has
increments equal to those of a martingale `Q`, up to the mixed
martingale--occupation cancellation supplied by `K` and `J`, then `N` is a
martingale. -/
theorem martingale_of_squareCompensation_increment
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF) (z : V)
    (N Q K : ℝ≥0 → PF.Ω → ℝ) (J : ℝ≥0 → ℝ≥0 → PF.Ω → ℝ)
    (hNa : StronglyAdapted PF.naturalFiltration N)
    (hNi : ∀ t, Integrable (N t) (PF.P z))
    (hQ : Martingale Q PF.naturalFiltration (PF.P z))
    (hKi : ∀ t, Integrable (K t) (PF.P z))
    (hinc : ∀ {s t : ℝ≥0} (hst : s ≤ t),
      (fun ω ↦ N t ω - N s ω) =ᵐ[PF.P z]
        fun ω ↦ (Q t ω - Q s ω) -
          2 * ((K t ω - K s ω) - J s t ω))
    (hmixed : ∀ {s t : ℝ≥0} (hst : s ≤ t) {E : Set PF.Ω},
      MeasurableSet[PF.naturalFiltration s] E →
      (∫ ω in E, K t ω - K s ω ∂PF.P z) =
        ∫ ω in E, J s t ω ∂PF.P z) :
    Martingale N PF.naturalFiltration (PF.P z) := by
  refine ⟨hNa, fun s t hst ↦ ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq
    (PF.naturalFiltration.le s) (hNi t) (fun _ _ _ ↦ (hNi s).integrableOn) ?_
      (hNa s).aestronglyMeasurable).symm
  intro E hE _
  have hinc' := hinc hst
  have hJi : Integrable (J s t) (PF.P z) := by
    have hi := ((hKi t).sub (hKi s)).sub
      ((((hQ.integrable t).sub (hQ.integrable s)).sub
        ((hNi t).sub (hNi s))).const_mul (1 / 2))
    apply hi.congr
    filter_upwards [hinc'] with ω hω
    change (K t ω - K s ω) - (1 / 2) *
      ((Q t ω - Q s ω) - (N t ω - N s ω)) = J s t ω
    linarith
  have hmixed' := hmixed hst hE
  have hzero : (∫ ω in E, N t ω - N s ω ∂PF.P z) = 0 := by
    calc
      _ = ∫ ω in E, (Q t ω - Q s ω) -
          2 * ((K t ω - K s ω) - J s t ω) ∂PF.P z :=
        integral_congr_ae (ae_restrict_of_ae hinc')
      _ = ((∫ ω in E, Q t ω ∂PF.P z) - ∫ ω in E, Q s ω ∂PF.P z) -
          2 * ((∫ ω in E, K t ω - K s ω ∂PF.P z) -
            ∫ ω in E, J s t ω ∂PF.P z) := by
        have hsplit := integral_sub (μ := (PF.P z).restrict E)
          ((hQ.integrable t).sub (hQ.integrable s)).integrableOn
          ((((hKi t).sub (hKi s)).sub hJi).const_mul 2).integrableOn
        have hKsplit := integral_sub (μ := (PF.P z).restrict E)
          ((hKi t).sub (hKi s)).integrableOn hJi.integrableOn
        simp only [Pi.sub_apply] at hsplit hKsplit
        rw [hsplit, integral_const_mul, hKsplit,
          integral_sub (hQ.integrable t).integrableOn (hQ.integrable s).integrableOn]
      _ = 0 := by
        rw [hmixed', hQ.setIntegral_eq hst hE]
        ring
  rw [integral_sub (hNi t).integrableOn (hNi s).integrableOn] at hzero
  linarith

end ReflectedGMS
