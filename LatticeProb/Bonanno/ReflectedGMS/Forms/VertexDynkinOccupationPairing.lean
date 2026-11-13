/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexDynkinOccupationPairing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.MartingaleOccupationPairing
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinMartingale

/-!
# Pairing the vertex Dynkin martingale with its occupation drift

This specializes the conditional Fubini identity to the actual (raw-path)
vertex Dynkin martingale and drift.  Joint measurability is obtained from their
canonical dyadic versions and the simultaneous almost-sure identification of
the dyadic and raw paths.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- Uniform finite-horizon bound for the ordinary vertex Dynkin martingale. -/
theorem norm_vertexDynkinMartingale_le [DecidableEq V]
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha) (y : V)
    {r t : ℝ≥0} (hrt : r ≤ t) (ω : PF.Ω) :
    ‖vertexDynkinMartingale PF G m alpha y r ω‖ ≤
      1 / alpha + (t : ℝ) * 2 := by
  unfold vertexDynkinMartingale
  calc
    ‖(PF.X r ω).elim 0 (vertexOccupationPotential G m alpha · y) -
        boundedStateOccupationVersion PF (vertexDynkinIntegrand G m alpha y) r ω‖
        ≤ ‖(PF.X r ω).elim 0 (vertexOccupationPotential G m alpha · y)‖ +
          ‖boundedStateOccupationVersion PF
            (vertexDynkinIntegrand G m alpha y) r ω‖ := norm_sub_le _ _
    _ ≤ 1 / alpha + (r : ℝ) * 2 := by
      apply add_le_add
      · cases PF.X r ω with
        | none => simpa using one_div_nonneg.mpr ha.le
        | some x =>
            rw [Option.elim_some, Real.norm_eq_abs,
              abs_of_nonneg (vertexOccupationPotential_nonneg G m hm ha x y)]
            exact vertexOccupationPotential_le_inv G m hm ha x y
      · exact norm_boundedStateOccupationVersion_le PF _ r
          (vertexDynkinIntegrand_bound G m hm ha y) ω
    _ ≤ 1 / alpha + (t : ℝ) * 2 := by
      gcongr

theorem measurable_uncurry_real_dyadicLimit (PF : ProcessFamily V) :
    Measurable (fun p : ℝ × PF.Ω ↦
      dyadicLimit PF.X p.1.toNNReal p.2) := by
  have h : Measurable (fun p : PF.Ω × ℝ ↦
      dyadicLimit PF.X p.2.toNNReal p.1) :=
    measurable_swap_toNNReal (measurable_uncurry_dyadicLimit PF.measurable_X)
  have hs : Measurable (fun p : ℝ × PF.Ω ↦ (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  change Measurable ((fun p : PF.Ω × ℝ ↦
    dyadicLimit PF.X p.2.toNNReal p.1) ∘ (fun p : ℝ × PF.Ω ↦ (p.2, p.1)))
  exact h.comp hs

private theorem boundedStateOccupationVersion_sub_eq_dyadicIntegral
    (PF : ProcessFamily V) (f : Option V → ℝ) {C : ℝ}
    (hf : ∀ q, |f q| ≤ C) {s t : ℝ≥0} (hst : s ≤ t) (ω : PF.Ω) :
    boundedStateOccupationVersion PF f t ω -
        boundedStateOccupationVersion PF f s ω =
      ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        f (dyadicLimit PF.X r.toNNReal ω) := by
  let g : ℝ → ℝ := fun r ↦ f (dyadicLimit PF.X r.toNNReal ω)
  have hg : Measurable g :=
    (measurable_of_countable f).comp
      (measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω)
  have hC : 0 ≤ C := (abs_nonneg (f none)).trans (hf none)
  have hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    constructor
    · apply (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
      · exact hg.aestronglyMeasurable
      filter_upwards [] with r
      simpa [g, Real.norm_eq_abs, abs_of_nonneg hC] using
        hf (dyadicLimit PF.X r.toNNReal ω)
    · apply (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self).mono'
      · exact hg.aestronglyMeasurable
      filter_upwards [] with r
      simpa [g, Real.norm_eq_abs, abs_of_nonneg hC] using
        hf (dyadicLimit PF.X r.toNNReal ω)
  have hstR : (s : ℝ) ≤ (t : ℝ) := by exact_mod_cast hst
  rw [boundedStateOccupationVersion_eq_dyadicIntegral,
    boundedStateOccupationVersion_eq_dyadicIntegral]
  change (∫ r : ℝ in Icc 0 (t : ℝ), g r) -
      (∫ r : ℝ in Icc 0 (s : ℝ), g r) =
    ∫ r : ℝ in Icc (s : ℝ) (t : ℝ), g r
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le t.coe_nonneg,
    ← intervalIntegral.integral_of_le s.coe_nonneg,
    ← intervalIntegral.integral_of_le hstR]
  linarith [intervalIntegral.integral_add_adjacent_intervals
    (hgi 0 (s : ℝ)) (hgi (s : ℝ) (t : ℝ))]

/-- On every starting law, increments of the canonical occupation equal the
raw-path occupation over the corresponding time interval. -/
theorem boundedStateOccupationVersion_sub_ae_eq_raw_integral
    {G : ConductanceGraph V} {w : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V} (h : IsReflectedWalk G w hmin PF)
    (f : Option V → ℝ) {C : ℝ} (hf : ∀ q, |f q| ≤ C)
    (z : V) {s t : ℝ≥0} (hst : s ≤ t) :
    (fun ω ↦ boundedStateOccupationVersion PF f t ω -
        boundedStateOccupationVersion PF f s ω) =ᵐ[PF.P z]
      fun ω ↦ ∫ r : ℝ in Icc (s : ℝ) (t : ℝ),
        f (PF.X r.toNNReal ω) := by
  filter_upwards [ae_dyadicLimit_eq (h z).2.2.1 (h z).2.2.2.1] with ω hω
  rw [boundedStateOccupationVersion_sub_eq_dyadicIntegral PF f hf hst ω]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r _
  change f (dyadicLimit PF.X r.toNNReal ω) = f (PF.X r.toNNReal ω)
  rw [hω]

end ReflectedGMS
