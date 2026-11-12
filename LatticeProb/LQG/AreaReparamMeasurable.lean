import LatticeProb.Analysis.VagueLimitMeasurable
import LatticeProb.LQG.MassReparamBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCone.AreaBridge
import LatticeProb.Bonanno.LQGMetric.Field.LQGMeasureFieldMeasurable
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-!
# Measurability of the area reparametrization of curves

The `γ`-LQG area measure `lqgArea γ h` is the vague limit of the dyadic area approximations of `h`
when that limit exists, and the junk value `0` otherwise. On the set of fields `h` whose
approximations do converge vaguely, the area measure depends measurably on `h` for the subspace
`σ`-algebra (`measurable_lqgArea_subtype`), and so does the reparametrization
`t ↦ massReparam (lqgArea γ h) c t` of a continuous curve `c` by the `γ`-LQG mass
(`measurable_areaReparam_domRestrict`). The set of such fields need not be measurable, so these
are statements about the restriction to that set.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.LQG

open LQGMetric MatedCRTHarmonic.CellScaling LatticeProb.VagueLimit

/-- The dyadic density `(h, z) ↦ 2^{-kγ²/2} e^{γ h_{2^{-k}}(z)}` of the `γ`-LQG area approximation
is jointly measurable in the field and the point. -/
theorem measurable_lqgAreaDensity_uncurry_field (γ : ℝ) (k : ℕ) :
    Measurable (Function.uncurry fun (h : DistC) (z : ℂ) =>
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * circleAvg h (dyadicScale k) z)) := by
  have h1 : Measurable fun p : DistC × ℂ => circleAvg p.1 (dyadicScale k) p.2 :=
    measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, dyadicScale k, p.2))
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul h1))

/-- The integral of a continuous function against the `k`-th dyadic `γ`-LQG area approximation is a
measurable function of the field. -/
theorem measurable_integral_lqgAreaApprox (γ : ℝ) (k : ℕ) {f : ℂ → ℝ} (hf : Measurable f) :
    Measurable fun h : DistC => ∫ z, f z ∂(lqgAreaApprox γ h k) :=
  measurable_integral_withDensity_ofReal_uncurry (measurable_lqgAreaDensity_uncurry_field γ k)
    (fun _ _ => mul_nonneg (Real.rpow_nonneg (by unfold dyadicScale; positivity) _)
      (Real.exp_pos _).le) hf

/-- **The `γ`-LQG area measure is measurable on the set of fields where it is a vague limit.** -/
theorem measurable_lqgArea_subtype (γ : ℝ) :
    Measurable fun h : {h : DistC | ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ} => lqgArea γ h.1 :=
  measurable_vagueLimitOrZero_subtype (m := fun k h => lqgAreaApprox γ h k)
    fun k _ hf _ => measurable_integral_lqgAreaApprox γ k hf.measurable

/-- The `γ`-LQG area measure of any field is finite on compact sets. -/
theorem isFiniteMeasureOnCompacts_lqgArea (γ : ℝ) (h : DistC) :
    IsFiniteMeasureOnCompacts (lqgArea γ h) :=
  ⟨fun _ hK => vagueLimitOrZero_lt_top (lqgAreaApprox γ h) hK⟩

/-- **Measurability of the area reparametrization.** On the set of pairs `(h, c)` of a field whose
dyadic `γ`-LQG area approximations converge vaguely and a continuous curve `c`, the map
`(h, c) ↦ (h, t ↦ massReparam (lqgArea γ h) c t)` is measurable for the subspace `σ`-algebra. -/
theorem measurable_areaReparam_domRestrict (γ : ℝ) :
    Measurable (({h : DistC | ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ} ×ˢ
        (univ : Set C(ℝ, ℂ))).domRestrict
      fun p : DistC × C(ℝ, ℂ) => (p.1, fun t => massReparam (lqgArea γ p.1) p.2 t)) := by
  set S := {h : DistC | ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ}
  have hfst : Measurable fun p : ↥(S ×ˢ (univ : Set C(ℝ, ℂ))) => p.1.1 :=
    measurable_fst.comp measurable_subtype_coe
  have hμ : Measurable fun p : ↥(S ×ˢ (univ : Set C(ℝ, ℂ))) => lqgArea γ p.1.1 :=
    (measurable_lqgArea_subtype γ).comp (f := fun p : ↥(S ×ˢ (univ : Set C(ℝ, ℂ))) =>
      (⟨p.1.1, p.2.1⟩ : S)) hfst.subtype_mk
  refine hfst.prodMk (Measurable.of_eval fun t => ?_)
  exact measurable_massReparam hμ (fun p => isFiniteMeasureOnCompacts_lqgArea γ p.1.1)
    (fun p => p.1.2.continuous)
    (fun s => (continuous_eval_const s).measurable.comp
      (measurable_snd.comp measurable_subtype_coe)) t

end LatticeProb.LQG
