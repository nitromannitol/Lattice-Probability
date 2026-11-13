/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryPotentialVariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryReflectedLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedSemigroupAction
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Stationary variance of a vertex resolvent potential

Starting the actual reflected process from the finite speed measure identifies
the exact squared increment of every weighted L² function with the usual
semigroup quadratic form.  The proof uses the actual time-zero law in each
starting component; no separate stationarity or form-process association
hypothesis is introduced.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem integral_sq_vertexSpeedMeasure
    (m : V → ℝ) (hm : ∀ x, 0 < m x) (f : V → ℝ)
    (hf : HasSpeedL2 m f) :
    (∫ x, (f x) ^ 2 ∂vertexSpeedMeasure m) =
      ‖weightedValue m f hf‖ ^ 2 := by
  rw [vertexSpeedMeasure, integral_sum_dirac (fun _ ↦ ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (hm _).le, smul_eq_mul]
  exact (weightedValue_norm_sq m hm f hf).symm

private theorem reflectedSpeedLaw_eq_sum
    (PF : ProcessFamily V) (m : V → ℝ) :
    reflectedSpeedLaw PF m =
      Measure.sum (fun z ↦ ENNReal.ofReal (m z) • PF.P z) := by
  unfold reflectedSpeedLaw
  rw [Measure.comp_eq_sum_of_countable]
  apply congrArg Measure.sum
  funext z
  rw [vertexSpeedMeasure_singleton]
  rfl

/-- Every weighted L² vector remains L² under the unnormalized stationary law. -/
theorem memLp_two_reflected_unweight_speedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : ValueSpace V) (t : ℝ≥0) :
    MemLp (fun ω ↦ (PF.X t ω).elim 0 (unweight m U)) 2
      (reflectedSpeedLaw PF m) := by
  let u := unweight m U
  let raw : Option V → ℝ := fun q ↦ q.elim 0 u
  have hu := hasSpeedL2_unweight m hm U
  have hs : Summable (fun x ↦ m x * (u x) ^ 2) := by
    unfold HasSpeedL2 at hu
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)] at hu
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs, mul_pow, Real.sq_sqrt (hm _).le] using hu
  have hi : Integrable (fun x ↦ (u x) ^ 2) (vertexSpeedMeasure m) := by
    apply integrable_sum_dirac (fun _ ↦ ENNReal.ofReal_ne_top)
    simpa only [ENNReal.toReal_ofReal (hm _).le, Real.norm_eq_abs, abs_sq] using hs
  have hr : Measurable raw := measurable_of_countable _
  have himap : Integrable (fun q ↦ (raw q) ^ 2)
      ((vertexSpeedMeasure m).map (some : V → Option V)) :=
    (integrable_map_measure (hr.pow_const 2).aestronglyMeasurable
      (measurable_of_countable (some : V → Option V)).aemeasurable).2 hi
  rw [← reflectedSpeedLaw_map_position h hG hm hmsum t] at himap
  apply (memLp_two_iff_integrable_sq
    (hr.comp (PF.measurable_X t)).aestronglyMeasurable).2
  exact (integrable_map_measure (hr.pow_const 2).aestronglyMeasurable
    (PF.measurable_X t).aemeasurable).1 himap

/-- Exact stationary expected squared increment for every weighted L² vector. -/
theorem integral_sq_sub_unweight_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : ValueSpace V) (t : ℝ≥0) :
    (∫ ω, ((PF.X t ω).elim 0 (unweight m U) -
        (PF.X 0 ω).elim 0 (unweight m U)) ^ 2 ∂reflectedSpeedLaw PF m) =
      2 * (‖U‖ ^ 2 - ⟪U, fullFormSemigroup G m t U⟫_ℝ) := by
  let u : V → ℝ := unweight m U
  let raw : Option V → ℝ := fun q ↦ q.elim 0 u
  let Z : ℝ≥0 → PF.Ω → ℝ := fun s ω ↦ raw (PF.X s ω)
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have huU : u = unweight m U := rfl
  have huL2 : HasSpeedL2 m u := hasSpeedL2_unweight m hm U
  have hweighted : weightedValue m u huL2 = U := weightedValue_unweight m hm U
  have hraw_meas : Measurable raw := measurable_of_countable _
  have hZ_meas (s : ℝ≥0) : Measurable (Z s) :=
    hraw_meas.comp (PF.measurable_X s)
  have hZ2 (s : ℝ≥0) : MemLp (Z s) 2 (reflectedSpeedLaw PF m) :=
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum U s
  have hZ_sq_int (s : ℝ≥0) :
      Integrable (fun ω ↦ (Z s ω) ^ 2) (reflectedSpeedLaw PF m) :=
    (memLp_two_iff_integrable_sq (hZ_meas s).aestronglyMeasurable).1 (hZ2 s)
  have hcross_int : Integrable (fun ω ↦ Z t ω * Z 0 ω)
      (reflectedSpeedLaw PF m) := (hZ2 t).integrable_mul (hZ2 0)
  have hsq (s : ℝ≥0) :
      (∫ ω, (Z s ω) ^ 2 ∂reflectedSpeedLaw PF m) = ‖U‖ ^ 2 := by
    calc
      (∫ ω, (Z s ω) ^ 2 ∂reflectedSpeedLaw PF m) =
          ∫ q, (raw q) ^ 2 ∂(reflectedSpeedLaw PF m).map (PF.X s) := by
        simpa only [Z, Function.comp_apply] using
          (integral_map (PF.measurable_X s).aemeasurable
            (hraw_meas.pow_const 2).aestronglyMeasurable).symm
      _ = ∫ q, (raw q) ^ 2
          ∂(vertexSpeedMeasure m).map (some : V → Option V) := by
        rw [reflectedSpeedLaw_map_position h hG hm hmsum s]
      _ = ∫ x, (u x) ^ 2 ∂vertexSpeedMeasure m := by
        simpa only [raw, Function.comp_apply, Option.elim_some] using
          integral_map (measurable_of_countable (some : V → Option V)).aemeasurable
            (hraw_meas.pow_const 2).aestronglyMeasurable
      _ = ‖weightedValue m u huL2‖ ^ 2 :=
        integral_sq_vertexSpeedMeasure m hm u huL2
      _ = ‖U‖ ^ 2 := by rw [hweighted]
  have hcross :
      (∫ ω, Z t ω * Z 0 ω ∂reflectedSpeedLaw PF m) =
        ⟪U, fullFormSemigroup G m t U⟫_ℝ := by
    have hcross_sum : Integrable (fun ω ↦ Z t ω * Z 0 ω)
        (Measure.sum (fun z ↦ ENNReal.ofReal (m z) • PF.P z)) := by
      rw [← reflectedSpeedLaw_eq_sum PF m]
      exact hcross_int
    rw [reflectedSpeedLaw_eq_sum PF m, integral_sum_measure hcross_sum]
    simp only [integral_smul_measure,
      ENNReal.toReal_ofReal (hm _).le, smul_eq_mul]
    rw [lp.inner_eq_tsum]
    apply tsum_congr
    intro z
    have hcomponent :
        (∫ ω, Z t ω * Z 0 ω ∂PF.P z) =
          u z * unweight m (fullFormSemigroup G m t U) z := by
      calc
        (∫ ω, Z t ω * Z 0 ω ∂PF.P z) =
            ∫ ω, u z * Z t ω ∂PF.P z := by
          apply integral_congr_ae
          filter_upwards [(h z).1] with ω hzero
          simp only [Z, raw, hzero, Option.elim_some]
          ring
        _ = u z * ∫ ω, Z t ω ∂PF.P z := by
          rw [integral_const_mul]
        _ = u z * unweight m (fullFormSemigroup G m t U) z := by
          rw [show (∫ ω, Z t ω ∂PF.P z) =
              unweight m (fullFormSemigroup G m t U) z by
            change (∫ ω, (PF.X t ω).elim 0 u ∂PF.P z) = _
            rw [huU]
            exact integral_reflected_unweight_at_time h hG hm hmsum t z U]
    rw [hcomponent]
    simp only [Real.inner_apply]
    rw [show U z = Real.sqrt (m z) * u z by
      rw [← hweighted]
      rfl]
    unfold unweight
    have hs : Real.sqrt (m z) ≠ 0 := (Real.sqrt_pos.2 (hm z)).ne'
    field_simp [hs]
    rw [Real.sq_sqrt (hm z).le]
    ring
  change (∫ ω, (Z t ω - Z 0 ω) ^ 2 ∂reflectedSpeedLaw PF m) =
    2 * (‖U‖ ^ 2 - ⟪U, fullFormSemigroup G m t U⟫_ℝ)
  rw [show (fun ω ↦ (Z t ω - Z 0 ω) ^ 2) =
      fun ω ↦ (Z t ω) ^ 2 - 2 * (Z t ω * Z 0 ω) + (Z 0 ω) ^ 2 by
    funext ω
    ring]
  have htwo_cross : Integrable (fun ω ↦ 2 * (Z t ω * Z 0 ω))
      (reflectedSpeedLaw PF m) := hcross_int.const_mul 2
  have hsub : Integrable (fun ω ↦ (Z t ω) ^ 2 - 2 * (Z t ω * Z 0 ω))
      (reflectedSpeedLaw PF m) := (hZ_sq_int t).sub htwo_cross
  rw [integral_add hsub (hZ_sq_int 0),
    integral_sub (hZ_sq_int t) htwo_cross, integral_const_mul,
    hsq t, hcross, hsq 0]
  ring

end ReflectedGMS
