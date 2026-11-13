/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.JumpOccupationL1Continuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.L1StateTimeIntegrability
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpRateEnergyContinuity

/-!
# L1 continuity of the adapted jump occupation

The all-time raw-integral representation of the adapted occupation turns the
difference of two occupations into the time integral of the difference of
their canonical ordinary-edge rates. Fubini and stationarity give the exact
speed-`L1` operator norm, and the positive mass of a starting vertex transfers
the estimate to every actual starting law.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u_1
variable {V : Type u_1} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem integrable_stateVertexCarreDuChamp_toReal
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    Integrable (fun x : V ↦
      (stateVertexCarreDuChamp G m u (some x)).toReal)
      (vertexSpeedMeasure m) := by
  have hzero : G.HasFiniteEnergy (0 : V → ℝ) := by
    change Summable (G.gradSq (0 : V → ℝ))
    convert (summable_zero : Summable (fun _ : V × V ↦ (0 : ℝ))) using 1
    funext p
    simp [ConductanceGraph.gradSq]
  have h := integrable_stateVertexCarreDuChamp_toReal_sub G m hm hu hzero
  simpa [stateVertexCarreDuChamp, vertexCarreDuChamp] using h

/-- The adapted jump-occupation map is an `L1` contraction up to elapsed time
and the reciprocal mass of the starting vertex. -/
theorem mul_integral_abs_adaptedJumpOccupation_sub_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u v : V → ℝ}
    (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v)
    (T : ℝ≥0) (z : V) :
    m z * (∫ ω, |adaptedJumpOccupation PF G m u T ω -
        adaptedJumpOccupation PF G m v T ω| ∂PF.P z) ≤
      (T : ℝ) * (∫ x : V,
        |(stateVertexCarreDuChamp G m u (some x)).toReal -
          (stateVertexCarreDuChamp G m v (some x)).toReal|
        ∂vertexSpeedMeasure m) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let f : V → ℝ := fun x ↦
    (stateVertexCarreDuChamp G m u (some x)).toReal -
      (stateVertexCarreDuChamp G m v (some x)).toReal
  have hf : Integrable f (vertexSpeedMeasure m) :=
    integrable_stateVertexCarreDuChamp_toReal_sub G m hm hu hv
  have hfu : Integrable (fun x : V ↦
      (stateVertexCarreDuChamp G m u (some x)).toReal)
      (vertexSpeedMeasure m) :=
    integrable_stateVertexCarreDuChamp_toReal G m hm hu
  have hfv : Integrable (fun x : V ↦
      (stateVertexCarreDuChamp G m v (some x)).toReal)
      (vertexSpeedMeasure m) :=
    integrable_stateVertexCarreDuChamp_toReal G m hm hv
  have hjoint : Integrable (Function.uncurry (dyadicStateObservable PF f))
      ((reflectedSpeedLaw PF m).prod
        (volume.restrict (Icc 0 (T : ℝ)))) :=
    integrable_dyadicStateObservable_time_reflectedSpeedLaw
      h hG hm hmsum hf T
  have hjointZ : Integrable (Function.uncurry (dyadicStateObservable PF f))
      ((PF.P z).prod (volume.restrict (Icc 0 (T : ℝ)))) :=
    integrable_dyadicStateObservable_time_start h hG hm hmsum hf T z
  have hjointZu := integrable_dyadicStateObservable_time_start
    h hG hm hmsum hfu T z
  have hjointZv := integrable_dyadicStateObservable_time_start
    h hG hm hmsum hfv T z
  let B : PF.Ω → ℝ := fun ω ↦
    ∫ r : ℝ in Icc 0 (T : ℝ), ‖dyadicStateObservable PF f ω r‖
  have hBintS : Integrable B (reflectedSpeedLaw PF m) := hjoint.norm.integral_prod_left
  have hBintZ : Integrable B (PF.P z) := hjointZ.norm.integral_prod_left
  have hpoint : ∀ᵐ ω ∂PF.P z,
      |adaptedJumpOccupation PF G m u T ω -
        adaptedJumpOccupation PF G m v T ω| ≤ B ω := by
    filter_upwards [adaptedJumpOccupation_ae_eq_all_continuous_monotone
        h hG hm hmsum hu z,
      adaptedJumpOccupation_ae_eq_all_continuous_monotone
        h hG hm hmsum hv z,
      ae_rightRegularAt (h z).2.2.1 (h z).2.2.2.1,
      hjointZu.prod_right_ae, hjointZv.prod_right_ae] with ω huω hvω hreg hiu hiv
    rw [huω.1 T, hvω.1 T]
    have heu :
        (∫ r : ℝ in Icc 0 (T : ℝ),
          (stateVertexCarreDuChamp G m u
            (PF.X (Real.toNNReal r) ω)).toReal) =
        ∫ r : ℝ in Icc 0 (T : ℝ),
          dyadicStateObservable PF
            (fun x ↦ (stateVertexCarreDuChamp G m u (some x)).toReal) ω r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      simp only [dyadicStateObservable,
        dyadicLimit_eq_of_rightRegular hreg]
      cases PF.X (Real.toNNReal r) ω <;> rfl
    have hev :
        (∫ r : ℝ in Icc 0 (T : ℝ),
          (stateVertexCarreDuChamp G m v
            (PF.X (Real.toNNReal r) ω)).toReal) =
        ∫ r : ℝ in Icc 0 (T : ℝ),
          dyadicStateObservable PF
            (fun x ↦ (stateVertexCarreDuChamp G m v (some x)).toReal) ω r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      simp only [dyadicStateObservable,
        dyadicLimit_eq_of_rightRegular hreg]
      cases PF.X (Real.toNNReal r) ω <;> rfl
    change Integrable (fun r ↦ dyadicStateObservable PF
      (fun x ↦ (stateVertexCarreDuChamp G m u (some x)).toReal) ω r)
      (volume.restrict (Icc 0 (T : ℝ))) at hiu
    change Integrable (fun r ↦ dyadicStateObservable PF
      (fun x ↦ (stateVertexCarreDuChamp G m v (some x)).toReal) ω r)
      (volume.restrict (Icc 0 (T : ℝ))) at hiv
    rw [heu, hev, ← integral_sub hiu hiv]
    apply (abs_integral_le_integral_abs).trans_eq
    apply integral_congr_ae
    filter_upwards with r
    simp only [Real.norm_eq_abs, dyadicStateObservable, f,
      dyadicLimit_eq_of_rightRegular hreg]
    cases PF.X (Real.toNNReal r) ω <;> simp
  have hleft : Integrable (fun ω ↦
      |adaptedJumpOccupation PF G m u T ω -
        adaptedJumpOccupation PF G m v T ω|) (PF.P z) :=
    ((integrable_adaptedJumpOccupation h hG hm hmsum hu T z).sub
      (integrable_adaptedJumpOccupation h hG hm hmsum hv T z)).abs
  have hstart :
      m z * (∫ ω, |adaptedJumpOccupation PF G m u T ω -
          adaptedJumpOccupation PF G m v T ω| ∂PF.P z) ≤
        m z * ∫ ω, B ω ∂PF.P z := by
    exact mul_le_mul_of_nonneg_left
      (integral_mono_ae hleft hBintZ hpoint) (hm z).le
  have hdom := integral_mono_measure
    (smul_start_le_reflectedSpeedLaw PF m z)
    (ae_of_all _ fun ω ↦ by exact integral_nonneg fun _ ↦ norm_nonneg _)
    hBintS
  have hstationary :
      (∫ ω, B ω ∂reflectedSpeedLaw PF m) =
        (T : ℝ) * ∫ x : V, |f x| ∂vertexSpeedMeasure m := by
    calc
      (∫ ω, B ω ∂reflectedSpeedLaw PF m) =
          ∫ r : ℝ in Icc 0 (T : ℝ),
            ∫ ω, ‖dyadicStateObservable PF f ω r‖
              ∂reflectedSpeedLaw PF m := integral_integral_swap hjoint.norm
      _ = ∫ r : ℝ in Icc 0 (T : ℝ),
            ∫ x : V, ‖f x‖ ∂vertexSpeedMeasure m := by
          apply integral_congr_ae
          filter_upwards with r
          exact integral_norm_dyadicStateObservable_reflectedSpeedLaw
            h hG hm hmsum f r
      _ = (T : ℝ) * ∫ x : V, |f x| ∂vertexSpeedMeasure m := by
          simp only [Real.norm_eq_abs]
          rw [setIntegral_const, measureReal_def, Real.volume_Icc]
          simp only [sub_zero, ENNReal.toReal_ofReal T.coe_nonneg, smul_eq_mul]
  apply hstart.trans
  calc
    m z * ∫ ω, B ω ∂PF.P z =
        ∫ ω, B ω ∂(ENNReal.ofReal (m z) • PF.P z) := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal (hm z).le, smul_eq_mul]
    _ ≤ ∫ ω, B ω ∂reflectedSpeedLaw PF m := hdom
    _ = (T : ℝ) * ∫ x : V, |f x| ∂vertexSpeedMeasure m := hstationary
    _ = (T : ℝ) * (∫ x : V,
        |(stateVertexCarreDuChamp G m u (some x)).toReal -
          (stateVertexCarreDuChamp G m v (some x)).toReal|
        ∂vertexSpeedMeasure m) := rfl

end ReflectedGMS
