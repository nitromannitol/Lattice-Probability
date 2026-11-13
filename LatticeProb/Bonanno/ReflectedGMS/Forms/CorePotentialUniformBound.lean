/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CorePotentialUniformBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryPotentialUniformTime
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreMartingale
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreLinearity

/-!
# Uniform maximal bounds for compact resolvent-core potentials

The finite-grid stationary maximal estimate transfers to the actual compact
realization of every countable resolvent-core potential.  The compact process
supplies the required measurable càdlàg modification, while its fixed-time
projection identifies each dyadic value with the decoded full-form potential.
-/

-- Merged from `ReflectedGMS/Forms/StoppedGeneratorLocalization.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_StoppedGeneratorLocalization

/-!
# Localization of compact resolvent-core Dynkin martingales

The canonical occupation compensator vanishes up to a stopping time whenever
its state density vanishes on every vertex visited strictly before that time.
The endpoint is removed using atomlessness of Lebesgue measure.  This is the
localization step needed before a resolvent-core potential can be used as a
stopped martingale; no generator-domain or boundary-bracket conclusion is made.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The compact realization of a resolvent-core potential, written as the
same finite rational combination used in `compactResolventCoreMartingale`. -/
noncomputable def compactResolventCorePotential
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V) :
    ℝ≥0 → PF.Ω → ℝ :=
  q.sum fun y a ↦ (a : ℝ) • fun t omega ↦
    ResolventCompactSpace.potentialCoordinate G m hm y
      (reflectedCompactProcess G m hm PF default t omega)

/-- Exact compact Dynkin representation for a finite resolvent-core
combination. -/
theorem compactResolventCoreMartingale_eq_potential_sub_occupation
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (omega : PF.Ω) :
    compactResolventCoreMartingale G m hm PF default q t omega =
      compactResolventCorePotential G m hm PF default q t omega -
        boundedStateOccupationVersion PF (resolventCoreDrift G m q) t omega := by
  classical
  rw [boundedStateOccupationVersion_resolventCoreDrift PF G m hm q t omega]
  unfold compactResolventCoreMartingale compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    compactVertexDynkinMartingale, mul_sub]
  rw [Finset.sum_sub_distrib]

end ReflectedGMS

end Merged_StoppedGeneratorLocalization

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- A compact resolvent-core potential is bounded by the coefficient `l1` norm. -/
theorem norm_compactResolventCorePotential_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) (omega : PF.Ω) :
    ‖compactResolventCorePotential G m hm PF default q t omega‖ ≤
      countableResolventCoreBound q := by
  classical
  unfold compactResolventCorePotential countableResolventCoreBound Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  calc
    ‖∑ y ∈ q.support, (q y : ℝ) •
        ResolventCompactSpace.potentialCoordinate G m hm y
          (reflectedCompactProcess G m hm PF default t omega)‖ ≤
        ∑ y ∈ q.support, ‖(q y : ℝ) •
          ResolventCompactSpace.potentialCoordinate G m hm y
            (reflectedCompactProcess G m hm PF default t omega)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ y ∈ q.support, |(q y : ℝ)| := by
      apply Finset.sum_le_sum
      intro y hy
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (ResolventCompactSpace.potentialCoordinate_norm_le_one G m hm y _)

/-- The compact core potential is measurable at each deterministic time. -/
theorem stronglyMeasurable_compactResolventCorePotential
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) :
    StronglyMeasurable (compactResolventCorePotential G m hm PF default q t) := by
  classical
  unfold compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.stronglyMeasurable_sum
  intro y hy
  exact ((ResolventCompactSpace.potentialCoordinate G m hm y).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_reflectedCompactProcess G m hm PF default t)).const_smul _

/-- At a fixed time, the compact core potential is the decoded full-form
potential along the actual reflected process under the stationary speed law. -/
theorem compactResolventCorePotential_ae_eq_stationary
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V)
    (t : ℝ≥0) :
    compactResolventCorePotential G m hm PF default q t =ᵐ[reflectedSpeedLaw PF m]
      fun omega ↦ (PF.X t omega).elim 0 (countableResolventCoreFeature G m q) := by
  apply (ae_reflectedSpeedLaw_iff PF m hm _).2
  intro z
  classical
  filter_upwards [reflectedCompactProcess_ae_eq_sample_at_time
      h hG hm hmsum default z t, (h z).2.1 t] with omega hc hx
  obtain ⟨x, hx⟩ := hx.1
  unfold compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply, hc, reflectedCompactSample, hx,
    Option.getD_some, ResolventCompactSpace.potentialCoordinate_vertex,
    Option.elim_some, smul_eq_mul]
  exact (countableResolventCoreFeature_eq_sum G m q x).symm

/-- Compact resolvent-core potentials have right-continuous paths almost surely
under the stationary speed law. -/
theorem compactResolventCorePotential_ae_isRightContinuous
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V) :
    ∀ᵐ omega ∂reflectedSpeedLaw PF m,
      IsRightContinuous
        (fun t ↦ compactResolventCorePotential G m hm PF default q t omega) := by
  rw [ae_reflectedSpeedLaw_iff PF m hm]
  intro z
  classical
  filter_upwards [reflectedCompactProcess_ae_cadlag_and_projection
      h hG hm hmsum default z] with omega hc
  unfold compactResolventCorePotential Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  have hpath (y : V) : IsCadlag (fun t ↦
      (q y : ℝ) • ResolventCompactSpace.potentialCoordinate G m hm y
        (reflectedCompactProcess G m hm PF default t omega)) :=
    by
      have hy := (hc.1.continuous_comp
          (ResolventCompactSpace.potentialCoordinate G m hm y).continuous).const_smul
            (q y : ℝ)
      convert hy using 1 <;> funext s <;> rfl
  have hsum : IsCadlag (fun t ↦ ∑ y ∈ q.support,
      (q y : ℝ) • ResolventCompactSpace.potentialCoordinate G m hm y
        (reflectedCompactProcess G m hm PF default t omega)) := by
    induction q.support using Finset.induction_on with
    | empty => simpa using (IsCadlag.const (c := (0 : ℝ)))
    | @insert y s hy ih =>
        have hadd := (hpath y).add ih
        convert hadd using 1
        funext t
        rw [Finset.sum_insert hy]
        rfl
  exact hsum.isRightContinuous

/-- Uniform all-time square-maximal envelope for an actual compact core
potential under the stationary speed law.  The constant is inherited from the
finite-grid maximal estimate and the elementary dyadic count bound. -/
theorem exists_integrable_sq_envelope_compactResolventCorePotential
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V)
    (T : ℝ≥0) :
    ∃ D : PF.Ω → ℝ, Measurable D ∧
      Integrable D (reflectedSpeedLaw PF m) ∧
      (∀ᵐ omega ∂reflectedSpeedLaw PF m, ∀ t ≤ T,
        (compactResolventCorePotential G m hm PF default q t omega -
          compactResolventCorePotential G m hm PF default q 0 omega) ^ 2 ≤ D omega) ∧
      (∫ omega, D omega ∂reflectedSpeedLaw PF m) ≤
        2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q) := by
  let Y := compactResolventCorePotential G m hm PF default q
  let U := countableResolventCoreVector G m q
  let P := reflectedSpeedLaw PF m
  letI : IsFiniteMeasure P := reflectedSpeedLaw_isFinite PF m hmsum
  have hdecode : unweight m (valueInclusion G m U) =
      countableResolventCoreFeature G m q := by
    dsimp only [U]
    rw [countableResolventCoreVector_eq_inHilbertDomain G m hm,
      valueInclusion_inHilbertDomain, unweight_weightedValue m hm]
  have hY : ∀ t, Measurable (Y t) := fun t ↦
    (stronglyMeasurable_compactResolventCorePotential G m hm PF default q t).measurable
  have hgridEq (n : ℕ) :
      dyadicCenteredAbsMax Y T n =ᵐ[P]
        fun omega ↦ (Finset.range (2 ^ n + 1)).sup'
          Finset.nonempty_range_add_one
          (fun k ↦ |stationaryGridPotential PF G m U
            (T / (2 ^ n : ℝ≥0)) k omega -
              stationaryGridPotential PF G m U (T / (2 ^ n : ℝ≥0)) 0 omega|) := by
    have hall : ∀ᵐ omega ∂P, ∀ k,
        Y (dyadicTime T n k) omega =
          stationaryGridPotential PF G m U (T / (2 ^ n : ℝ≥0)) k omega := by
      filter_upwards [ae_all_iff.2 fun k ↦
        compactResolventCorePotential_ae_eq_stationary
          h hG hm hmsum default q (dyadicTime T n k)] with omega homega
      intro k
      dsimp only [Y]
      rw [homega k]
      simp only [stationaryGridPotential, stationaryGridTime, dyadicTime, hdecode]
      rw [mul_div_assoc]
    filter_upwards [hall] with omega homega
    unfold dyadicCenteredAbsMax
    apply Finset.sup'_congr Finset.nonempty_range_add_one rfl
    intro k hk
    rw [homega k]
    rw [show Y 0 omega = stationaryGridPotential PF G m U
        (T / (2 ^ n : ℝ≥0)) 0 omega by
      simpa only [dyadicTime, Nat.cast_zero, zero_mul, zero_div] using homega 0]
  have hgridInt : ∀ n, Integrable
      (fun omega ↦ (dyadicCenteredAbsMax Y T n omega) ^ 2) P := by
    intro n
    apply Integrable.of_bound
      ((measurable_dyadicCenteredAbsMax hY T n).pow_const 2).aestronglyMeasurable
      ((2 * countableResolventCoreBound q) ^ 2)
    filter_upwards [] with omega
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hmax : dyadicCenteredAbsMax Y T n omega ≤
        2 * countableResolventCoreBound q := by
      apply (Finset.sup'_le_iff Finset.nonempty_range_add_one _).2
      intro k hk
      rw [abs_le]
      have hkbound := norm_compactResolventCorePotential_le
        G m hm PF default q (dyadicTime T n k) omega
      have h0bound := norm_compactResolventCorePotential_le
        G m hm PF default q 0 omega
      simp only [Real.norm_eq_abs] at hkbound h0bound
      constructor <;> linarith [le_abs_self (Y (dyadicTime T n k) omega),
        neg_abs_le (Y (dyadicTime T n k) omega), le_abs_self (Y 0 omega),
        neg_abs_le (Y 0 omega)]
    have hmax0 := dyadicCenteredAbsMax_nonneg Y T n omega
    nlinarith
  have hgrid : ∀ n,
      (∫ omega, (dyadicCenteredAbsMax Y T n omega) ^ 2 ∂P) ≤
        2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q) := by
    intro n
    calc
      (∫ omega, (dyadicCenteredAbsMax Y T n omega) ^ 2 ∂P) =
          ∫ omega, ((Finset.range (2 ^ n + 1)).sup'
            Finset.nonempty_range_add_one
            (fun k ↦ |stationaryGridPotential PF G m U
              (T / (2 ^ n : ℝ≥0)) k omega -
                stationaryGridPotential PF G m U (T / (2 ^ n : ℝ≥0)) 0 omega|)) ^ 2 ∂P := by
        apply integral_congr_ae
        exact (hgridEq n).mono fun omega heq ↦ congrArg (fun a : ℝ ↦ a ^ 2) heq
      _ ≤ 1024 * (((2 ^ n : ℕ) : ℝ) + 1) *
          ((T / (2 ^ n : ℝ≥0) : ℝ≥0) : ℝ) *
            G.Energy (unweight m (valueInclusion G m U)) :=
        stationaryGridPotential_maximal_sq_integral_le h hG hm hmsum U
          (T / (2 ^ n : ℝ≥0)) (countableResolventCoreBound q)
          (by intro x; rw [hdecode, Real.norm_eq_abs];
              exact countableResolventCoreFeature_abs_le G m hm q x) (2 ^ n)
      _ ≤ 2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q) := by
        rw [hdecode]
        rw [NNReal.coe_div]
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        change 1024 * ((2 : ℝ) ^ n + 1) *
            ((T : ℝ) / (2 : ℝ) ^ n) *
              G.Energy (countableResolventCoreFeature G m q) ≤
            2048 * (T : ℝ) *
              G.Energy (countableResolventCoreFeature G m q)
        have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have hpone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
        have hE : 0 ≤ G.Energy (countableResolventCoreFeature G m q) :=
          G.Energy_nonneg _
        have hfrac : (((2 : ℝ) ^ n + 1) / (2 : ℝ) ^ n) ≤ 2 := by
          rw [div_le_iff₀ hpow]
          nlinarith
        have htime : ((2 : ℝ) ^ n + 1) *
            ((T : ℝ) / (2 : ℝ) ^ n) ≤ 2 * (T : ℝ) := by
          calc
            ((2 : ℝ) ^ n + 1) * ((T : ℝ) / (2 : ℝ) ^ n) =
                (((2 : ℝ) ^ n + 1) / (2 : ℝ) ^ n) * (T : ℝ) := by
              field_simp
            _ ≤ 2 * (T : ℝ) :=
              mul_le_mul_of_nonneg_right hfrac T.coe_nonneg
        have hmul := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htime (by norm_num : (0 : ℝ) ≤ 1024)) hE
        calc
          1024 * ((2 : ℝ) ^ n + 1) *
              ((T : ℝ) / (2 : ℝ) ^ n) *
                G.Energy (countableResolventCoreFeature G m q) =
              1024 * (((2 : ℝ) ^ n + 1) *
                ((T : ℝ) / (2 : ℝ) ^ n)) *
                  G.Energy (countableResolventCoreFeature G m q) := by ring
          _ ≤ 1024 * (2 * (T : ℝ)) *
                G.Energy (countableResolventCoreFeature G m q) := hmul
          _ = 2048 * (T : ℝ) *
                G.Energy (countableResolventCoreFeature G m q) := by ring
  exact exists_integrable_sq_envelope_of_dyadic_grids Y T hY hgridInt
    (2048 * (T : ℝ) * G.Energy (countableResolventCoreFeature G m q)) hgrid
    (compactResolventCorePotential_ae_isRightContinuous
      h hG hm hmsum default q)

end ReflectedGMS
