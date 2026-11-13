/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StationaryGridMaximal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryGridMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompensatedPotentialL2
import LatticeProb.Bonanno.ReflectedGMS.Forms.MartingaleL2MaximalEnvelope
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupEnergyBound

/-!
# Square and maximal bounds for the stationary grid martingale

The centered Doob martingale on the stationary grid is square integrable.  Its
terminal second moment is controlled by the full network energy, and the
existing finite-grid Doob inequality gives the corresponding maximal bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory ProbabilityTheory Set Filter Finset
open scoped BigOperators InnerProductSpace NNReal ENNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private theorem integral_sq_sub_eq
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ ω, (f ω - g ω) ^ 2 ∂μ) =
      (∫ ω, (f ω) ^ 2 ∂μ) - 2 * (∫ ω, f ω * g ω ∂μ) +
        ∫ ω, (g ω) ^ 2 ∂μ := by
  have hf2 : Integrable (fun ω => (f ω) ^ 2) μ := hf.integrable_sq
  have hg2 : Integrable (fun ω => (g ω) ^ 2) μ := hg.integrable_sq
  have hfg : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  calc
    (∫ ω, (f ω - g ω) ^ 2 ∂μ) =
        ∫ ω, ((f ω) ^ 2 - 2 * (f ω * g ω)) + (g ω) ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
    _ = (∫ ω, (f ω) ^ 2 - 2 * (f ω * g ω) ∂μ) +
        ∫ ω, (g ω) ^ 2 ∂μ := integral_add (hf2.sub (hfg.const_mul 2)) hg2
    _ = _ := by rw [integral_sub hf2 (hfg.const_mul 2), integral_const_mul]

private theorem integral_sub_condExp_sq_le_four
    {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∫ ω, (f ω - μ[f | m] ω) ^ 2 ∂μ) ≤ 4 * ∫ ω, (f ω) ^ 2 ∂μ := by
  have hce : MemLp μ[f | m] 2 μ := hf.condExp (m := m) one_le_two
  have hpoint : ∀ ω, (f ω - μ[f | m] ω) ^ 2 ≤
      2 * (f ω) ^ 2 + 2 * (μ[f | m] ω) ^ 2 := fun ω => by
    nlinarith [sq_nonneg (f ω + μ[f | m] ω)]
  have hint := integral_mono (hf.sub hce).integrable_sq
    ((hf.integrable_sq.const_mul 2).add (hce.integrable_sq.const_mul 2)) hpoint
  have hcontract := integral_norm_condExp_rpow_le (μ := μ) (m := m)
    (f := f) (p := (2 : ℝ)) (by norm_num) (by
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hf.integrable_sq)
  have hcontract' : (∫ ω, (μ[f | m] ω) ^ 2 ∂μ) ≤
      ∫ ω, (f ω) ^ 2 ∂μ := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs] using hcontract
  calc
    (∫ ω, (f ω - μ[f | m] ω) ^ 2 ∂μ) ≤
        ∫ ω, 2 * (f ω) ^ 2 + 2 * (μ[f | m] ω) ^ 2 ∂μ := hint
    _ = 2 * ∫ ω, (f ω) ^ 2 ∂μ +
          2 * ∫ ω, (μ[f | m] ω) ^ 2 ∂μ := by
      rw [integral_add (hf.integrable_sq.const_mul 2) (hce.integrable_sq.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 4 * ∫ ω, (f ω) ^ 2 ∂μ := by linarith

/-- The centered stationary-grid Doob martingale is square integrable at every
grid time. -/
theorem stationaryGridMartingale_memLp_two
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0) (n : ℕ) :
    MemLp (stationaryGridMartingale PF G m U δ n) 2
      (reflectedSpeedLaw PF m) := by
  let Y := stationaryGridPotential PF G m U δ
  let F := stationaryGridFiltration PF δ
  let μ := reflectedSpeedLaw PF m
  have hY2 : ∀ k, MemLp (Y k) 2 μ := fun k =>
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (valueInclusion G m U) (stationaryGridTime δ k)
  have hpart : MemLp (martingalePart Y F μ n) 2 μ := by
    rw [martingalePart_eq_sum]
    apply (hY2 0).add
    have hs : MemLp (fun a => ∑ k ∈ range n,
        (Y (k + 1) - Y k - μ[Y (k + 1) - Y k | F k]) a) 2 μ :=
      memLp_finsetSum (range n) fun k _ => by
          have hinc : MemLp (Y (k + 1) - Y k) 2 μ :=
            (hY2 (k + 1)).sub (hY2 k)
          exact hinc.sub (hinc.condExp (m := F k) one_le_two)
    exact (memLp_congr_ae (Eventually.of_forall fun a => by
      simp only [Finset.sum_apply])).2 hs
  exact hpart.sub (hY2 0)

private theorem stationaryGridMartingale_succ_sub
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (U : hilbertDomain G m) (δ : ℝ≥0) (n : ℕ) :
    stationaryGridMartingale PF G m U δ (n + 1) -
        stationaryGridMartingale PF G m U δ n =
      stationaryGridPotential PF G m U δ (n + 1) -
        stationaryGridPotential PF G m U δ n -
        (reflectedSpeedLaw PF m)[
          stationaryGridPotential PF G m U δ (n + 1) -
            stationaryGridPotential PF G m U δ n |
          stationaryGridFiltration PF δ n] := by
  simp only [stationaryGridMartingale, martingalePart_eq_sum,
    Finset.sum_range_succ, Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  abel

private theorem stationaryGridPotential_increment_sq_integral_eq
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (n : ℕ) :
    (∫ ω, (stationaryGridPotential PF G m U δ (n + 1) ω -
        stationaryGridPotential PF G m U δ n ω) ^ 2
        ∂reflectedSpeedLaw PF m) =
      2 * (‖valueInclusion G m U‖ ^ 2 -
        ⟪valueInclusion G m U,
          fullFormSemigroup G m δ (valueInclusion G m U)⟫_ℝ) := by
  let μ := reflectedSpeedLaw PF m
  let Y := stationaryGridPotential PF G m U δ
  let R : ℕ → PF.Ω → ℝ := fun k ω =>
    (PF.X (stationaryGridTime δ k) ω).elim 0
      (unweight m (fullFormSemigroup G m δ (valueInclusion G m U)))
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hY2 : ∀ k, MemLp (Y k) 2 μ := fun k =>
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (valueInclusion G m U) (stationaryGridTime δ k)
  have hR2 : ∀ k, MemLp (R k) 2 μ := fun k =>
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (fullFormSemigroup G m δ (valueInclusion G m U))
      (stationaryGridTime δ k)
  have hcross (k : ℕ) :
      (∫ ω, Y (k + 1) ω * Y k ω ∂μ) = ∫ ω, Y k ω * R k ω ∂μ := by
    have hp : Integrable (Y k * Y (k + 1)) μ :=
      (hY2 k).integrable_mul (hY2 (k + 1))
    have hc := condExp_stationaryGridPotential_succ
      h hG hm hmsum U δ C hbounded k
    calc
      (∫ ω, Y (k + 1) ω * Y k ω ∂μ) = ∫ ω, (Y k * Y (k + 1)) ω ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        simp only [Pi.mul_apply]
        ring
      _ = ∫ ω, μ[Y k * Y (k + 1) | stationaryGridFiltration PF δ k] ω ∂μ :=
        (integral_condExp (Filtration.le (stationaryGridFiltration PF δ) k)).symm
      _ = ∫ ω, (Y k * μ[Y (k + 1) | stationaryGridFiltration PF δ k]) ω ∂μ :=
        integral_congr_ae (condExp_mul_of_aestronglyMeasurable_left
          (stronglyAdapted_stationaryGridPotential PF G m U δ k).aestronglyMeasurable
          hp ((hY2 (k + 1)).integrable one_le_two))
      _ = ∫ ω, Y k ω * R k ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hc] with ω hω
        exact congrArg (Y k ω * ·) hω
  have hmarginal (k : ℕ) : (∫ ω, Y k ω * R k ω ∂μ) =
      ∫ ω, Y 0 ω * R 0 ω ∂μ := by
    let q : Option V → ℝ := fun z => z.elim 0
      (unweight m (valueInclusion G m U)) * z.elim 0
      (unweight m (fullFormSemigroup G m δ (valueInclusion G m U)))
    have hq : Measurable q := measurable_of_countable _
    calc
      (∫ ω, Y k ω * R k ω ∂μ) =
          ∫ z, q z ∂μ.map (PF.X (stationaryGridTime δ k)) := by
        rw [integral_map (PF.measurable_X _).aemeasurable hq.aestronglyMeasurable]
        rfl
      _ = ∫ z, q z ∂μ.map (PF.X 0) := by
        rw [reflectedSpeedLaw_map_position h hG hm hmsum
          (stationaryGridTime δ k), reflectedSpeedLaw_map_position h hG hm hmsum 0]
      _ = ∫ ω, Y 0 ω * R 0 ω ∂μ := by
        rw [integral_map (PF.measurable_X 0).aemeasurable hq.aestronglyMeasurable]
        change (∫ ω, (PF.X 0 ω).elim 0
          (unweight m (valueInclusion G m U)) *
          (PF.X 0 ω).elim 0
            (unweight m (fullFormSemigroup G m δ (valueInclusion G m U))) ∂μ) =
          ∫ ω, (PF.X (stationaryGridTime δ 0) ω).elim 0
            (unweight m (valueInclusion G m U)) *
            (PF.X (stationaryGridTime δ 0) ω).elim 0
              (unweight m (fullFormSemigroup G m δ (valueInclusion G m U))) ∂μ
        rw [show stationaryGridTime δ 0 = 0 by simp [stationaryGridTime]]
  have hsq (k : ℕ) : (∫ ω, (Y k ω) ^ 2 ∂μ) = ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
    let q : Option V → ℝ := fun z => (z.elim 0
      (unweight m (valueInclusion G m U))) ^ 2
    have hq : Measurable q := (measurable_of_countable _).pow_const 2
    calc
      (∫ ω, (Y k ω) ^ 2 ∂μ) =
          ∫ z, q z ∂μ.map (PF.X (stationaryGridTime δ k)) := by
        rw [integral_map (PF.measurable_X _).aemeasurable hq.aestronglyMeasurable]
        rfl
      _ = ∫ z, q z ∂μ.map (PF.X 0) := by
        rw [reflectedSpeedLaw_map_position h hG hm hmsum
          (stationaryGridTime δ k), reflectedSpeedLaw_map_position h hG hm hmsum 0]
      _ = ∫ ω, (Y 0 ω) ^ 2 ∂μ := by
        rw [integral_map (PF.measurable_X 0).aemeasurable hq.aestronglyMeasurable]
        change (∫ ω, ((PF.X 0 ω).elim 0
          (unweight m (valueInclusion G m U))) ^ 2 ∂μ) =
          ∫ ω, ((PF.X (stationaryGridTime δ 0) ω).elim 0
            (unweight m (valueInclusion G m U))) ^ 2 ∂μ
        rw [show stationaryGridTime δ 0 = 0 by simp [stationaryGridTime]]
  have hshift : (∫ ω, (Y (n + 1) ω - Y n ω) ^ 2 ∂μ) =
      ∫ ω, (Y 1 ω - Y 0 ω) ^ 2 ∂μ := by
    rw [integral_sq_sub_eq (hY2 (n + 1)) (hY2 n),
      integral_sq_sub_eq (hY2 1) (hY2 0), hsq (n + 1), hsq n, hsq 1,
      hcross n, hcross 0, hmarginal n]
  change (∫ ω, (Y (n + 1) ω - Y n ω) ^ 2 ∂μ) = _
  rw [hshift]
  have hbase := integral_sq_sub_unweight_reflectedSpeedLaw h hG hm hmsum
    (valueInclusion G m U) δ
  change (∫ ω, ((PF.X (stationaryGridTime δ 1) ω).elim 0
      (unweight m (valueInclusion G m U)) -
      (PF.X (stationaryGridTime δ 0) ω).elim 0
        (unweight m (valueInclusion G m U))) ^ 2 ∂reflectedSpeedLaw PF m) = _
  rw [show stationaryGridTime δ 1 = δ by simp [stationaryGridTime],
    show stationaryGridTime δ 0 = 0 by simp [stationaryGridTime]]
  exact hbase

/-- The terminal second moment of the centered stationary-grid martingale has
the universal energy bound needed for boundary control. -/
theorem stationaryGridMartingale_sq_integral_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (N : ℕ) :
    (∫ ω, (stationaryGridMartingale PF G m U δ N ω) ^ 2
        ∂reflectedSpeedLaw PF m) ≤
      8 * N * (δ : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
  let μ := reflectedSpeedLaw PF m
  let M := stationaryGridMartingale PF G m U δ
  let Y := stationaryGridPotential PF G m U δ
  let F := stationaryGridFiltration PF δ
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hM : Martingale M F μ := stationaryGridMartingale_isMartingale
    h hG hm hmsum U δ
  have hM2 : ∀ k, MemLp (M k) 2 μ :=
    stationaryGridMartingale_memLp_two h hG hm hmsum U δ
  have hY2 : ∀ k, MemLp (Y k) 2 μ := fun k =>
    memLp_two_reflected_unweight_speedLaw h hG hm hmsum
      (valueInclusion G m U) (stationaryGridTime δ k)
  have hone (k : ℕ) :
      (∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂μ) ≤
        8 * (δ : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
    let D := Y (k + 1) - Y k
    have hD2 : MemLp D 2 μ := (hY2 (k + 1)).sub (hY2 k)
    have hcenter := integral_sub_condExp_sq_le_four
      (μ := μ) (m := F k) (f := D) hD2
    have hvar := stationaryGridPotential_increment_sq_integral_eq
      h hG hm hmsum U δ C hbounded k
    have henergy := fullFormSemigroup_quadratic_deficit_le_energy G m hm U δ
    have hfun : (fun ω => (M (k + 1) ω - M k ω) ^ 2) =
        fun ω => (D ω - μ[D | F k] ω) ^ 2 := by
      funext ω
      change ((stationaryGridMartingale PF G m U δ (k + 1) -
        stationaryGridMartingale PF G m U δ k) ω) ^ 2 = _
      rw [congrFun (stationaryGridMartingale_succ_sub PF G m U δ k) ω]
      rfl
    rw [hfun]
    calc
      (∫ ω, (D ω - μ[D | F k] ω) ^ 2 ∂μ) ≤
          4 * ∫ ω, (D ω) ^ 2 ∂μ := hcenter
      _ = 8 * (‖valueInclusion G m U‖ ^ 2 -
          ⟪valueInclusion G m U,
            fullFormSemigroup G m δ (valueInclusion G m U)⟫_ℝ) := by
        change 4 * (∫ ω, (stationaryGridPotential PF G m U δ (k + 1) ω -
          stationaryGridPotential PF G m U δ k ω) ^ 2
          ∂reflectedSpeedLaw PF m) = _
        rw [hvar]
        ring
      _ ≤ 8 * (δ : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
        nlinarith
  have hzero : M 0 = 0 := by
    unfold M stationaryGridMartingale
    simp
  induction N with
  | zero =>
      rw [show stationaryGridMartingale PF G m U δ 0 = 0 by exact hzero]
      simp
  | succ N ih =>
      have htel := martingale_sq_increment_integral hM hM2 (Nat.le_succ N)
      have hstep := hone N
      simp only [Nat.cast_succ] at ⊢
      nlinarith [htel, ih, hstep]

/-- Strong finite-grid maximal control for the actual centered stationary-grid
martingale. -/
theorem stationaryGridMartingale_maximal_sq_integral_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (U : hilbertDomain G m) (δ : ℝ≥0)
    (C : ℝ) (hbounded : ∀ x, ‖unweight m (valueInclusion G m U) x‖ ≤ C)
    (N : ℕ) :
    (∫ ω, ((range (N + 1)).sup' nonempty_range_add_one
        (fun k => |stationaryGridMartingale PF G m U δ k ω|)) ^ 2
        ∂reflectedSpeedLaw PF m) ≤
      32 * N * (δ : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hmax := martingale_abs_discrete_maximal_integral_le
    (stationaryGridMartingale_isMartingale h hG hm hmsum U δ)
    (stationaryGridMartingale_memLp_two h hG hm hmsum U δ) N
  have hterm := stationaryGridMartingale_sq_integral_le
    h hG hm hmsum U δ C hbounded N
  exact hmax.trans (by nlinarith)

end ReflectedGMS
