/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderVanishing at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderPartialTerm
import LatticeProb.Bonanno.ReflectedGMS.Forms.SojournOccupationLowerBound

/-!
# The stopped remainder vanishes: `P^τ = M^τ` before the spatial exit of a harmonic region

**The stopped, fixed-start zero-energy statement of `p:lem:localharm`.**  Let `U` be a
bounded full-domain vector, spatially harmonic on the vertex region `A` in the sense of the
full variational test `hU`, and let `τ` be the spatial exit time of `A`.  Then, under every
starting law `P_z`, the stopped full-energy path and the stopped Fukushima martingale agree at
all times:

`stoppedProcess P τ = stoppedProcess M τ`  a.s.

This is the manuscript's "the difference from its Fukushima martingale is a continuous
zero-energy local martingale, hence zero", made precise **without** a stopped or fixed-start
energy notion: the stopped remainder `N = P^τ − M^τ` is an `L²` martingale null at zero
(`Forms/StoppedRemainderMartingale`), so `E_z[N_t²]` is the sum of its squared increments
along any partition; those are bounded pathwise by the *unstopped* increments of the
continuous remainder plus a partial-interval term (`Forms/StoppedRemainderMartingaleTools`);
mixing the starts with the speed measure, the unstopped sums vanish by the stationary
zero-energy property along partitions (`Forms/StoppedRemainderIncrementEnergy`) and the
partial-interval terms by dominated convergence (`Forms/StoppedRemainderPartialTerm`).  Hence
`E_m[N_t²] = 0`, and since every vertex carries positive speed, `E_z[N_t²] = 0` for every `z`.

Main results:
* `integral_sq_stoppedRemainder_eq_zero`: `E_z[N_t²] = 0`;
* `stoppedRemainder_ae_forall_eq_zero`: `∀ᵐ ω, ∀ t, N_t ω = 0` (dyadic exit);
* `ae_forall_stopped_fullEnergyPath_eq_martingale_exitHitting`: the same for the actual exit
  time `exitHitting PF A`.

The speed `m` is the generic summable speed of the fast-side modules; the boundedness
hypothesis `hC` is the manuscript's "u_N is bounded" (the cutoff of a harmonic coordinate).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedRemainder

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.StoppedFormAssociation ReflectedGMS.StoppedRemainderTools
open ReflectedGMS.MartingaleLimit ReflectedGMS.SojournOccupationLowerBound

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m) (A : Set V)

include h hG hm hmsum

/-! ## The unstopped increments under the speed law -/

theorem remainderPath_sub_ae_eq_remainderIncrement (z : V) (s r : ℝ≥0) :
    (fun ω ↦ remainderPath G m hm PF default U r ω - remainderPath G m hm PF default U s ω)
      =ᵐ[PF.P z] remainderIncrement G m hm PF default U s r := by
  filter_upwards [fullEnergyPotentialPathLimit_ae_eq h hG hm hmsum default U z r,
    fullEnergyPotentialPathLimit_ae_eq h hG hm hmsum default U z s] with ω hr hs
  simp only [remainderPath, remainderIncrement, rawPathIncrement, hr, hs]
  ring

theorem lintegral_remainderPath_increment_eq (s r : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((remainderPath G m hm PF default U r ω -
        remainderPath G m hm PF default U s ω) ^ 2) ∂reflectedSpeedLaw PF m =
      ENNReal.ofReal (∫ ω, (remainderIncrement G m hm PF default U s r ω) ^ 2
        ∂reflectedSpeedLaw PF m) := by
  have hae : (fun ω ↦ ENNReal.ofReal ((remainderPath G m hm PF default U r ω -
      remainderPath G m hm PF default U s ω) ^ 2)) =ᵐ[reflectedSpeedLaw PF m]
      fun ω ↦ ENNReal.ofReal ((remainderIncrement G m hm PF default U s r ω) ^ 2) := by
    apply (ae_reflectedSpeedLaw_iff PF m hm _).2
    intro z
    exact (remainderPath_sub_ae_eq_remainderIncrement h hG hm hmsum default U z s r).mono
      fun ω hω ↦ by simp only [hω]
  rw [lintegral_congr_ae hae]
  exact (ofReal_integral_eq_lintegral_ofReal
    (remainderIncrement_memLp_two h hG hm hmsum default U s r).integrable_sq
    (Eventually.of_forall fun ω ↦ sq_nonneg _)).symm

/-! ## The mixture inequality -/

/-- **`E_m[N_t²] ≤ RPSS_n + Σ_z m(z) E_z[Y_n]`** under the unnormalized speed law. -/
theorem lintegral_sq_stoppedRemainder_speedLaw_le
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2)
        ∂reflectedSpeedLaw PF m ≤
      ENNReal.ofReal (remainderPartitionSquareSum G m hm PF default U t n) +
        ∑' z, ENNReal.ofReal (m z) *
          ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z := by
  rw [lintegral_reflectedSpeedLaw_eq_tsum]
  calc ∑' z, ENNReal.ofReal (m z) *
        ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z
      ≤ ∑' z, ENNReal.ofReal (m z) *
          ((∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂PF.P z) +
          ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z) := by
        apply ENNReal.tsum_le_tsum
        intro z
        exact mul_le_mul' le_rfl
          (lintegral_sq_stoppedRemainder_le h hG hm hmsum default U A hU z t hn)
    _ = ∑' z, (ENNReal.ofReal (m z) *
          (∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂PF.P z) +
          ENNReal.ofReal (m z) *
          ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z) := by
        simp only [mul_add]
    _ = (∑' z, ENNReal.ofReal (m z) *
          ∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂PF.P z) +
          ∑' z, ENNReal.ofReal (m z) *
          ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z :=
        ENNReal.tsum_add
    _ = _ := by
        congr 1
        have hmeas : ∀ k : ℕ, AEMeasurable (fun ω ↦ ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2))
            (reflectedSpeedLaw PF m) := fun k ↦
          ((((measurable_remainderPath h hG hm hmsum default U _).sub
            (measurable_remainderPath h hG hm hmsum default U _)).pow_const 2).ennreal_ofReal).aemeasurable
        have hsum : ∫⁻ ω, ∑ k ∈ Finset.range n, ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂reflectedSpeedLaw PF m =
            ∑ k ∈ Finset.range n, ∫⁻ ω, ENNReal.ofReal
            ((remainderPath G m hm PF default U (uniformGrid t n (k + 1)) ω -
              remainderPath G m hm PF default U (uniformGrid t n k) ω) ^ 2) ∂reflectedSpeedLaw PF m :=
          lintegral_finsetSum' _ fun k _ ↦ hmeas k
        rw [← lintegral_reflectedSpeedLaw_eq_tsum, hsum, remainderPartitionSquareSum,
          ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ integral_nonneg fun ω ↦ sq_nonneg _)]
        exact Finset.sum_congr rfl fun k _ ↦
          lintegral_remainderPath_increment_eq h hG hm hmsum default U _ _

/-! ## The mixed partial-interval term vanishes -/

/-- A crude second-moment bound for the stopped remainder from a bound `C` on the stopped
full-energy path: `E_z[N_t²] ≤ 2 C² + 2 E_z[M_t²]`. -/
theorem integral_sq_stoppedRemainder_le (z : V) {C : ℝ}
    (hPb : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (t : ℝ≥0) :
    ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z ≤
      2 * C ^ 2 + 2 * ∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z := by
  have htau := isStoppingTime_rightCont_dyadicExit PF A
  have hrM := ae_isRightContinuous_martingaleLimit h hG hm hmsum default U z
  have hMmart := fullEnergyMartingaleLimit_isMartingale h hG hm hmsum default U z
  have hM2 := (fullEnergyMartingaleLimit_memLp_and_L2_convergence h hG hm hmsum default U z t).1
  obtain ⟨hMs2, hMle⟩ := stoppedProcess_memLp_two_and_second_moment_le hMmart htau hrM t hM2
  have hN2 : Integrable (fun ω ↦ (stoppedRemainder G m hm PF default U A t ω) ^ 2) (PF.P z) :=
    (stoppedRemainder_memLp_two h hG hm hmsum default U A z t).integrable_sq
  have hMs2i : Integrable (fun ω ↦ (stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U)
      (dyadicExit PF A) t ω) ^ 2) (PF.P z) := hMs2.integrable_sq
  have hPb' : ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (dyadicExit PF A) t ω|
        ≤ C := by
    filter_upwards [hPb, ae_dyadicExit_eq_exitHitting h A z] with ω hω hτ
    intro t
    have := hω t
    simpa only [stoppedProcess, hτ] using this
  have hpt : (∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z) ≤
      ∫ ω, 2 * C ^ 2 + 2 * (stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U)
        (dyadicExit PF A) t ω) ^ 2 ∂PF.P z := by
    apply integral_mono_ae hN2 ((integrable_const _).add (hMs2i.const_mul 2))
    filter_upwards [hPb'] with ω hω
    rw [stoppedRemainder_apply]
    simp only [Pi.add_apply]
    have hb := hω t
    have hsq : (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
        (dyadicExit PF A) t ω) ^ 2 ≤ C ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    nlinarith [sq_nonneg (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
      (dyadicExit PF A) t ω + stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U)
      (dyadicExit PF A) t ω), hsq]
  rw [integral_add (integrable_const _) (hMs2i.const_mul 2), integral_const, integral_const_mul,
    smul_eq_mul] at hpt
  have hprob : (PF.P z).real Set.univ = 1 := by simp
  rw [hprob, one_mul] at hpt
  linarith

theorem tsum_speed_mul_ofReal_integral_sq_martingaleLimit_ne_top (t : ℝ≥0) :
    ∑' z, ENNReal.ofReal (m z) *
      ENNReal.ofReal (∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z)
      ≠ ⊤ := by
  have hz : ∀ z, ENNReal.ofReal (∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2
      ∂PF.P z) = ∫⁻ ω, ENNReal.ofReal ((fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2)
      ∂PF.P z := fun z ↦
    ofReal_integral_eq_lintegral_ofReal
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence h hG hm hmsum default U z t).1.integrable_sq
      (Eventually.of_forall fun ω ↦ sq_nonneg _)
  simp_rw [hz]
  rw [← lintegral_reflectedSpeedLaw_eq_tsum, ← ofReal_integral_eq_lintegral_ofReal
    (fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw h hG hm hmsum default U t).integrable_sq
    (Eventually.of_forall fun ω ↦ sq_nonneg _)]
  exact ENNReal.ofReal_ne_top

theorem tsum_speed_ne_top : ∑' z, ENNReal.ofReal (m z) ≠ ⊤ := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have := lintegral_reflectedSpeedLaw_eq_tsum PF m (fun _ ↦ (1 : ℝ≥0∞))
  simp only [lintegral_one, measure_univ, mul_one] at this
  rw [← this]
  exact measure_ne_top _ _

/-- The mixed dominator of the partial-interval terms is summable. -/
theorem tsum_dominator_ne_top {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (t : ℝ≥0) :
    ∑' z, ENNReal.ofReal (m z) * (ENNReal.ofReal 4 * ENNReal.ofReal
      (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z)) ≠ ⊤ := by
  have hle : ∀ z, ENNReal.ofReal (m z) * (ENNReal.ofReal 4 * ENNReal.ofReal
      (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z)) ≤
      ENNReal.ofReal (m z) * ENNReal.ofReal (32 * C ^ 2) +
        ENNReal.ofReal 32 * (ENNReal.ofReal (m z) * ENNReal.ofReal
          (∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z)) := by
    intro z
    have hb := integral_sq_stoppedRemainder_le h hG hm hmsum default U A z (hPb z) t
    have hM0 : 0 ≤ ∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z :=
      integral_nonneg fun ω ↦ sq_nonneg _
    calc ENNReal.ofReal (m z) * (ENNReal.ofReal 4 * ENNReal.ofReal
          (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z))
        ≤ ENNReal.ofReal (m z) * (ENNReal.ofReal 4 * ENNReal.ofReal
          (4 * (2 * C ^ 2 + 2 * ∫ ω,
            (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (by linarith)))
      _ = ENNReal.ofReal (m z) * ENNReal.ofReal (32 * C ^ 2) +
          ENNReal.ofReal 32 * (ENNReal.ofReal (m z) * ENNReal.ofReal
            (∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z)) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
            show (4 : ℝ) * (4 * (2 * C ^ 2 + 2 * ∫ ω,
              (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z)) =
              32 * C ^ 2 + 32 * ∫ ω,
                (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 ∂PF.P z by ring,
            ENNReal.ofReal_add (by positivity) (mul_nonneg (by norm_num) hM0), mul_add,
            ENNReal.ofReal_mul (q := ∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2
              ∂PF.P z) (by norm_num : (0 : ℝ) ≤ 32)]
          ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (tsum_speed_ne_top h hG hm hmsum)
    ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (tsum_speed_mul_ofReal_integral_sq_martingaleLimit_ne_top h hG hm hmsum default U t)⟩

/-- **`Σ_z m(z) E_z[Y_n] → 0`** by dominated convergence over the countable vertex set. -/
theorem tsum_lintegral_remainderPartialTerm_tendsto_zero {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (t : ℝ≥0) :
    Tendsto (fun n ↦ ∑' z, ENNReal.ofReal (m z) *
      ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z)
      atTop (𝓝 0) := by
  have hpt : ∀ z, Tendsto (fun n ↦ ENNReal.ofReal (m z) *
      ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z)
      atTop (𝓝 0) := fun z ↦ by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (m z))
      (lintegral_remainderPartialTerm_tendsto_zero h hG hm hmsum default U A hU z t)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero] using this
  have key := tendsto_lintegral_of_dominated_convergence (μ := (Measure.count : Measure V))
    (F := fun n z ↦ ENNReal.ofReal (m z) *
      ∫⁻ ω, ENNReal.ofReal (remainderPartialTerm G m hm PF default U A t n ω) ∂PF.P z)
    (f := fun _ ↦ 0)
    (fun z ↦ ENNReal.ofReal (m z) * (ENNReal.ofReal 4 * ENNReal.ofReal
      (4 * ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z)))
    (fun n ↦ measurable_of_countable _)
    (fun n ↦ Eventually.of_forall fun z ↦
      mul_le_mul' le_rfl (lintegral_remainderPartialTerm_le h hG hm hmsum default U A hU z t n))
    (by rw [lintegral_count]; exact tsum_dominator_ne_top h hG hm hmsum default U A hPb t)
    (Eventually.of_forall hpt)
  simp only [lintegral_count, lintegral_zero] at key
  exact key

/-! ## Conclusion -/

/-- **`E_m[N_t²] = 0`.** -/
theorem lintegral_sq_stoppedRemainder_speedLaw_eq_zero {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2)
      ∂reflectedSpeedLaw PF m = 0 := by
  have h1 := (ENNReal.continuous_ofReal.tendsto 0).comp
    (remainderPartitionSquareSum_tendsto_zero h hG hm hmsum default U t)
  simp only [Function.comp_def, ENNReal.ofReal_zero] at h1
  have hlim := h1.add (tsum_lintegral_remainderPartialTerm_tendsto_zero
    h hG hm hmsum default U A hPb hU t)
  simp only [add_zero] at hlim
  refine le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_) zero_le
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact lintegral_sq_stoppedRemainder_speedLaw_le h hG hm hmsum default U A hU t hn

/-- **`E_z[N_t²] = 0` for every start `z`.** -/
theorem integral_sq_stoppedRemainder_eq_zero {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) :
    ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z = 0 := by
  have h0 := lintegral_sq_stoppedRemainder_speedLaw_eq_zero h hG hm hmsum default U A hPb hU t
  rw [lintegral_reflectedSpeedLaw_eq_tsum] at h0
  have hz : ENNReal.ofReal (m z) *
      ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z = 0 := by
    have hle := ENNReal.le_tsum (f := fun z ↦ ENNReal.ofReal (m z) *
      ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z) z
    rw [h0] at hle
    exact le_antisymm hle zero_le
  have hmz : ENNReal.ofReal (m z) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]
    exact not_le.2 (hm z)
  have h1 : ∫⁻ ω, ENNReal.ofReal ((stoppedRemainder G m hm PF default U A t ω) ^ 2) ∂PF.P z
      = 0 := (mul_eq_zero.1 hz).resolve_left hmz
  have hN2 : Integrable (fun ω ↦ (stoppedRemainder G m hm PF default U A t ω) ^ 2) (PF.P z) :=
    (stoppedRemainder_memLp_two h hG hm hmsum default U A z t).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hN2 (Eventually.of_forall fun ω ↦ sq_nonneg _),
    ENNReal.ofReal_eq_zero] at h1
  exact le_antisymm h1 (integral_nonneg fun ω ↦ sq_nonneg _)

/-- **The stopped remainder vanishes at every fixed time**, almost surely. -/
theorem stoppedRemainder_ae_eq_zero {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, stoppedRemainder G m hm PF default U A t ω = 0 := by
  have hN2 : Integrable (fun ω ↦ (stoppedRemainder G m hm PF default U A t ω) ^ 2) (PF.P z) :=
    (stoppedRemainder_memLp_two h hG hm hmsum default U A z t).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun ω ↦ sq_nonneg _) hN2).1
    (integral_sq_stoppedRemainder_eq_zero h hG hm hmsum default U A hPb hU z t)
  filter_upwards [hae] with ω hω
  have hsq : (stoppedRemainder G m hm PF default U A t ω) ^ 2 = 0 := hω
  exact (pow_eq_zero_iff two_ne_zero).1 hsq

/-- **The stopped remainder vanishes at all times simultaneously**, almost surely: the fixed-time
statement on the countable dyadic support, plus right continuity of the stopped path. -/
theorem stoppedRemainder_ae_forall_eq_zero {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t, stoppedRemainder G m hm PF default U A t ω = 0 := by
  have hD : ∀ᵐ ω ∂PF.P z, ∀ s ∈ globalDyadicSupport,
      stoppedRemainder G m hm PF default U A s ω = 0 := by
    rw [ae_ball_iff globalDyadicSupport_countable]
    intro s _
    exact stoppedRemainder_ae_eq_zero h hG hm hmsum default U A hPb hU z s
  filter_upwards [hD, ae_continuous_remainderPath h hG hm hmsum default U z] with ω hω hcont
  intro t
  have hrc : IsRightContinuous (fun s ↦ stoppedRemainder G m hm PF default U A s ω) :=
    isRightContinuous_stoppedProcess_common ω hcont.isRightContinuous (dyadicExit PF A)
  have := globalDyadicSupport_nhdsWithin_Ioi_neBot t
  have hlim : Tendsto (fun s ↦ stoppedRemainder G m hm PF default U A s ω)
      (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 (stoppedRemainder G m hm PF default U A t ω)) :=
    (hrc t).tendsto.mono_left (nhdsWithin_mono t inter_subset_right)
  have hzero : Tendsto (fun s ↦ stoppedRemainder G m hm PF default U A s ω)
      (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hω s hs.1).symm
  exact tendsto_nhds_unique hlim hzero

/-- **`P^τ = M^τ` at all times, for the actual spatial exit time `exitHitting PF A`.**  This is
the stopped, fixed-start zero-energy statement: the stopped full-energy path of a vector harmonic
on `A`, bounded before the exit, is its stopped Fukushima martingale. -/
theorem ae_forall_stopped_fullEnergyPath_eq_martingale_exitHitting {C : ℝ}
    (hPb : ∀ z : V, ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ C)
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t,
      stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω =
        stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U) (exitHitting PF A) t ω := by
  filter_upwards [stoppedRemainder_ae_forall_eq_zero h hG hm hmsum default U A hPb hU z,
    ae_dyadicExit_eq_exitHitting h A z] with ω hω hτ
  intro t
  have := hω t
  rw [stoppedRemainder_apply, sub_eq_zero] at this
  simpa only [stoppedProcess, hτ] using this

/-- The stopped-path bound from a global bound on the vector (`Forms/StoppedFormAssociationPathBound`). -/
theorem stoppedPath_bound_of_bounded {C : ℝ}
    (hC : ∀ x, |unweight m (valueInclusion G m U) x| ≤ C) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (exitHitting PF A) t ω|
        ≤ 2 * C :=
  stoppedProcess_fullEnergyPotentialPathLimit_ae_forall_abs_le h hG hm hmsum default U z hC
    (exitHitting PF A)

end ReflectedGMS.StoppedRemainder
