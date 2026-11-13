/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedRemainderMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedRemainderMartingaleTools
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedFormAssociationFastStopped
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity
import LatticeProb.Bonanno.ReflectedGMS.Limit.StoppedL2

/-!
# The stopped remainder `P^τ − M^τ` is an `L²` martingale with continuous paths

For a full-domain vector `U` that is spatially harmonic on a vertex region `A` (the `hU`
variational test of `Forms/StoppedFormAssociationFastStopped`), the stopped full-energy path
`P^τ` and the stopped Fukushima martingale `M^τ` are both martingales, so their difference — the
**stopped remainder** `N = P^τ − M^τ` — is a martingale null at zero.  This module records the
raw-filtration facts about `N` needed by `Forms/StoppedRemainderVanishing`:

* `stoppedRemainder_setIntegral_eq`: the martingale set-integral identities on the
  right-continuous natural filtration (from the drift elimination
  `stopped_fullEnergyPath_integrable_and_increment_eq_zero_dyadicExit` and the optional stopping
  of `M`);
* `stoppedRemainder_memLp_two`: `N_t ∈ L²(P_z)` for every start `z`;
* `martingale_stoppedRemainderVersion`: an exactly adapted version `N'` of `N` is a genuine
  `Martingale` of the raw right-continuous filtration under `P_z`;
* `integral_sq_stoppedRemainder_eq_sum`: the orthogonal-increment identity along uniform grids;
* `ae_continuous_remainderPath`: the unstopped remainder `P − M` has continuous paths (it is the
  locally uniform limit of the drift occupations of the core approximants).

The stopping time is the **dyadic exit** `dyadicExit PF A`, an exact stopping time of the raw
filtration; the transfer to the actual exit time `exitHitting PF A` is by almost-sure equality
at the end of `Forms/StoppedRemainderVanishing`.
-/

-- Merged from `ReflectedGMS/Forms/StoppedFormAssociationPathBound.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_StoppedFormAssociationPathBound

/-!
# A uniform almost-sure bound on the full-energy potential path of a bounded vector

The clock change of `StoppedFormAssociationOptionalSampling` transports a **bounded**
fast-clock martingale.  The fast-clock martingale of the bracket lane is the stopped
full-energy potential path `fullEnergyPotentialPathLimit … U` of a spatial cutoff `U` of the
harmonic coordinate, which is a bounded vertex function.  At vertex times the path is
`U(X_t) − U(X_0)` (`fullEnergyPotentialPathLimit_ae_eq_at_vertex_times`); at every other
time it is the right limit of its values at the dyadic times, which are almost surely vertex
times (property (i) of `IsReflectedWalk`) and are right dense
(`globalDyadicSupport_nhdsWithin_Ioi_neBot`).  Hence the whole path is bounded by twice the
sup norm of `U`, on one full-probability event, simultaneously at all times.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedFormAssociation

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m)

include h hG hm hmsum

/-- Almost surely every dyadic time is a vertex time. -/
theorem ae_dyadic_vertex_times (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ s ∈ globalDyadicSupport, ∃ x : V, PF.X s ω = some x := by
  rw [ae_ball_iff globalDyadicSupport_countable]
  intro s _
  exact ((h z).2.1 s).mono fun _ hω => hω.1

/-- **Uniform bound on the full-energy potential path of a bounded vector.**  If
`|U x| ≤ C` at every vertex, then almost surely `|fullEnergyPotentialPathLimit … U t| ≤ 2C`
at every time. -/
theorem fullEnergyPotentialPathLimit_ae_forall_abs_le (z : V) {C : ℝ}
    (hC : ∀ x, |unweight m (valueInclusion G m U) x| ≤ C) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |fullEnergyPotentialPathLimit G m hm PF default U t ω| ≤ 2 * C := by
  filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum default U z,
    fullEnergyPotentialPathLimit_ae_eq_at_vertex_times h hG hm hmsum default U z,
    ae_dyadic_vertex_times h hG hm hmsum z] with ω hcad hvert hdy
  intro t
  have hne := globalDyadicSupport_nhdsWithin_Ioi_neBot t
  -- the path value at `t` is the right limit along dyadic times
  have hlim : Tendsto (fun s => |fullEnergyPotentialPathLimit G m hm PF default U s ω|)
      (𝓝[globalDyadicSupport ∩ Ioi t] t)
      (𝓝 |fullEnergyPotentialPathLimit G m hm PF default U t ω|) :=
    ((hcad.1.isRightContinuous t).tendsto.mono_left
      (nhdsWithin_mono t inter_subset_right)).abs
  -- at dyadic times the path is `U x − U z`
  have hbound : ∀ᶠ s in 𝓝[globalDyadicSupport ∩ Ioi t] t,
      |fullEnergyPotentialPathLimit G m hm PF default U s ω| ≤ 2 * C := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨x, hx⟩ := hdy s hs.1
    rw [hvert s x hx]
    calc |unweight m (valueInclusion G m U) x - unweight m (valueInclusion G m U) z|
        ≤ |unweight m (valueInclusion G m U) x| + |unweight m (valueInclusion G m U) z| :=
          abs_sub _ _
      _ ≤ C + C := add_le_add (hC x) (hC z)
      _ = 2 * C := by ring
  exact le_of_tendsto hlim hbound

/-- The stopped path of a bounded vector is bounded by the same constant, at every time and
for every stopping rule. -/
theorem stoppedProcess_fullEnergyPotentialPathLimit_ae_forall_abs_le (z : V) {C : ℝ}
    (hC : ∀ x, |unweight m (valueInclusion G m U) x| ≤ C) (τ : PF.Ω → WithTop ℝ≥0) :
    ∀ᵐ ω ∂PF.P z, ∀ t : ℝ≥0,
      |stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) τ t ω| ≤ 2 * C := by
  filter_upwards [fullEnergyPotentialPathLimit_ae_forall_abs_le h hG hm hmsum default U z hC]
    with ω hω
  intro t
  exact hω _

end ReflectedGMS.StoppedFormAssociation

end Merged_StoppedFormAssociationPathBound

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.StoppedRemainder

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open ReflectedGMS.StoppedFormAssociation ReflectedGMS.StoppedRemainderTools
open ReflectedGMS.MartingaleLimit

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-! ## Definitions -/

/-- The unstopped remainder path `P − M` of the full-energy decomposition. -/
noncomputable def remainderPath (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (t : ℝ≥0) (ω : PF.Ω) : ℝ :=
  fullEnergyPotentialPathLimit G m hm PF default U t ω -
    fullEnergyMartingaleLimit G m hm PF default U t ω

/-- The remainder path stopped at the dyadic exit of `A`. -/
noncomputable def stoppedRemainder (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (A : Set V) :
    ℝ≥0 → PF.Ω → ℝ :=
  stoppedProcess (remainderPath G m hm PF default U) (dyadicExit PF A)

theorem stoppedRemainder_apply (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (A : Set V)
    (t : ℝ≥0) (ω : PF.Ω) :
    stoppedRemainder G m hm PF default U A t ω =
      stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) (dyadicExit PF A) t ω -
        stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U) (dyadicExit PF A) t ω :=
  rfl

theorem remainderPath_zero (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (ω : PF.Ω) :
    remainderPath G m hm PF default U 0 ω = 0 := by
  simp only [remainderPath, fullEnergyMartingaleLimit_zero, sub_zero, fullEnergyPotentialPathLimit,
    fullEnergyPotentialApprox, sub_self]
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).limUnder_eq

theorem stoppedRemainder_zero (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (U : hilbertDomain G m) (A : Set V) (ω : PF.Ω) :
    stoppedRemainder G m hm PF default U A 0 ω = 0 := by
  rw [stoppedRemainder,
    stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ dyadicExit PF A ω from bot_le)]
  exact remainderPath_zero G m hm PF default U ω

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m) (A : Set V)

include h hG hm hmsum

/-! ## Path regularity -/

theorem ae_isRightContinuous_martingaleLimit (z : V) :
    ∀ᵐ ω ∂PF.P z,
      IsRightContinuous (fun t ↦ fullEnergyMartingaleLimit G m hm PF default U t ω) :=
  (fullEnergyMartingaleLimit_ae_cadlag_and_uniform h hG hm hmsum default U z).mono
    fun _ hω ↦ hω.1.isRightContinuous

/-- **The unstopped remainder has continuous paths**: it is the locally uniform limit of the
drift occupations `occ_n(t) − occ_n(0)` of the core approximants, each of which is continuous. -/
theorem ae_continuous_remainderPath (z : V) :
    ∀ᵐ ω ∂PF.P z, Continuous (fun t ↦ remainderPath G m hm PF default U t ω) := by
  have hP := fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum default U z
  have hM := fullEnergyMartingaleLimit_ae_cadlag_and_uniform h hG hm hmsum default U z
  have hocc : ∀ᵐ ω ∂PF.P z, ∀ n : ℕ, Continuous (fun s ↦ boundedStateOccupationVersion PF
      (resolventCoreDrift G m (fullEnergyCoreIndex G m hm U (2 * n))) s ω) := by
    rw [ae_all_iff]
    intro n
    have hf : ∀ q, |resolventCoreDrift G m (fullEnergyCoreIndex G m hm U (2 * n)) q| ≤
        2 * countableResolventCoreBound (fullEnergyCoreIndex G m hm U (2 * n)) := fun q ↦ by
      simpa only [Real.norm_eq_abs] using norm_resolventCoreDrift_le G m hm _ q
    exact (boundedStateOccupationVersion_ae_eq_all_and_continuous h _ hf z).mono fun _ hω ↦ hω.2
  filter_upwards [hP, hM, hocc] with ω hPω hMω hoccω
  have hRn : ∀ n s, fullEnergyPotentialApprox G m hm PF default U n s ω -
      fullEnergyMartingaleApprox G m hm PF default U n s ω =
      boundedStateOccupationVersion PF
          (resolventCoreDrift G m (fullEnergyCoreIndex G m hm U (2 * n))) s ω -
        boundedStateOccupationVersion PF
          (resolventCoreDrift G m (fullEnergyCoreIndex G m hm U (2 * n))) 0 ω := by
    intro n s
    simp only [fullEnergyPotentialApprox, fullEnergyMartingaleApprox,
      compactResolventCoreMartingale_eq_potential_sub_occupation]
    ring
  have hcontn : ∀ n, Continuous (fun s ↦ fullEnergyPotentialApprox G m hm PF default U n s ω -
      fullEnergyMartingaleApprox G m hm PF default U n s ω) := by
    intro n
    simp_rw [hRn]
    exact (hoccω n).sub continuous_const
  have hunif : ∀ T : ℕ, TendstoUniformlyOn
      (fun n s ↦ fullEnergyPotentialApprox G m hm PF default U n s ω -
        fullEnergyMartingaleApprox G m hm PF default U n s ω)
      (fun s ↦ remainderPath G m hm PF default U s ω) atTop (Icc 0 (T : ℝ≥0)) := fun T ↦
    (hPω.2 T).sub (hMω.2 T)
  rw [continuous_iff_continuousAt]
  intro s
  obtain ⟨T, hT⟩ := exists_nat_gt s
  have hcont : ContinuousOn (fun s ↦ remainderPath G m hm PF default U s ω)
      (Icc 0 (T : ℝ≥0)) :=
    (hunif T).continuousOn (Eventually.of_forall fun n ↦ (hcontn n).continuousOn).frequently
  have hmem : Icc (0 : ℝ≥0) (T : ℝ≥0) ∈ 𝓝 s := by
    have : Icc (0 : ℝ≥0) (T : ℝ≥0) = Iic (T : ℝ≥0) := by
      ext x
      simp [zero_le]
    rw [this]
    exact Iic_mem_nhds hT
  exact hcont.continuousAt hmem

/-! ## Adaptedness, integrability, set-integral identities -/

theorem stoppedRemainder_aestronglyMeasurable (z : V) (s : ℝ≥0) :
    AEStronglyMeasurable[PF.naturalFiltration.rightCont s]
      (stoppedRemainder G m hm PF default U A s) (PF.P z) := by
  have htau := isStoppingTime_rightCont_dyadicExit PF A
  exact (aestronglyMeasurable_stopped_fullEnergyPotentialPathLimit_rightCont
      h hG hm hmsum default z htau U s).sub
    (aestronglyMeasurable_stoppedProcess_of_ae_isRightContinuous
      (stronglyAdapted_fullEnergyMartingaleLimit h hG hm hmsum default U)
      (ae_isRightContinuous_martingaleLimit h hG hm hmsum default U z) htau s)

theorem stoppedRemainder_memLp_two (z : V) (t : ℝ≥0) :
    MemLp (stoppedRemainder G m hm PF default U A t) 2 (PF.P z) := by
  have htau := isStoppingTime_rightCont_dyadicExit PF A
  exact (stopped_fullEnergyPotentialPathLimit_memLp_and_L2_convergence
      h hG hm hmsum default z htau U t).1.sub
    (stoppedProcess_memLp_two_and_second_moment_le
      (fullEnergyMartingaleLimit_isMartingale h hG hm hmsum default U z) htau
      (ae_isRightContinuous_martingaleLimit h hG hm hmsum default U z) t
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence h hG hm hmsum default U z t).1).1

/-- **The martingale set-integral identities of the stopped remainder**, from the drift
elimination of `p:lem:localharm` (`hU` is the full spatial variational harmonicity of `U` on
`A`) and the optional stopping of the Fukushima martingale. -/
theorem stoppedRemainder_setIntegral_eq
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) {s t : ℝ≥0} (hst : s ≤ t) {B : Set PF.Ω}
    (hB : MeasurableSet[PF.naturalFiltration.rightCont s] B) :
    ∫ ω in B, stoppedRemainder G m hm PF default U A t ω ∂PF.P z =
      ∫ ω in B, stoppedRemainder G m hm PF default U A s ω ∂PF.P z := by
  have htau := isStoppingTime_rightCont_dyadicExit PF A
  have hrM := ae_isRightContinuous_martingaleLimit h hG hm hmsum default U z
  have hMmart := fullEnergyMartingaleLimit_isMartingale h hG hm hmsum default U z
  obtain ⟨hPt, hPs, hPeq⟩ := stopped_fullEnergyPath_integrable_and_increment_eq_zero_dyadicExit
    h hG hm hmsum z A U B default hst hU hB
  have hMeq := stoppedProcess_setIntegral_eq hMmart htau hrM hst hB
  have hMt := integrable_stoppedProcess_of_ae_rightContinuous hMmart htau hrM t
  have hMs := integrable_stoppedProcess_of_ae_rightContinuous hMmart htau hrM s
  calc ∫ ω in B, stoppedRemainder G m hm PF default U A t ω ∂PF.P z
      = (∫ ω in B, stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
            (dyadicExit PF A) t ω ∂PF.P z) -
          ∫ ω in B, stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U)
            (dyadicExit PF A) t ω ∂PF.P z :=
        integral_sub hPt.integrableOn hMt.integrableOn
    _ = (∫ ω in B, stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U)
            (dyadicExit PF A) s ω ∂PF.P z) -
          ∫ ω in B, stoppedProcess (fullEnergyMartingaleLimit G m hm PF default U)
            (dyadicExit PF A) s ω ∂PF.P z := by rw [hPeq, hMeq]
    _ = _ := (integral_sub hPs.integrableOn hMs.integrableOn).symm

/-! ## An exactly adapted version, and its martingale property -/

/-- An exactly `rightCont s`-measurable version of the stopped remainder at time `s`. -/
noncomputable def stoppedRemainderVersion (z : V) (s : ℝ≥0) : PF.Ω → ℝ :=
  (stoppedRemainder_aestronglyMeasurable h hG hm hmsum default U A z s).mk _

theorem stoppedRemainderVersion_ae_eq (z : V) (s : ℝ≥0) :
    stoppedRemainder G m hm PF default U A s =ᵐ[PF.P z]
      stoppedRemainderVersion h hG hm hmsum default U A z s :=
  (stoppedRemainder_aestronglyMeasurable h hG hm hmsum default U A z s).ae_eq_mk

theorem stronglyMeasurable_stoppedRemainderVersion (z : V) (s : ℝ≥0) :
    StronglyMeasurable[PF.naturalFiltration.rightCont s]
      (stoppedRemainderVersion h hG hm hmsum default U A z s) :=
  (stoppedRemainder_aestronglyMeasurable h hG hm hmsum default U A z s).stronglyMeasurable_mk

theorem memLp_two_stoppedRemainderVersion (z : V) (t : ℝ≥0) :
    MemLp (stoppedRemainderVersion h hG hm hmsum default U A z t) 2 (PF.P z) :=
  (stoppedRemainder_memLp_two h hG hm hmsum default U A z t).ae_eq
    (stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z t)

/-- **The stopped remainder is a martingale** (in its exactly adapted version) of the raw
right-continuous natural filtration under every starting law. -/
theorem martingale_stoppedRemainderVersion
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) :
    Martingale (stoppedRemainderVersion h hG hm hmsum default U A z)
      PF.naturalFiltration.rightCont (PF.P z) := by
  refine ⟨fun s ↦ stronglyMeasurable_stoppedRemainderVersion h hG hm hmsum default U A z s,
    fun s t hst ↦ ?_⟩
  have hint : ∀ r, Integrable (stoppedRemainderVersion h hG hm hmsum default U A z r) (PF.P z) :=
    fun r ↦ (memLp_two_stoppedRemainderVersion h hG hm hmsum default U A z r).integrable
      one_le_two
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq (PF.naturalFiltration.rightCont.le s) (hint t)
    (fun B _ _ ↦ (hint s).integrableOn) (fun B hB _ ↦ ?_)
    (stronglyMeasurable_stoppedRemainderVersion h hG hm hmsum default U A z s).aestronglyMeasurable
  have hBm : MeasurableSet B := PF.naturalFiltration.rightCont.le s _ hB
  rw [setIntegral_congr_ae hBm
      ((stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z s).symm.mono fun ω hω _ ↦ hω),
    setIntegral_congr_ae hBm
      ((stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z t).symm.mono fun ω hω _ ↦ hω)]
  exact (stoppedRemainder_setIntegral_eq h hG hm hmsum default U A hU z hst hB).symm

/-! ## Orthogonal increments along the uniform grids -/

/-- **`E_z[N_t²] = Σ_k E_z[(N_{t_{k+1}} − N_{t_k})²]`** along the uniform grid of `[0, t]`. -/
theorem integral_sq_stoppedRemainder_eq_sum
    (hU : ∀ v : hilbertDomain G m,
      (∀ x ∉ A, unweight m (valueInclusion G m v) x = 0) →
      G.dirichletForm (unweight m (valueInclusion G m U))
        (unweight m (valueInclusion G m v)) = 0)
    (z : V) (t : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, (stoppedRemainder G m hm PF default U A t ω) ^ 2 ∂PF.P z =
      ∑ k ∈ Finset.range n, ∫ ω,
        (stoppedRemainder G m hm PF default U A (uniformGrid t n (k + 1)) ω -
          stoppedRemainder G m hm PF default U A (uniformGrid t n k) ω) ^ 2 ∂PF.P z := by
  have hmart := martingale_stoppedRemainderVersion h hG hm hmsum default U A hU z
  have h2 := memLp_two_stoppedRemainderVersion h hG hm hmsum default U A z
  have hae := stoppedRemainderVersion_ae_eq h hG hm hmsum default U A z
  have key := integral_sq_eq_sum_sq_increments hmart h2 (uniformGrid t n)
    (fun a b hab ↦ uniformGrid_mono t n hab) n
  rw [uniformGrid_self t hn, uniformGrid_zero t n] at key
  have hv : ∀ r, (fun ω ↦ (stoppedRemainder G m hm PF default U A r ω) ^ 2) =ᵐ[PF.P z]
      fun ω ↦ (stoppedRemainderVersion h hG hm hmsum default U A z r ω) ^ 2 :=
    fun r ↦ (hae r).mono fun ω hω ↦ by simp only [hω]
  have h0 : ∫ ω, (stoppedRemainderVersion h hG hm hmsum default U A z 0 ω) ^ 2 ∂PF.P z = 0 := by
    rw [← integral_congr_ae (hv 0)]
    simp only [stoppedRemainder_zero, zero_pow two_ne_zero, integral_zero]
  rw [h0, zero_add] at key
  rw [integral_congr_ae (hv t), key]
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  filter_upwards [hae (uniformGrid t n (k + 1)), hae (uniformGrid t n k)] with ω h1 h2
  rw [h1, h2]

/-! ## Measurability facts -/

theorem measurable_remainderPath (r : ℝ≥0) :
    Measurable (remainderPath G m hm PF default U r) :=
  (((stronglyAdapted_fullEnergyPotentialPathLimit_rightCont G m hm PF default U r).mono
    (PF.naturalFiltration.rightCont.le r)).measurable).sub
    (((stronglyAdapted_fullEnergyMartingaleLimit h hG hm hmsum default U r).mono
      (PF.naturalFiltration.rightCont.le r)).measurable)

omit h hG hm hmsum in
theorem measurable_dyadicExit : Measurable (dyadicExit PF A) :=
  (isStoppingTime_rightCont_dyadicExit PF A).measurable'

end ReflectedGMS.StoppedRemainder
