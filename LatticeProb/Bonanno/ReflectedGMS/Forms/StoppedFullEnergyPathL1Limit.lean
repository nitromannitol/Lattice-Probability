/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.StoppedFullEnergyPathL1Limit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StoppedResolventMomentBound
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.L2CauchyAELimit

/-! Fixed-start bounded stopped-time convergence of the full-energy path.
The core square estimate gives an L2 Cauchy sequence directly; no new
all-time envelope or uniform-integrability hypothesis is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace
namespace ReflectedGMS
open ReflectedWalk FullNetworkForm
variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default z : V)
  {tau : PF.Ω → WithTop ℝ≥0}
  (htau : IsStoppingTime PF.naturalFiltration.rightCont tau)

include h hG hmsum htau

/-- Centered stopped core potentials remain square integrable. -/
theorem stopped_centeredCorePotential_memLp_two
    (q : CountableResolventCoreIndex V) (t : ℝ≥0) :
    MemLp (fun ω ↦
      stoppedProcess (compactResolventCorePotential G m hm PF default q) tau t ω -
        compactResolventCorePotential G m hm PF default q 0 ω) 2 (PF.P z) := by
  have hi := integrable_stopped_compactResolventCorePotential
    h hG hm hmsum default z q htau t
  apply MemLp.of_bound (hi.1.sub
    (stronglyMeasurable_compactResolventCorePotential G m hm PF default q 0).aestronglyMeasurable)
    (2 * countableResolventCoreBound q)
  filter_upwards [] with ω
  exact (norm_sub_le _ _).trans ((add_le_add
    (norm_compactResolventCorePotential_le G m hm PF default q _ ω)
    (norm_compactResolventCorePotential_le G m hm PF default q 0 ω)).trans_eq (by ring))

/-- The fixed-start square estimate applies to arbitrary pairs of the
actual stopped approximants, with the full-domain geometric error. -/
theorem stopped_fullEnergyPotentialApprox_sq_difference_integral_le
    (U : hilbertDomain G m) (t : ℝ≥0) (n k : ℕ) :
    (∫ ω, (stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t ω -
      stoppedProcess (fullEnergyPotentialApprox G m hm PF default U k) tau t ω) ^ 2
      ∂PF.P z) ≤
      (2048 * (t : ℝ) / m z) *
        ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := by
  let q := fullEnergyCoreIndex G m hm U
  let r := q (2 * n) - q (2 * k)
  let F : PF.Ω → ℝ := fun ω ↦
    stoppedProcess (compactResolventCorePotential G m hm PF default r) tau t ω -
      compactResolventCorePotential G m hm PF default r 0 ω
  have hF : MemLp F 2 (PF.P z) :=
    stopped_centeredCorePotential_memLp_two h hG hm hmsum default z htau r t
  obtain ⟨D, _, hDi, hDb, hDint⟩ :=
    exists_start_sq_envelope_compactResolventCorePotential h hG hm hmsum default z r t
  have hFD : ∀ᵐ ω ∂PF.P z, F ω ^ 2 ≤ D ω := by
    filter_upwards [hDb] with ω hω
    let theta := min (t : WithTop ℝ≥0) (tau ω)
    have htheta : theta ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    exact hω.2 theta.untopA ((WithTop.untopA_le_iff htheta).2 (min_le_left _ _))
  have hbound := integral_mono_ae hF.integrable_sq hDi hFD
  have hpair : G.Energy (countableResolventCoreFeature G m r) ≤
      ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := by
    dsimp only [r]
    rw [countableResolventCoreFeature_sub]
    exact countableResolventCore_pair_energy_le_of_geometric_bound G m U q
      (fullEnergyCoreIndex_bound G m hm U) _ _
  have henergy : (∫ ω, F ω ^ 2 ∂PF.P z) ≤
      (2048 * (t : ℝ) / m z) *
        ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := by
    calc
      _ ≤ ∫ ω, D ω ∂PF.P z := hbound
      _ ≤ (2048 * (t : ℝ) * G.Energy (countableResolventCoreFeature G m r)) / m z := by
        apply (le_div_iff₀ (hm z)).2
        simpa only [mul_comm] using hDint
      _ ≤ (2048 * (t : ℝ) *
          ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2) / m z :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpair (by positivity)) (hm z).le
      _ = _ := by ring
  convert henergy using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  congr 1
  dsimp only [F, r, q, stoppedProcess, fullEnergyPotentialApprox]
  rw [compactResolventCorePotential_sub]
  simp only [Pi.sub_apply]
  ring

/-- The actual full-energy path at a bounded stopped time is square
integrable, and its centered even-core approximants converge in L2. -/
theorem stopped_fullEnergyPotentialPathLimit_memLp_and_L2_convergence
    (U : hilbertDomain G m) (t : ℝ≥0) :
    MemLp (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau t)
      2 (PF.P z) ∧
    Tendsto (fun n ↦ eLpNorm
      (stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t -
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau t)
      2 (PF.P z)) atTop (𝓝 0) := by
  let F : ℕ → PF.Ω → ℝ := fun n ↦
    stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t
  have hF : ∀ n, MemLp (F n) 2 (PF.P z) := fun n ↦
    stopped_centeredCorePotential_memLp_two h hG hm hmsum default z htau
      (fullEnergyCoreIndex G m hm U (2 * n)) t
  apply memLp_two_and_tendsto_eLpNorm_of_cauchySeq_of_tendsto_ae hF
  ·
    let A : ℝ := 2048 * (t : ℝ) / m z
    let b : ℕ → ℝ := fun N ↦ Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))
    apply cauchySeq_of_le_tendsto_0 b
    · intro n k N hn hk
      have hdiff : MemLp (F n - F k) 2 (PF.P z) := (hF n).sub (hF k)
      have hsub : (hF n).toLp (F n) - (hF k).toLp (F k) =
          hdiff.toLp (F n - F k) := by
        exact (MemLp.toLp_sub (hF n) (hF k)).symm
      rw [dist_eq_norm, hsub]
      have hsq := stopped_fullEnergyPotentialApprox_sq_difference_integral_le
        h hG hm hmsum default z htau U t n k
      change (∫ ω, (F n ω - F k ω) ^ 2 ∂PF.P z) ≤ _ at hsq
      have hpow_n : (1 / 2 : ℝ) ^ (2 * n) ≤ (1 / 2 : ℝ) ^ (2 * N) := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.mul_le_mul_left 2 hn)
      have hpow_k : (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ (2 * N) := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Nat.mul_le_mul_left 2 hk)
      have hA : 0 ≤ A := by
        dsimp only [A]
        exact div_nonneg (mul_nonneg (by norm_num) t.coe_nonneg) (hm z).le
      have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
      have hnorm_nonneg : 0 ≤ ‖hdiff.toLp (F n - F k)‖ := norm_nonneg _
      have hsum_nonneg : 0 ≤
          (1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k) := by positivity
      have hb_nonneg : 0 ≤ b N := by dsimp only [b]; positivity
      apply (sq_le_sq₀ hnorm_nonneg hb_nonneg).mp
      calc
        ‖hdiff.toLp (F n - F k)‖ ^ 2 =
            ∫ ω, (F n ω - F k ω) ^ 2 ∂PF.P z := by
          rw [← real_inner_self_eq_norm_sq, L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hdiff.coeFn_toLp] with ω hω
          rw [hω]
          simp only [Pi.sub_apply, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
        _ ≤ A * ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 := hsq
        _ ≤ A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ hA
          exact (sq_le_sq₀ hsum_nonneg (by positivity)).2 (by linarith)
        _ = (b N) ^ 2 := by
          change A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 =
            (Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))) ^ 2
          calc
            A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 =
                (Real.sqrt A) ^ 2 * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by
              rw [hsqrt]
            _ = (Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))) ^ 2 := by ring
    · dsimp only [b]
      convert (tendsto_const_nhds.mul
        (tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_lt_one
            (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 2)
            (by norm_num : (1 / 2 : ℝ) ^ 2 < 1)))) using 1
      · ext N
        rw [← pow_mul]
      · ring
  · filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform
      h hG hm hmsum default U z] with ω hω
    let theta := min (t : WithTop ℝ≥0) (tau ω)
    have htheta : theta ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
    obtain ⟨T, ht⟩ := exists_nat_ge theta.untopA
    exact (hω.2 T).tendsto_at ⟨zero_le, ht⟩

/-- Fixed-start stopped L1 convergence, including integrability of the
actual path limit. -/
theorem stopped_fullEnergyPotentialPathLimit_integrable_and_L1_convergence
    (U : hilbertDomain G m) (t : ℝ≥0) :
    Integrable (stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau t)
      (PF.P z) ∧
    Tendsto (fun n ↦ eLpNorm
      (stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t -
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau t)
      1 (PF.P z)) atTop (𝓝 0) := by
  obtain ⟨hL, hc⟩ := stopped_fullEnergyPotentialPathLimit_memLp_and_L2_convergence
    h hG hm hmsum default z htau U t
  refine ⟨hL.integrable (by norm_num), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ ↦ zero_le)
  intro n
  have hn : MemLp
      (stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t)
      2 (PF.P z) := stopped_centeredCorePotential_memLp_two h hG hm hmsum default z htau
        (fullEnergyCoreIndex G m hm U (2 * n)) t
  simpa only [measure_univ, ENNReal.one_rpow, mul_one] using
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hn.aestronglyMeasurable.sub hL.aestronglyMeasurable)

/-- Event-restricted stopped integrals converge to those of the actual
full-energy path limit under each fixed vertex starting law. -/
theorem stopped_fullEnergyPotentialPathLimit_setIntegral_tendsto
    (U : hilbertDomain G m) (t : ℝ≥0) (B : Set PF.Ω) :
    Tendsto (fun n ↦ ∫ ω in B,
      stoppedProcess (fullEnergyPotentialApprox G m hm PF default U n) tau t ω ∂PF.P z)
      atTop (𝓝 (∫ ω in B,
        stoppedProcess (fullEnergyPotentialPathLimit G m hm PF default U) tau t ω ∂PF.P z)) := by
  obtain ⟨hi, hc⟩ := stopped_fullEnergyPotentialPathLimit_integrable_and_L1_convergence
    h hG hm hmsum default z htau U t
  exact tendsto_setIntegral_of_L1' _ (Eventually.of_forall fun n ↦
    (stopped_centeredCorePotential_memLp_two h hG hm hmsum default z htau
      (fullEnergyCoreIndex G m hm U (2 * n)) t).integrable (by norm_num)) hc B

end ReflectedGMS
