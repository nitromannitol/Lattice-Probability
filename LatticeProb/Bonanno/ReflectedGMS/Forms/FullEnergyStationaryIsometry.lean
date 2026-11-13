/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyStationaryIsometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.SquareCompensatorLimit

/-!
# Stationary isometry for the full-energy martingale

The finite speed measure is deliberately left unnormalized.  The exact
resolvent-core stationary identity passes to the full form domain by L2
convergence under that measure.
-/

set_option autoImplicit false

open Filter MeasureTheory ProbabilityTheory Topology Set
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m)

include h hG hm hmsum

omit h hG hmsum in
private theorem fullEnergyCore_energy_tendsto_stationary :
    Tendsto (fun n ↦ G.Energy
      (countableResolventCoreFeature G m (fullEnergyCoreIndex G m hm U (2 * n))))
      atTop (𝓝 (G.Energy (unweight m (valueInclusion G m U)))) := by
  let Un : ℕ → hilbertDomain G m := fun n ↦
    countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U (2 * n))
  have hUn : Tendsto Un atTop (𝓝 U) := by
    apply countableResolventCoreVector_tendsto_of_geometric_bound G m U
      (fun n ↦ fullEnergyCoreIndex G m hm U (2 * n))
    intro n
    exact (fullEnergyCoreIndex_bound G m hm U (2 * n)).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (Nat.le_mul_of_pos_left n (by norm_num)))
  have hgrad : Tendsto (fun n ↦ ‖gradientInclusion G m (Un n)‖ ^ 2)
      atTop (𝓝 (‖gradientInclusion G m U‖ ^ 2)) :=
    (((gradientInclusion G m).continuous.continuousAt.tendsto.comp hUn).norm).pow 2
  convert hgrad using 1
  · ext n
    dsimp only [Un]
    rw [countableResolventCoreVector_eq_inHilbertDomain G m hm,
      gradientInclusion_inHilbertDomain, weightedGradient_norm_sq]
  · rw [gradientInclusion_eq, weightedGradient_norm_sq]

private theorem fullEnergyMartingaleApprox_stationary_sq_difference_integral_eq
    (t : ℝ≥0) (n k : ℕ) :
    (∫ ω, (fullEnergyMartingaleApprox G m hm PF default U n t ω -
        fullEnergyMartingaleApprox G m hm PF default U k t ω) ^ 2
      ∂reflectedSpeedLaw PF m) =
      (t : ℝ) * (2 * G.Energy
        (countableResolventCoreFeature G m
          (fullEnergyCoreIndex G m hm U (2 * n)) -
        countableResolventCoreFeature G m
          (fullEnergyCoreIndex G m hm U (2 * k)))) := by
  let qn := fullEnergyCoreIndex G m hm U (2 * n)
  let qk := fullEnergyCoreIndex G m hm U (2 * k)
  let r : CountableResolventCoreIndex V := qn - qk
  let D : PF.Ω → ℝ := fun ω ↦
    compactResolventCoreMartingale G m hm PF default r t ω -
      compactResolventCoreMartingale G m hm PF default r 0 ω
  have hpoint (ω : PF.Ω) :
      fullEnergyMartingaleApprox G m hm PF default U n t ω -
        fullEnergyMartingaleApprox G m hm PF default U k t ω = D ω := by
    dsimp only [fullEnergyMartingaleApprox, D, r, qn, qk]
    rw [compactResolventCoreMartingale_sub]
    simp only [Pi.sub_apply]
    ring
  have hae (q : CountableResolventCoreIndex V) (a : ℝ≥0) :
      compactResolventCoreMartingale G m hm PF default q a =ᵐ[reflectedSpeedLaw PF m]
        rawResolventCoreMartingale PF G m q a := by
    exact (ae_reflectedSpeedLaw_iff PF m hm (fun ω ↦
      compactResolventCoreMartingale G m hm PF default q a ω =
        rawResolventCoreMartingale PF G m q a ω)).2 (fun z ↦
      compactResolventCoreMartingale_ae_eq h hG hm hmsum default q z a)
  have heq : (∫ ω, D ω ^ 2 ∂reflectedSpeedLaw PF m) =
      ∫ ω, (rawResolventCoreMartingale PF G m r t ω -
        rawResolventCoreMartingale PF G m r 0 ω) ^ 2
        ∂reflectedSpeedLaw PF m := by
    apply integral_congr_ae
    filter_upwards [hae r t, hae r 0] with ω ht h0
    dsimp only [D]
    rw [ht, h0]
  rw [integral_congr_ae (Eventually.of_forall fun ω ↦ congrArg (· ^ 2) (hpoint ω)),
    heq, rawResolventCoreMartingale_stationary_increment_energy
      h hG hm hmsum r (zero_le : 0 ≤ t)]
  dsimp only [r, qn, qk]
  rw [countableResolventCoreFeature_sub]
  norm_num

private theorem fullEnergyMartingaleApprox_stationary_toLp_cauchySeq (t : ℝ≥0) :
    let P := reflectedSpeedLaw PF m
    let _ : IsFiniteMeasure P := reflectedSpeedLaw_isFinite PF m hmsum
    let F : ℕ → PF.Ω → ℝ := fun n ↦
      fullEnergyMartingaleApprox G m hm PF default U n t
    let hF : ∀ n, MemLp (F n) 2 P := fun n ↦
      fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U P n t
    CauchySeq fun n ↦ (hF n).toLp (F n) := by
  dsimp only
  let P := reflectedSpeedLaw PF m
  letI : IsFiniteMeasure P := reflectedSpeedLaw_isFinite PF m hmsum
  let F : ℕ → PF.Ω → ℝ := fun n ↦
    fullEnergyMartingaleApprox G m hm PF default U n t
  let hF : ∀ n, MemLp (F n) 2 P := fun n ↦
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U P n t
  let A : ℝ := 2 * (t : ℝ)
  let b : ℕ → ℝ := fun N ↦ Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))
  apply cauchySeq_of_le_tendsto_0 b
  · intro n k N hn hk
    have hdiff : MemLp (F n - F k) 2 P := (hF n).sub (hF k)
    have hsub : (hF n).toLp (F n) - (hF k).toLp (F k) =
        hdiff.toLp (F n - F k) := (MemLp.toLp_sub (hF n) (hF k)).symm
    rw [dist_eq_norm, hsub]
    have hsq := fullEnergyMartingaleApprox_stationary_sq_difference_integral_eq
      h hG hm hmsum default U t n k
    change (∫ ω, (F n ω - F k ω) ^ 2 ∂P) = _ at hsq
    have henergy := countableResolventCore_pair_energy_le_of_geometric_bound G m U
      (fullEnergyCoreIndex G m hm U) (fullEnergyCoreIndex_bound G m hm U)
      (2 * n) (2 * k)
    have hpow_n : (1 / 2 : ℝ) ^ (2 * n) ≤ (1 / 2 : ℝ) ^ (2 * N) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left 2 hn)
    have hpow_k : (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ (2 * N) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.mul_le_mul_left 2 hk)
    have hA : 0 ≤ A := by dsimp only [A]; positivity
    have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
    apply (sq_le_sq₀ (norm_nonneg _) (by dsimp only [b]; positivity)).mp
    calc
      ‖hdiff.toLp (F n - F k)‖ ^ 2 =
          ∫ ω, (F n ω - F k ω) ^ 2 ∂P := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hdiff.coeFn_toLp] with ω hω
        rw [hω]
        simp only [Pi.sub_apply, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = A * G.Energy
          (countableResolventCoreFeature G m
            (fullEnergyCoreIndex G m hm U (2 * n)) -
          countableResolventCoreFeature G m
            (fullEnergyCoreIndex G m hm U (2 * k))) := by
        rw [hsq]
        dsimp only [A]
        ring
      _ ≤ A * ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * k)) ^ 2 :=
        mul_le_mul_of_nonneg_left henergy hA
      _ ≤ A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 (by linarith)
      _ = (b N) ^ 2 := by
        change A * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 =
          (Real.sqrt A * (2 * (1 / 2 : ℝ) ^ (2 * N))) ^ 2
        calc
          _ = (Real.sqrt A) ^ 2 * (2 * (1 / 2 : ℝ) ^ (2 * N)) ^ 2 := by rw [hsqrt]
          _ = _ := by ring
  · dsimp only [b]
    convert (tendsto_const_nhds.mul
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 2)
          (by norm_num : (1 / 2 : ℝ) ^ 2 < 1)))) using 1
    · ext N
      rw [← pow_mul]
    · ring

/-- The pathwise full-energy limit is square-integrable under the finite,
unnormalized stationary speed measure, and the core approximants converge to
it in L2. -/
theorem fullEnergyMartingaleLimit_memLp_and_L2_convergence_reflectedSpeedLaw
    (t : ℝ≥0) :
    MemLp (fullEnergyMartingaleLimit G m hm PF default U t) 2
        (reflectedSpeedLaw PF m) ∧
      Tendsto (fun n ↦ eLpNorm
        (fullEnergyMartingaleApprox G m hm PF default U n t -
          fullEnergyMartingaleLimit G m hm PF default U t) 2
        (reflectedSpeedLaw PF m)) atTop (𝓝 0) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hF := fun n ↦ fullEnergyMartingaleApprox_memLp_two
    h hG hm hmsum default U (reflectedSpeedLaw PF m) n t
  apply memLp_two_and_tendsto_eLpNorm_of_cauchySeq_of_tendsto_ae hF
  · exact fullEnergyMartingaleApprox_stationary_toLp_cauchySeq
      h hG hm hmsum default U t
  · rw [ae_reflectedSpeedLaw_iff PF m hm]
    intro z
    filter_upwards [fullEnergyMartingaleLimit_ae_cadlag_and_uniform
      h hG hm hmsum default U z] with ω hω
    obtain ⟨T, ht⟩ := exists_nat_ge t
    exact (hω.2 T).tendsto_at ⟨zero_le, ht⟩

theorem fullEnergyMartingaleLimit_memLp_two_reflectedSpeedLaw (t : ℝ≥0) :
    MemLp (fullEnergyMartingaleLimit G m hm PF default U t) 2
      (reflectedSpeedLaw PF m) :=
  (fullEnergyMartingaleLimit_memLp_and_L2_convergence_reflectedSpeedLaw
    h hG hm hmsum default U t).1

/-- Exact stationary increment isometry for the actual full-domain martingale.
The speed measure is not divided by its total mass. -/
theorem fullEnergyMartingaleLimit_stationary_increment_energy
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (fullEnergyMartingaleLimit G m hm PF default U t ω -
        fullEnergyMartingaleLimit G m hm PF default U s ω) ^ 2
      ∂reflectedSpeedLaw PF m) =
      2 * ((t : ℝ) - (s : ℝ)) *
        G.Energy (unweight m (valueInclusion G m U)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  let P := reflectedSpeedLaw PF m
  let Mn : ℕ → ℝ≥0 → PF.Ω → ℝ := fun n ↦
    fullEnergyMartingaleApprox G m hm PF default U n
  let M : ℝ≥0 → PF.Ω → ℝ := fullEnergyMartingaleLimit G m hm PF default U
  let Dn : ℕ → PF.Ω → ℝ := fun n ↦ Mn n t - Mn n s
  let D : PF.Ω → ℝ := M t - M s
  have hMn2 (n : ℕ) (a : ℝ≥0) : MemLp (Mn n a) 2 P :=
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U P n a
  have hM2 (a : ℝ≥0) : MemLp (M a) 2 P :=
    (fullEnergyMartingaleLimit_memLp_and_L2_convergence_reflectedSpeedLaw
      h hG hm hmsum default U a).1
  have hDn2 (n : ℕ) : MemLp (Dn n) 2 P := (hMn2 n t).sub (hMn2 n s)
  have hD2 : MemLp D 2 P := (hM2 t).sub (hM2 s)
  have hL2 : Tendsto (fun n ↦ eLpNorm (Dn n - D) 2 P) atTop (𝓝 0) := by
    have ht := (fullEnergyMartingaleLimit_memLp_and_L2_convergence_reflectedSpeedLaw
      h hG hm hmsum default U t).2
    have hs := (fullEnergyMartingaleLimit_memLp_and_L2_convergence_reflectedSpeedLaw
      h hG hm hmsum default U s).2
    have hu : Tendsto (fun n ↦ eLpNorm (Mn n t - M t) 2 P +
        eLpNorm (Mn n s - M s) 2 P) atTop (𝓝 0) := by simpa using ht.add hs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun _ ↦ zero_le) (fun n ↦ ?_)
    have htri := eLpNorm_sub_le (f := Mn n t - M t) (g := Mn n s - M s) (μ := P)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    calc
      eLpNorm (Dn n - D) 2 P = eLpNorm
          ((Mn n t - M t) - (Mn n s - M s)) 2 P := by
        congr 1
        funext ω
        dsimp only [Dn, D, Pi.sub_apply]
        ring
      _ ≤ _ := htri
  have hsq := tendsto_eLpNorm_sq_sub_sq_one_of_tendsto_eLpNorm_two hDn2 hD2 hL2
  have hint : Tendsto (fun n ↦ ∫ ω, (Dn n ω) ^ 2 ∂P) atTop
      (𝓝 (∫ ω, (D ω) ^ 2 ∂P)) := by
    apply tendsto_integral_of_L1'
    · exact Eventually.of_forall fun n ↦ (hDn2 n).integrable_sq
    · convert hsq using 1
  have hcore : Tendsto (fun n ↦ ((t : ℝ) - (s : ℝ)) *
      (2 * G.Energy (countableResolventCoreFeature G m
        (fullEnergyCoreIndex G m hm U (2 * n))))) atTop
      (𝓝 (((t : ℝ) - (s : ℝ)) *
        (2 * G.Energy (unweight m (valueInclusion G m U))))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.mul
      (fullEnergyCore_energy_tendsto_stationary hm U))
  have heq (n : ℕ) : (∫ ω, (Dn n ω) ^ 2 ∂P) =
      ((t : ℝ) - (s : ℝ)) * (2 * G.Energy
        (countableResolventCoreFeature G m
          (fullEnergyCoreIndex G m hm U (2 * n)))) := by
    let q := fullEnergyCoreIndex G m hm U (2 * n)
    have hae (a : ℝ≥0) :
        compactResolventCoreMartingale G m hm PF default q a =ᵐ[P]
          rawResolventCoreMartingale PF G m q a := by
      exact (ae_reflectedSpeedLaw_iff PF m hm (fun ω ↦
        compactResolventCoreMartingale G m hm PF default q a ω =
          rawResolventCoreMartingale PF G m q a ω)).2 (fun z ↦
        compactResolventCoreMartingale_ae_eq h hG hm hmsum default q z a)
    calc
      (∫ ω, (Dn n ω) ^ 2 ∂P) =
          ∫ ω, (rawResolventCoreMartingale PF G m q t ω -
            rawResolventCoreMartingale PF G m q s ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hae t, hae s] with ω ht hs
        change (((compactResolventCoreMartingale G m hm PF default q t ω -
          compactResolventCoreMartingale G m hm PF default q 0 ω) -
          (compactResolventCoreMartingale G m hm PF default q s ω -
          compactResolventCoreMartingale G m hm PF default q 0 ω)) ^ 2) = _
        rw [ht, hs]
        ring
      _ = _ := rawResolventCoreMartingale_stationary_increment_energy
        h hG hm hmsum q hst
  have hlimit := tendsto_nhds_unique (hint.congr' (Eventually.of_forall heq)) hcore
  simpa only [D, M, P, Pi.sub_apply, mul_assoc, mul_left_comm, mul_comm] using hlimit

end ReflectedGMS
