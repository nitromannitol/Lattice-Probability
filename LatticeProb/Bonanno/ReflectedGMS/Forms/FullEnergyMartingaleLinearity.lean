/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyMartingaleLinearity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreLinearity

/-! Linearity of the full-energy martingale at each fixed time, modulo the
null set belonging to the chosen starting law.  The proof compares the three
independently chosen canonical core approximations in `L²`. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}

private theorem countableResolventCoreVector_add
    (q r : CountableResolventCoreIndex V) :
    countableResolventCoreVector G m (q + r) =
      countableResolventCoreVector G m q + countableResolventCoreVector G m r := by
  unfold countableResolventCoreVector
  rw [countableResolventCoreInput_add]
  exact map_add (oneResolventLift G m) _ _

private theorem countableResolventCoreVector_sub
    (q r : CountableResolventCoreIndex V) :
    countableResolventCoreVector G m (q - r) =
      countableResolventCoreVector G m q - countableResolventCoreVector G m r := by
  unfold countableResolventCoreVector
  rw [show countableResolventCoreInput G m (q - r) =
      countableResolventCoreInput G m q - countableResolventCoreInput G m r by
    exact map_sub (countableResolventCoreInputAddHom G m) q r]
  exact map_sub (oneResolventLift G m) _ _

theorem countableResolventCore_centeredMartingale_toLp_norm_le
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (q : CountableResolventCoreIndex V) (t : ℝ≥0) :
    let D : PF.Ω → ℝ := fun ω ↦
      compactResolventCoreMartingale G m hm PF default q t ω -
        compactResolventCoreMartingale G m hm PF default q 0 ω
    let hD : MemLp D 2 (PF.P z) :=
      (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) t).sub
        (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) 0)
    ‖hD.toLp D‖ ≤ Real.sqrt (2 * (t : ℝ) / m z) *
      ‖countableResolventCoreVector G m q‖ := by
  dsimp only
  let D : PF.Ω → ℝ := fun ω ↦
    compactResolventCoreMartingale G m hm PF default q t ω -
      compactResolventCoreMartingale G m hm PF default q 0 ω
  let hD : MemLp D 2 (PF.P z) :=
    (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) 0)
  have heq : (∫ ω, D ω ^ 2 ∂PF.P z) =
      ∫ ω, (rawResolventCoreMartingale PF G m q t ω -
        rawResolventCoreMartingale PF G m q 0 ω) ^ 2 ∂PF.P z := by
    apply integral_congr_ae
    filter_upwards [compactResolventCoreMartingale_ae_eq h hG hm hmsum default q z t,
      compactResolventCoreMartingale_ae_eq h hG hm hmsum default q z 0] with ω ht h0
    dsimp only [D]
    rw [ht, h0]
  have henergy : m z * (∫ ω, D ω ^ 2 ∂PF.P z) ≤
      (t : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m q)) := by
    rw [heq]
    exact mul_rawResolventCoreMartingale_sq_increment_integral_le
      h hG hm hmsum q z (zero_le : 0 ≤ t)
  have hE : G.Energy (countableResolventCoreFeature G m q) ≤
      ‖countableResolventCoreVector G m q‖ ^ 2 := by
    have hzero : unweight m (valueInclusion G m (0 : hilbertDomain G m)) = 0 := by
      funext x
      simp [unweight]
    have hbase := countableResolventCore_energy_error_le_norm_sq G m
      (0 : hilbertDomain G m) q
    rw [hzero, sub_zero] at hbase
    simpa using hbase
  let A : ℝ := 2 * (t : ℝ) / m z
  have hint : (∫ ω, D ω ^ 2 ∂PF.P z) ≤
      A * ‖countableResolventCoreVector G m q‖ ^ 2 := by
    rw [show A * ‖countableResolventCoreVector G m q‖ ^ 2 =
        ((t : ℝ) * (2 * ‖countableResolventCoreVector G m q‖ ^ 2)) / m z by
      dsimp only [A]
      ring]
    apply (le_div_iff₀ (hm z)).2
    calc
      (∫ ω, D ω ^ 2 ∂PF.P z) * m z =
          m z * (∫ ω, D ω ^ 2 ∂PF.P z) := by ring
      _ ≤ (t : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m q)) := henergy
      _ ≤ (t : ℝ) * (2 * ‖countableResolventCoreVector G m q‖ ^ 2) := by
        gcongr
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg (mul_nonneg (by norm_num) t.coe_nonneg) (hm z).le
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖hD.toLp D‖ ^ 2 = ∫ ω, D ω ^ 2 ∂PF.P z := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hD.coeFn_toLp] with ω hω
      rw [hω]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ ≤ A * ‖countableResolventCoreVector G m q‖ ^ 2 := hint
    _ = (Real.sqrt A * ‖countableResolventCoreVector G m q‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hA]

theorem fullEnergyMartingaleLimit_add_ae
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (U W : hilbertDomain G m) (t : ℝ≥0) :
    fullEnergyMartingaleLimit G m hm PF default (U + W) t =ᵐ[PF.P z]
      fullEnergyMartingaleLimit G m hm PF default U t +
        fullEnergyMartingaleLimit G m hm PF default W t := by
  let FU : ℕ → PF.Ω → ℝ := fun n ↦ fullEnergyMartingaleApprox G m hm PF default U n t
  let FW : ℕ → PF.Ω → ℝ := fun n ↦ fullEnergyMartingaleApprox G m hm PF default W n t
  let Fsum : ℕ → PF.Ω → ℝ := fun n ↦
    fullEnergyMartingaleApprox G m hm PF default (U + W) n t
  let MU : PF.Ω → ℝ := fullEnergyMartingaleLimit G m hm PF default U t
  let MW : PF.Ω → ℝ := fullEnergyMartingaleLimit G m hm PF default W t
  let Msum : PF.Ω → ℝ := fullEnergyMartingaleLimit G m hm PF default (U + W) t
  have hFU (n : ℕ) : MemLp (FU n) 2 (PF.P z) :=
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U (PF.P z) n t
  have hFW (n : ℕ) : MemLp (FW n) 2 (PF.P z) :=
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default W (PF.P z) n t
  have hFsum (n : ℕ) : MemLp (Fsum n) 2 (PF.P z) :=
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default (U + W) (PF.P z) n t
  have hMU := (fullEnergyMartingaleLimit_memLp_and_L2_convergence
    h hG hm hmsum default U z t).1
  have hMW := (fullEnergyMartingaleLimit_memLp_and_L2_convergence
    h hG hm hmsum default W z t).1
  have hMsum := (fullEnergyMartingaleLimit_memLp_and_L2_convergence
    h hG hm hmsum default (U + W) z t).1
  have hULp : Tendsto (fun n ↦ (hFU n).toLp (FU n)) atTop (𝓝 (hMU.toLp MU)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' FU hFU MU hMU).2
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence
        h hG hm hmsum default U z t).2
  have hWLp : Tendsto (fun n ↦ (hFW n).toLp (FW n)) atTop (𝓝 (hMW.toLp MW)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' FW hFW MW hMW).2
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence
        h hG hm hmsum default W z t).2
  have hsumLp : Tendsto (fun n ↦ (hFsum n).toLp (Fsum n)) atTop
      (𝓝 (hMsum.toLp Msum)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Fsum hFsum Msum hMsum).2
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence
        h hG hm hmsum default (U + W) z t).2
  let r : ℕ → CountableResolventCoreIndex V := fun n ↦
    fullEnergyCoreIndex G m hm (U + W) (2 * n) -
      (fullEnergyCoreIndex G m hm U (2 * n) + fullEnergyCoreIndex G m hm W (2 * n))
  let D : ℕ → PF.Ω → ℝ := fun n ω ↦
    compactResolventCoreMartingale G m hm PF default (r n) t ω -
      compactResolventCoreMartingale G m hm PF default (r n) 0 ω
  have hD (n : ℕ) : MemLp (D n) 2 (PF.P z) :=
    (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) 0)
  have hrnorm (n : ℕ) : ‖countableResolventCoreVector G m (r n)‖ ≤
      3 * (1 / 2 : ℝ) ^ (2 * n) := by
    rw [show countableResolventCoreVector G m (r n) =
        (countableResolventCoreVector G m (fullEnergyCoreIndex G m hm (U + W) (2 * n)) - (U + W)) -
          ((countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U (2 * n)) - U) +
            (countableResolventCoreVector G m (fullEnergyCoreIndex G m hm W (2 * n)) - W)) by
      dsimp only [r]
      rw [countableResolventCoreVector_sub, countableResolventCoreVector_add]
      module]
    calc
      _ ≤ ‖countableResolventCoreVector G m (fullEnergyCoreIndex G m hm (U + W) (2 * n)) - (U + W)‖ +
          (‖countableResolventCoreVector G m (fullEnergyCoreIndex G m hm U (2 * n)) - U‖ +
            ‖countableResolventCoreVector G m (fullEnergyCoreIndex G m hm W (2 * n)) - W‖) :=
        (norm_sub_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
      _ ≤ (1 / 2 : ℝ) ^ (2 * n) + ((1 / 2 : ℝ) ^ (2 * n) + (1 / 2 : ℝ) ^ (2 * n)) := by
        gcongr
        · exact fullEnergyCoreIndex_bound G m hm (U + W) (2 * n)
        · exact fullEnergyCoreIndex_bound G m hm U (2 * n)
        · exact fullEnergyCoreIndex_bound G m hm W (2 * n)
      _ = _ := by ring
  have hDnorm : Tendsto (fun n ↦ ‖(hD n).toLp (D n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ (countableResolventCore_centeredMartingale_toLp_norm_le
        h hG hm hmsum default z (r n) t).trans
          (mul_le_mul_of_nonneg_left (hrnorm n) (Real.sqrt_nonneg _)))
    convert (tendsto_const_nhds.mul
      (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 2)
          (by norm_num : (1 / 2 : ℝ) ^ 2 < 1)))) using 1
    · ext n
      rw [← pow_mul]
    · ring
  have hDLp : Tendsto (fun n ↦ (hD n).toLp (D n)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hDnorm
  have hpoint (n : ℕ) : Fsum n = FU n + FW n + D n := by
    funext ω
    dsimp only [Fsum, FU, FW, D, r, fullEnergyMartingaleApprox]
    rw [compactResolventCoreMartingale_sub, compactResolventCoreMartingale_add]
    simp only [Pi.sub_apply, Pi.add_apply]
    change _ =
      (compactResolventCoreMartingale G m hm PF default
          (fullEnergyCoreIndex G m hm U (2 * n)) t ω -
        compactResolventCoreMartingale G m hm PF default
          (fullEnergyCoreIndex G m hm U (2 * n)) 0 ω) +
      (compactResolventCoreMartingale G m hm PF default
          (fullEnergyCoreIndex G m hm W (2 * n)) t ω -
        compactResolventCoreMartingale G m hm PF default
          (fullEnergyCoreIndex G m hm W (2 * n)) 0 ω) + _
    ring
  have hseq : (fun n ↦ (hFsum n).toLp (Fsum n)) =
      fun n ↦ (hFU n).toLp (FU n) + (hFW n).toLp (FW n) + (hD n).toLp (D n) := by
    funext n
    have hFUW : MemLp (FU n + FW n) 2 (PF.P z) := (hFU n).add (hFW n)
    have htotal : MemLp (FU n + FW n + D n) 2 (PF.P z) := hFUW.add (hD n)
    calc
      (hFsum n).toLp (Fsum n) =
          htotal.toLp (FU n + FW n + D n) := by
        apply MemLp.toLp_congr
        exact Filter.Eventually.of_forall fun ω ↦ congrFun (hpoint n) ω
      _ = hFUW.toLp (FU n + FW n) + (hD n).toLp (D n) :=
        MemLp.toLp_add hFUW (hD n)
      _ = (hFU n).toLp (FU n) + (hFW n).toLp (FW n) + (hD n).toLp (D n) := by
        rw [MemLp.toLp_add (hFU n) (hFW n)]
  have hlimit : Tendsto (fun n ↦ (hFsum n).toLp (Fsum n)) atTop
      (𝓝 (hMU.toLp MU + hMW.toLp MW)) := by
    rw [hseq]
    simpa using (hULp.add hWLp).add hDLp
  have heqLp : hMsum.toLp Msum = hMU.toLp MU + hMW.toLp MW :=
    tendsto_nhds_unique hsumLp hlimit
  apply (MemLp.toLp_eq_toLp_iff hMsum (hMU.add hMW)).mp
  rw [MemLp.toLp_add]
  exact heqLp

end ReflectedGMS
