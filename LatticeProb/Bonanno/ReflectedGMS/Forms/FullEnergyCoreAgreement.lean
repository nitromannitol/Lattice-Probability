/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergyCoreAgreement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingaleLinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareAlgebra

/-!
# Agreement of the full-energy martingale with the resolvent core

On an actual countable-resolvent-core vector, the canonical full-domain
martingale is the centered core Dynkin martingale.  Consequently its
zero-energy remainder is exactly the bounded occupation of the core drift.
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

private theorem countableResolventCoreVector_sub_core
    (q r : CountableResolventCoreIndex V) :
    countableResolventCoreVector G m (q - r) =
      countableResolventCoreVector G m q - countableResolventCoreVector G m r := by
  unfold countableResolventCoreVector
  rw [show countableResolventCoreInput G m (q - r) =
      countableResolventCoreInput G m q - countableResolventCoreInput G m r by
    exact map_sub (countableResolventCoreInputAddHom G m) q r]
  exact map_sub (oneResolventLift G m) _ _

/-- On a vector already in the countable resolvent core, the full-energy
martingale agrees at each fixed time with the original centered core
martingale. -/
theorem fullEnergyMartingaleLimit_countableResolventCore_ae
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (q : CountableResolventCoreIndex V) (t : ℝ≥0) :
    fullEnergyMartingaleLimit G m hm PF default
        (countableResolventCoreVector G m q) t =ᵐ[PF.P z]
      fun ω ↦ compactResolventCoreMartingale G m hm PF default q t ω -
        compactResolventCoreMartingale G m hm PF default q 0 ω := by
  let U : hilbertDomain G m := countableResolventCoreVector G m q
  let F : ℕ → PF.Ω → ℝ := fun n ↦
    fullEnergyMartingaleApprox G m hm PF default U n t
  let M : PF.Ω → ℝ := fullEnergyMartingaleLimit G m hm PF default U t
  let C : PF.Ω → ℝ := fun ω ↦
    compactResolventCoreMartingale G m hm PF default q t ω -
      compactResolventCoreMartingale G m hm PF default q 0 ω
  let r : ℕ → CountableResolventCoreIndex V := fun n ↦
    fullEnergyCoreIndex G m hm U (2 * n) - q
  let D : ℕ → PF.Ω → ℝ := fun n ω ↦
    compactResolventCoreMartingale G m hm PF default (r n) t ω -
      compactResolventCoreMartingale G m hm PF default (r n) 0 ω
  have hF (n : ℕ) : MemLp (F n) 2 (PF.P z) :=
    fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U (PF.P z) n t
  have hM : MemLp M 2 (PF.P z) :=
    (fullEnergyMartingaleLimit_memLp_and_L2_convergence
      h hG hm hmsum default U z t).1
  have hC : MemLp C 2 (PF.P z) :=
    (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z) 0)
  have hD (n : ℕ) : MemLp (D n) 2 (PF.P z) :=
    (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) t).sub
      (compactResolventCoreMartingale_memLp_two G m hm PF default (r n) (PF.P z) 0)
  have hrvector (n : ℕ) :
      countableResolventCoreVector G m (r n) =
        countableResolventCoreVector G m
          (fullEnergyCoreIndex G m hm U (2 * n)) - U := by
    dsimp only [r]
    rw [countableResolventCoreVector_sub_core]
  have hrnorm (n : ℕ) : ‖countableResolventCoreVector G m (r n)‖ ≤
      (1 / 2 : ℝ) ^ (2 * n) := by
    rw [hrvector]
    exact fullEnergyCoreIndex_bound G m hm U (2 * n)
  have hDnorm : Tendsto (fun n ↦ ‖(hD n).toLp (D n)‖) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦
        (countableResolventCore_centeredMartingale_toLp_norm_le
          h hG hm hmsum default z (r n) t).trans
            (mul_le_mul_of_nonneg_left (hrnorm n) (Real.sqrt_nonneg _)))
    convert (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (1 / 2) ^ 2)
        (by norm_num : (1 / 2 : ℝ) ^ 2 < 1))) using 1
    · ext n
      rw [← pow_mul]
    · ring
  have hDLp : Tendsto (fun n ↦ (hD n).toLp (D n)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hDnorm
  have hFLp : Tendsto (fun n ↦ (hF n).toLp (F n)) atTop
      (𝓝 (hM.toLp M)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' F hF M hM).2
      (fullEnergyMartingaleLimit_memLp_and_L2_convergence
        h hG hm hmsum default U z t).2
  have hpoint (n : ℕ) : F n = C + D n := by
    funext ω
    dsimp only [F, C, D, r, fullEnergyMartingaleApprox]
    rw [compactResolventCoreMartingale_sub]
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hseq : (fun n ↦ (hF n).toLp (F n)) =
      fun n ↦ hC.toLp C + (hD n).toLp (D n) := by
    funext n
    have hCD : MemLp (C + D n) 2 (PF.P z) := hC.add (hD n)
    calc
      (hF n).toLp (F n) = hCD.toLp (C + D n) := by
        apply MemLp.toLp_congr
        exact Eventually.of_forall fun ω ↦ congrFun (hpoint n) ω
      _ = hC.toLp C + (hD n).toLp (D n) := MemLp.toLp_add hC (hD n)
  have hClimit : Tendsto (fun n ↦ (hF n).toLp (F n)) atTop
      (𝓝 (hC.toLp C)) := by
    rw [hseq]
    simpa using tendsto_const_nhds.add hDLp
  have heqLp : hM.toLp M = hC.toLp C := tendsto_nhds_unique hFLp hClimit
  change M =ᵐ[PF.P z] C
  exact (MemLp.toLp_eq_toLp_iff hM hC).mp heqLp

/-- The zero-energy remainder of a resolvent-core coordinate is exactly its
bounded state-occupation drift, under every fixed-vertex starting law. -/
theorem countableResolventCore_fullEnergyRemainder_ae
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V)
    (q : CountableResolventCoreIndex V) (t : ℝ≥0) :
    (fun ω ↦
      rawResolventCorePotential G m q (PF.X t ω) -
        rawResolventCorePotential G m q (PF.X 0 ω) -
        fullEnergyMartingaleLimit G m hm PF default
          (countableResolventCoreVector G m q) t ω) =ᵐ[PF.P z]
      boundedStateOccupationVersion PF (resolventCoreDrift G m q) t := by
  filter_upwards
    [fullEnergyMartingaleLimit_countableResolventCore_ae
      h hG hm hmsum default z q t,
     compactResolventCoreMartingale_ae_eq
      h hG hm hmsum default q z t,
     compactResolventCoreMartingale_ae_eq
      h hG hm hmsum default q z 0] with ω hfull ht h0
  rw [hfull, ht, h0,
    rawResolventCoreMartingale_eq_potential_sub_occupation PF G m hm q t ω,
    rawResolventCoreMartingale_eq_potential_sub_occupation PF G m hm q 0 ω]
  have hocc0 : boundedStateOccupationVersion PF (resolventCoreDrift G m q) 0 ω = 0 := by
    unfold boundedStateOccupationVersion
    simp
  rw [hocc0]
  ring

end ReflectedGMS
