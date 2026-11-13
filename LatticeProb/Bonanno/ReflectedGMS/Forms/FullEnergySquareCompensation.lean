/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.FullEnergySquareCompensation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullFormJumpRateConvergence
import LatticeProb.Bonanno.ReflectedGMS.Forms.JumpOccupationL1Continuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactResolventCoreCovariation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import LatticeProb.Bonanno.ReflectedGMS.Forms.SquareCompensatorLimit

/-! Full-energy diagonal square compensation, obtained by passing the actual
core martingales and their canonical jump occupations to the limit. -/

-- Merged from `ReflectedGMS/Forms/CenteredSquareCompensation.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_CenteredSquareCompensation

/-! Centering a square-integrable martingale at its random initial value
preserves its square compensator. Conditional-expectation pull-out handles the
initial value without any extra boundedness or deterministic-start premise. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace ReflectedGMS

theorem martingale_initial_mul
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P) :
    Martingale (fun t ω ↦ M 0 ω * M t ω) F P := by
  refine ⟨fun t ↦ ((hM.stronglyMeasurable 0).mono (F.mono bot_le)).mul
    (hM.stronglyMeasurable t), fun s t hst ↦ ?_⟩
  have hpull := condExp_mul_of_stronglyMeasurable_left
    ((hM.stronglyMeasurable 0).mono (F.mono (show 0 ≤ s from bot_le)))
    ((h2 0).integrable_mul (h2 t)) (hM.integrable t)
  change P[fun ω ↦ M 0 ω * M t ω | F s] =ᵐ[P]
    (fun ω ↦ M 0 ω * P[M t | F s] ω) at hpull
  filter_upwards [hpull, hM.condExp_ae_eq hst] with ω hp ht
  simpa only [Pi.mul_apply, ht] using hp

theorem martingale_centered_square_compensation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {M A : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P) (h2 : ∀ t, MemLp (M t) 2 P)
    (hN : Martingale (fun t ω ↦ (M t ω) ^ 2 - A t ω) F P) :
    Martingale (fun t ω ↦ (M t ω - M 0 ω) ^ 2 - A t ω) F P := by
  have h0i : Integrable (fun ω ↦ (M 0 ω) ^ 2) P := by
    apply ((h2 0).integrable_mul (h2 0)).congr
    filter_upwards [] with ω
    exact (pow_two _).symm
  have h0 := martingale_const_fun F P ((hM.stronglyMeasurable 0).pow 2) h0i
  have hc := (hN.sub ((martingale_initial_mul hM h2).smul 2)).add h0
  convert hc using 1 <;> funext t ω <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.pow_apply] <;> ring

open ReflectedWalk FullNetworkForm

theorem centered_compactResolventCore_squareCompensation_isMartingale
    {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
    [Countable V] [Nontrivial V] [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default : V) (q : CountableResolventCoreIndex V) (z : V) :
    Martingale (fun t ω ↦
      (compactResolventCoreMartingale G m hm PF default q t ω -
        compactResolventCoreMartingale G m hm PF default q 0 ω) ^ 2 -
      adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) t ω)
      PF.naturalFiltration.rightCont (PF.P z) :=
  martingale_centered_square_compensation
    (compactResolventCoreMartingale_isMartingale h hG hm hmsum default q z)
    (compactResolventCoreMartingale_memLp_two G m hm PF default q (PF.P z))
    (compactResolventCoreSquareCompensation_isMartingale h hG hm hmsum default q z)

end ReflectedGMS

end Merged_CenteredSquareCompensation

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V) (U : hilbertDomain G m) (z : V)

include h hG hm hmsum

theorem fullEnergyCore_jumpOccupation_L1_tendsto (t : ℝ≥0) :
    Tendsto (fun n ↦ eLpNorm
      (adaptedJumpOccupation PF G m (countableResolventCoreFeature G m
        (fullEnergyCoreIndex G m hm U (2 * n))) t -
        adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t)
      1 (PF.P z)) atTop (𝓝 0) := by
  let u := unweight m (valueInclusion G m U)
  let un := fun n ↦ countableResolventCoreFeature G m
    (fullEnergyCoreIndex G m hm U (2 * n))
  let I := fun n ↦ ∫ ω, ‖adaptedJumpOccupation PF G m (un n) t ω -
    adaptedJumpOccupation PF G m u t ω‖ ∂PF.P z
  let R := fun n ↦ ∫ x : V,
    ‖(stateVertexCarreDuChamp G m (un n) (some x)).toReal -
      (stateVertexCarreDuChamp G m u (some x)).toReal‖ ∂vertexSpeedMeasure m
  have hu := hilbertDomain_hasFiniteEnergy G m U
  have hun (n : ℕ) := countableResolventCoreFeature_hasFiniteEnergy G m
    (fullEnergyCoreIndex G m hm U (2 * n))
  have hR : Tendsto R atTop (𝓝 0) := fullEnergyCore_jumpRate_integral_norm_tendsto G m hm U
  have hb (n : ℕ) : I n ≤ ((t : ℝ) / m z) * R n := by
    have hh : m z * I n ≤ (t : ℝ) * R n := by
      simpa only [I, R, un, u, Real.norm_eq_abs] using
        mul_integral_abs_adaptedJumpOccupation_sub_le h hG hm hmsum (hun n) hu t z
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (hm z)).2
    nlinarith
  have hI : Tendsto I atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using hR.const_mul ((t : ℝ) / m z))
      (fun n ↦ integral_nonneg (fun _ ↦ norm_nonneg _)) hb
  have heq (n : ℕ) :
      eLpNorm (adaptedJumpOccupation PF G m (un n) t -
        adaptedJumpOccupation PF G m u t) 1 (PF.P z) = ENNReal.ofReal (I n) := by
    have hi := (integrable_adaptedJumpOccupation h hG hm hmsum (hun n) t z).sub
      (integrable_adaptedJumpOccupation h hG hm hmsum hu t z)
    rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hi]
    rfl
  have ht : Tendsto (fun n ↦ ENNReal.ofReal (I n)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using (ENNReal.continuous_ofReal.tendsto 0).comp hI
  exact ht.congr' (Eventually.of_forall (fun n ↦ (heq n).symm))

theorem fullEnergyMartingaleLimit_squareCompensation_isMartingale :
    Martingale (fun t ω ↦
      (fullEnergyMartingaleLimit G m hm PF default U t ω) ^ 2 -
        adaptedJumpOccupation PF G m (unweight m (valueInclusion G m U)) t ω)
      PF.naturalFiltration.rightCont (PF.P z) := by
  apply squareCompensator_martingale_of_tendsto
    (fun n t ↦ fullEnergyMartingaleApprox_memLp_two h hG hm hmsum default U (PF.P z) n t)
    (fun t ↦ (fullEnergyMartingaleLimit_memLp_and_L2_convergence
      h hG hm hmsum default U z t).1)
    (fun t ↦ (fullEnergyMartingaleLimit_memLp_and_L2_convergence
      h hG hm hmsum default U z t).2)
  · intro n
    exact centered_compactResolventCore_squareCompensation_isMartingale
      h hG hm hmsum default (fullEnergyCoreIndex G m hm U (2 * n)) z
  · intro t
    exact ((stronglyAdapted_fullEnergyMartingaleLimit h hG hm hmsum default U t).pow 2).sub
      ((stronglyAdapted_adaptedJumpOccupation PF G m
        (unweight m (valueInclusion G m U)) t).mono (PF.naturalFiltration.le_rightCont t))
  · intro t
    exact integrable_adaptedJumpOccupation h hG hm hmsum
      (hilbertDomain_hasFiniteEnergy G m U) t z
  · intro t
    exact fullEnergyCore_jumpOccupation_L1_tendsto h hG hm hmsum U z t

end ReflectedGMS
