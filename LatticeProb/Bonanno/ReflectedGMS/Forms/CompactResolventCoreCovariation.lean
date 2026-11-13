/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompactResolventCoreCovariation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreLinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.PolarizedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.SquareCovariationPolarization

/-!
# Predictable covariation on the compact resolvent core

The raw compensated-square martingale on the finite rational resolvent core is
transferred to the compact cadlag realization in the right-continuous natural
filtration.  Polarization then identifies the exact mixed continuous
predictable covariation with the canonical polarized ordinary-edge occupation.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk FullNetworkForm
open SquareCovariationPolarization

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The compact core martingale squared and compensated by its canonical
adapted ordinary-edge jump occupation. -/
noncomputable def compactResolventCoreSquareCompensation
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (PF : ProcessFamily V) (default : V) (q : CountableResolventCoreIndex V) :
    ℝ≥0 → PF.Ω → ℝ :=
  fun t ω ↦ (compactResolventCoreMartingale G m hm PF default q t ω) ^ 2 -
    adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) t ω

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (default : V)
  (q r : CountableResolventCoreIndex V) (z : V)

include h hG hmsum z

theorem stronglyAdapted_compactResolventCoreSquareCompensation :
    StronglyAdapted PF.naturalFiltration.rightCont
      (compactResolventCoreSquareCompensation G m hm PF default q) := by
  intro t
  exact (((compactResolventCoreMartingale_isMartingale
    h hG hm hmsum default q z).stronglyMeasurable t).pow 2).sub
      ((stronglyAdapted_adaptedJumpOccupation PF G m
        (countableResolventCoreFeature G m q) t).mono
          (PF.naturalFiltration.le_rightCont t))

theorem compactResolventCoreSquareCompensation_ae_eq (t : ℝ≥0) :
    compactResolventCoreSquareCompensation G m hm PF default q t =ᵐ[PF.P z]
      fun ω ↦ (rawResolventCoreMartingale PF G m q t ω) ^ 2 -
        adaptedJumpOccupation PF G m
          (countableResolventCoreFeature G m q) t ω := by
  filter_upwards [compactResolventCoreMartingale_ae_eq
    h hG hm hmsum default q z t] with ω hω
  simp only [compactResolventCoreSquareCompensation, hω]

theorem compactResolventCoreSquareCompensation_ae_isCadlag :
    ∀ᵐ ω ∂PF.P z,
      IsCadlag (fun t ↦
        compactResolventCoreSquareCompensation G m hm PF default q t ω) := by
  filter_upwards [compactResolventCoreMartingale_ae_isCadlag
      h hG hm hmsum default q z,
    adaptedJumpOccupation_ae_eq_all_continuous_monotone h hG hm hmsum
      (countableResolventCoreFeature_hasFiniteEnergy G m q) z] with ω hM hA
  have hMsq : IsCadlag (fun t ↦
      compactResolventCoreMartingale G m hm PF default q t ω *
        compactResolventCoreMartingale G m hm PF default q t ω) :=
    hM.continuous_comp₂ hM continuous_mul
  simpa only [compactResolventCoreSquareCompensation, pow_two] using
    hMsq.continuous_comp₂ hA.2.1.isCadlag continuous_sub

/-- The compact compensated square is a genuine martingale in the
right-continuous natural filtration. -/
theorem compactResolventCoreSquareCompensation_isMartingale :
    Martingale (fun t ω ↦
      (compactResolventCoreMartingale G m hm PF default q t ω) ^ 2 -
        adaptedJumpOccupation PF G m
          (countableResolventCoreFeature G m q) t ω)
      PF.naturalFiltration.rightCont (PF.P z) := by
  apply martingale_rightCont_of_ae_eq_of_ae_rightContinuous_of_locallyIntegrablyDominated
    (rawResolventCoreSquareCompensation_isMartingale h hG hm hmsum q z)
    (stronglyAdapted_compactResolventCoreSquareCompensation
      h hG hm hmsum default q z)
    (compactResolventCoreSquareCompensation_ae_eq
      h hG hm hmsum default q z)
    ((compactResolventCoreSquareCompensation_ae_isCadlag
      h hG hm hmsum default q z).mono fun _ hω ↦ hω.isRightContinuous)
    (fun T ω ↦ (countableResolventCoreBound q) ^ 2 *
        (1 + 2 * (T : ℝ)) ^ 2 +
      adaptedJumpOccupation PF G m
        (countableResolventCoreFeature G m q) T ω)
  · intro T
    exact (integrable_const ((countableResolventCoreBound q) ^ 2 *
      (1 + 2 * (T : ℝ)) ^ 2)).add
        (integrable_adaptedJumpOccupation h hG hm hmsum
          (countableResolventCoreFeature_hasFiniteEnergy G m q) T z)
  · intro T
    filter_upwards [adaptedJumpOccupation_ae_eq_all_continuous_monotone
      h hG hm hmsum
      (countableResolventCoreFeature_hasFiniteEnergy G m q) z] with ω hA
    intro t ht
    calc
      ‖compactResolventCoreSquareCompensation G m hm PF default q t ω‖ ≤
          ‖(compactResolventCoreMartingale G m hm PF default q t ω) ^ 2‖ +
            ‖adaptedJumpOccupation PF G m
              (countableResolventCoreFeature G m q) t ω‖ := norm_sub_le _ _
      _ ≤ (countableResolventCoreBound q) ^ 2 *
            (1 + 2 * (T : ℝ)) ^ 2 +
          adaptedJumpOccupation PF G m
            (countableResolventCoreFeature G m q) T ω := by
        apply add_le_add
        · rw [norm_pow]
          have hnorm := norm_compactResolventCoreMartingale_le
            G m hm PF default q t ω
          have ht' : (t : ℝ) ≤ T := ht
          have hB : 0 ≤ countableResolventCoreBound q := by
            unfold countableResolventCoreBound Finsupp.sum
            positivity
          have htime : 1 + 2 * (t : ℝ) ≤ 1 + 2 * (T : ℝ) := by
            linarith
          have hprod : countableResolventCoreBound q * (1 + 2 * (t : ℝ)) ≤
              countableResolventCoreBound q * (1 + 2 * (T : ℝ)) :=
            mul_le_mul_of_nonneg_left htime hB
          calc
            ‖compactResolventCoreMartingale G m hm PF default q t ω‖ ^ 2 ≤
                (countableResolventCoreBound q * (1 + 2 * (T : ℝ))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hnorm.trans hprod) 2
            _ = (countableResolventCoreBound q) ^ 2 *
                (1 + 2 * (T : ℝ)) ^ 2 := by ring
        · have hnonneg : 0 ≤ adaptedJumpOccupation PF G m
              (countableResolventCoreFeature G m q) t ω := by
            unfold adaptedJumpOccupation
            exact ENNReal.toReal_nonneg
          rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
          exact hA.2.2 ht

end ReflectedGMS
