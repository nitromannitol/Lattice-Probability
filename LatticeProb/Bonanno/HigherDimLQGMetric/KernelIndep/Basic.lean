/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLQGMetric.KernelIndep.Basic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLQGMetric.Frozen.DistExp
import LatticeProb.Bonanno.HigherDimLFPP.Exist.Exponent
import LatticeProb.Bonanno.HigherDimLFPP.Field.LawTransfer

/-!
# Kernel-specific LFPP exponents and Gaussian law transfer

The exponent predicate is the universe-zero specialization of HigherDimLFPP's existence theorem.
The law-transfer lemma records that a centered white-noise process is determined by its Gram matrix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN IsWhiteNoise IsBandVersion IsLFPPKernel IsLFPPExponent)

/-- The LFPP exponent for one kernel, uniformly over all white-noise realizations. -/
def IsExponentFor (d : ℕ) (κ : Rd d → ℝ) (ζ lam : ℝ) : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : WN d → Ω → ℝ),
    IsWhiteNoise P W →
      ∀ H : ℝ → Rd d → Ω → ℝ,
        (∀ ε ∈ Ioo (0 : ℝ) 1, IsBandVersion P W κ ε 1 (H ε)) →
          IsLFPPExponent H P ζ lam

/-- The exponent supplied by HigherDimLFPP works on every universe-zero realization. -/
theorem exists_isExponentFor {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ}
    (hκ : IsLFPPKernel κ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ lam : ℝ, IsExponentFor d κ ζ lam := by
  obtain ⟨lam, hlam⟩ := HigherDimLFPP.exponent_exists.{0} d hd κ hκ ζ hζ
  exact ⟨lam, fun Ω _ P W hW H hH => hlam Ω P W hW H hH⟩

/-- White-noise processes indexed by families with equal Gram matrices have equal laws. -/
theorem map_eq_of_inner_eq {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {W : WN d → Ω → ℝ} {W' : WN d → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {T : Type*}
    (F F' : T → WN d)
    (hF : ∀ s t, inner ℝ (F s) (F t) = inner ℝ (F' s) (F' t)) :
    P.map (fun ω t => W (F t) ω) = P'.map (fun ω t => W' (F' t) ω) := by
  have := hW.isProbabilityMeasure
  have := hW'.isProbabilityMeasure
  apply LQGMetric.WhiteNoise.map_eq_of_forall_finset'
    (measurable_pi_iff.2 fun t => hW.measurable (F t)).aemeasurable
    (measurable_pi_iff.2 fun t => hW'.measurable (F' t)).aemeasurable
  intro I
  exact QuantumZipper.WedgeRes.map_eq_of_gaussian_vec
    (ι := I) (U := fun i => W (F i)) (V := fun i => W' (F' i))
    (hW.hasGaussianLaw_fintype fun i : I => F i)
    (hW'.hasGaussianLaw_fintype fun i : I => F' i)
    (fun i => hW.measurable _) (fun i => hW'.measurable _)
    (fun i => hW.memLp _ 2 ENNReal.ofNat_ne_top)
    (fun i => hW'.memLp _ 2 ENNReal.ofNat_ne_top)
    (fun i => hW.integral_eq_zero _) (fun i => hW'.integral_eq_zero _)
    (fun i j => by rw [hW.cov_eq, hW'.cov_eq, hF])

end HigherDimLQGMetric
