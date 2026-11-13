/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.PolarizedJumpOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.PredictableJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Forms.SquareCovariationPolarization

/-!
# Polarized adapted jump occupation

The mixed ordinary-edge occupation is defined by polarizing the three canonical
adapted diagonal occupations.  It is therefore predictable in both the natural
and right-continuous natural filtrations.  On one full-probability event under
each starting law, it is the literal time integral of the polarized ordinary-
edge carre-du-champ and has continuous locally bounded-variation paths.

This module makes no martingale or stochastic-covariation identification.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm
open SquareCovariationPolarization

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- The real mixed ordinary-edge rate on the compact state type, obtained by
polarizing the canonical diagonal rates. -/
noncomputable def polarizedStateVertexCarreDuChamp
    (G : ConductanceGraph V) (m : V → ℝ) (u v : V → ℝ) (q : Option V) : ℝ :=
  ((stateVertexCarreDuChamp G m (u + v) q).toReal -
      (stateVertexCarreDuChamp G m u q).toReal -
      (stateVertexCarreDuChamp G m v q).toReal) / 2

/-- The canonical mixed adapted occupation, defined by polarizing the three
canonical adapted diagonal occupations. -/
noncomputable def polarizedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u v : V → ℝ) : ℝ≥0 → PF.Ω → ℝ :=
  polarizedCompensator
    (adaptedJumpOccupation PF G m u)
    (adaptedJumpOccupation PF G m v)
    (adaptedJumpOccupation PF G m (u + v))

/-- The canonical mixed occupation remains predictable in the right-continuous
natural filtration. -/
theorem stronglyPredictable_rightCont_polarizedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u v : V → ℝ) :
    IsStronglyPredictable PF.naturalFiltration.rightCont
      (polarizedJumpOccupation PF G m u v) := by
  have hu := stronglyPredictable_rightCont_adaptedJumpOccupation PF G m u
  have hv := stronglyPredictable_rightCont_adaptedJumpOccupation PF G m v
  have huv := stronglyPredictable_rightCont_adaptedJumpOccupation PF G m (u + v)
  unfold IsStronglyPredictable at hu hv huv ⊢
  convert ((huv.sub hu).sub hv).const_smul (1 / 2 : ℝ) using 1 <;>
    funext p <;> rcases p with ⟨t, ω⟩ <;>
    simp only [Function.uncurry_apply_pair, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, polarizedJumpOccupation, polarizedCompensator] <;> ring

@[simp] theorem polarizedJumpOccupation_zero
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u v : V → ℝ) (ω : PF.Ω) :
    polarizedJumpOccupation PF G m u v 0 ω = 0 := by
  simp [polarizedJumpOccupation, polarizedCompensator]

/-- **Integer horizons suffice for pathwise finiteness of the occupation.**

`stationaryJumpOccupation PF G m u t ω` is monotone in `t` (it is a set
lintegral over `Icc 0 t`), so finiteness along the naturals upgrades to
finiteness at every real horizon.  This is the standard `ae_all_iff` bridge:
an a.e. statement can be quantified over a *countable* index set, so the
countable family `n : ℕ` is what one can actually extract from a measure-theoretic
argument, and this lemma converts it to the uncountable `∀ t : ℝ≥0` form that
`CanonicalOccupationLocallyFinite` and
`LocalizedBracketOccupation.adaptedJumpOccupation_ae_integrableOn_and_eq_integral_of_ae_lt_top`
consume.  It is unconditional: no walk, energy, or summability hypothesis. -/
theorem stationaryJumpOccupation_lt_top_all_of_nat
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (ω : PF.Ω)
    (hfinite : ∀ n : ℕ,
      stationaryJumpOccupation PF G m u (n : ℝ≥0) ω < ∞) :
    ∀ t : ℝ≥0, stationaryJumpOccupation PF G m u t ω < ∞ := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t : ℝ)
  have htn : t ≤ (n : ℝ≥0) := by
    rw [← NNReal.coe_le_coe]
    exact hn.le
  exact (lintegral_mono_set (Icc_subset_Icc_right (by exact_mod_cast htn))).trans_lt
    (hfinite n)

private theorem integrableOn_stateVertexCarreDuChamp_toReal
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω)
    (hreg : RightRegularAt PF.X ω)
    (hfinite : stationaryJumpOccupation PF G m u t ω < ∞) :
    IntegrableOn (fun r : ℝ ↦
      (stateVertexCarreDuChamp G m u
        (PF.X (Real.toNNReal r) ω)).toReal) (Icc 0 (t : ℝ)) := by
  have hstate : Measurable (fun r : ℝ ↦ PF.X (Real.toNNReal r) ω) := by
    have hd : Measurable (fun r : ℝ ↦
        dyadicLimit PF.X (Real.toNNReal r) ω) :=
      measurable_section (measurable_uncurry_dyadicLimit PF.measurable_X) ω
    convert hd using 1
    funext r
    exact (dyadicLimit_eq_of_rightRegular hreg (Real.toNNReal r)).symm
  have hgamma : Measurable (fun r : ℝ ↦
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) :=
    (measurable_of_countable (stateVertexCarreDuChamp G m u)).comp hstate
  apply integrable_toReal_of_lintegral_ne_top hgamma.aemeasurable.restrict
  have heq : (∫⁻ r : ℝ in Icc 0 (t : ℝ),
      stateVertexCarreDuChamp G m u (PF.X (Real.toNNReal r) ω)) =
      stationaryJumpOccupation PF G m u t ω := by
    unfold stationaryJumpOccupation
    apply lintegral_congr
    intro r
    simp only [dyadicVertexCarreDuChamp,
      dyadicLimit_eq_of_rightRegular hreg]
  rw [heq]
  exact hfinite.ne

end ReflectedGMS
