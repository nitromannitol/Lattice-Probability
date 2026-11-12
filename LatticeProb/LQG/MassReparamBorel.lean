import LatticeProb.Prob.KernelCurveImage
import LatticeProb.LQG.AreaParametrizedCurve
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# The mass-parametrized reparametrization is a Borel function of the measure and the curve

Let `μ` be a measure on a metric space `E` and `L : ℝ → E` a curve. The *signed mass clock* of `(μ, L)` is
`massClock μ L u = μ (L [0, u])` for `u ≥ 0` and `-μ (L [u, 0])` for `u < 0`. When `η = L ∘ v` is parametrized by
`μ`-mass for an increasing homeomorphism `v` of `ℝ` with `v 0 = 0` (for space-filling SLE parametrized by `γ`-LQG
area, `L` is the curve parametrized by Lebesgue measure), the clock is `v⁻¹`
(`LatticeProb.LQG.orderIso_symm_eq_measure_image`). We define the inverse clock by a formula that makes sense for
every pair `(μ, L)`,
`massClockInv μ L t = inf {q ∈ ℚ : t < massClock μ L q}` (an infimum in `EReal`, then `toReal`),
and the *mass reparametrization* `massReparam μ L = L ∘ massClockInv μ L`.

## Main results

* `massClockInv_eq_of_massParam`, `massReparam_eq_of_massParam`: if `η = L ∘ v` is parametrized by `μ`-mass, then
  `massClockInv μ L = v` and `massReparam μ L = η`. So the mass-parametrized curve is recovered from `(μ, L)` by one
  fixed formula.
* `measurable_massClockInv`, `measurable_massReparam`: for a measurable family of measures `μ ω` that are finite on
  compact sets and a family of continuous curves `L ω` measurable at each time, `ω ↦ massClockInv (μ ω) (L ω) t` and
  `ω ↦ massReparam (μ ω) (L ω) t` are measurable for every `t`.

The measurability rests on `LatticeProb.measurable_measure_image_Icc` (the mass of the image of an interval is
measurable) and on the fact that the infimum of countably many measurable `EReal`-valued maps is measurable.
-/

open MeasureTheory Set

namespace LatticeProb.LQG

section Pathwise

variable {E : Type*} [MeasurableSpace E]

/-- The signed mass clock of a curve `L` for a measure `μ`: `μ (L [0, u])` for `u ≥ 0`, and `-μ (L [u, 0])` for
`u < 0`. -/
noncomputable def massClock (μ : Measure E) (L : ℝ → E) (u : ℝ) : ℝ :=
  if 0 ≤ u then (μ (L '' Icc 0 u)).toReal else -(μ (L '' Icc u 0)).toReal

/-- The inverse of the signed mass clock, given by a formula valid for every `(μ, L)`: the infimum (in `EReal`) of
the rationals `q` with `t < massClock μ L q`, converted to a real number. -/
noncomputable def massClockInv (μ : Measure E) (L : ℝ → E) (t : ℝ) : ℝ :=
  (⨅ q : ℚ, if t < massClock μ L q then ((q : ℝ) : EReal) else ⊤).toReal

/-- The mass reparametrization `L ∘ massClockInv μ L` of a curve `L` by the mass of `μ`. -/
noncomputable def massReparam (μ : Measure E) (L : ℝ → E) (t : ℝ) : E :=
  L (massClockInv μ L t)

/-- A real number is the infimum, in `EReal`, of the rationals strictly above it. -/
theorem iInf_rat_ite_lt_eq (a : ℝ) :
    (⨅ q : ℚ, if a < (q : ℝ) then ((q : ℝ) : EReal) else ⊤) = (a : EReal) := by
  apply le_antisymm
  · apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    obtain ⟨x, hax, hxc⟩ := EReal.lt_iff_exists_real_btwn.mp hc
    obtain ⟨q, haq, hqx⟩ := exists_rat_btwn (EReal.coe_lt_coe_iff.mp hax)
    calc (⨅ q : ℚ, if a < (q : ℝ) then ((q : ℝ) : EReal) else ⊤)
        ≤ (if a < (q : ℝ) then ((q : ℝ) : EReal) else ⊤) := iInf_le _ q
      _ = ((q : ℝ) : EReal) := by simp only [haq, ↓reduceIte]
      _ ≤ c := (lt_trans (EReal.coe_lt_coe_iff.mpr hqx) hxc).le
  · refine le_iInf fun q => ?_
    split_ifs with h
    · exact EReal.coe_le_coe_iff.mpr h.le
    · exact le_top

/-- If `η = L ∘ v` is parametrized by `μ`-mass, then the signed mass clock of `L` is `v⁻¹`. -/
theorem massClock_eq_symm_of_massParam (μ : Measure E) (L η : ℝ → E) (v : ℝ ≃o ℝ) (hv : v 0 = 0)
    (hη : ∀ t, η t = L (v t)) (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (u : ℝ) : massClock μ L u = v.symm u :=
  (orderIso_symm_eq_measure_image μ L η v hv hη harea u).symm

/-- **The inverse mass clock is the clock.** If `η = L ∘ v` is parametrized by `μ`-mass, with `v` an increasing
homeomorphism of `ℝ` fixing `0`, then `massClockInv μ L = v`. -/
theorem massClockInv_eq_of_massParam (μ : Measure E) (L η : ℝ → E) (v : ℝ ≃o ℝ) (hv : v 0 = 0)
    (hη : ∀ t, η t = L (v t)) (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (t : ℝ) : massClockInv μ L t = v t := by
  have hiff : ∀ q : ℚ, (t < massClock μ L q) ↔ (v t < (q : ℝ)) := fun q => by
    rw [massClock_eq_symm_of_massParam μ L η v hv hη harea, ← v.lt_iff_lt, v.apply_symm_apply]
  unfold massClockInv
  simp_rw [hiff]
  rw [iInf_rat_ite_lt_eq, EReal.toReal_coe]

/-- **The mass-parametrized curve is the mass reparametrization.** If `η = L ∘ v` is parametrized by `μ`-mass, with
`v` an increasing homeomorphism of `ℝ` fixing `0`, then `massReparam μ L = η`. -/
theorem massReparam_eq_of_massParam (μ : Measure E) (L η : ℝ → E) (v : ℝ ≃o ℝ) (hv : v 0 = 0)
    (hη : ∀ t, η t = L (v t)) (harea : ∀ s t : ℝ, s ≤ t → μ (η '' Icc s t) = ENNReal.ofReal (t - s))
    (t : ℝ) : massReparam μ L t = η t := by
  rw [massReparam, massClockInv_eq_of_massParam μ L η v hv hη harea, hη]

end Pathwise

section Measurability

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [SigmaCompactSpace E]

/-- The signed mass clock is measurable in the parameter, for a measurable family of measures finite on compact
sets and a family of continuous curves measurable at each time. -/
theorem measurable_massClock {μ : Ω → Measure E} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → E} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) (u : ℝ) :
    Measurable fun ω => massClock (μ ω) (L ω) u := by
  unfold massClock
  by_cases hu : 0 ≤ u
  · simp only [hu, ↓reduceIte]
    exact (measurable_measure_image_Icc hμ hfin hLc hLm hu).ennreal_toReal
  · simp only [hu, ↓reduceIte]
    exact (measurable_measure_image_Icc hμ hfin hLc hLm (le_of_not_ge hu)).ennreal_toReal.neg

/-- **The inverse mass clock is measurable** in the parameter. -/
theorem measurable_massClockInv {μ : Ω → Measure E} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → E} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) (t : ℝ) :
    Measurable fun ω => massClockInv (μ ω) (L ω) t := by
  unfold massClockInv
  refine Measurable.ereal_toReal (Measurable.iInf fun q => ?_)
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_massClock hμ hfin hLc hLm q))
    measurable_const measurable_const

/-- **The mass reparametrization is measurable** in the parameter: for a measurable family of measures finite on
compact sets and a family of continuous curves measurable at each time, `ω ↦ massReparam (μ ω) (L ω) t` is
measurable for every `t`. -/
theorem measurable_massReparam {μ : Ω → Measure E} (hμ : Measurable μ)
    (hfin : ∀ ω, IsFiniteMeasureOnCompacts (μ ω)) {L : Ω → ℝ → E} (hLc : ∀ ω, Continuous (L ω))
    (hLm : ∀ t, Measurable fun ω => L ω t) (t : ℝ) :
    Measurable fun ω => massReparam (μ ω) (L ω) t := by
  have hjoint : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => L ω s) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hLc ω) hLm
  exact hjoint.comp ((measurable_massClockInv hμ hfin hLc hLm t).prodMk measurable_id)

end Measurability

end LatticeProb.LQG
