import Mathlib
import LatticeProb.Prob.BrownianTimeReversal
import LatticeProb.Prob.BrownianRestartPath
import LatticeProb.Prob.UpcrossIntervals

/-!
# Duality of Lebesgue starting points on path space

`LatticeProb.lintegral_lebesgue_drift_rev` is stated for functionals of the product sigma-algebra
on `ℝ≥0 → ℝ`.  The functionals met in the study of up-crossings (hitting times, pieces of paths)
are measurable on `C(ℝ≥0, ℝ)` only.

* `LatticeProb.exists_pi_extension`: a measurable functional on `C(ℝ≥0, ℝ)` is the restriction of a
  measurable functional on `ℝ≥0 → ℝ`;
* `LatticeProb.affinePath x m w`: the path `s ↦ x + w s + m s`; `LatticeProb.revStopC c t w`: the
  path stopped at `t`, reversed and reflected at the level `c` (as an element of `C(ℝ≥0, ℝ)`);
* `LatticeProb.lintegral_lebesgue_drift_rev_path`: for a Brownian motion `B` with continuous paths,
  `∫ dx E Φ(stop_t (x + B + m ·)) = ∫ dx E Φ(rev_{c,t} (x + B + m ·))` for measurable
  `Φ : C(ℝ≥0, ℝ) → ℝ≥0∞`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- A measurable functional on `C(ℝ≥0, ℝ)` extends to a measurable functional on `ℝ≥0 → ℝ`. -/
theorem exists_pi_extension {Φ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∃ Φ' : (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable Φ' ∧ ∀ v : C(ℝ≥0, ℝ), Φ' (v : ℝ≥0 → ℝ) = Φ v := by
  refine Measurable.ennreal_induction
    (motive := fun Φ => ∃ Φ' : (ℝ≥0 → ℝ) → ℝ≥0∞, Measurable Φ' ∧
      ∀ v : C(ℝ≥0, ℝ), Φ' (v : ℝ≥0 → ℝ) = Φ v) ?_ ?_ ?_ hΦ
  · intro c s hs
    obtain ⟨A, hA, hAs⟩ := exists_measurableSet_coe_preimage hs
    refine ⟨A.indicator fun _ => c, measurable_const.indicator hA, fun v => ?_⟩
    subst hAs
    rfl
  · rintro f g - hf hg ⟨f', hf', hf'v⟩ ⟨g', hg', hg'v⟩
    exact ⟨f' + g', hf'.add hg', fun v => by simp [hf'v, hg'v]⟩
  · intro f hf hmono h
    choose f' hf'm hf'v using h
    exact ⟨fun w => ⨆ n, f' n w, Measurable.iSup hf'm, fun v => by simp [hf'v]⟩

/-- The path `s ↦ x + w s + m s`. -/
def affinePath (x m : ℝ) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun s := x + w s + m * (s : ℝ)
  continuous_toFun :=
    (continuous_const.add w.continuous).add (continuous_const.mul NNReal.continuous_coe)

@[simp] lemma affinePath_apply (x m : ℝ) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    affinePath x m w s = x + w s + m * (s : ℝ) := rfl

/-- The path stopped at `t`, reversed and reflected at the level `c`, as an element of
`C(ℝ≥0, ℝ)`. -/
def revStopC (c : ℝ) (t : ℝ≥0) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) where
  toFun := revStop c t (w : ℝ≥0 → ℝ)
  continuous_toFun :=
    continuous_const.sub (w.continuous.comp (continuous_const.sub (continuous_id.min continuous_const)))

@[simp] lemma revStopC_apply (c : ℝ) (t : ℝ≥0) (w : C(ℝ≥0, ℝ)) (s : ℝ≥0) :
    revStopC c t w s = c - w (t - min s t) := rfl

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Duality of Lebesgue starting points on path space.** -/
theorem lintegral_lebesgue_drift_rev_path (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (m b : ℝ) (t : ℝ≥0)
    {Φ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x : ℝ, ∫⁻ ω, Φ (stopAt (t : ℝ≥0∞) (affinePath x m (pathMap B hcont ω))) ∂P
      = ∫⁻ x : ℝ, ∫⁻ ω, Φ (revStopC b t (affinePath x m (pathMap B hcont ω))) ∂P := by
  obtain ⟨Φ', hΦ', hv⟩ := exists_pi_extension hΦ
  have key := lintegral_lebesgue_drift_rev hB hm m b t Φ' hΦ'
  have e1 : ∀ x ω, Φ (stopAt (t : ℝ≥0∞) (affinePath x m (pathMap B hcont ω))) =
      Φ' (fun s => x + B (min s t) ω + m * ((min s t : ℝ≥0) : ℝ)) := fun x ω =>
    (hv _).symm.trans (congrArg Φ' (funext fun s => by simp only [stopAt_coe, affinePath_apply, pathMap_apply]))
  have e2 : ∀ x ω, Φ (revStopC b t (affinePath x m (pathMap B hcont ω))) =
      Φ' (fun s => b - (x + B (t - min s t) ω + m * ((t - min s t : ℝ≥0) : ℝ))) := fun x ω =>
    (hv _).symm.trans (congrArg Φ' (funext fun s => by simp))
  simp only [e1, e2]
  exact key

end LatticeProb
