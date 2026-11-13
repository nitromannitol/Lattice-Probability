/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.IGLaw.OBase at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.IGLaw.CurveLaws
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling

/-!
# Elementary curve and bundle facts

The small facts from `IGLaw/FirstHit.lean` are proved against
the mating-of-trees bundle, whose `igMap` carries the positive-radius clause as its second conjunct.
The statements here use the current `igMap` clause.

* `rotCurve θ c = e^{iθ} c`, its measurability, `affineReroot_zero_one_of_firstHit` (a rotation re-rooting is a
  spatial rotation once the root time is `0`), full turns (`cexp_two_pi_int`, `rotCurve_two_pi_int`,
  `igPullback_full_turn`), `igPullback_one_zero`;
* `time_shift_eq_zero_of_transient`, `period_pos_of_uniform`;
* bundle facts: `IsMatingOfTreesCoupling.ae_rootTime_zero` (`firstHit ηL 0 = 0` a.s.) and
  `IsMatingOfTreesCoupling.indepFun_ηL_coneData` (`ηL` is independent of the complete cone tuple).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace MatedCRTHarmonic.IGLaw

open MatedCRTHarmonic.MatedCRT

/-- Counterclockwise spatial rotation of a continuous curve: `t ↦ e^{iθ} c(t)`. -/
def rotCurve (θ : ℝ) (c : C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => Complex.exp (θ * Complex.I) * c t, by fun_prop⟩

lemma rotCurve_eq_comp (θ : ℝ) :
    rotCurve θ = (ContinuousMap.comp
      (⟨fun z => Complex.exp (θ * Complex.I) * z, by fun_prop⟩ : C(ℂ, ℂ))) := by
  funext c
  rfl

lemma measurable_rotCurve (θ : ℝ) : Measurable (rotCurve θ) := by
  rw [rotCurve_eq_comp]
  exact (ContinuousMap.continuous_postcomp _).measurable

/-- The IG coordinate map at the identity. -/
theorem igPullback_one_zero (γ : ℝ) (H : ℝ → ℂ → ℝ) : igPullback γ 0 1 0 H = H := by
  funext ρ w
  simp [igPullback]

/-- Once the root time is `0`, the rotation re-rooting is the spatial rotation by `−θ`. -/
theorem affineReroot_zero_one_of_firstHit (c : C(ℝ, ℂ)) (θ : ℝ) (hτ : firstHit c 0 = 0) :
    affineReroot 0 1 θ c = rotCurve (-θ) c := by
  ext t
  simp [affineReroot, rotCurve, hτ, Complex.exp_neg]

/-- A full turn is the identity of the plane. -/
theorem cexp_two_pi_int (k : ℤ) :
    Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
  have he : (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I k

theorem rotCurve_two_pi_int (c : C(ℝ, ℂ)) (k : ℤ) : rotCurve (2 * Real.pi * (k : ℝ)) c = c := by
  ext t
  change Complex.exp (((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) * Complex.I) * c t = c t
  rw [cexp_two_pi_int]
  simp

/-- The identity-centred IG pullback at a full turn is a shift by an integer IG period. -/
theorem igPullback_full_turn (γ : ℝ) (H : ℝ → ℂ → ℝ) (k : ℤ) :
    igPullback γ 0 1 (2 * Real.pi * (k : ℝ)) H =
      fun ρ w => H ρ w - (2 * Real.pi * igChi γ) * (k : ℝ) := by
  funext ρ w
  simp only [igPullback]
  rw [cexp_two_pi_int k]
  simp
  ring

/-- A transient continuous curve invariant under a fixed time shift has zero shift. -/
theorem time_shift_eq_zero_of_transient (c : C(ℝ, ℂ)) (τ : ℝ)
    (htr : Tendsto c (cocompact ℝ) (cocompact ℂ)) (hshift : ∀ t, c t = c (τ + t)) : τ = 0 := by
  by_contra hτ
  have hn : ∀ n : ℕ, c (n * τ) = c 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have h := hshift (k * τ)
      have hk : τ + (k : ℝ) * τ = ((k + 1 : ℕ) : ℝ) * τ := by
        push_cast
        ring
      rw [hk] at h
      rw [← h, ih]
  have hK : ({c 0}ᶜ : Set ℂ) ∈ cocompact ℂ := isCompact_singleton.compl_mem_cocompact
  obtain ⟨C, hC, hCsub⟩ := Filter.mem_cocompact.1 (htr hK)
  obtain ⟨M, hM⟩ := hC.isBounded.exists_norm_le
  have hτpos : 0 < |τ| := abs_pos.2 hτ
  obtain ⟨n, hn'⟩ := exists_nat_gt (M / |τ|)
  have hmem : (n : ℝ) * τ ∈ C := by
    by_contra hnot
    have h1 := hCsub hnot
    simp [hn n] at h1
  have h2 := hM _ hmem
  rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast] at h2
  rw [div_lt_iff₀ hτpos] at hn'
  linarith

/-- A uniform law on `[0, r)` forces `r > 0` (the conditioned measure of an empty interval vanishes). -/
theorem period_pos_of_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {U : Ω → ℝ} {r : ℝ} (hU : P.map U = volume[|Ico (0 : ℝ) r]) :
    0 < r := by
  have hmapne : P.map U ≠ 0 := by
    by_cases hUm : AEMeasurable U P
    · rw [Measure.map_ne_zero_iff hUm]
      exact IsProbabilityMeasure.ne_zero P
    · rw [Measure.map_of_not_aemeasurable_of_ne_zero hUm (IsProbabilityMeasure.ne_zero P)]
      exact Measure.dirac_ne_zero
  have hcondne : (volume[|Ico (0 : ℝ) r] : Measure ℝ) ≠ 0 := by
    rw [← hU]
    exact hmapne
  by_contra hnot
  have hset : Ico (0 : ℝ) r = ∅ := Ico_eq_empty_of_le (le_of_not_gt hnot)
  rw [hset] at hcondne
  simp [ProbabilityTheory.cond] at hcondne

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRTHarmonic.MatedCRT.Field}
  {B B' B₀ B₀' : NNReal → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRTHarmonic.MatedCRT.Path2}

/-- **The root time of `ηL` is `0`** almost surely (the identity coordinate clause and transience). -/
theorem IsMatingOfTreesCoupling.ae_rootTime_zero
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, firstHit (ηL ω) 0 = 0 := by
  obtain ⟨Φ, -, -, hroot, hcc, -⟩ := hC.igMap
  filter_upwards [hroot, hcc 0 1 0 one_pos, hC.spaceFilling] with ω hr hc hs
  rw [igPullback_one_zero] at hc
  have hfix : ∀ t, ηL ω t = ηL ω (firstHit (ηL ω) 0 + t) := by
    intro t
    have h := congrArg (fun c : C(ℝ, ℂ) => c t) (hr.trans hc)
    simpa [affineReroot] using h
  exact time_shift_eq_zero_of_transient (ηL ω) _ hs.2.1 hfix

/-- **`ηL` is independent of the complete cone tuple** `(X, B, B', X₀, B₀, B₀')` (from `igMap`'s factorization and
`indep_curve`). -/
theorem IsMatingOfTreesCoupling.indepFun_ηL_coneData
    (hC : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    IndepFun ηL (fun ω => (X ω, (fun t => B t ω), (fun t => B' t ω), X₀ ω,
      (fun t => B₀ t ω), (fun t => B₀' t ω))) P := by
  obtain ⟨Φ, hΦ, -, hfactor, -⟩ := hC.igMap
  exact indepFun_igCurve_of_draft_factor hC.indep_curve hΦ hfactor

end Bundle

end MatedCRTHarmonic.IGLaw
