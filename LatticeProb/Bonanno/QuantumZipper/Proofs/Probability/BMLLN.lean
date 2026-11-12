/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.BMLLN at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
`BMLLN.ae_tendsto_div_atTop`: for a Brownian motion `B` (mathlib's `IsBrownianReal`, a.s.
continuous paths), almost surely `B_t / t → 0` as `t → ∞` along all real times.

Source: J.-F. Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus* (Springer GTM 274,
2016), Exercise 2.25 (time inversion, p. 38 printed / PDF p. 51): `W_t = t B_{1/t}` is a
pre-Brownian motion (mathlib: `IsPreBrownianReal.inv`), hence `W` has the law of `B` on the
rationals, so `W_q → 0` as `q ↓ 0` along the rationals a.s.; continuity of `B` on `(0,∞)` then
gives `B_t / t → 0` along all real `t → ∞`. We follow that route:

1. `map_ratPath_eq`: two pre-Brownian motions have the same law on `ℚ → ℝ`
   (uniqueness of projective limits, `IsProjectiveLimit.unique`).
2. `ratSmall`: the measurable event "`f q → 0` as `q ↓ 0`, `q ∈ ℚ`".
3. The deterministic step `tendsto_div_of_ratSmall`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open ProbabilityTheory.BrownianReal

namespace QuantumZipper

namespace BMLLN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The path of a process restricted to the rationals (negative rationals are sent to `0`). -/
def ratPath (Y : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℚ → ℝ := fun r => Y (r : ℝ).toNNReal ω

theorem aemeasurable_ratPath {Y : ℝ≥0 → Ω → ℝ} (hY : IsPreBrownianReal Y P) :
    AEMeasurable (ratPath Y) P :=
  AEMeasurable.of_eval fun q => hY.aemeasurable _

/-- The finite-dimensional marginals of `ratPath Y` only depend on the law of a pre-Brownian `Y`. -/
theorem map_restrict_ratPath {Y : ℝ≥0 → Ω → ℝ} (hY : IsPreBrownianReal Y P) (J : Finset ℚ) :
    (P.map (ratPath Y)).map J.restrict =
      (projectiveFamily (J.image fun q : ℚ => (q : ℝ).toNNReal)).map
        (fun f (j : J) => f ⟨((j : ℚ) : ℝ).toNNReal, Finset.mem_image_of_mem _ j.2⟩) := by
  classical
  set I : Finset ℝ≥0 := J.image fun q : ℚ => (q : ℝ).toNNReal
  set e : (I → ℝ) → (J → ℝ) := fun f j => f ⟨((j : ℚ) : ℝ).toNNReal, Finset.mem_image_of_mem _ j.2⟩
  have he : Measurable e := Measurable.of_eval fun j => measurable_pi_apply _
  have h1 := (hY.hasLaw I)
  rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable
      (aemeasurable_ratPath hY), ← h1.map_eq, AEMeasurable.map_map_of_aemeasurable
      he.aemeasurable h1.aemeasurable]
  rfl

/-- Two pre-Brownian motions have the same law on the rationals. -/
theorem map_ratPath_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    {Y : ℝ≥0 → Ω → ℝ} {Z : ℝ≥0 → Ω' → ℝ} (hY : IsPreBrownianReal Y P)
    (hZ : IsPreBrownianReal Z P') : P.map (ratPath Y) = P'.map (ratPath Z) := by
  have := hY.isGaussianProcess.isProbabilityMeasure
  have := hZ.isGaussianProcess.isProbabilityMeasure
  refine IsProjectiveLimit.unique (P := fun J => (P.map (ratPath Y)).map J.restrict)
    (fun J => rfl) (fun J => ?_)
  show _ = (P.map (ratPath Y)).map J.restrict
  rw [map_restrict_ratPath hY, map_restrict_ratPath hZ]

/-- The event "`f q → 0` as `q ↓ 0` along the positive rationals". -/
def ratSmall : Set (ℚ → ℝ) :=
  {f | ∀ m : ℕ, ∃ k : ℕ, ∀ q : ℚ, 0 < q → q < 1 / ((k : ℚ) + 1) → |f q| ≤ 1 / ((m : ℝ) + 1)}

theorem measurableSet_ratSmall : MeasurableSet ratSmall := by
  have : ratSmall = ⋂ m : ℕ, ⋃ k : ℕ, ⋂ q : ℚ,
      {f : ℚ → ℝ | 0 < q → q < 1 / ((k : ℚ) + 1) → |f q| ≤ 1 / ((m : ℝ) + 1)} := by
    ext f; simp [ratSmall]
  rw [this]
  refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun k => MeasurableSet.iInter fun q => ?_
  by_cases h : 0 < q ∧ q < 1 / ((k : ℚ) + 1)
  · simp only [h.1, h.2, true_implies]
    exact measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply q)) measurable_const
  · have : {f : ℚ → ℝ | 0 < q → q < 1 / ((k : ℚ) + 1) → |f q| ≤ 1 / ((m : ℝ) + 1)} = univ := by
      ext f; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [this]; exact MeasurableSet.univ

/-- A continuous path vanishing at `0` is `ratSmall`. -/
theorem ratSmall_of_continuous {b : ℝ≥0 → ℝ} (hb : Continuous b) (h0 : b 0 = 0) :
    (fun q : ℚ => b (q : ℝ).toNNReal) ∈ ratSmall := by
  intro m
  have hc : Continuous fun s : ℝ => b s.toNNReal := hb.comp continuous_real_toNNReal
  have ht := hc.tendsto 0
  simp only [Real.toNNReal_zero, h0] at ht
  obtain ⟨δ, hδ, hδb⟩ := Metric.tendsto_nhds_nhds.1 ht (1 / ((m : ℝ) + 1)) (by positivity)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
  refine ⟨k, fun q hq hqk => ?_⟩
  have hq' : ((q : ℝ)) < 1 / ((k : ℝ) + 1) := by
    have := (Rat.cast_lt (K := ℝ)).2 hqk; push_cast at this; exact this
  have := hδb (x := (q : ℝ)) (by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by exact_mod_cast hq)]; linarith)
  rw [Real.dist_eq, sub_zero] at this
  exact this.le

/-- Deterministic step: if `q ↦ q b(1/q)` is `ratSmall` and `b` is continuous, then
`b_t / t → 0`. -/
theorem tendsto_div_of_ratSmall {b : ℝ≥0 → ℝ} (hb : Continuous b)
    (hs : (fun q : ℚ => (((q : ℝ).toNNReal : ℝ≥0) : ℝ) * b (1 / (q : ℝ).toNNReal)) ∈ ratSmall) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * b t) atTop (𝓝 0) := by
  set G : ℝ → ℝ := fun s => s⁻¹ * b s.toNNReal with hG
  have hGc : ∀ s : ℝ, s ≠ 0 → ContinuousAt G s := fun s hs0 =>
    (continuousAt_inv₀ hs0).mul (hb.comp continuous_real_toNNReal).continuousAt
  -- bound at rationals
  have hrat : ∀ m : ℕ, ∃ k : ℕ, ∀ r : ℚ, (k : ℚ) + 1 < r → |G r| ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨k, hk⟩ := hs m
    refine ⟨k, fun r hr => ?_⟩
    have hr0 : (0 : ℚ) < r := lt_trans (by positivity) hr
    have h := hk r⁻¹ (inv_pos.2 hr0) (by
      rw [one_div]; exact inv_strictAnti₀ (by positivity) hr)
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    have e1 : (((r⁻¹ : ℚ) : ℝ).toNNReal : ℝ) = (r : ℝ)⁻¹ := by
      rw [Real.coe_toNNReal _ (by rw [Rat.cast_inv]; exact inv_nonneg.2 hr0'.le), Rat.cast_inv]
    have e2 : (1 / ((r⁻¹ : ℚ) : ℝ).toNNReal : ℝ≥0) = (r : ℝ).toNNReal := by
      apply NNReal.eq
      rw [NNReal.coe_div, NNReal.coe_one, e1, Real.coe_toNNReal _ hr0'.le, one_div, inv_inv]
    beta_reduce at h
    rw [e1, e2] at h
    exact h
  -- bound at reals, by continuity
  have hreal : ∀ m : ℕ, ∃ k : ℕ, ∀ t : ℝ, (k : ℝ) + 1 < t → |G t| ≤ 1 / ((m : ℝ) + 1) := by
    intro m
    obtain ⟨k, hk⟩ := hrat m
    refine ⟨k, fun t ht => ?_⟩
    have hseq : ∀ n : ℕ, ∃ r : ℚ, t < r ∧ (r : ℝ) < t + 1 / ((n : ℝ) + 1) := fun n =>
      exists_rat_btwn (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity])
    choose r hr using hseq
    have hrt : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 t) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
        (fun n => (hr n).1.le) (fun n => (hr n).2.le)
      simpa using (tendsto_const_nhds (x := t)).add tendsto_one_div_add_atTop_nhds_zero_nat
    have ht0 : t ≠ 0 := by
      have : (0 : ℝ) < t := lt_trans (by positivity) ht
      exact this.ne'
    have hlim := ((hGc t ht0).tendsto.comp hrt).abs
    refine le_of_tendsto' hlim fun n => hk (r n) ?_
    have : ((k : ℝ) + 1) < (r n : ℝ) := ht.trans (hr n).1
    exact_mod_cast this
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hk⟩ := hreal m
  refine ⟨((k : ℝ) + 2).toNNReal, fun t ht => ?_⟩
  have ht' : (k : ℝ) + 2 ≤ t := by
    have := (Real.toNNReal_le_iff_le_coe).1 ht
    exact this
  have := hk t (by linarith)
  rw [Real.dist_eq, sub_zero]
  simp only [G, Real.toNNReal_coe] at this
  exact lt_of_le_of_lt this hm

/-- **Continuous-time law of large numbers** (Le Gall 2016, Exercise 2.25): for a Brownian
motion, almost surely `B_t / t → 0` as `t → ∞`. -/
theorem ae_tendsto_div_atTop {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * B t ω) atTop (𝓝 0) := by
  have hW : IsPreBrownianReal (fun t ω => (t : ℝ) * B (1 / t) ω) P :=
    hB.toIsPreBrownianReal.inv
  have hlaw := map_ratPath_eq hB.toIsPreBrownianReal hW
  have hBs : ∀ᵐ f ∂P.map (ratPath B), f ∈ ratSmall := by
    refine (ae_map_iff (p := fun f => f ∈ ratSmall) (aemeasurable_ratPath hB.toIsPreBrownianReal)
      measurableSet_ratSmall).2 ?_
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
    exact ratSmall_of_continuous h1 h2
  rw [hlaw] at hBs
  have hWs := ae_of_ae_map (aemeasurable_ratPath hW) hBs
  filter_upwards [hWs, hB.cont] with ω h1 h2
  exact tendsto_div_of_ratSmall h2 h1

end BMLLN

end QuantumZipper
