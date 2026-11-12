/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Fin3 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Fin2

/-!
Node W5(ii) of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). `killed_fd_eq_of_integrated` is the
abstract de-integration step (right-continuity + FTC, `W5Fin2`); `killed_fd_eq_postLast_revHit`
applies it to W5(i) (`lintegral_killed_fd_eq`): for bounded continuous `g ≥ 0`, `c > 0` and
`u₁, …, uₙ ≤ U`,

`E[g(Ŷ(uᵢ)); U < λ_c(Ŷ)] = E[g(p(uᵢ)); U < T_c]`,   `(T_c, p) = revHit X c`.

Finiteness comes from `E[T_c] < ∞` (`lintegral_hitLevel_lt_top`) alone: the `Ŷ` side has the same
time integral by W5(i). Own elementary bookkeeping (blueprint sketch).
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem lintegral_Ioi_killedFD_swap [IsProbabilityMeasure P] {L : Ω → ℝ≥0}
    {p : Ω → ℝ≥0 → ℝ} (hLm : Measurable L) (hpc : ∀ ω, Continuous (p ω))
    (hpm : ∀ v, Measurable fun ω => p ω v) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0)
    {g : (Fin n → ℝ) → ℝ≥0} (hg : Continuous g) (x : ℝ) :
    ∫⁻ s in Ioi x, killedFD P L p u U g s
      = ∫⁻ ω, (∫⁻ s in Ioi x, {s : ℝ | s.toNNReal + U < L ω}.indicator
          (fun s => (g (fun i => p ω (s.toNNReal + u i)) : ℝ≥0∞)) s) ∂P :=
  (lintegral_lintegral_swap
    (measurable_killedFD_integrand hLm hpc hpm u U hg).aemeasurable).symm

/-- **W5(ii), abstract form.** -/
theorem killed_fd_eq_of_integrated [IsProbabilityMeasure P] {L₁ L₂ : Ω → ℝ≥0}
    {p₁ p₂ : Ω → ℝ≥0 → ℝ} (hL₁ : Measurable L₁) (hL₂ : Measurable L₂)
    (hp₁c : ∀ ω, Continuous (p₁ ω)) (hp₂c : ∀ ω, Continuous (p₂ ω))
    (hp₁m : ∀ v, Measurable fun ω => p₁ ω v) (hp₂m : ∀ v, Measurable fun ω => p₂ ω v)
    (hE₂ : ∫⁻ ω, (L₂ ω : ℝ≥0∞) ∂P ≠ ∞) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0)
    {g : (Fin n → ℝ) → ℝ≥0} (hg : Continuous g) {M : ℝ≥0} (hM : ∀ x, g x ≤ M)
    (heq : ∀ r : ℝ≥0, ∫⁻ ω, (∫⁻ s in Ioi (r : ℝ), {s : ℝ | s.toNNReal + U < L₁ ω}.indicator
          (fun s => (g (fun i => p₁ ω (s.toNNReal + u i)) : ℝ≥0∞)) s) ∂P
        = ∫⁻ ω, (∫⁻ s in Ioi (r : ℝ), {s : ℝ | s.toNNReal + U < L₂ ω}.indicator
          (fun s => (g (fun i => p₂ ω (s.toNNReal + u i)) : ℝ≥0∞)) s) ∂P) :
    ∫⁻ ω, {ω | U < L₁ ω}.indicator (fun ω => (g (fun i => p₁ ω (u i)) : ℝ≥0∞)) ω ∂P
      = ∫⁻ ω, {ω | U < L₂ ω}.indicator (fun ω => (g (fun i => p₂ ω (u i)) : ℝ≥0∞)) ω ∂P := by
  have hK₁m : Measurable (killedFD P L₁ p₁ u U g) :=
    (measurable_killedFD_integrand hL₁ hp₁c hp₁m u U hg).lintegral_prod_left'
  have hK₂m : Measurable (killedFD P L₂ p₂ u U g) :=
    (measurable_killedFD_integrand hL₂ hp₂c hp₂m u U hg).lintegral_prod_left'
  have heq' : ∀ x, 0 ≤ x → ∫⁻ s in Ioi x, killedFD P L₁ p₁ u U g s
      = ∫⁻ s in Ioi x, killedFD P L₂ p₂ u U g s := by
    intro x hx
    have h := heq x.toNNReal
    rw [Real.coe_toNNReal _ hx] at h
    rw [lintegral_Ioi_killedFD_swap hL₁ hp₁c hp₁m u U hg,
      lintegral_Ioi_killedFD_swap hL₂ hp₂c hp₂m u U hg, h]
  -- finiteness of the `p₂` side, hence of the `p₁` side
  have hfin2 : ∫⁻ s in Ioi (0 : ℝ), killedFD P L₂ p₂ u U g s ≠ ∞ := by
    rw [lintegral_Ioi_killedFD_swap hL₂ hp₂c hp₂m u U hg]
    refine ne_top_of_le_ne_top (b := ∫⁻ ω, (M : ℝ≥0∞) * L₂ ω ∂P) ?_ (lintegral_mono fun ω => ?_)
    · rw [lintegral_const_mul _ hL₂.coe_nnreal_ennreal]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hE₂
    · rw [← lintegral_indicator measurableSet_Ioi]
      calc _ ≤ ∫⁻ s, (Ioc (0 : ℝ) (L₂ ω)).indicator (fun _ => (M : ℝ≥0∞)) s := by
            refine lintegral_mono fun s => ?_
            by_cases h0 : s ∈ Ioi (0 : ℝ)
            · rw [indicator_of_mem h0]
              by_cases h1 : s ∈ {s : ℝ | s.toNNReal + U < L₂ ω}
              · have hs : s ≤ L₂ ω := by
                  have h1' : s.toNNReal ≤ L₂ ω := le_self_add.trans (le_of_lt h1)
                  have := NNReal.coe_le_coe.2 h1'
                  rwa [Real.coe_toNNReal _ (le_of_lt h0)] at this
                rw [indicator_of_mem h1, indicator_of_mem (show s ∈ Ioc (0 : ℝ) (L₂ ω) from
                  ⟨h0, hs⟩)]
                exact ENNReal.coe_le_coe.2 (hM _)
              · rw [indicator_of_notMem h1]; exact zero_le
            · rw [indicator_of_notMem h0]; exact zero_le
        _ = (M : ℝ≥0∞) * L₂ ω := by
            rw [lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc, sub_zero,
              ENNReal.ofReal_coe_nnreal]
  have hfin1 : ∫⁻ s in Ioi (0 : ℝ), killedFD P L₁ p₁ u U g s ≠ ∞ := by
    rw [heq' 0 le_rfl]; exact hfin2
  have hKfin : ∀ (L : Ω → ℝ≥0) (p : Ω → ℝ≥0 → ℝ), killedFD P L p u U g 0 ≠ ∞ := by
    intro L p
    refine ne_top_of_le_ne_top (b := ∫⁻ _, (M : ℝ≥0∞) ∂P) (by simp) (lintegral_mono fun ω => ?_)
    by_cases h : ω ∈ {ω | (0 : ℝ).toNNReal + U < L ω}
    · rw [indicator_of_mem h]; exact ENNReal.coe_le_coe.2 (hM _)
    · rw [indicator_of_notMem h]; exact zero_le
  have h := eq_of_lintegral_Ioi_eq hK₁m hK₂m hfin1 hfin2 heq'
    (continuousWithinAt_killedFD hL₁ hp₁c hp₁m u U hg hM le_rfl)
    (continuousWithinAt_killedFD hL₂ hp₂c hp₂m u U hg hM le_rfl)
  have h' := (ENNReal.toReal_eq_toReal_iff' (hKfin L₁ p₁) (hKfin L₂ p₂)).1 h
  simpa only [killedFD, Real.toNNReal_zero, zero_add] using h'

variable {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

theorem measurable_postLast_eval (hb : GoodBM b P) (σ μ : ℝ) (v : ℝ≥0) :
    Measurable fun ω => postLast (dpath σ μ b ω) 0 v :=
  (StrongMarkov.measurable_randomTime_eval (B := fun t ω => dpath σ μ b ω t)
    (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t)
    ((measurable_lastPass (continuous_dpath hb σ μ)
      (fun t => measurable_dpath hb σ μ t)).add_const v)).sub_const 0

theorem continuous_postLast_dpath (hb : GoodBM b P) (σ μ : ℝ) (ω : Ω) :
    Continuous (postLast (dpath σ μ b ω) 0) :=
  ((continuous_dpath hb σ μ ω).comp (continuous_const.add continuous_id)).sub continuous_const

theorem measurable_lastPass_postLast (hb : GoodBM b P) (σ μ c : ℝ) :
    Measurable fun ω => lastPass (postLast (dpath σ μ b ω) 0) c := by
  have h := measurable_lastPass (f := fun ω t => postLast (dpath σ μ b ω) 0 t - c)
    (fun ω => (continuous_postLast_dpath hb σ μ ω).sub continuous_const)
    (fun t => (measurable_postLast_eval hb σ μ t).sub_const c)
  have e : ∀ w : ℝ≥0 → ℝ, lastPass (fun t => w t - c) 0 = lastPass w c := fun w => by
    simp only [lastPass, sub_eq_zero]
  simpa only [e] using h

theorem continuous_revHit_dpath (hb : GoodBM b P) (σ μ c : ℝ) (ω : Ω) :
    Continuous (revHit (dpath σ μ b ω) c).2 :=
  ((continuous_dpath hb σ μ ω).comp (continuous_const.sub continuous_id)).add continuous_const

theorem measurable_revHit_eval (hb : GoodBM b P) (σ μ c : ℝ) (v : ℝ≥0) :
    Measurable fun ω => (revHit (dpath σ μ b ω) c).2 v :=
  (StrongMarkov.measurable_randomTime_eval (B := fun t ω => dpath σ μ b ω t)
    (continuous_dpath hb σ μ) (fun t => measurable_dpath hb σ μ t)
    ((measurable_hitLevel_dpath hb σ μ (-c)).sub_const v)).add_const c

/-- **W5(ii): the killed finite-dimensional laws agree** (blueprint W5(ii) at `s = 0`). -/
theorem killed_fd_eq_postLast_revHit (hb : GoodBM b P) (hσ : 0 < σ) (hμ : 0 < μ) {c : ℝ}
    (hc : 0 < c) {n : ℕ} (u : Fin n → ℝ≥0) (U : ℝ≥0) (hu : ∀ i, u i ≤ U)
    {g : (Fin n → ℝ) → ℝ≥0} (hg : Continuous g) {M : ℝ≥0} (hM : ∀ x, g x ≤ M) :
    ∫⁻ ω, {ω | U < lastPass (postLast (dpath σ μ b ω) 0) c}.indicator
        (fun ω => (g (fun i => postLast (dpath σ μ b ω) 0 (u i)) : ℝ≥0∞)) ω ∂P
      = ∫⁻ ω, {ω | U < (revHit (dpath σ (-μ) b ω) c).1}.indicator
        (fun ω => (g (fun i => (revHit (dpath σ (-μ) b ω) c).2 (u i)) : ℝ≥0∞)) ω ∂P := by
  haveI : IsProbabilityMeasure P := isProbabilityMeasure_of_goodBM hb
  have hT : Measurable fun ω => hitLevel (dpath σ (-μ) b ω) (-c) :=
    measurable_hitLevel_dpath hb σ (-μ) (-c)
  have hL₁ := measurable_lastPass_postLast hb σ μ c
  have hp₁c := continuous_postLast_dpath hb σ μ
  have hp₂c := continuous_revHit_dpath hb σ (-μ) c
  have hp₁m := measurable_postLast_eval hb σ μ
  have hp₂m := measurable_revHit_eval hb σ (-μ) c
  refine killed_fd_eq_of_integrated hL₁ hT hp₁c hp₂c hp₁m hp₂m
    (lintegral_hitLevel_lt_top hb hσ hμ hc).ne u U hg hM fun r => ?_
  exact lintegral_killed_fd_eq hb hσ hμ hc u U hu
    (g := fun x => (g x : ℝ≥0∞)) (measurable_coe_nnreal_ennreal.comp hg.measurable) r

end QuantumZipper.Williams
