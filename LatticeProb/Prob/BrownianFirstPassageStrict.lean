import LatticeProb.Prob.ExcursionCountRestartLaw
import LatticeProb.Prob.BrownianDriftConditionedRestart
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianG0NearZero
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.BrownianPathFacts

/-!
# The strict first passage of a Brownian motion below a level is its hitting time

For a path `X : ℝ → ℝ`, `firstPassageBelow X 0 a = inf {t ≥ 0 | X t < X 0 - a}` is the *strict* first passage
below the level `X 0 - a`, while the hitting time `hitDrift (-B) 0 a` of the closed half-line `{B ≤ -a}` is a
stopping time of the natural filtration. For a real Brownian motion `B` with continuous paths the two agree almost
surely: by the strong Markov property at the (truncated) hitting time, the restarted motion takes negative values at
arbitrarily small times, so `B` goes strictly below the level right after hitting it. By recurrence the hitting time
is almost surely finite.

* `firstPassageBelow_eq_of_hit`: a deterministic criterion for `firstPassageBelow X 0 a = σ`;
* `negNearZeroSet`: the paths that are negative at the time `1 / (k + 1)` for infinitely many `k`; a Brownian motion,
  and a Brownian motion restarted at a stopping time (`ae_restart_mem_negNearZeroSet`), lies in it almost surely;
* `ae_hitDrift_neg_lt_top`: the hitting time of `{B ≤ -a}` is almost surely finite;
* `ae_firstPassageBelow_eq_hitDriftTrunc`, `ae_firstPassageBelow_eq_hitDrift`: almost surely the strict first
  passage below `B 0 - a` is the hitting time of `{B ≤ -a}`, and the path does go below `B 0 - a`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

open QuantumZipper.GermZeroOne MatedCRTHarmonic.MatedCRT

/-- **Deterministic criterion for the first passage.** If `X σ ≤ X 0 - a`, `X` stays strictly above `X 0 - a` on
`[0, σ)`, and `X` takes values strictly below `X σ` at times `σ + r` with `r > 0` arbitrarily small, then the
strict first passage of `X` below `X 0 - a` is `σ` (and `X` does go below `X 0 - a`). -/
theorem firstPassageBelow_eq_of_hit {X : ℝ → ℝ} {a σ : ℝ} (hσ : 0 ≤ σ) (hXσ : X σ ≤ X 0 - a)
    (hbefore : ∀ s, 0 ≤ s → s < σ → X 0 - a < X s)
    (hafter : ∀ δ, 0 < δ → ∃ r, 0 < r ∧ r < δ ∧ X (σ + r) < X σ) :
    firstPassageBelow X 0 a = σ ∧ ∃ s, 0 ≤ s ∧ X s < X 0 - a := by
  obtain ⟨r, hr0, -, hr⟩ := hafter 1 one_pos
  have hne : ∃ s, 0 ≤ s ∧ X s < X 0 - a := ⟨σ + r, by linarith, by linarith⟩
  refine ⟨le_antisymm ?_ ?_, hne⟩
  · show sInf {t | 0 ≤ t ∧ X t < X 0 - a} ≤ σ
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨r, hr0, hrδ, hr⟩ := hafter δ hδ
    have hle := csInf_le (s := {t | 0 ≤ t ∧ X t < X 0 - a}) ⟨0, fun _ h => h.1⟩
      (⟨by linarith, by linarith⟩ : σ + r ∈ {t | 0 ≤ t ∧ X t < X 0 - a})
    exact lt_of_le_of_lt hle (by linarith)
  · show σ ≤ sInf {t | 0 ≤ t ∧ X t < X 0 - a}
    obtain ⟨s, hs0, hs⟩ := hne
    exact le_csInf ⟨s, hs0, hs⟩ fun t ht => le_of_not_gt fun h => lt_asymm (hbefore t ht.1 h) ht.2

/-- The paths `f : ℝ≥0 → ℝ` that are negative at the time `1 / (k + 1)` for infinitely many `k`. -/
def negNearZeroSet : Set (ℝ≥0 → ℝ) :=
  ⋂ n : ℕ, ⋃ k : ℕ, ⋃ (_ : n ≤ k), {f | f (epsSeq k) < 0}

theorem measurableSet_negNearZeroSet : MeasurableSet negNearZeroSet :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (measurable_pi_apply _) measurable_const

theorem mem_negNearZeroSet {f : ℝ≥0 → ℝ} :
    f ∈ negNearZeroSet ↔ ∀ n : ℕ, ∃ k, n ≤ k ∧ f (epsSeq k) < 0 := by
  simp only [negNearZeroSet, mem_iInter, mem_iUnion, exists_prop, mem_ofPred_eq]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A Brownian motion is negative at the time `1 / (k + 1)` for infinitely many `k`, almost surely. -/
theorem ae_mem_negNearZeroSet [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) : ∀ᵐ ω ∂P, (fun t => B t ω) ∈ negNearZeroSet := by
  filter_upwards [BrownianG0NearZero.ae_frequently_lt hB hm 0] with ω hω
  refine mem_negNearZeroSet.2 fun n => ?_
  obtain ⟨k, hk, hlt⟩ := hω n
  exact ⟨k, hk, by simpa using hlt⟩

/-- **Immediate descent after a stopping time.** A real Brownian motion with continuous paths, restarted at a finite
stopping time of its natural filtration, is negative at the time `1 / (k + 1)` for infinitely many `k`, almost
surely. -/
theorem ae_restart_mem_negNearZeroSet [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞)) :
    ∀ᵐ ω ∂P, (fun t => B (τ ω + t) ω - B (τ ω) ω) ∈ negNearZeroSet := by
  have h0 : P {ω | (fun t => B t ω) ∈ negNearZeroSetᶜ} = 0 := ae_iff.1 (ae_mem_negNearZeroSet hB hm)
  have key := restart_real hB hm hcont τ hτ univ MeasurableSet.univ _ measurableSet_negNearZeroSet.compl
  rw [univ_inter, h0, mul_zero] at key
  exact ae_iff.2 key

/-- **Recurrence.** The first time a real Brownian motion is at most `-a` is almost surely finite. -/
theorem ae_hitDrift_neg_lt_top [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a : ℝ) :
    ∀ᵐ ω ∂P, hitDrift (fun t ω => -B t ω) 0 a ω < ⊤ := by
  filter_upwards [BrownianPathFacts.ae_unboundedBelowInt hB.toIsPreBrownianReal hm] with ω hω
  obtain ⟨n, -, hn⟩ := hω ⌈a⌉₊ 0
  have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
  have hle : hitDrift (fun t ω => -B t ω) 0 a ω ≤ ((n : ℝ≥0) : ℝ≥0∞) :=
    (hitDrift_le_iff hcont' 0 a ω n).2 ⟨n, le_rfl, by
      simp only [zero_mul, add_zero]
      have := Nat.le_ceil a
      linarith⟩
  exact lt_of_le_of_lt hle ENNReal.coe_lt_top

/-- **The strict first passage is the hitting time.** For a real Brownian motion `B` with continuous paths, a level
`a` and a horizon `N`, almost surely on the event that `B` is at most `-a` before `N`, the strict first passage of
`B` below `B 0 - a` is the (truncated) hitting time of `{B ≤ -a}`, and `B` does go below `B 0 - a`. -/
theorem ae_firstPassageBelow_eq_hitDriftTrunc [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a : ℝ) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, hitDrift (fun t ω => -B t ω) 0 a ω ≤ (N : ℝ≥0∞) →
      firstPassageBelow (nnExtend fun t => B t ω) 0 a = hitDriftTrunc (fun t ω => -B t ω) 0 a N ω ∧
        ∃ s, 0 ≤ s ∧ nnExtend (fun t => B t ω) s < nnExtend (fun t => B t ω) 0 - a := by
  have hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞) := by
    have h := (isStoppingTime_hitDrift_neg_natFiltration hm hcont 0 a).min_const (i := N)
    rw [neg_zero] at h
    have hfun : (fun ω => ((hitDriftTrunc (fun t ω => -B t ω) 0 a N ω : ℝ≥0) : ℝ≥0∞))
        = fun ω => min (hitDrift (fun t ω => -B t ω) 0 a ω) (N : ℝ≥0∞) := by
      funext ω
      exact coe_hitDriftTrunc _ _ a N ω
    rw [hfun]
    exact h
  have hcont' : ∀ ω, Continuous fun s => (fun t ω => -B t ω) s ω := fun ω => (hcont ω).neg
  filter_upwards [ae_restart_mem_negNearZeroSet hB hm hcont
    (fun ω => hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) hτ, hB.eval_zero_ae_eq_zero] with ω hW h0 hle
  have hσ := coe_hitDriftTrunc_of_le (fun t ω => -B t ω) 0 a N ω hle
  have hW' : ∀ n : ℕ, ∃ k, n ≤ k ∧ B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + epsSeq k) ω -
      B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω < 0 := mem_negNearZeroSet.1 hW
  clear hW
  generalize hσdef : hitDriftTrunc (fun t ω => -B t ω) 0 a N ω = σ at hσ hW' ⊢
  have hbefore : ∀ s : ℝ≥0, s < σ → -a < B s ω := by
    intro s hs
    refine not_le.1 fun hcon => ?_
    have hle' : hitDrift (fun t ω => -B t ω) 0 a ω ≤ (s : ℝ≥0∞) :=
      (hitDrift_le_iff hcont' 0 a ω s).2 ⟨s, le_rfl, by simp only [zero_mul, add_zero]; linarith⟩
    rw [← hσ] at hle'
    exact absurd (ENNReal.coe_le_coe.1 hle') (not_le.2 hs)
  have hXσ : B σ ω ≤ -a := by
    obtain ⟨s, hsσ, hs⟩ := (hitDrift_le_iff hcont' 0 a ω σ).1 hσ.symm.le
    simp only [zero_mul, add_zero] at hs
    rcases hsσ.lt_or_eq with hlt | rfl
    · linarith [hbefore s hlt]
    · linarith
  have hX : ∀ t : ℝ≥0, nnExtend (fun t => B t ω) t = B t ω := fun t => by
    simp only [nnExtend, Real.toNNReal_coe]
  have hX0 : nnExtend (fun t => B t ω) 0 = 0 := by
    simp only [nnExtend, Real.toNNReal_zero, h0]
  refine firstPassageBelow_eq_of_hit (NNReal.coe_nonneg σ) ?_ ?_ ?_
  · rw [hX, hX0]
    linarith
  · intro s hs0 hsσ
    rw [hX0, show nnExtend (fun t => B t ω) s = B s.toNNReal ω from rfl]
    have := hbefore s.toNNReal ((Real.toNNReal_lt_iff_lt_coe hs0).2 hsσ)
    linarith
  · intro δ hδ
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    obtain ⟨k, hk, hlt⟩ := hW' n
    refine ⟨(epsSeq k : ℝ), NNReal.coe_pos.2 (epsSeq_pos k), ?_, ?_⟩
    · have he : (epsSeq k : ℝ) = 1 / ((k : ℝ) + 1) := by simp [epsSeq]
      rw [he]
      refine lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) ?_) hn
      have : (n : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    · rw [← NNReal.coe_add, hX, hX]
      linarith

/-- **The strict first passage is the hitting time, almost surely.** For a real Brownian motion `B` with continuous
paths and a level `a`, almost surely the hitting time of `{B ≤ -a}` is finite, it is the strict first passage of `B`
below `B 0 - a`, and `B` does go below `B 0 - a`. -/
theorem ae_firstPassageBelow_eq_hitDrift [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a : ℝ) :
    ∀ᵐ ω ∂P, hitDrift (fun t ω => -B t ω) 0 a ω < ⊤ ∧
      firstPassageBelow (nnExtend fun t => B t ω) 0 a = (hitDrift (fun t ω => -B t ω) 0 a ω).toReal ∧
        ∃ s, 0 ≤ s ∧ nnExtend (fun t => B t ω) s < nnExtend (fun t => B t ω) 0 - a := by
  have hall := ae_all_iff.2 fun N : ℕ => ae_firstPassageBelow_eq_hitDriftTrunc hB hm hcont a N
  filter_upwards [hall, ae_hitDrift_neg_lt_top hB hm hcont a] with ω hω hlt
  obtain ⟨N, hN⟩ : ∃ N : ℕ, hitDrift (fun t ω => -B t ω) 0 a ω ≤ ((N : ℝ≥0) : ℝ≥0∞) := by
    refine ⟨⌈(hitDrift (fun t ω => -B t ω) 0 a ω).toNNReal⌉₊, ?_⟩
    calc hitDrift (fun t ω => -B t ω) 0 a ω
        = ((hitDrift (fun t ω => -B t ω) 0 a ω).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hlt.ne).symm
      _ ≤ _ := ENNReal.coe_le_coe.2 (Nat.le_ceil _)
  obtain ⟨h1, h2⟩ := hω N hN
  refine ⟨hlt, ?_, h2⟩
  rw [h1, ← coe_hitDriftTrunc_of_le _ _ a _ ω hN, ENNReal.coe_toReal]

end LatticeProb.LadderSet
