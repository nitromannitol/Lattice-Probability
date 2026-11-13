import LatticeProb.Prob.ExcursionCountMeanAdditive
import LatticeProb.Prob.BrownianRestartPath

/-!
# The excursion count before a first passage is determined by the past at the hitting time

For a path `f : ℝ≥0 → ℝ` and a time `s`, `stopWithDrift s f` is `f` stopped at `s` and followed by the unit downward
drift: `t ↦ f (min t s) - (t - s)⁺`. If `s` is the strict first passage of `f` below `f 0 - a` and `f` does go below
that level, the excursion count of `f` before its first passage (`pathExcursionCount f a ε`) equals that of
`stopWithDrift s f`, which depends on `f` on `[0, s]` only.

For a real Brownian motion `B` with continuous paths this gives the strong Markov independence of the excursion count
before the hitting time `σ` of `{B ≤ -a}` and the excursion count of the restarted motion `B (σ + ·) - B σ`:

* `excursionCount_congr_inter`, `forwardLadderSet_inter_Icc_congr`: locality of the excursion count and of the
  forward ladder set;
* `pathExcursionCount_stopWithDrift`: the deterministic identity above;
* `measurable_stopWithDrift`: the path stopped at a stopping time `τ`, with the drift, is measurable for the
  σ-algebra at `τ`;
* `exists_measurableSet_hitDriftTrunc_le_pathExcursionCount`: on `{σ < N}` the event `{k ≤ J_ε(a)}` coincides almost
  surely with an event of the σ-algebra at the truncated hitting time;
* `measure_inter_restart_pathExcursionCount`: the independence statement.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace LatticeProb.LadderSet

/-- **Locality of the excursion count.** The excursion count of `K` in `[s, t]` depends only on `K ∩ [s, t]`. -/
theorem excursionCount_congr_inter {K K' : Set ℝ} {s t : ℝ} (h : K ∩ Icc s t = K' ∩ Icc s t) (ε : ℝ) :
    excursionCount K s t ε = excursionCount K' s t ε := by
  have hd : Icc s t \ K = Icc s t \ K' := by
    rw [← sdiff_inter_self_eq_sdiff, h, sdiff_inter_self_eq_sdiff]
  simp only [excursionCount, complementaryIntervals, hd]

theorem forwardLadderSet_inter_Icc_subset {X Y : ℝ → ℝ} {a s : ℝ} (h : ∀ u ∈ Icc a s, X u = Y u) :
    forwardLadderSet X a ∩ Icc a s ⊆ forwardLadderSet Y a ∩ Icc a s := by
  rintro t ⟨⟨hat, hX⟩, ht⟩
  refine ⟨⟨hat, fun u hu => ?_⟩, ht⟩
  have hu' : u ∈ Icc a s := ⟨hu.1, hu.2.trans ht.2⟩
  rw [← h t ht, ← h u hu']
  exact hX u hu

/-- **Locality of the forward ladder set.** If `X = Y` on `[a, s]`, their forward ladder sets from `a` agree on
`[a, s]`. -/
theorem forwardLadderSet_inter_Icc_congr {X Y : ℝ → ℝ} {a s : ℝ} (h : ∀ u ∈ Icc a s, X u = Y u) :
    forwardLadderSet X a ∩ Icc a s = forwardLadderSet Y a ∩ Icc a s :=
  Subset.antisymm (forwardLadderSet_inter_Icc_subset h)
    (forwardLadderSet_inter_Icc_subset fun u hu => (h u hu).symm)

/-- The path `f` stopped at the time `s` and followed by the unit downward drift: `t ↦ f (min t s) - (t - s)⁺`. -/
def stopWithDrift (s : ℝ≥0) (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  f (min t s) - ((t - s : ℝ≥0) : ℝ)

theorem continuous_stopWithDrift {f : ℝ≥0 → ℝ} (hf : Continuous f) (s : ℝ≥0) :
    Continuous (stopWithDrift s f) :=
  (hf.comp (continuous_id.min continuous_const)).sub
    (NNReal.continuous_coe.comp (continuous_id.sub continuous_const))

theorem nnExtend_stopWithDrift_of_le {f : ℝ≥0 → ℝ} {s : ℝ≥0} {u : ℝ} (hu : u ≤ s) :
    nnExtend (stopWithDrift s f) u = nnExtend f u := by
  have h : u.toNNReal ≤ s := Real.toNNReal_le_iff_le_coe.2 hu
  simp only [nnExtend, stopWithDrift, min_eq_left h, tsub_eq_zero_of_le h, NNReal.coe_zero, sub_zero]

theorem nnExtend_stopWithDrift_of_lt {f : ℝ≥0 → ℝ} {s : ℝ≥0} {u : ℝ} (hu : (s : ℝ) < u) :
    nnExtend (stopWithDrift s f) u = f s - (u - s) := by
  have h : s < u.toNNReal := Real.lt_toNNReal_iff_coe_lt.2 hu
  have hu0 : 0 ≤ u := s.coe_nonneg.trans hu.le
  simp only [nnExtend, stopWithDrift, min_eq_right h.le, NNReal.coe_sub h.le, Real.coe_toNNReal u hu0]

/-- **The excursion count is determined by the path before the first passage.** If `s` is the strict first passage
of the continuous path `f` below `f 0 - a` and `f` does go below that level, then `f` and the stopped path
`stopWithDrift s f` have the same excursion count before their first passage below the level `a`. -/
theorem pathExcursionCount_stopWithDrift {f : ℝ≥0 → ℝ} (hf : Continuous f) {s : ℝ≥0} {a : ℝ}
    (hT : firstPassageBelow (nnExtend f) 0 a = s)
    (hex : ∃ u, 0 ≤ u ∧ nnExtend f u < nnExtend f 0 - a) (ε : ℝ) :
    pathExcursionCount (stopWithDrift s f) a ε = pathExcursionCount f a ε := by
  set S := {t : ℝ | 0 ≤ t ∧ nnExtend f t < nnExtend f 0 - a} with hS
  have hSne : S.Nonempty := hex
  have hSbdd : BddBelow S := ⟨0, fun _ h => h.1⟩
  have hT' : sInf S = s := hT
  -- `f s ≤ f 0 - a`, by continuity
  have hfs : nnExtend f s ≤ nnExtend f 0 - a := by
    have hC : IsClosed {t : ℝ | nnExtend f t ≤ nnExtend f 0 - a} :=
      isClosed_le (continuous_nnExtend hf) continuous_const
    have hmem := closure_minimal (fun t (ht : t ∈ S) => ht.2.le) hC (csInf_mem_closure hSne hSbdd)
    rw [hT'] at hmem
    exact hmem
  have h0 : nnExtend (stopWithDrift s f) 0 = nnExtend f 0 :=
    nnExtend_stopWithDrift_of_le s.coe_nonneg
  have heq : ∀ u ∈ Icc (0 : ℝ) s, nnExtend (stopWithDrift s f) u = nnExtend f u :=
    fun u hu => nnExtend_stopWithDrift_of_le hu.2
  -- the first passage of the stopped path is `s`
  have hTg : firstPassageBelow (nnExtend (stopWithDrift s f)) 0 a = s := by
    set Sg := {t : ℝ | 0 ≤ t ∧ nnExtend (stopWithDrift s f) t < nnExtend (stopWithDrift s f) 0 - a}
    have hgt : ∀ t : ℝ, (s : ℝ) < t → t ∈ Sg := by
      intro t ht
      refine ⟨s.coe_nonneg.trans ht.le, ?_⟩
      rw [nnExtend_stopWithDrift_of_lt ht, h0]
      have hs' : nnExtend f s = f s := by simp [nnExtend]
      linarith
    have hge : ∀ t ∈ Sg, (s : ℝ) ≤ t := by
      intro t ht
      by_contra hlt
      push Not at hlt
      have htS : t ∈ S := by
        refine ⟨ht.1, ?_⟩
        have := ht.2
        rwa [heq t ⟨ht.1, hlt.le⟩, h0] at this
      have := csInf_le hSbdd htS
      rw [hT'] at this
      linarith
    show sInf Sg = s
    refine le_antisymm ?_ ?_
    · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
      exact csInf_le ⟨0, fun _ h => h.1⟩ (hgt c hc)
    · exact le_csInf ⟨s + 1, hgt _ (by linarith)⟩ hge
  unfold pathExcursionCount
  rw [hTg, hT]
  exact excursionCount_congr_inter (forwardLadderSet_inter_Icc_congr heq) ε

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **The stopped path is measurable for the past at the stopping time.** For a real process with measurable
coordinates and continuous paths and a finite stopping time `τ` of the natural filtration, the path stopped at `τ`
and followed by the unit downward drift is measurable for the σ-algebra at `τ`. -/
theorem measurable_stopWithDrift (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (natFiltration (liftOne B) (stronglyMeasurable_liftOne hm))
      fun ω => (τ ω : ℝ≥0∞)) :
    Measurable[hτ.measurableSpace] fun ω => stopWithDrift (τ ω) (fun t => B t ω) := by
  have hstop := measurable_stopAt_pathMap (stronglyAdapted_natFiltration_real hm) hcont hτ
  have hτm : Measurable[hτ.measurableSpace] τ := by
    have h := ENNReal.measurable_toNNReal.comp hτ.measurable
    have he : (ENNReal.toNNReal ∘ fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)) = τ := by
      funext ω
      simp
    rwa [he] at h
  refine @Measurable.of_eval Ω ℝ≥0 (fun _ => ℝ) hτ.measurableSpace _ _ fun t => ?_
  have h1 : Measurable[hτ.measurableSpace] fun ω => B (min t (τ ω)) ω := by
    have h := (continuous_eval_const t).measurable.comp hstop
    have he : ((fun w : C(ℝ≥0, ℝ) => w t) ∘ fun ω => stopAt ((τ ω : ℝ≥0) : ℝ≥0∞) (pathMap B hcont ω)) =
        fun ω => B (min t (τ ω)) ω := by
      funext ω
      simp only [Function.comp_apply, stopAt_apply, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
      rfl
    rwa [he] at h
  have h2 : Measurable[hτ.measurableSpace] fun ω => ((t - τ ω : ℝ≥0) : ℝ) :=
    (NNReal.continuous_coe.comp (continuous_const.sub continuous_id)).measurable.comp hτm
  exact h1.sub h2

/-- **The excursion count before the hitting time is measurable for the past at the hitting time.** For a real
Brownian motion `B` with continuous paths, a level `a`, `ε > 0`, a horizon `N` and `k : ℕ`, the event that `B`
reaches `{B ≤ -a}` before `N` and has at least `k` excursions above its running minimum, of length larger than `ε`,
before its first passage below `B 0 - a`, coincides almost surely with an event of the σ-algebra at the truncated
hitting time of `{B ≤ -a}`. -/
theorem exists_measurableSet_hitDriftTrunc_le_pathExcursionCount [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a : ℝ)
    {ε : ℝ} (hε : 0 < ε) (N : ℝ≥0) (k : ℕ) :
    ∃ E : Set Ω,
      MeasurableSet[(isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a N).measurableSpace] E ∧
      E =ᵐ[P] {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞) ∧
        k ≤ pathExcursionCount (fun t => B t ω) a ε} := by
  set σ : Ω → ℝ≥0 := hitDriftTrunc (fun t ω => -B t ω) 0 a N with hσ_def
  have hσ := isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a N
  obtain ⟨Γ, hΓ, hΓP⟩ := exists_measurableSet_le_pathExcursionCount a hε k
  have hlt : ∀ ω, ((σ ω : ℝ≥0) : ℝ≥0∞) < N ↔ hitDrift (fun t ω => -B t ω) 0 a ω < N := by
    intro ω
    rw [hσ_def, coe_hitDriftTrunc, inf_lt_iff]
    simp
  refine ⟨{ω | stopWithDrift (σ ω) (fun t => B t ω) ∈ Γ} ∩ {ω | ((σ ω : ℝ≥0) : ℝ≥0∞) < N}, ?_, ?_⟩
  · exact (measurable_stopWithDrift hm hcont σ hσ hΓ).inter (hσ.measurableSet_lt' N)
  · filter_upwards [ae_firstPassageBelow_eq_hitDriftTrunc hB hm hcont a N] with ω hω
    have key : ∀ hN : hitDrift (fun t ω => -B t ω) 0 a ω < N,
        (stopWithDrift (σ ω) (fun t => B t ω) ∈ Γ ↔ k ≤ pathExcursionCount (fun t => B t ω) a ε) := by
      intro hN
      obtain ⟨hT, hex⟩ := hω hN.le
      rw [hΓP _ (continuous_stopWithDrift (hcont ω) _),
        pathExcursionCount_stopWithDrift (hcont ω) hT hex ε]
    refine propext ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
    · have hN := (hlt ω).1 h2
      exact ⟨hN, (key hN).1 h1⟩
    · exact ⟨(key h1).2 h2, (hlt ω).2 h1⟩

/-- **Strong Markov independence of the excursion counts.** For a real Brownian motion `B` with continuous paths,
levels `a, b`, `ε > 0`, a horizon `N` and `k, m : ℕ`, with `σ` the hitting time of `{B ≤ -a}` truncated at `N`: the
event `{σ < N, k ≤ J_ε(a)}` is independent of the event that the restarted motion `B (σ + ·) - B σ` has at least `m`
excursions of length larger than `ε` before its first passage below `-b`, which has the probability of
`{m ≤ J_ε(b)}`. -/
theorem measure_inter_restart_pathExcursionCount [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (a b : ℝ) {ε : ℝ} (hε : 0 < ε)
    (N : ℝ≥0) (k m : ℕ) :
    P ({ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞) ∧
          k ≤ pathExcursionCount (fun t => B t ω) a ε} ∩
        {ω | m ≤ pathExcursionCount (fun t => B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω + t) ω -
          B (hitDriftTrunc (fun t ω => -B t ω) 0 a N ω) ω) b ε})
      = P {ω | hitDrift (fun t ω => -B t ω) 0 a ω < (N : ℝ≥0∞) ∧
          k ≤ pathExcursionCount (fun t => B t ω) a ε} *
        P {ω | m ≤ pathExcursionCount (fun t => B t ω) b ε} := by
  obtain ⟨E, hE, hEeq⟩ := exists_measurableSet_hitDriftTrunc_le_pathExcursionCount hB hm hcont a hε N k
  rw [← measure_congr (hEeq.inter (Filter.EventuallyEq.refl _ _)), ← measure_congr hEeq]
  exact restart_le_pathExcursionCount hB hm hcont _ (isStoppingTime_hitDriftTrunc_neg_natFiltration hm hcont a N)
    E hE b hε m

end LatticeProb.LadderSet
