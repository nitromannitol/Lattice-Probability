import LatticeProb.Analysis.ExcursionCountMonotone

/-!
# From first-passage levels to all times in Lévy's excursion-count theorem

Let `X : ℝ → ℝ` be continuous, `a ∈ ℝ`, and let `K = forwardLadderSet X a` be the set of times `t ≥ a` at which `X`
attains its running minimum from `a`. For `b ∈ ℝ` the first-passage time of `X` below the level `X a - b` after `a` is
`firstPassageBelow X a b = inf {t ≥ a | X t < X a - b}`.

* `firstPassageBelow_le`, `le_firstPassageBelow`: if the running descent `X a - min_{[a, t]} X` is larger than `b`,
  then the first passage below `X a - b` happens before `t`; if it is smaller than `b`, it happens after `t`;
* `apply_firstPassageBelow_le`, `firstPassageBelow_mem_forwardLadderSet`: the first-passage time is a ladder time;
* `tendsto_excursionCount_forwardLadderSet`: the deterministic sandwich. If `X` is unbounded below on `[a, ∞)` and,
  for every rational level `b > 0`, `√(π ε / 2)` times the number of excursions of `X` above its running minimum of
  length larger than `ε` completed before the first passage below `X a - b` tends to `b` as `ε → 0`, then for every
  `t ≥ a` the same normalized count on `[a, t]` tends to the running descent `X a - min_{[a, t]} X`.

The proof uses only the monotonicity of the excursion count in the right end point
(`excursionCount_mono_right`) and squeezes the count at `t` between the counts at two rational first-passage levels
on either side of the running descent.
-/

open Filter Set Topology

namespace LatticeProb.LadderSet

/-- The first-passage time of `X` below the level `X a - b` after time `a`. -/
noncomputable def firstPassageBelow (X : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf {t | a ≤ t ∧ X t < X a - b}

variable {X : ℝ → ℝ} {a b t : ℝ}

/-- If the running descent of `X` over `[a, t]` exceeds `b`, the first passage below `X a - b` happens by time `t`. -/
theorem firstPassageBelow_le (ht : a ≤ t) (h : b < X a - sInf (X '' Icc a t)) :
    firstPassageBelow X a b ≤ t := by
  have hlt : sInf (X '' Icc a t) < X a - b := by linarith
  obtain ⟨_, ⟨s, hs, rfl⟩, hsb⟩ := exists_lt_of_csInf_lt ((nonempty_Icc.2 ht).image X) hlt
  exact (csInf_le (s := {t | a ≤ t ∧ X t < X a - b}) ⟨a, fun r hr => hr.1⟩ ⟨hs.1, hsb⟩).trans hs.2

/-- If `X` is continuous, goes below `X a - b` after `a`, and its running descent over `[a, t]` is smaller than `b`,
then the first passage below `X a - b` happens after time `t`. -/
theorem le_firstPassageBelow (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b)
    (h : X a - sInf (X '' Icc a t) < b) : t ≤ firstPassageBelow X a b := by
  refine le_csInf hne fun s hs => le_of_not_gt fun hst => ?_
  have hbdd : BddBelow (X '' Icc a t) := isCompact_Icc.bddBelow_image hX.continuousOn
  have := csInf_le hbdd ⟨s, ⟨hs.1, hst.le⟩, rfl⟩
  linarith [hs.2]

theorem le_firstPassageBelow_self (hne : ∃ s, a ≤ s ∧ X s < X a - b) : a ≤ firstPassageBelow X a b :=
  le_csInf hne fun _ hs => hs.1

/-- At the first-passage time, `X` is at most the level `X a - b`. -/
theorem apply_firstPassageBelow_le (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b) :
    X (firstPassageBelow X a b) ≤ X a - b := by
  have hmem := csInf_mem_closure hne ⟨a, fun _ hr => hr.1⟩
  have hcl : closure {t | a ≤ t ∧ X t < X a - b} ⊆ {t | X t ≤ X a - b} :=
    closure_minimal (fun _ hr => hr.2.le) (isClosed_le hX continuous_const)
  exact hcl hmem

/-- The first-passage time below `X a - b` is a forward ladder time of `X` from `a`. -/
theorem firstPassageBelow_mem_forwardLadderSet (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b) :
    firstPassageBelow X a b ∈ forwardLadderSet X a := by
  refine ⟨le_firstPassageBelow_self hne, fun s hs => ?_⟩
  rcases hs.2.lt_or_eq with hlt | rfl
  · refine (apply_firstPassageBelow_le hX hne).trans (le_of_not_gt fun hsb => ?_)
    exact (csInf_le (s := {t | a ≤ t ∧ X t < X a - b}) ⟨a, fun _ hr => hr.1⟩ ⟨hs.1, hsb⟩).not_gt hlt
  · exact le_rfl

/-- **Sandwich from first-passage levels to all times.** If `X` is continuous and unbounded below on `[a, ∞)`, and
the normalized excursion count `√(π ε / 2) N_ε` of `X` above its running minimum from `a` converges to `b` at the
first passage below `X a - b`, for every rational `b > 0`, then at every time `t ≥ a` it converges to the running
descent `X a - min_{[a, t]} X`. -/
theorem tendsto_excursionCount_forwardLadderSet (hX : Continuous X)
    (hunb : ∀ b : ℝ, ∃ s, a ≤ s ∧ X s < X a - b)
    (hlev : ∀ b : ℚ, 0 < b → Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a (firstPassageBelow X a b) ε : ℝ)) (𝓝[>] 0) (𝓝 (b : ℝ)))
    (ht : a ≤ t) :
    Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε / 2) *
      (excursionCount (forwardLadderSet X a) a t ε : ℝ)) (𝓝[>] 0) (𝓝 (X a - sInf (X '' Icc a t))) := by
  have hbdd : BddBelow (X '' Icc a t) := isCompact_Icc.bddBelow_image hX.continuousOn
  have hL : 0 ≤ X a - sInf (X '' Icc a t) := sub_nonneg.2 (csInf_le hbdd ⟨a, ⟨le_rfl, ht⟩, rfl⟩)
  have hmono : ∀ u v : ℝ, u ≤ v → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      Real.sqrt (Real.pi * ε / 2) * (excursionCount (forwardLadderSet X a) a u ε : ℝ) ≤
        Real.sqrt (Real.pi * ε / 2) * (excursionCount (forwardLadderSet X a) a v ε : ℝ) :=
    fun u v huv => eventually_nhdsWithin_of_forall fun ε hε =>
      mul_le_mul_of_nonneg_left (Nat.cast_le.2 (excursionCount_mono_right _ _ hε huv)) (Real.sqrt_nonneg _)
  rw [tendsto_order]
  refine ⟨fun c hc => ?_, fun c hc => ?_⟩
  · rcases lt_or_ge c 0 with hc0 | hc0
    · exact Eventually.of_forall fun ε => hc0.trans_le (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    obtain ⟨q, hcq, hqL⟩ := exists_rat_btwn hc
    have hq0 : (0 : ℝ) < q := hc0.trans_lt hcq
    filter_upwards [(hlev q (by exact_mod_cast hq0)).eventually (lt_mem_nhds hcq),
      hmono _ _ (firstPassageBelow_le ht hqL)] with ε h1 h2
    exact h1.trans_le h2
  · obtain ⟨q, hLq, hqc⟩ := exists_rat_btwn hc
    have hq0 : (0 : ℝ) < q := hL.trans_lt hLq
    filter_upwards [(hlev q (by exact_mod_cast hq0)).eventually (gt_mem_nhds hqc),
      hmono _ _ (le_firstPassageBelow hX (hunb q) hLq)] with ε h1 h2
    exact h2.trans_lt h1

end LatticeProb.LadderSet
