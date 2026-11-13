/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.PathProperties at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.IndexSet
import LatticeProb.Bonanno.ReflectedWalk.Theorem16Statement
import LatticeProb.Bonanno.ReflectedWalk.PathSpace
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Group.Measure

/-!
# Path properties of the process `X` of (3.26)
(Gwynne–Sung, arXiv:2506.18827, Sections 3.3–3.4: Lemmas 3.6, 3.7, 3.8 and properties (i), (ii)
of Theorem 1.6)

`IndexSet.lean` builds, deterministically in the sample `(Y, E)`, the clock `τ_η` of (3.25),
the successor `η̂` of (3.24), the intervals `[τ_η, τ_η̂)` and the process `X : ℝ≥0 → Option V`
of (3.26).  This file proves the path properties of `X` on top of that skeleton.

* The deterministic layer (section `deterministic`): the interval structure
  `τ_η̂ = τ_η + T_η` (`tau_succ`); right continuity of every sample path with
  `Consistent` (`X_rightContinuous`); Lemma 3.6 (`tendsto_tsum_notMem`), a dominated-convergence
  statement once `τ_η < ∞` is known; the first paragraph of the proof of Lemma 3.7 —
  Lebesgue-a.e. `t > 0` lies in the interior of a holding interval
  (`volume_notInOpenInterval`) — and its transfer along the first holding time `T_{ξ₀}`
  (`volume_notInOpenInterval_update`), the deterministic content of the absolute-continuity
  argument of the second paragraph; the processes `Xⁿ` of (3.15) (`Xn`), the identity (3.29)
  (`tau_eq_levelTau_add`) and (3.28) of Lemma 3.8 (`eventually_Xn_eq_X`); and the `L¹_loc`
  convergence `Xⁿ → X` for every sample with (3.12) and (3.16)
  (`tendsto_expMeasure_Xn_ne_X`).
* Measurability (section `measurability`): every quantity of `IndexSet.lean` is a measurable
  function of the sample `(Y, E)`, and the process, cut off to `∞` on the null event where
  the coupling identity (3.12) fails (`process`), is a genuine stochastic process
  (`measurable_process`); `X` and `Xⁿ` are jointly measurable in `(ω, t)`.
* The probabilistic layer (section `probabilistic`): property (ii) (`rightContinuous`),
  Lemma 3.7 (`ae_inOpenInterval`), property (i) (`almostEverywhereDefined`), the pointwise
  clause of Lemma 3.8 (`ae_eventually_processN_eq`) and the almost-sure convergence
  `Xⁿ → X` in `L¹_loc` (`ae_tendsto_pathClassN`), for `process Gs w Y E` on an arbitrary
  probability space carrying the paths `Y : Ω → ℕ → ℕ → V` and the unit holding times
  `E : Ω → (ℕ →₀ ℕ) → ℝ`.
* Convergence in law (section `law`): the paths of `Xⁿ` and `X` are random elements of
  `L¹_loc([0,∞), VG ∪ {∞})` with its Borel σ-algebra (`measurable_pathClassN`,
  `measurable_pathClass`), and their laws converge weakly (`tendsto_lawN`) — the form of
  Lemma 3.8 used for property (iv) on p. 25.

## Hypotheses carried, and who discharges them

* `Consistent Gs (Y ω)` a.s. — the coupling of Lemma 3.4 (`Coupling.lean`).
* `Monotone Gs`, `∀ x, ∃ n, x ∈ Gs n` — the exhaustion `G_n ↑ G` of Section 2.3.
* `HoldingTimesSummable Gs (Y ω) w (E ω)` a.s. — the conclusion (3.16) of Lemma 3.5, whose
  deterministic reductions are `IndexSet.holdingTimesSummable_of`.
* `Measurable Y`, `Measurable E` — the paths and holding times are random variables.
* `∀ x, 0 < w x` — the rate function of Theorem 1.6.
* `IndepFun (E · 0) (rest Y E) P` and `P.map (E · 0) ≪ volume.restrict (Ioi 0)` — the unit
  holding time `E_{ξ₀}` of the first element `ξ₀ = 0` of `Ξ` is independent of the paths and of
  the other holding times, with an absolutely continuous law supported on `(0, ∞)`: this is
  the paper's "conditionally independent, `T_ξ ~ Exponential(w(Y_ξ))`" for `ξ = ξ₀`, and it
  holds for the i.i.d. `Exponential(1)` family of `IndexSet.lean`'s module docstring
  (`expMeasure_absolutelyContinuous` supplies the second clause).  Only Lemma 3.7 and its
  consequences (property (i), the pointwise clause of Lemma 3.8) use these two.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

universe u

namespace ReflectedWalk.PathProperties

open IndexSet

variable {V : Type u}

/-! ### The deterministic layer -/

section deterministic

variable (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) (E : (ℕ →₀ ℕ) → ℝ)

/-- Nothing lies below the least element `ξ₀ = 0` of `Ξ`. -/
lemma below_zero : below Gs Y 0 = ∅ := by
  ext a
  simp only [below, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _ h
  exact absurd h (not_lt.mpr (zero_le_xi a))

/-- `τ_{ξ₀} = 0`: the clock (3.25) starts at zero. -/
lemma tau_zero : tau Gs Y w E 0 = 0 := by
  simp [tau, below_zero]

/-- Splitting off one point of an indicator sum. -/
lemma tsum_indicator_insert {S : Set (ℕ →₀ ℕ)} {a : ℕ →₀ ℕ} (ha : a ∉ S)
    (g : (ℕ →₀ ℕ) → ℝ≥0∞) :
    ∑' b, (insert a S).indicator g b = g a + ∑' b, S.indicator g b := by
  rw [Set.insert_eq, Set.indicator_union_of_disjoint (Set.disjoint_singleton_left.mpr ha)]
  simp only [ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_single a]
  · exact Set.indicator_of_mem (Set.mem_singleton a) _
  · intro b hb
    exact Set.indicator_of_notMem (fun hc => hb (Set.mem_singleton_iff.mp hc)) _

/-- `{ξ ∈ Ξ : ξ < η̂} = {ξ ∈ Ξ : ξ < η} ∪ {η}`, since nothing in `Ξ` lies strictly between `η`
and its successor (p. 23). -/
lemma below_succ (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) :
    below Gs Y (succ Gs Y η) = insert η (below Gs Y η) := by
  obtain ⟨_, hlt, hnone⟩ := h.succ_spec Gs Y hG hcov hη
  ext a
  simp only [below, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro ⟨ha, halt⟩
    rcases lt_trichotomy (toLex a) (toLex η) with h1 | h1 | h1
    · exact Or.inr ⟨ha, h1⟩
    · exact Or.inl (toLex_inj.mp h1)
    · exact absurd ⟨h1, halt⟩ (hnone a ha)
  · rintro (rfl | ⟨ha, halt⟩)
    · exact ⟨hη, hlt⟩
    · exact ⟨ha, halt.trans hlt⟩

/-- `τ_η̂ = τ_η + T_η`: the holding interval `[τ_η, τ_η̂)` of (3.26) has length `T_η` (used
implicitly throughout Section 3.3, e.g. in the proof of Lemma 3.8, "`X` is constant on
`[τ_η, τ_η̂)`"). -/
lemma tau_succ (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) :
    tau Gs Y w E (succ Gs Y η) = tau Gs Y w E η + holding Gs Y w E η := by
  have hnot : η ∉ below Gs Y η := fun hc => lt_irrefl _ hc.2
  unfold tau
  rw [below_succ Gs Y h hG hcov hη, tsum_indicator_insert hnot, add_comm]

/-- **Property (ii), deterministic core** (p. 24, "Property (ii): Right continuity").  If
`X_t ∈ VG` then `t ∈ [τ_ξ, τ_ξ̂)` for some `ξ ∈ Ξ`, and `X` is constant on that interval, so it
is constant on `[t, t + ε)` for `ε := τ_ξ̂ - t > 0`.  Holds for every sample path satisfying the
coupling identity (3.12). -/
theorem X_rightContinuous (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (t : ℝ≥0) (ht : ∃ x : V, X Gs Y w E t = some x) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Set.Ico t (t + ε), X Gs Y w E s = X Gs Y w E t := by
  obtain ⟨η, hη⟩ : ∃ η, InInterval Gs Y w E η t := by
    by_contra hc
    obtain ⟨x, hx⟩ := ht
    rw [(X_eq_none_iff Gs Y w E t).mpr hc] at hx
    exact absurd hx (by simp)
  rw [h.X_eq_of_inInterval Gs Y w E hG hcov hη]
  rcases eq_or_ne (tau Gs Y w E (succ Gs Y η)) ⊤ with htop | htop
  · refine ⟨1, one_pos, fun s hs => ?_⟩
    refine h.X_eq_of_inInterval Gs Y w E hG hcov ⟨hη.1, ?_, ?_⟩
    · exact le_trans hη.2.1 (ENNReal.coe_le_coe.mpr hs.1)
    · rw [htop]; exact ENNReal.coe_lt_top
  · have hbe : ((tau Gs Y w E (succ Gs Y η)).toNNReal : ℝ≥0∞) = tau Gs Y w E (succ Gs Y η) :=
      ENNReal.coe_toNNReal htop
    have htb : t < (tau Gs Y w E (succ Gs Y η)).toNNReal := by
      rw [← ENNReal.coe_lt_coe, hbe]; exact hη.2.2
    refine ⟨_ - t, tsub_pos_iff_lt.mpr htb, fun s hs => ?_⟩
    refine h.X_eq_of_inInterval Gs Y w E hG hcov ⟨hη.1, ?_, ?_⟩
    · exact le_trans hη.2.1 (ENNReal.coe_le_coe.mpr hs.1)
    · rw [← hbe, ENNReal.coe_lt_coe]
      have := hs.2
      rwa [add_tsub_cancel_of_le htb.le] at this

/-- **Lemma 3.6**, deterministic form: for `η ∈ Ξ` with `τ_η < ∞`,
`∑{T_ξ : ξ ∈ Ξ, ξ < η, Y_ξ ∉ G_n} → 0` as `n → ∞`.  (The paper writes `ξ ≤ η`; the term
`ξ = η` is `0` for `n` large, so the two forms agree.)  Dominated convergence: each `Y_ξ`
lies in some `G_n`, and the sum is dominated by `τ_η`.  The hypothesis `τ_η < ∞` is the
second clause of (3.16), Lemma 3.5. -/
theorem tendsto_tsum_notMem (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) (η : ℕ →₀ ℕ)
    (hτ : tau Gs Y w E η ≠ ⊤) :
    Tendsto (fun n => ∑' a, (below Gs Y η ∩ {a | Yxi Gs Y a ∉ Gs n}).indicator
      (holding Gs Y w E) a) atTop (𝓝 0) := by
  let _ : MeasurableSpace (ℕ →₀ ℕ) := ⊤
  have _ : MeasurableSingletonClass (ℕ →₀ ℕ) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have key := tendsto_lintegral_of_dominated_convergence (μ := Measure.count)
    (F := fun n a => (below Gs Y η ∩ {a | Yxi Gs Y a ∉ Gs n}).indicator (holding Gs Y w E) a)
    (f := fun _ => 0) ((below Gs Y η).indicator (holding Gs Y w E))
    (fun _ => measurable_from_top)
    (fun _ => Filter.Eventually.of_forall fun a =>
      Set.indicator_le_indicator_of_subset Set.inter_subset_left (fun _ => zero_le) a)
    (by rw [lintegral_count]; exact hτ)
    (Filter.Eventually.of_forall fun a => ?_)
  · simpa only [lintegral_count, lintegral_zero] using key
  · obtain ⟨m, hm⟩ := hcov (Yxi Gs Y a)
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨m, fun n hn => ?_⟩)
    exact (Set.indicator_of_notMem (fun hc => hc.2 (hG hn hm)) _).symm

/-! #### The interior of the holding intervals: Lemma 3.7, first paragraph -/

/-- `t ∈ (τ_η, τ_η̂)` for some `η ∈ Ξ` (written with `τ_η̂ = τ_η + T_η`): the time `t` lies in
the *interior* of a holding interval of (3.26).  This is the event of Lemma 3.7. -/
def InOpenInterval (t : ℝ≥0∞) : Prop :=
  ∃ η, Realized Gs Y η ∧ tau Gs Y w E η < t ∧ t < tau Gs Y w E η + holding Gs Y w E η

/-- `⨆_K τ_{[(0,K)]} = ∑_{ξ ∈ Ξ} T_ξ`: the level-`0` clocks exhaust the total time
(cofinality of the level-`0` elements, `lt_addr_zero_succ`). -/
lemma iSup_tau_addr_zero : ⨆ K, tau Gs Y w E (addr Gs Y 0 K) = totalTime Gs Y w E := by
  refine le_antisymm (iSup_le fun K => tau_le_totalTime Gs Y w E _) ?_
  unfold totalTime
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  refine le_trans ?_ (le_iSup (fun K => tau Gs Y w E (addr Gs Y 0 K))
    (s.sup (fun a : ℕ →₀ ℕ => a 0) + 1))
  unfold tau
  refine le_trans (Finset.sum_le_sum fun a ha => ?_) (ENNReal.sum_le_tsum s)
  by_cases hr : Realized Gs Y a
  · rw [Set.indicator_of_mem (show a ∈ realizedSet Gs Y from hr), Set.indicator_of_mem]
    refine ⟨hr, lt_of_lt_of_le (lt_addr_zero_succ Gs Y hr) ((addr_le_addr_iff Gs Y).mpr ?_)⟩
    exact Nat.succ_le_succ (Finset.le_sup (f := fun a : ℕ →₀ ℕ => a 0) ha)
  · rw [Set.indicator_of_notMem (show a ∉ realizedSet Gs Y from hr)]
    exact zero_le

/-- Under the first clause of (3.16), the level-`0` clocks are unbounded: every finite time is
exceeded by some `τ_{[(0,K)]}` (p. 23, "since `η` is arbitrary"). -/
lemma exists_lt_tau_addr_zero (htot : totalTime Gs Y w E = ⊤) {s : ℝ≥0∞} (hs : s ≠ ⊤) :
    ∃ K, s < tau Gs Y w E (addr Gs Y 0 K) := by
  have : s < ⨆ K, tau Gs Y w E (addr Gs Y 0 K) := by
    rw [iSup_tau_addr_zero, htot]; exact hs.lt_top
  exact lt_iSup_iff.mp this

/-- **Lemma 3.7, first paragraph**, for one clock: if `θ ∈ Ξ` and `τ_θ < ∞`, Lebesgue-a.e.
`s ∈ (0, τ_θ)` lies in the interior of a holding interval.  The intervals `[τ_ξ, τ_ξ̂)`,
`ξ < θ`, `Y_ξ ∈ G_n`, are disjoint subintervals of `[0, τ_θ)` of total length
`∑{T_ξ : ξ < θ, Y_ξ ∈ G_n}`; the part of `[0, τ_θ)` they leave uncovered has measure
`∑{T_ξ : ξ < θ, Y_ξ ∉ G_n} → 0` (Lemma 3.6); the endpoints `τ_ξ` are countably many. -/
theorem volume_notInOpenInterval_lt (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {θ : ℕ →₀ ℕ} (hθ : Realized Gs Y θ)
    (hτ : tau Gs Y w E θ ≠ ⊤) :
    volume {s : ℝ | 0 < s ∧ s < (tau Gs Y w E θ).toReal ∧
      ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} = 0 := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = (tau Gs Y w E θ).toReal := ⟨_, rfl⟩
  rw [← hT]
  have hfin' : ∀ ξ ∈ below Gs Y θ, tau Gs Y w E ξ ≠ ⊤ := fun ξ hξ =>
    ne_top_of_le_ne_top hτ (tau_mono Gs Y w E hξ.2.le)
  have hfin : ∀ ξ ∈ below Gs Y θ, tau Gs Y w E (succ Gs Y ξ) ≠ ⊤ := fun ξ hξ =>
    ne_top_of_le_ne_top hτ (h.tau_succ_le Gs Y w E hG hcov hξ.1 hθ hξ.2)
  -- the holding intervals, as subsets of `ℝ`
  obtain ⟨I, hI⟩ : ∃ I : (ℕ →₀ ℕ) → Set ℝ, ∀ ξ, I ξ =
      Set.Ico (tau Gs Y w E ξ).toReal (tau Gs Y w E (succ Gs Y ξ)).toReal := ⟨_, fun _ => rfl⟩
  have hmemI : ∀ ξ ∈ below Gs Y θ, ∀ s ∈ I ξ, InInterval Gs Y w E ξ (ENNReal.ofReal s) := by
    intro ξ hξ s hs
    rw [hI, Set.mem_Ico] at hs
    refine ⟨hξ.1, ?_, ?_⟩
    · exact (ENNReal.le_ofReal_iff_toReal_le (hfin' ξ hξ)
        (ENNReal.toReal_nonneg.trans hs.1)).mpr hs.1
    · exact (ENNReal.ofReal_lt_iff_lt_toReal (ENNReal.toReal_nonneg.trans hs.1)
        (hfin ξ hξ)).mpr hs.2
  have hdisj : ∀ ξ ∈ below Gs Y θ, ∀ ξ' ∈ below Gs Y θ, ξ ≠ ξ' → Disjoint (I ξ) (I ξ') := by
    intro ξ hξ ξ' hξ' hne
    rw [Set.disjoint_left]
    intro s hs hs'
    exact hne (h.inInterval_unique Gs Y w E hG hcov (hmemI ξ hξ s hs) (hmemI ξ' hξ' s hs'))
  have hlen : ∀ ξ ∈ below Gs Y θ, volume (I ξ) = holding Gs Y w E ξ := by
    intro ξ hξ
    rw [hI, Real.volume_Ico, tau_succ Gs Y w E h hG hcov hξ.1,
      ENNReal.toReal_add (hfin' ξ hξ) (holding_ne_top Gs Y w E ξ), add_sub_cancel_left,
      ENNReal.ofReal_toReal (holding_ne_top Gs Y w E ξ)]
  have hsubI : ∀ ξ ∈ below Gs Y θ, I ξ ⊆ Set.Ico 0 T := by
    intro ξ hξ s hs
    rw [hI, Set.mem_Ico] at hs
    refine ⟨ENNReal.toReal_nonneg.trans hs.1, lt_of_lt_of_le hs.2 ?_⟩
    rw [hT]
    exact ENNReal.toReal_mono hτ (h.tau_succ_le Gs Y w E hG hcov hξ.1 hθ hξ.2)
  -- the intervals with `Y_ξ ∈ G_n`
  obtain ⟨A, hA⟩ : ∃ A : ℕ → Set (ℕ →₀ ℕ), ∀ n, A n =
      below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∈ Gs n} := ⟨_, fun _ => rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : ℕ → (ℕ →₀ ℕ) → Set ℝ, ∀ n ξ, f n ξ = if ξ ∈ A n then I ξ else ∅ :=
    ⟨_, fun _ _ => rfl⟩
  have hf_meas : ∀ n ξ, MeasurableSet (f n ξ) := by
    intro n ξ
    rw [hf]
    split_ifs
    · rw [hI]; exact measurableSet_Ico
    · exact MeasurableSet.empty
  have hf_disj : ∀ n, Pairwise fun ξ ξ' => Disjoint (f n ξ) (f n ξ') := by
    intro n ξ ξ' hne
    simp only [hf]
    split_ifs with h1 h2
    · rw [hA] at h1 h2
      exact hdisj ξ h1.1 ξ' h2.1 hne
    · exact Set.disjoint_empty _
    · exact Set.empty_disjoint _
    · exact Set.empty_disjoint _
  have hU_vol : ∀ n, volume (⋃ ξ, f n ξ) = ∑' ξ, (A n).indicator (holding Gs Y w E) ξ := by
    intro n
    rw [measure_iUnion (hf_disj n) (hf_meas n)]
    refine tsum_congr fun ξ => ?_
    rw [hf]
    split_ifs with hξ
    · rw [Set.indicator_of_mem hξ]
      rw [hA] at hξ
      exact hlen ξ hξ.1
    · rw [Set.indicator_of_notMem hξ, measure_empty]
  have hU_sub : ∀ n, (⋃ ξ, f n ξ) ⊆ Set.Ico 0 T := by
    intro n
    refine Set.iUnion_subset fun ξ => ?_
    rw [hf]
    split_ifs with hξ
    · rw [hA] at hξ
      exact hsubI ξ hξ.1
    · exact Set.empty_subset _
  -- splitting `τ_θ` according to `Y_ξ ∈ G_n`
  have hsplit : ∀ n, tau Gs Y w E θ = ∑' ξ, (A n).indicator (holding Gs Y w E) ξ +
      ∑' ξ, (below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∉ Gs n}).indicator (holding Gs Y w E) ξ := by
    intro n
    rw [← ENNReal.tsum_add]
    unfold tau
    refine tsum_congr fun ξ => ?_
    have e : below Gs Y θ = A n ∪ (below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∉ Gs n}) := by
      rw [hA]
      ext ξ
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    have hd : Disjoint (A n) (below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∉ Gs n}) := by
      rw [hA, Set.disjoint_left]
      intro ξ h1 h2
      exact h2.2 h1.2
    conv_lhs => rw [e]
    rw [Set.indicator_union_of_disjoint hd]
  have hA_ne_top : ∀ n, ∑' ξ, (A n).indicator (holding Gs Y w E) ξ ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top hτ (by rw [hsplit n]; exact le_self_add)
  -- the uncovered part of `[0, T)`
  have hR : ∀ n, volume (Set.Ico 0 T \ ⋃ ξ, f n ξ) =
      ∑' ξ, (below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∉ Gs n}).indicator (holding Gs Y w E) ξ := by
    intro n
    rw [measure_sdiff (hU_sub n) (MeasurableSet.iUnion (hf_meas n)).nullMeasurableSet
      (by rw [hU_vol n]; exact hA_ne_top n), hU_vol n, Real.volume_Ico, sub_zero, hT,
      ENNReal.ofReal_toReal hτ, hsplit n]
    exact ENNReal.add_sub_cancel_left (hA_ne_top n)
  -- the uncovered set lies in the uncovered part of `[0,T)` together with the endpoints
  have hN : ∀ n, {s : ℝ | 0 < s ∧ s < T ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} ⊆
      (Set.Ico 0 T \ ⋃ ξ, f n ξ) ∪ Set.range (fun ξ => (tau Gs Y w E ξ).toReal) := by
    intro n s hs
    obtain ⟨hs0, hsT, hsn⟩ := hs
    by_cases hU : s ∈ ⋃ ξ, f n ξ
    · obtain ⟨ξ, hξ⟩ := Set.mem_iUnion.mp hU
      rw [hf] at hξ
      split_ifs at hξ with hξA
      · rw [hA] at hξA
        rw [hI, Set.mem_Ico] at hξ
        rcases eq_or_lt_of_le hξ.1 with heq | hlt
        · exact Or.inr ⟨ξ, heq⟩
        · exfalso
          apply hsn
          refine ⟨ξ, hξA.1.1, (ENNReal.lt_ofReal_iff_toReal_lt (hfin' ξ hξA.1)).mpr hlt, ?_⟩
          rw [← tau_succ Gs Y w E h hG hcov hξA.1.1]
          exact (ENNReal.ofReal_lt_iff_lt_toReal hs0.le (hfin ξ hξA.1)).mpr hξ.2
      · exact absurd hξ (Set.notMem_empty s)
    · exact Or.inl ⟨⟨hs0.le, hsT⟩, hU⟩
  have hle : ∀ n, volume {s : ℝ | 0 < s ∧ s < T ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} ≤
      ∑' ξ, (below Gs Y θ ∩ {ξ | Yxi Gs Y ξ ∉ Gs n}).indicator (holding Gs Y w E) ξ := by
    intro n
    calc volume {s : ℝ | 0 < s ∧ s < T ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)}
        ≤ volume ((Set.Ico 0 T \ ⋃ ξ, f n ξ) ∪
            Set.range (fun ξ => (tau Gs Y w E ξ).toReal)) := measure_mono (hN n)
      _ ≤ volume (Set.Ico 0 T \ ⋃ ξ, f n ξ) +
            volume (Set.range (fun ξ => (tau Gs Y w E ξ).toReal)) := measure_union_le _ _
      _ = _ := by rw [(Set.countable_range _).measure_zero, add_zero, hR n]
  exact le_antisymm (le_of_tendsto_of_tendsto' tendsto_const_nhds
    (tendsto_tsum_notMem Gs Y w E hG hcov θ hτ) hle) zero_le

/-- **Lemma 3.7, first paragraph**: under (3.16), Lebesgue-a.e. `t > 0` lies in the interior
of a holding interval of (3.26). -/
theorem volume_notInOpenInterval (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hsum : HoldingTimesSummable Gs Y w E) :
    volume {s : ℝ | 0 < s ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} = 0 := by
  have hsub : {s : ℝ | 0 < s ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} ⊆
      ⋃ K, {s : ℝ | 0 < s ∧ s < (tau Gs Y w E (addr Gs Y 0 K)).toReal ∧
        ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)} := by
    intro s hs
    obtain ⟨K, hK⟩ := exists_lt_tau_addr_zero Gs Y w E hsum.1 (s := ENNReal.ofReal s)
      ENNReal.ofReal_ne_top
    refine Set.mem_iUnion.mpr ⟨K, hs.1, ?_, hs.2⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal hs.1.le
      (hsum.2 _ (realized_addr Gs Y 0 K)).ne).mp hK
  exact measure_mono_null hsub (measure_iUnion_null fun K =>
    volume_notInOpenInterval_lt Gs Y w E h hG hcov (realized_addr Gs Y 0 K)
      (hsum.2 _ (realized_addr Gs Y 0 K)).ne)

/-! #### The dependence on the first holding time `T_{ξ₀}` (Lemma 3.7, second paragraph) -/

/-- `T_{ξ₀} = E_{ξ₀} / w(z)` when `E_{ξ₀}` is replaced by `x`. -/
lemma holding_update_zero (x : ℝ) :
    holding Gs Y w (Function.update E 0 x) 0 = ENNReal.ofReal (x / w (Y 0 0)) := by
  simp [holding, Yxi_zero]

/-- The other holding times do not see `E_{ξ₀}`. -/
lemma holding_update_of_ne (x : ℝ) {a : ℕ →₀ ℕ} (ha : a ≠ 0) :
    holding Gs Y w (Function.update E 0 x) a = holding Gs Y w E a := by
  simp [holding, Function.update_of_ne ha]

/-- An indicator sum over a set containing `ξ₀` splits as `T_{ξ₀}` plus a sum not involving
`E_{ξ₀}`. -/
lemma tsum_indicator_update_zero {S : Set (ℕ →₀ ℕ)} (hS : (0 : ℕ →₀ ℕ) ∈ S) (x : ℝ) :
    ∑' a, S.indicator (holding Gs Y w (Function.update E 0 x)) a =
      ENNReal.ofReal (x / w (Y 0 0)) + ∑' a, (S \ {0}).indicator (holding Gs Y w E) a := by
  have hS' : S = insert 0 (S \ {0}) :=
    (Set.insert_sdiff_singleton.trans (Set.insert_eq_of_mem hS)).symm
  have h0 : (0 : ℕ →₀ ℕ) ∉ S \ {0} := fun hc => hc.2 (Set.mem_singleton 0)
  conv_lhs => rw [hS']
  rw [tsum_indicator_insert h0, holding_update_zero]
  congr 1
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ S \ {0}
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha,
      holding_update_of_ne Gs Y w E x (fun hc => ha.2 (Set.mem_singleton_iff.mpr hc))]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- `τ_η = T_{ξ₀} + (τ_η with E_{ξ₀} := 0)` for `η > ξ₀`: shifting `T_{ξ₀}` shifts every
later clock (p. 23, "the laws of `{τ_ξ}` and `{τ_ξ + U}` are mutually absolutely continuous"). -/
lemma tau_update_zero (x : ℝ) {η : ℕ →₀ ℕ} (hη : toLex (0 : ℕ →₀ ℕ) < toLex η) :
    tau Gs Y w (Function.update E 0 x) η =
      ENNReal.ofReal (x / w (Y 0 0)) + tau Gs Y w (Function.update E 0 0) η := by
  have h0 : (0 : ℕ →₀ ℕ) ∈ below Gs Y η := ⟨realized_zero Gs Y, hη⟩
  unfold tau
  rw [tsum_indicator_update_zero Gs Y w E h0 x, tsum_indicator_update_zero Gs Y w E h0 0,
    zero_div, ENNReal.ofReal_zero, zero_add]

/-- The total time (3.16) shifts by `T_{ξ₀}` in the same way. -/
lemma totalTime_update_zero (x : ℝ) :
    totalTime Gs Y w (Function.update E 0 x) =
      ENNReal.ofReal (x / w (Y 0 0)) + totalTime Gs Y w (Function.update E 0 0) := by
  have h0 : (0 : ℕ →₀ ℕ) ∈ realizedSet Gs Y := realized_zero Gs Y
  unfold totalTime
  rw [tsum_indicator_update_zero Gs Y w E h0 x, tsum_indicator_update_zero Gs Y w E h0 0,
    zero_div, ENNReal.ofReal_zero, zero_add]

/-- (3.16) does not depend on the value of `E_{ξ₀}`. -/
lemma holdingTimesSummable_update_zero_iff (x : ℝ) :
    HoldingTimesSummable Gs Y w (Function.update E 0 x) ↔
      HoldingTimesSummable Gs Y w (Function.update E 0 0) := by
  unfold HoldingTimesSummable
  rw [totalTime_update_zero Gs Y w E x, ENNReal.add_eq_top, or_iff_right ENNReal.ofReal_ne_top]
  refine and_congr Iff.rfl (forall_congr' fun η => imp_congr Iff.rfl ?_)
  rcases eq_or_lt_of_le (zero_le_xi η) with h0 | h0
  · have : η = 0 := (toLex_inj.mp h0).symm
    subst this
    simp [tau_zero]
  · rw [tau_update_zero Gs Y w E x h0, ENNReal.add_lt_top, and_iff_right ENNReal.ofReal_lt_top]

/-- **Lemma 3.7, second paragraph, deterministic content.**  Fix the paths and all holding
times but `T_{ξ₀}`, with (3.12) and (3.16), and fix `t > 0`.  Then the set of values `x > 0` of
`E_{ξ₀}` for which `t` is *not* interior to a holding interval is Lebesgue-null: for
`x / w(z) < t` the event is the event that `t - x / w(z)` is not interior to a holding
interval of the process with `T_{ξ₀} = 0`, which is null in `t - x / w(z)` by
`volume_notInOpenInterval`, and the affine change of variables preserves null sets. -/
theorem volume_notInOpenInterval_update (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hsum : HoldingTimesSummable Gs Y w E) (hE0 : E 0 = 0)
    (hc : 0 < w (Y 0 0)) {t : ℝ} (ht : 0 < t) :
    volume {x : ℝ | 0 < x ∧
      ¬ InOpenInterval Gs Y w (Function.update E 0 x) (ENNReal.ofReal t)} = 0 := by
  have hE : Function.update E 0 0 = E := by rw [← hE0]; exact Function.update_eq_self 0 E
  have hN := volume_notInOpenInterval Gs Y w E h hG hcov hsum
  have hpre : volume ((fun x : ℝ => t - x / w (Y 0 0)) ⁻¹'
      {u : ℝ | 0 < u ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal u)}) = 0 := by
    have e : (fun x : ℝ => t - x / w (Y 0 0)) =
        (fun y => t + y) ∘ (fun x => (-(w (Y 0 0))⁻¹) * x) := by
      funext x; simp only [Function.comp]; ring
    rw [e, Set.preimage_comp, Real.volume_preimage_mul_left (neg_ne_zero.mpr (inv_ne_zero hc.ne')),
      measure_preimage_add, hN, mul_zero]
  refine measure_mono_null (t := {w (Y 0 0) * t} ∪ (fun x : ℝ => t - x / w (Y 0 0)) ⁻¹'
    {u : ℝ | 0 < u ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal u)}) ?_
    (measure_union_null Real.volume_singleton hpre)
  intro x hx
  obtain ⟨hx0, hxn⟩ := hx
  -- since `ξ₀` does not cover `t`, `x / w(z) ≤ t`
  have hle : x / w (Y 0 0) ≤ t := by
    by_contra hlt
    push Not at hlt
    apply hxn
    refine ⟨0, realized_zero Gs Y, ?_, ?_⟩
    · rw [tau_zero]; exact ENNReal.ofReal_pos.mpr ht
    · rw [tau_zero, zero_add, holding_update_zero]
      exact (ENNReal.ofReal_lt_ofReal_iff (lt_trans ht hlt)).mpr hlt
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact Or.inl (by rw [Set.mem_singleton_iff, (div_eq_iff hc.ne').mp heq, mul_comm])
  · refine Or.inr ⟨sub_pos.mpr hlt, fun hu => hxn ?_⟩
    obtain ⟨η, hη, h1, h2⟩ := hu
    have hη0 : toLex (0 : ℕ →₀ ℕ) < toLex η := by
      rcases eq_or_lt_of_le (zero_le_xi η) with h0 | h0
      · exfalso
        have : η = 0 := (toLex_inj.mp h0).symm
        subst this
        rw [tau_zero, zero_add] at h2
        have : holding Gs Y w E 0 = 0 := by simp [holding, Yxi_zero, hE0]
        rw [this] at h2
        exact absurd h2 (not_lt.mpr zero_le)
      · exact h0
    have hadd : ENNReal.ofReal (x / w (Y 0 0)) + ENNReal.ofReal (t - x / w (Y 0 0)) =
        ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add (div_nonneg hx0.le hc.le) (sub_pos.mpr hlt).le]
      congr 1; ring
    refine ⟨η, hη, ?_, ?_⟩
    · rw [tau_update_zero Gs Y w E x hη0, hE, ← hadd]
      exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mpr h1
    · rw [tau_update_zero Gs Y w E x hη0, hE,
        holding_update_of_ne Gs Y w E x (fun h0 => by subst h0; exact lt_irrefl _ hη0),
        add_assoc, ← hadd]
      exact (ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top).mpr h2

/-! #### Interior points at `t = 0` -/

/-- `0 ∈ [τ_{ξ₀}, τ_{ξ̂₀}) = [0, T_{ξ₀})` as soon as `E_{ξ₀} > 0`. -/
lemma inInterval_zero (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hw : 0 < w (Y 0 0)) (hp : 0 < E 0) : InInterval Gs Y w E 0 (0 : ℝ≥0) := by
  refine ⟨realized_zero _ _, by rw [tau_zero]; exact le_rfl, ?_⟩
  rw [tau_succ Gs Y w E h hG hcov (realized_zero _ _), tau_zero, zero_add]
  simp only [holding, Yxi_zero]
  exact ENNReal.ofReal_pos.mpr (div_pos hp hw)

/-! #### The processes `Xⁿ` of (3.15) and Lemma 3.8 -/

/-- The level-`n` clock `∑_{i<k} T_{[(n,i)]}` of (3.15): the left endpoint of the `k`-th holding
interval of `Xⁿ`. -/
noncomputable def levelTau (n k : ℕ) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range k, holding Gs Y w E (addr Gs Y n i)

lemma levelTau_succ (n k : ℕ) :
    levelTau Gs Y w E n (k + 1) = levelTau Gs Y w E n k + holding Gs Y w E (addr Gs Y n k) :=
  Finset.sum_range_succ _ _

lemma levelTau_mono (n : ℕ) : Monotone (levelTau Gs Y w E n) := by
  refine monotone_nat_of_le_succ fun k => ?_
  rw [levelTau_succ]; exact le_self_add

/-- `t ∈ [∑_{i<k} T_{[(n,i)]}, ∑_{i≤k} T_{[(n,i)]})`, the `k`-th holding interval of (3.15). -/
def InLevelInterval (n k : ℕ) (t : ℝ≥0∞) : Prop :=
  levelTau Gs Y w E n k ≤ t ∧ t < levelTau Gs Y w E n (k + 1)

/-- The holding intervals of (3.15) are pairwise disjoint. -/
lemma inLevelInterval_unique {n k k' : ℕ} {t : ℝ≥0∞} (h1 : InLevelInterval Gs Y w E n k t)
    (h2 : InLevelInterval Gs Y w E n k' t) : k = k' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (lt_of_lt_of_le h1.2 (le_trans (levelTau_mono Gs Y w E n hlt) h2.1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le h2.2 (le_trans (levelTau_mono Gs Y w E n hlt) h1.1)) (lt_irrefl _)

open Classical in
/-- **(3.15)**: the continuous-time version `Xⁿ` of `Yⁿ`, `Xⁿ_t := Yⁿ_k` for
`t ∈ [∑_{i<k} T_{[(n,i)]}, ∑_{i≤k} T_{[(n,i)]})`; `∞` (`none`) if `t` lies in no such interval
(a null event, since `∑_i T_{[(n,i)]} = ∞` a.s.). -/
noncomputable def Xn (n : ℕ) (t : ℝ≥0) : Option V :=
  if h : ∃ k, InLevelInterval Gs Y w E n k t then some (Y n (Classical.choose h)) else none

lemma Xn_eq_of_inLevelInterval {n k : ℕ} {t : ℝ≥0} (hk : InLevelInterval Gs Y w E n k t) :
    Xn Gs Y w E n t = some (Y n k) := by
  unfold Xn
  rw [dite_eq_left ⟨k, hk⟩]
  exact congrArg (fun k => some (Y n k)) (inLevelInterval_unique Gs Y w E
    (Classical.choose_spec (⟨k, hk⟩ : ∃ k, InLevelInterval Gs Y w E n k t)) hk)

lemma Xn_eq_none_iff (n : ℕ) (t : ℝ≥0) :
    Xn Gs Y w E n t = none ↔ ¬ ∃ k, InLevelInterval Gs Y w E n k t := by
  unfold Xn
  split_ifs with hx <;> simp [hx]

/-- The remainder `Rⁿ` of (3.29): the time before `η` spent at the `ξ ∈ Ξ` without a level-`n`
representative. -/
noncomputable def remainder (n : ℕ) (η : ℕ →₀ ℕ) : ℝ≥0∞ :=
  ∑' a, (below Gs Y η \ Set.range (addr Gs Y n)).indicator (holding Gs Y w E) a

/-- `0 ≤ Rⁿ ≤ ∑{T_ξ : ξ < η, Y_ξ ∉ G_n}` (p. 24): by (3.14), a class without level-`n`
representative has `Y_ξ ∉ G_n`. -/
lemma remainder_le (h : Consistent Gs Y) (hG : Monotone Gs) (n : ℕ) (η : ℕ →₀ ℕ) :
    remainder Gs Y w E n η ≤
      ∑' a, (below Gs Y η ∩ {a | Yxi Gs Y a ∉ Gs n}).indicator (holding Gs Y w E) a :=
  have hsub : below Gs Y η \ Set.range (addr Gs Y n) ⊆
      below Gs Y η ∩ {a | Yxi Gs Y a ∉ Gs n} :=
    fun _ ha => ⟨ha.1, fun hmem => ha.2 (h.exists_addr_eq_of_mem Gs Y hG ha.1.1 hmem)⟩
  ENNReal.tsum_le_tsum fun a => Set.indicator_le_indicator_of_subset hsub (fun _ => zero_le) a

/-- **(3.29)**: `τ_{[(n,j)]} = ∑_{i<j} T_{[(n,i)]} + Rⁿ`. -/
lemma tau_eq_levelTau_add (n j : ℕ) :
    tau Gs Y w E (addr Gs Y n j) =
      levelTau Gs Y w E n j + remainder Gs Y w E n (addr Gs Y n j) := by
  have e : below Gs Y (addr Gs Y n j) =
      (((Finset.range j).image (addr Gs Y n) : Finset (ℕ →₀ ℕ)) : Set (ℕ →₀ ℕ)) ∪
        (below Gs Y (addr Gs Y n j) \ Set.range (addr Gs Y n)) := by
    ext a
    simp only [Set.mem_union, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      Set.mem_sdiff, Set.mem_range, below, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨ha, halt⟩
      by_cases hr : ∃ i, addr Gs Y n i = a
      · obtain ⟨i, rfl⟩ := hr
        exact Or.inl ⟨i, (addr_lt_addr_iff Gs Y).mp halt, rfl⟩
      · exact Or.inr ⟨⟨ha, halt⟩, hr⟩
    · rintro (⟨i, hi, rfl⟩ | ⟨ha, -⟩)
      · exact ⟨realized_addr Gs Y n i, (addr_lt_addr_iff Gs Y).mpr hi⟩
      · exact ha
  have hd : Disjoint (((Finset.range j).image (addr Gs Y n) : Finset (ℕ →₀ ℕ)) : Set (ℕ →₀ ℕ))
      (below Gs Y (addr Gs Y n j) \ Set.range (addr Gs Y n)) := by
    rw [Set.disjoint_left]
    intro a ha hb
    rw [Finset.coe_image] at ha
    obtain ⟨i, -, rfl⟩ := ha
    exact hb.2 ⟨i, rfl⟩
  unfold tau remainder
  conv_lhs => rw [e, Set.indicator_union_of_disjoint hd]
  simp only [ENNReal.tsum_add]
  congr 1
  rw [tsum_eq_sum (s := (Finset.range j).image (addr Gs Y n))
    (fun a ha => Set.indicator_of_notMem ha _),
    Finset.sum_image (fun i _ i' _ hii' => addr_injective Gs Y n hii')]
  exact Finset.sum_congr rfl fun i hi =>
    Set.indicator_of_mem (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hi)) _

/-- The right endpoint: `τ_{[(n,j)]^} = ∑_{i≤j} T_{[(n,i)]} + Rⁿ`. -/
lemma tau_succ_eq_levelTau_add (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (n j : ℕ) :
    tau Gs Y w E (succ Gs Y (addr Gs Y n j)) =
      levelTau Gs Y w E n (j + 1) + remainder Gs Y w E n (addr Gs Y n j) := by
  rw [tau_succ Gs Y w E h hG hcov (realized_addr Gs Y n j), tau_eq_levelTau_add, levelTau_succ,
    add_right_comm]

/-- **Lemma 3.8, the core of (3.28)–(3.29)**: if `t ∈ [τ_η, τ_η̂)` with `η = [(n, j)]` and
`t + Rⁿ < τ_η̂`, then `t` lies in the `j`-th holding interval of `Xⁿ`, so `Xⁿ_t = Yⁿ_j = X_t`. -/
theorem Xn_eq_X (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    {n j : ℕ} {t : ℝ≥0} (ht : InInterval Gs Y w E (addr Gs Y n j) t)
    (hR : (t : ℝ≥0∞) + remainder Gs Y w E n (addr Gs Y n j) <
      tau Gs Y w E (succ Gs Y (addr Gs Y n j))) :
    Xn Gs Y w E n t = X Gs Y w E t := by
  have hRne : remainder Gs Y w E n (addr Gs Y n j) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ne_top_of_le_ne_top ENNReal.coe_ne_top ht.2.1) ?_
    rw [tau_eq_levelTau_add]; exact le_add_self
  rw [h.X_eq_of_inInterval Gs Y w E hG hcov ht, h.Yxi_addr]
  refine Xn_eq_of_inLevelInterval Gs Y w E ⟨?_, ?_⟩
  · refine le_trans ?_ ht.2.1
    rw [tau_eq_levelTau_add]; exact le_self_add
  · rw [tau_succ_eq_levelTau_add Gs Y w E h hG hcov] at hR
    exact (ENNReal.add_lt_add_iff_right hRne).mp hR

/-- **Lemma 3.8, (3.28)**: for `η ∈ Ξ` with `τ_η < ∞` and any `s < τ_η̂`, for all large `n`
(how large depends on `η` and `s`) `Xⁿ_t = X_t` for every `t ∈ [τ_η, s]`.  Every compact
`K ⊆ [τ_η, τ_η̂)` lies in such a `[τ_η, s]`.  Uses Lemma 3.6 through `remainder_le`. -/
theorem eventually_Xn_eq_X (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) (hτ : tau Gs Y w E η ≠ ⊤) {s : ℝ≥0∞}
    (hs : s < tau Gs Y w E (succ Gs Y η)) :
    ∀ᶠ n in atTop, ∀ t : ℝ≥0, tau Gs Y w E η ≤ t → (t : ℝ≥0∞) ≤ s →
      Xn Gs Y w E n t = X Gs Y w E t := by
  obtain ⟨δ, hδ, hsδ⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp hs
  have hev : ∀ᶠ n in atTop, ∑' a, (below Gs Y η ∩ {a | Yxi Gs Y a ∉ Gs n}).indicator
      (holding Gs Y w E) a < δ :=
    (tendsto_order.1 (tendsto_tsum_notMem Gs Y w E hG hcov η hτ)).2 _ (ENNReal.coe_pos.mpr hδ)
  obtain ⟨m, hm⟩ := hcov (Yxi Gs Y η)
  filter_upwards [hev, Filter.eventually_ge_atTop m] with n hn hmn t ht1 ht2
  obtain ⟨j, rfl⟩ := h.exists_addr_eq_of_mem Gs Y hG hη (hG hmn hm)
  refine Xn_eq_X Gs Y w E h hG hcov ⟨hη, ht1, lt_of_le_of_lt ht2 hs⟩ ?_
  calc (t : ℝ≥0∞) + remainder Gs Y w E n (addr Gs Y n j) ≤ s + δ :=
        add_le_add ht2 (le_trans (remainder_le Gs Y w E h hG n _) hn.le)
    _ < _ := hsδ

/-- **Lemma 3.8, pointwise clause, deterministic core**: if `t ∈ [τ_η, τ_η̂)` for some
`η ∈ Ξ` (which by Lemma 3.7 holds a.s. for each fixed `t`), then `Xⁿ_t = X_t` for all large `n`. -/
theorem eventually_Xn_eq_X_of_inInterval (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {t : ℝ≥0} {η : ℕ →₀ ℕ} (hη : InInterval Gs Y w E η t) :
    ∀ᶠ n in atTop, Xn Gs Y w E n t = X Gs Y w E t := by
  have hτ : tau Gs Y w E η ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hη.2.1
  filter_upwards [eventually_Xn_eq_X Gs Y w E h hG hcov hη.1 hτ hη.2.2] with n hn
  exact hn t hη.2.1 le_rfl


/-- The fibre of `∞`, as the complement of the fibres of the vertices. -/
lemma preimage_none_eq_compl_iUnion {α : Type*} (F : α → Option V) :
    F ⁻¹' {none} = (⋃ x, F ⁻¹' {some x})ᶜ := by
  ext a
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
    not_exists]
  generalize F a = o
  cases o <;> simp

/-- `X_t = x` iff `t ∈ [τ_η, τ_η̂)` for some `η ∈ Ξ` with `Y_η = x` (with `τ_η̂ = τ_η + T_η`). -/
lemma X_eq_some_iff (h : Consistent Gs Y) (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (t : ℝ≥0) (x : V) :
    X Gs Y w E t = some x ↔ ∃ η, Realized Gs Y η ∧ tau Gs Y w E η ≤ t ∧
      (t : ℝ≥0∞) < tau Gs Y w E η + holding Gs Y w E η ∧ Yxi Gs Y η = x := by
  constructor
  · intro ht
    obtain ⟨η, hη⟩ : ∃ η, InInterval Gs Y w E η t := by
      by_contra hn
      rw [(X_eq_none_iff _ _ _ _ _).mpr hn] at ht
      exact absurd ht (by simp)
    rw [h.X_eq_of_inInterval _ _ _ _ hG hcov hη] at ht
    refine ⟨η, hη.1, hη.2.1, ?_, Option.some_injective V ht⟩
    rw [← tau_succ _ _ _ _ h hG hcov hη.1]; exact hη.2.2
  · rintro ⟨η, hη, h1, h2, hx⟩
    rw [h.X_eq_of_inInterval _ _ _ _ hG hcov ⟨hη, h1, by rwa [tau_succ _ _ _ _ h hG hcov hη]⟩, hx]

/-- `Xⁿ_t = x` iff `t` lies in the `k`-th holding interval of (3.15) for some `k` with
`Yⁿ_k = x`. -/
lemma Xn_eq_some_iff (n : ℕ) (t : ℝ≥0) (x : V) :
    Xn Gs Y w E n t = some x ↔ ∃ k, levelTau Gs Y w E n k ≤ t ∧
      (t : ℝ≥0∞) < levelTau Gs Y w E n (k + 1) ∧ Y n k = x := by
  constructor
  · intro ht
    obtain ⟨k, hk⟩ : ∃ k, InLevelInterval Gs Y w E n k t := by
      by_contra hn
      rw [(Xn_eq_none_iff _ _ _ _ _ _).mpr hn] at ht
      exact absurd ht (by simp)
    rw [Xn_eq_of_inLevelInterval _ _ _ _ hk] at ht
    exact ⟨k, hk.1, hk.2, Option.some_injective V ht⟩
  · rintro ⟨k, h1, h2, hx⟩
    rw [Xn_eq_of_inLevelInterval _ _ _ _ ⟨h1, h2⟩, hx]

/-! #### The paths as elements of `L¹_loc([0,∞), VG ∪ {∞})` -/

section pathSpaceDet

variable [Countable V]

/-- The fibres of `t ↦ X_{t⁺}` (with `X` read at `max t 0`) are Borel subsets of `ℝ`, for a
sample with (3.12): each is a countable union of intervals `[τ_η, τ_η̂)`. -/
lemma measurableSet_X_toNNReal_fiber (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (o : Option V) :
    MeasurableSet ((fun t : ℝ => X Gs Y w E (Real.toNNReal t)) ⁻¹' {o}) := by
  have hsome : ∀ x : V, (fun t : ℝ => X Gs Y w E (Real.toNNReal t)) ⁻¹' {some x} =
      ⋃ η, ({t : ℝ | tau Gs Y w E η ≤ ENNReal.ofReal t} ∩
        {t : ℝ | ENNReal.ofReal t < tau Gs Y w E η + holding Gs Y w E η}) ∩
        {_t : ℝ | Realized Gs Y η ∧ Yxi Gs Y η = x} := by
    intro x
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro ht
      obtain ⟨η, hη⟩ : ∃ η, InInterval Gs Y w E η (Real.toNNReal t) := by
        by_contra hn
        rw [(X_eq_none_iff _ _ _ _ _).mpr hn] at ht
        exact absurd ht (by simp)
      rw [h.X_eq_of_inInterval _ _ _ _ hG hcov hη] at ht
      refine ⟨η, ⟨hη.2.1, ?_⟩, hη.1, Option.some_injective V ht⟩
      rw [← tau_succ _ _ _ _ h hG hcov hη.1]; exact hη.2.2
    · rintro ⟨η, ⟨h1, h2⟩, hη, hx⟩
      rw [h.X_eq_of_inInterval _ _ _ _ hG hcov ⟨hη, h1, by rwa [tau_succ _ _ _ _ h hG hcov hη]⟩, hx]
  have hmeas : ∀ x : V, MeasurableSet ((fun t : ℝ => X Gs Y w E (Real.toNNReal t)) ⁻¹' {some x}) := by
    intro x
    rw [hsome x]
    refine MeasurableSet.iUnion fun η => ((?_ : MeasurableSet _).inter ?_).inter (MeasurableSet.const _)
    · exact ENNReal.measurable_ofReal measurableSet_Ici
    · exact ENNReal.measurable_ofReal measurableSet_Iio
  cases o with
  | none =>
    have e : (fun t : ℝ => X Gs Y w E (Real.toNNReal t)) ⁻¹' {none} =
        (⋃ x, (fun t : ℝ => X Gs Y w E (Real.toNNReal t)) ⁻¹' {some x})ᶜ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        not_exists]
      generalize X Gs Y w E (Real.toNNReal t) = o
      cases o <;> simp
    rw [e]
    exact (MeasurableSet.iUnion hmeas).compl
  | some x => exact hmeas x

/-- The fibres of `t ↦ Xⁿ_{t⁺}` are Borel subsets of `ℝ`, for every sample. -/
lemma measurableSet_Xn_toNNReal_fiber (n : ℕ) (o : Option V) :
    MeasurableSet ((fun t : ℝ => Xn Gs Y w E n (Real.toNNReal t)) ⁻¹' {o}) := by
  have hsome : ∀ x : V, (fun t : ℝ => Xn Gs Y w E n (Real.toNNReal t)) ⁻¹' {some x} =
      ⋃ k, ({t : ℝ | levelTau Gs Y w E n k ≤ ENNReal.ofReal t} ∩
        {t : ℝ | ENNReal.ofReal t < levelTau Gs Y w E n (k + 1)}) ∩ {_t : ℝ | Y n k = x} := by
    intro x
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro ht
      obtain ⟨k, hk⟩ : ∃ k, InLevelInterval Gs Y w E n k (Real.toNNReal t) := by
        by_contra hn
        rw [(Xn_eq_none_iff _ _ _ _ _ _).mpr hn] at ht
        exact absurd ht (by simp)
      rw [Xn_eq_of_inLevelInterval _ _ _ _ hk] at ht
      exact ⟨k, ⟨hk.1, hk.2⟩, Option.some_injective V ht⟩
    · rintro ⟨k, ⟨h1, h2⟩, hx⟩
      rw [Xn_eq_of_inLevelInterval _ _ _ _ ⟨h1, h2⟩, hx]
  have hmeas : ∀ x : V,
      MeasurableSet ((fun t : ℝ => Xn Gs Y w E n (Real.toNNReal t)) ⁻¹' {some x}) := by
    intro x
    rw [hsome x]
    refine MeasurableSet.iUnion fun k => ((?_ : MeasurableSet _).inter ?_).inter (MeasurableSet.const _)
    · exact ENNReal.measurable_ofReal measurableSet_Ici
    · exact ENNReal.measurable_ofReal measurableSet_Iio
  cases o with
  | none =>
    have e : (fun t : ℝ => Xn Gs Y w E n (Real.toNNReal t)) ⁻¹' {none} =
        (⋃ x, (fun t : ℝ => Xn Gs Y w E n (Real.toNNReal t)) ⁻¹' {some x})ᶜ := by
      ext t
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        not_exists]
      generalize Xn Gs Y w E n (Real.toNNReal t) = o
      cases o <;> simp
    rw [e]
    exact (MeasurableSet.iUnion hmeas).compl
  | some x => exact hmeas x

/-- **Lemma 3.8 in `L¹_loc`, deterministic core**: for a sample with (3.12) and (3.16),
`∫₀^∞ e^{-t} 1_{Xⁿ_t ≠ X_t} dt → 0`, i.e. `Xⁿ → X` for the metric (3.30).  For Lebesgue-a.e.
`t > 0`, `t` is interior to a holding interval (`volume_notInOpenInterval`), so `Xⁿ_t = X_t`
for all large `n` (`eventually_Xn_eq_X_of_inInterval`); dominated convergence for the finite
measure `e^{-t} dt`. -/
theorem tendsto_expMeasure_Xn_ne_X (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hsum : HoldingTimesSummable Gs Y w E) :
    Tendsto (fun n => ReflectedWalk.expMeasure
      {t : ℝ | Xn Gs Y w E n (Real.toNNReal t) ≠ X Gs Y w E (Real.toNNReal t)}) atTop (𝓝 0) := by
  have hmeas : ∀ n, MeasurableSet
      {t : ℝ | Xn Gs Y w E n (Real.toNNReal t) ≠ X Gs Y w E (Real.toNNReal t)} := fun n =>
    L1loc.measurableSet_ne_of_fibers (measurableSet_Xn_toNNReal_fiber Gs Y w E n)
      (measurableSet_X_toNNReal_fiber Gs Y w E h hG hcov)
  have key := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (μ := ReflectedWalk.expMeasure)
    atTop (A := (∅ : Set ℝ)) MeasurableSet.empty hmeas ?_
  · rwa [measure_empty] at key
  rw [ae_expMeasure_iff, ae_restrict_iff' measurableSet_Ioi]
  have hN : ∀ᵐ s ∂(volume : Measure ℝ),
      ¬ (0 < s ∧ ¬ InOpenInterval Gs Y w E (ENNReal.ofReal s)) := by
    rw [ae_iff]
    simp only [not_not]
    exact volume_notInOpenInterval Gs Y w E h hG hcov hsum
  filter_upwards [hN] with t ht htpos
  obtain ⟨η, hη, h1, h2⟩ : InOpenInterval Gs Y w E (ENNReal.ofReal t) := by
    by_contra hc; exact ht ⟨htpos, hc⟩
  have hI : InInterval Gs Y w E η (Real.toNNReal t) :=
    ⟨hη, h1.le, by rw [tau_succ _ _ _ _ h hG hcov hη]; exact h2⟩
  filter_upwards [eventually_Xn_eq_X_of_inInterval Gs Y w E h hG hcov hI] with n hn
  simp only [Set.mem_empty_iff_false, iff_false, not_not]
  exact hn

end pathSpaceDet

end deterministic

/-! ### The process (3.26) as a stochastic process -/

section process

variable {Ω : Type u} (Gs : ℕ → Set V) (w : V → ℝ) (Y : Ω → ℕ → ℕ → V) (E : Ω → (ℕ →₀ ℕ) → ℝ)

open Classical in
/-- The process (3.26) as a stochastic process: `process Gs w Y E t ω` is `X_t` computed from
the sample paths `Y ω` and the unit holding times `E ω`, set to `∞` (`none`) on the null
event where the coupling identity (3.12) fails, so that each `X_t` is measurable
(`measurable_process`). -/
noncomputable def process (t : ℝ≥0) (ω : Ω) : Option V :=
  if Consistent Gs (Y ω) then X Gs (Y ω) w (E ω) t else none

lemma process_of_consistent {ω : Ω} (hω : Consistent Gs (Y ω)) (t : ℝ≥0) :
    process Gs w Y E t ω = X Gs (Y ω) w (E ω) t := by
  simp only [process, hω, ite_true]

end process

/-! ### Measurability of the deterministic constructions in the sample -/

section measurability

variable [MeasurableSpace V]
variable {Ω : Type u} [MeasurableSpace Ω]
variable (Gs : ℕ → Set V) (w : V → ℝ) {Y : Ω → ℕ → ℕ → V} {E : Ω → (ℕ →₀ ℕ) → ℝ}

lemma measurable_eval_pair : Measurable fun q : (ℕ → V) × ℕ => q.1 q.2 :=
  measurable_from_prod_countable_left fun k => measurable_pi_apply k

lemma measurable_coarsen_pair {S : Set V} (hS : MeasurableSet S) :
    Measurable fun q : (ℕ → V) × ℕ => coarsen S q.1 q.2 :=
  measurable_from_prod_countable_left fun k => measurable_coarsen hS k

/-- The excursion index `coarsenPred` is a measurable function of the path. -/
lemma measurable_coarsenPred {S : Set V} (hS : MeasurableSet S) (j : ℕ) :
    Measurable fun p : ℕ → V => coarsenPred S p j := by
  refine measurable_to_countable' fun k => ?_
  have e : (fun p : ℕ → V => coarsenPred S p j) ⁻¹' {k} =
      {p | coarsen S p k ≤ j} ∩ {p | j < coarsen S p (k + 1)} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro rfl
      exact ⟨coarsen_coarsenPred_le S p j, lt_coarsen_coarsenPred_succ S p j⟩
    · rintro ⟨h1, h2⟩
      exact coarsenPred_eq_of_le_of_lt S p h1 h2
  rw [e]
  exact ((measurable_coarsen hS k) (show MeasurableSet {m : ℕ | m ≤ j} from
      (Set.to_countable _).measurableSet)).inter
    ((measurable_coarsen hS (k + 1)) (show MeasurableSet {m : ℕ | j < m} from
      (Set.to_countable _).measurableSet))

lemma measurable_Y_level (hY : Measurable Y) (n : ℕ) : Measurable fun ω => Y ω n :=
  (measurable_pi_apply n).comp hY

variable [MeasurableSingletonClass V] [Countable V]

lemma measurableSet_Gs (n : ℕ) : MeasurableSet (Gs n) := (Set.to_countable _).measurableSet

lemma measurable_Jstep (hY : Measurable Y) (n : ℕ) {g : Ω → ℕ} (hg : Measurable g) :
    Measurable fun ω => Jstep Gs (Y ω) n (g ω) :=
  (measurable_coarsen_pair (measurableSet_Gs Gs n)).comp ((measurable_Y_level hY (n + 1)).prodMk hg)

lemma measurable_tm (hY : Measurable Y) (n : ℕ) (a : ℕ →₀ ℕ) :
    Measurable fun ω => tm Gs (Y ω) n a := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (measurable_of_countable (fun k : ℕ => k + a (n + 1))).comp (measurable_Jstep Gs hY n ih)

/-- `Y_ξ` is a measurable function of the paths. -/
lemma measurable_Yxi (hY : Measurable Y) (a : ℕ →₀ ℕ) : Measurable fun ω => Yxi Gs (Y ω) a :=
  measurable_eval_pair.comp
    ((measurable_Y_level hY (level a)).prodMk (measurable_tm Gs hY (level a) a))

/-- The class `[(n, j)]` is a measurable function of the paths. -/
lemma measurableSet_addr (hY : Measurable Y) (n j : ℕ) (a : ℕ →₀ ℕ) :
    MeasurableSet {ω | addr Gs (Y ω) n j = a} := by
  induction n generalizing j a with
  | zero =>
    simp only [addr_zero]
    exact MeasurableSet.const _
  | succ n ih =>
    have e : {ω | addr Gs (Y ω) (n + 1) j = a} = ⋃ k : ℕ, ⋃ m : ℕ, ⋃ b : ℕ →₀ ℕ,
        {ω | coarsenPred (Gs n) (Y ω (n + 1)) j = k} ∩ {ω | Jstep Gs (Y ω) n k = m} ∩
          {ω | addr Gs (Y ω) n k = b} ∩ {_ω | b + Finsupp.single (n + 1) (j - m) = a} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, and_assoc]
      constructor
      · intro hω
        rw [addr_succ] at hω
        exact ⟨_, _, _, rfl, rfl, rfl, hω⟩
      · rintro ⟨k, m, b, hk, hm, hb, hab⟩
        rw [addr_succ, hk, hm, hb]
        exact hab
    rw [e]
    refine MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun b => ((?_ : MeasurableSet _).inter ?_ |>.inter (ih k b)).inter
        (MeasurableSet.const _)
    · exact ((measurable_coarsenPred (measurableSet_Gs Gs n) j).comp (measurable_Y_level hY (n + 1)))
        (measurableSet_singleton k)
    · exact measurable_Jstep Gs hY n measurable_const (measurableSet_singleton m)

/-- Membership in `Ξ` is a measurable event. -/
lemma measurableSet_realized (hY : Measurable Y) (a : ℕ →₀ ℕ) :
    MeasurableSet {ω | Realized Gs (Y ω) a} := by
  have e : {ω | Realized Gs (Y ω) a} = ⋃ n, ⋃ j, {ω | addr Gs (Y ω) n j = a} := by
    ext ω; simp only [Realized, Set.mem_ofPred_eq, Set.mem_iUnion]
  rw [e]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun j => measurableSet_addr Gs hY n j a

lemma measurableSet_mem_below (hY : Measurable Y) (a η : ℕ →₀ ℕ) :
    MeasurableSet {ω | a ∈ below Gs (Y ω) η} :=
  (measurableSet_realized Gs hY a).inter (MeasurableSet.const _)

/-- The coupling identity (3.12) is a measurable event. -/
lemma measurableSet_consistent (hY : Measurable Y) : MeasurableSet {ω | Consistent Gs (Y ω)} := by
  have e : {ω | Consistent Gs (Y ω)} =
      ⋂ n, ⋂ k, {ω | Y ω (n + 1) (Jstep Gs (Y ω) n k) = Y ω n k} := by
    ext ω; simp only [Consistent, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [e]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => measurableSet_eq_fun ?_ ?_
  · exact measurable_eval_pair.comp
      ((measurable_Y_level hY (n + 1)).prodMk (measurable_Jstep Gs hY n measurable_const))
  · exact (measurable_pi_apply k).comp (measurable_Y_level hY n)

/-- The holding times `T_ξ` are measurable functions of the sample. -/
lemma measurable_holding (hY : Measurable Y) (hE : Measurable E) (a : ℕ →₀ ℕ) :
    Measurable fun ω => holding Gs (Y ω) w (E ω) a :=
  ENNReal.measurable_ofReal.comp (((measurable_pi_apply a).comp hE).div
    ((measurable_of_countable w).comp (measurable_Yxi Gs hY a)))

lemma measurable_tsum_indicator (hY : Measurable Y) (hE : Measurable E)
    (S : Ω → Set (ℕ →₀ ℕ)) (hS : ∀ a, MeasurableSet {ω | a ∈ S ω}) :
    Measurable fun ω => ∑' a, (S ω).indicator (holding Gs (Y ω) w (E ω)) a := by
  classical
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine Measurable.iSup fun s => Finset.measurable_sum s fun a _ => ?_
  simp only [Set.indicator_apply]
  exact Measurable.ite (hS a) (measurable_holding Gs w hY hE a) measurable_const

/-- The clocks `τ_η` of (3.25) are measurable functions of the sample. -/
lemma measurable_tau (hY : Measurable Y) (hE : Measurable E) (η : ℕ →₀ ℕ) :
    Measurable fun ω => tau Gs (Y ω) w (E ω) η :=
  measurable_tsum_indicator Gs w hY hE (fun ω => below Gs (Y ω) η)
    (fun a => measurableSet_mem_below Gs hY a η)

lemma measurable_totalTime (hY : Measurable Y) (hE : Measurable E) :
    Measurable fun ω => totalTime Gs (Y ω) w (E ω) :=
  measurable_tsum_indicator Gs w hY hE (fun ω => realizedSet Gs (Y ω))
    (fun a => measurableSet_realized Gs hY a)

lemma measurable_layerTime (hY : Measurable Y) (hE : Measurable E) (n : ℕ) (η : ℕ →₀ ℕ) :
    Measurable fun ω => layerTime Gs (Y ω) w (E ω) n η :=
  measurable_tsum_indicator Gs w hY hE
    (fun ω => below Gs (Y ω) η ∩ {a | Yxi Gs (Y ω) a ∈ layer Gs n})
    (fun a => (measurableSet_mem_below Gs hY a η).inter
      ((measurable_Yxi Gs hY a) (Set.to_countable _).measurableSet))

/-- The conclusion (3.16) of Lemma 3.5 is a measurable event. -/
lemma measurableSet_holdingTimesSummable (hY : Measurable Y) (hE : Measurable E) :
    MeasurableSet {ω | HoldingTimesSummable Gs (Y ω) w (E ω)} := by
  have e : {ω | HoldingTimesSummable Gs (Y ω) w (E ω)} =
      {ω | totalTime Gs (Y ω) w (E ω) = ⊤} ∩
        ⋂ η, ({ω | Realized Gs (Y ω) η}ᶜ ∪ {ω | tau Gs (Y ω) w (E ω) η < ⊤}) := by
    ext ω
    simp only [HoldingTimesSummable, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_union, Set.mem_compl_iff]
    exact and_congr Iff.rfl (forall_congr' fun η => imp_iff_not_or)
  rw [e]
  exact (measurable_totalTime Gs w hY hE (measurableSet_singleton ⊤)).inter
    (MeasurableSet.iInter fun η => (measurableSet_realized Gs hY η).compl.union
      (measurable_tau Gs w hY hE η measurableSet_Iio))

/-- The event of Lemma 3.7 is measurable. -/
lemma measurableSet_inOpenInterval (hY : Measurable Y) (hE : Measurable E) (t : ℝ≥0∞) :
    MeasurableSet {ω | InOpenInterval Gs (Y ω) w (E ω) t} := by
  have e : {ω | InOpenInterval Gs (Y ω) w (E ω) t} = ⋃ η, {ω | Realized Gs (Y ω) η} ∩
      {ω | tau Gs (Y ω) w (E ω) η < t} ∩
      {ω | t < tau Gs (Y ω) w (E ω) η + holding Gs (Y ω) w (E ω) η} := by
    ext ω
    simp only [InOpenInterval, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, and_assoc]
  rw [e]
  refine MeasurableSet.iUnion fun η =>
    ((measurableSet_realized Gs hY η).inter (measurable_tau Gs w hY hE η measurableSet_Iio)).inter ?_
  exact ((measurable_tau Gs w hY hE η).add (measurable_holding Gs w hY hE η)) measurableSet_Ioi

/-- `X_t` is a random variable: `process Gs w Y E t` is measurable for every `t`. -/
lemma measurable_process (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (t : ℝ≥0) : Measurable (process Gs w Y E t) := by
  have hsome : ∀ x : V, process Gs w Y E t ⁻¹' {some x} = {ω | Consistent Gs (Y ω)} ∩
      ⋃ η, ({ω | Realized Gs (Y ω) η} ∩ {ω | tau Gs (Y ω) w (E ω) η ≤ t} ∩
        {ω | (t : ℝ≥0∞) < tau Gs (Y ω) w (E ω) η + holding Gs (Y ω) w (E ω) η} ∩
        {ω | Yxi Gs (Y ω) η = x}) := by
    intro x
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_iUnion,
      Set.mem_ofPred_eq, and_assoc]
    constructor
    · intro hω
      by_cases hc : Consistent Gs (Y ω)
      · rw [process_of_consistent Gs w Y E hc] at hω
        refine ⟨hc, ?_⟩
        obtain ⟨η, hη⟩ : ∃ η, InInterval Gs (Y ω) w (E ω) η t := by
          by_contra hn
          rw [(X_eq_none_iff _ _ _ _ t).mpr hn] at hω
          exact absurd hω (by simp)
        rw [hc.X_eq_of_inInterval _ _ _ _ hG hcov hη] at hω
        refine ⟨η, hη.1, hη.2.1, ?_, Option.some_injective V hω⟩
        rw [← tau_succ _ _ _ _ hc hG hcov hη.1]; exact hη.2.2
      · simp only [process, hc, ite_false] at hω
        exact absurd hω (by simp)
    · rintro ⟨hc, η, hη, h1, h2, hx⟩
      rw [process_of_consistent Gs w Y E hc, hc.X_eq_of_inInterval _ _ _ _ hG hcov
        ⟨hη, h1, by rwa [tau_succ _ _ _ _ hc hG hcov hη]⟩, hx]
  have hmeas : ∀ x : V, MeasurableSet (process Gs w Y E t ⁻¹' {some x}) := by
    intro x
    rw [hsome x]
    refine (measurableSet_consistent Gs hY).inter (MeasurableSet.iUnion fun η => ?_)
    refine (((measurableSet_realized Gs hY η).inter
      (measurable_tau Gs w hY hE η measurableSet_Iic)).inter
      (((measurable_tau Gs w hY hE η).add (measurable_holding Gs w hY hE η)) measurableSet_Ioi)).inter
      ((measurable_Yxi Gs hY η) (measurableSet_singleton x))
  refine measurable_to_countable' fun o => ?_
  cases o with
  | none =>
    have e : process Gs w Y E t ⁻¹' {none} = (⋃ x, process Gs w Y E t ⁻¹' {some x})ᶜ := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
        not_exists]
      generalize process Gs w Y E t ω = o
      cases o <;> simp
    rw [e]
    exact (MeasurableSet.iUnion hmeas).compl
  | some x => exact hmeas x

/-- `T_{[(n,i)]}` is a measurable function of the sample (the class `[(n, i)]` itself depends
measurably on the paths, through countably many values). -/
lemma measurable_holding_addr (hY : Measurable Y) (hE : Measurable E) (n i : ℕ) :
    Measurable fun ω => holding Gs (Y ω) w (E ω) (addr Gs (Y ω) n i) := by
  let _ : MeasurableSpace (ℕ →₀ ℕ) := ⊤
  have _ : MeasurableSingletonClass (ℕ →₀ ℕ) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have h1 : Measurable fun q : Ω × (ℕ →₀ ℕ) => holding Gs (Y q.1) w (E q.1) q.2 :=
    measurable_from_prod_countable_left fun a => measurable_holding Gs w hY hE a
  have h2 : Measurable fun ω => addr Gs (Y ω) n i :=
    measurable_to_countable' fun a => measurableSet_addr Gs hY n i a
  exact h1.comp (measurable_id.prodMk h2)

lemma measurable_levelTau (hY : Measurable Y) (hE : Measurable E) (n k : ℕ) :
    Measurable fun ω => levelTau Gs (Y ω) w (E ω) n k := by
  unfold levelTau
  exact Finset.measurable_sum _ fun i _ => measurable_holding_addr Gs w hY hE n i

/-- The fibres of `(ω, t) ↦ Xⁿ_{t⁺}(ω)` are measurable in the product: `Xⁿ` is a jointly
measurable process. -/
lemma measurableSet_prod_Xn (hY : Measurable Y) (hE : Measurable E) (n : ℕ) (o : Option V) :
    MeasurableSet {p : Ω × ℝ | Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2) = o} := by
  have hmeas : ∀ x : V,
      MeasurableSet {p : Ω × ℝ | Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2) = some x} := by
    intro x
    simp only [Xn_eq_some_iff, Set.ofPred_exists]
    refine MeasurableSet.iUnion fun k => ?_
    refine (measurableSet_le ((measurable_levelTau Gs w hY hE n k).comp measurable_fst)
      (ENNReal.measurable_ofReal.comp measurable_snd)).inter ((measurableSet_lt
        (ENNReal.measurable_ofReal.comp measurable_snd)
        ((measurable_levelTau Gs w hY hE n (k + 1)).comp measurable_fst)).inter ?_)
    exact (((measurable_pi_apply k).comp (measurable_Y_level hY n)).comp measurable_fst)
      (measurableSet_singleton x)
  cases o with
  | none =>
    rw [show {p : Ω × ℝ | Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2) = none} =
      (fun p : Ω × ℝ => Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2)) ⁻¹' {none} from rfl,
      preimage_none_eq_compl_iUnion]
    exact (MeasurableSet.iUnion hmeas).compl
  | some x => exact hmeas x

/-- The fibres of `(ω, t) ↦ X_{t⁺}(ω)` are measurable in the product: `X` is a jointly
measurable process. -/
lemma measurableSet_prod_process (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (o : Option V) :
    MeasurableSet {p : Ω × ℝ | process Gs w Y E (Real.toNNReal p.2) p.1 = o} := by
  have hmeas : ∀ x : V,
      MeasurableSet {p : Ω × ℝ | process Gs w Y E (Real.toNNReal p.2) p.1 = some x} := by
    intro x
    have e : {p : Ω × ℝ | process Gs w Y E (Real.toNNReal p.2) p.1 = some x} =
        {p : Ω × ℝ | Consistent Gs (Y p.1)} ∩ ⋃ η, ({p : Ω × ℝ | Realized Gs (Y p.1) η} ∩
          {p : Ω × ℝ | tau Gs (Y p.1) w (E p.1) η ≤ ENNReal.ofReal p.2} ∩
          {p : Ω × ℝ | ENNReal.ofReal p.2 <
            tau Gs (Y p.1) w (E p.1) η + holding Gs (Y p.1) w (E p.1) η} ∩
          {p : Ω × ℝ | Yxi Gs (Y p.1) η = x}) := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion, and_assoc]
      constructor
      · intro hp
        have hc : Consistent Gs (Y p.1) := by
          by_contra hc
          simp only [process, hc, ite_false] at hp
          exact absurd hp (by simp)
        rw [process_of_consistent Gs w Y E hc, X_eq_some_iff _ _ _ _ hc hG hcov] at hp
        exact ⟨hc, hp⟩
      · rintro ⟨hc, hp⟩
        rw [process_of_consistent Gs w Y E hc, X_eq_some_iff _ _ _ _ hc hG hcov]
        exact hp
    rw [e]
    refine ((measurableSet_consistent Gs hY).preimage measurable_fst).inter
      (MeasurableSet.iUnion fun η => ?_)
    refine ((((measurableSet_realized Gs hY η).preimage measurable_fst).inter
      (measurableSet_le ((measurable_tau Gs w hY hE η).comp measurable_fst)
        (ENNReal.measurable_ofReal.comp measurable_snd))).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd)
        (((measurable_tau Gs w hY hE η).add (measurable_holding Gs w hY hE η)).comp
          measurable_fst))).inter ?_
    exact ((measurable_Yxi Gs hY η).comp measurable_fst) (measurableSet_singleton x)
  cases o with
  | none =>
    rw [show {p : Ω × ℝ | process Gs w Y E (Real.toNNReal p.2) p.1 = none} =
      (fun p : Ω × ℝ => process Gs w Y E (Real.toNNReal p.2) p.1) ⁻¹' {none} from rfl,
      preimage_none_eq_compl_iUnion]
    exact (MeasurableSet.iUnion hmeas).compl
  | some x => exact hmeas x

end measurability

/-! ### The probabilistic layer -/

section probabilistic

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
  (Gs : ℕ → Set V) (w : V → ℝ) (Y : Ω → ℕ → ℕ → V) (E : Ω → (ℕ →₀ ℕ) → ℝ)

/-- **Theorem 1.6, property (ii)** for the process (3.26): almost surely, for every `t` with
`X_t ∈ VG` the path is constant on `[t, t + ε)` for some `ε > 0`.  The only probabilistic
input is that the coupling identity (3.12) holds almost surely (Lemma 3.4). -/
theorem rightContinuous (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω)) :
    Theorem16.RightContinuous P (process Gs w Y E) :=
  hcons.mono fun ω hω t ht => by
    simp only [process_of_consistent Gs w Y E hω] at ht ⊢
    exact X_rightContinuous Gs (Y ω) w (E ω) hω hG hcov t ht

/-- The "rest" of the sample: the paths and all unit holding times except `E_{ξ₀}` (which is
set to `0`).  Lemma 3.7 needs `E_{ξ₀}` to be independent of this with an absolutely continuous
law. -/
def rest (ω : Ω) : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) := (Y ω, Function.update (E ω) 0 0)

/-- The processes `Xⁿ` of (3.15) as stochastic processes. -/
noncomputable def processN (n : ℕ) (t : ℝ≥0) (ω : Ω) : Option V := Xn Gs (Y ω) w (E ω) n t

/-- The path `t ↦ X_{t⁺}` of the outcome `ω` as an element of `L¹_loc([0,∞), VG ∪ {∞})`
(Definition 3.9); `X` is read at `max t 0`, only `t > 0` matters. -/
noncomputable def pathClass [Countable V] (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) (ω : Ω) :
    L1loc (Option V) := by
  classical
  exact L1loc.mk (fun t : ℝ => process Gs w Y E (Real.toNNReal t) ω) (by
    intro o
    by_cases hc : Consistent Gs (Y ω)
    · simp only [process_of_consistent Gs w Y E hc]
      exact measurableSet_X_toNNReal_fiber Gs (Y ω) w (E ω) hc hG hcov o
    · have e : (fun t : ℝ => process Gs w Y E (Real.toNNReal t) ω) = fun _ => none := by
        funext t; simp only [process, hc, ite_false]
      rw [e]
      exact measurable_const (measurableSet_singleton o))

/-- The path `t ↦ Xⁿ_{t⁺}` of the outcome `ω` as an element of `L¹_loc([0,∞), VG ∪ {∞})`. -/
noncomputable def pathClassN [Countable V] (n : ℕ) (ω : Ω) : L1loc (Option V) :=
  L1loc.mk (fun t : ℝ => Xn Gs (Y ω) w (E ω) n (Real.toNNReal t))
    (measurableSet_Xn_toNNReal_fiber Gs (Y ω) w (E ω) n)

variable [MeasurableSpace V]

lemma measurable_rest {Y : Ω → ℕ → ℕ → V} {E : Ω → (ℕ →₀ ℕ) → ℝ} (hY : Measurable Y)
    (hE : Measurable E) : Measurable (rest Y E) :=
  hY.prodMk (measurable_update'.comp (hE.prodMk measurable_const))

/-- `E_{ξ₀} > 0` almost surely, from the absolute continuity of its law with respect to Lebesgue
measure on `(0, ∞)`. -/
lemma ae_pos_E0 {E : Ω → (ℕ →₀ ℕ) → ℝ} (hE : Measurable E)
    (hlaw : P.map (fun ω => E ω 0) ≪ volume.restrict (Set.Ioi 0)) :
    ∀ᵐ ω ∂P, 0 < E ω 0 := by
  have hE0 : Measurable fun ω => E ω 0 := (measurable_pi_apply 0).comp hE
  have h : P.map (fun ω => E ω 0) (Set.Iic 0) = 0 := by
    refine hlaw ?_
    rw [Measure.restrict_apply' measurableSet_Ioi, Set.Iic_inter_Ioi, Set.Ioc_self, measure_empty]
  rw [Measure.map_apply hE0 measurableSet_Iic] at h
  have h' : {ω | ¬ 0 < E ω 0} = (fun ω => E ω 0) ⁻¹' Set.Iic 0 := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic, not_lt]
  rw [ae_iff, h']
  exact h

/-- The exponential law `Exponential(r)` is absolutely continuous with respect to Lebesgue
measure on `(0, ∞)`: this is the form in which the law of `E_{ξ₀}` enters Lemma 3.7. -/
lemma expMeasure_absolutelyContinuous (r : ℝ) :
    ProbabilityTheory.expMeasure r ≪ volume.restrict (Set.Ioi 0) := by
  intro s hs
  rw [Measure.restrict_apply' measurableSet_Ioi] at hs
  have h1 : ProbabilityTheory.expMeasure r (s ∩ Set.Ioi 0) = 0 :=
    withDensity_absolutelyContinuous _ _ hs
  have h2 : ProbabilityTheory.expMeasure r (s ∩ Set.Iic 0) = 0 := by
    refine measure_mono_null Set.inter_subset_right ?_
    have : Set.Iic (0 : ℝ) = Set.Iio 0 ∪ {0} := by
      ext x; simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
      exact le_iff_lt_or_eq
    rw [this]
    refine measure_union_null ?_ (withDensity_absolutelyContinuous _ _ Real.volume_singleton)
    rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
      withDensity_apply _ measurableSet_Iio]
    exact ProbabilityTheory.lintegral_exponentialPDF_of_nonpos le_rfl
  refine nonpos_iff_eq_zero.mp ?_
  calc ProbabilityTheory.expMeasure r s
      ≤ ProbabilityTheory.expMeasure r (s ∩ Set.Ioi 0) +
        ProbabilityTheory.expMeasure r (s ∩ Set.Iic 0) := by
        refine le_trans (measure_mono ?_) (measure_union_le _ _)
        intro x hx
        by_cases h0 : 0 < x
        · exact Or.inl ⟨hx, h0⟩
        · exact Or.inr ⟨hx, not_lt.mp h0⟩
    _ = 0 := by rw [h1, h2, add_zero]

omit [MeasurableSpace V] in
/-- **Lemma 3.8 in `L¹_loc`**: almost surely, `Xⁿ → X` for the metric (3.30) of
Definition 3.9.  (Convergence in law of `Xⁿ` to `X` in `L¹_loc`, as used for property (iv),
follows from this almost-sure convergence once the classes are shown to be random elements of
`L¹_loc`; that measurability statement is not part of this file.) -/
theorem ae_tendsto_pathClassN [Countable V] (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => pathClassN Gs w Y E n ω) atTop
      (𝓝 (pathClass Gs w Y E hG hcov ω)) := by
  filter_upwards [hcons, hsum] with ω hc hs
  rw [tendsto_iff_edist_tendsto_0]
  have e : ∀ n, edist (pathClassN Gs w Y E n ω) (pathClass Gs w Y E hG hcov ω) =
      ReflectedWalk.expMeasure {t : ℝ | Xn Gs (Y ω) w (E ω) n (Real.toNNReal t) ≠
        X Gs (Y ω) w (E ω) (Real.toNNReal t)} := by
    intro n
    unfold pathClassN pathClass
    rw [L1loc.edist_mk_mk]
    simp only [process_of_consistent Gs w Y E hc]
  simp only [e]
  exact tendsto_expMeasure_Xn_ne_X Gs (Y ω) w (E ω) hc hG hcov hs

variable [MeasurableSingletonClass V] [Countable V] [IsProbabilityMeasure P] {Y E}

/-- **Lemma 3.7**: for each fixed `t > 0`, almost surely `t ∈ (τ_ξ, τ_ξ̂)` for some `ξ ∈ Ξ`.

The first paragraph of the paper's proof is `volume_notInOpenInterval`; the second — the
transfer from Lebesgue-a.e. `t` to a fixed `t` — is done by conditioning on everything but
the first unit holding time `E_{ξ₀}` (`rest Y E`): given the rest, the bad set of values of
`E_{ξ₀}` is Lebesgue-null (`volume_notInOpenInterval_update`), and the law of `E_{ξ₀}` is
absolutely continuous.  Fubini (`Measure.prod_apply_symm`) then gives probability zero. -/
theorem ae_inOpenInterval (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hw : ∀ x, 0 < w x)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω))
    (hindep : IndepFun (fun ω => E ω 0) (rest Y E) P)
    (hlaw : P.map (fun ω => E ω 0) ≪ volume.restrict (Set.Ioi 0))
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ ω ∂P, InOpenInterval Gs (Y ω) w (E ω) t := by
  have hE0 : Measurable fun ω => E ω 0 := (measurable_pi_apply 0).comp hE
  have hrest := measurable_rest hY hE
  -- the bad set, as a set of pairs (value of `E_{ξ₀}`, rest)
  obtain ⟨B, hB⟩ : ∃ B : Set (ℝ × ((ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ))), B =
      {p | ¬ InOpenInterval Gs p.2.1 w (Function.update p.2.2 0 p.1) t} := ⟨_, rfl⟩
  have hBm : MeasurableSet B := by
    have hY' : Measurable fun p : ℝ × ((ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)) => p.2.1 :=
      measurable_fst.comp measurable_snd
    have hE' : Measurable fun p : ℝ × ((ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ)) =>
        Function.update p.2.2 0 p.1 :=
      measurable_update'.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    rw [hB]
    exact (measurableSet_inOpenInterval Gs w hY' hE' t).compl
  have hpre : {ω | ¬ InOpenInterval Gs (Y ω) w (E ω) t} =
      (fun ω => (E ω 0, rest Y E ω)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hB, rest, Function.update_idem,
      Function.update_eq_self]
  rw [ae_iff, hpre, ← Measure.map_apply (hE0.prodMk hrest) hBm,
    hindep.map_prod_eq_prod_map_map hE0.aemeasurable hrest.aemeasurable,
    Measure.prod_apply_symm hBm]
  -- a.e. properties of the rest
  have hae : ∀ᵐ r ∂(P.map (rest Y E)),
      Consistent Gs r.1 ∧ HoldingTimesSummable Gs r.1 w r.2 ∧ r.2 0 = 0 := by
    rw [ae_map_iff hrest.aemeasurable]
    · filter_upwards [hcons, hsum] with ω h1 h2
      simp only [rest]
      refine ⟨h1, ?_, Function.update_self 0 0 (E ω)⟩
      refine (holdingTimesSummable_update_zero_iff Gs (Y ω) w (E ω) (E ω 0)).mp ?_
      rwa [Function.update_eq_self]
    · exact (measurableSet_consistent Gs measurable_fst).inter
        ((measurableSet_holdingTimesSummable Gs w measurable_fst measurable_snd).inter
          (((measurable_pi_apply 0).comp measurable_snd) (measurableSet_singleton 0)))
  refine (lintegral_congr_ae (hae.mono fun r hr => ?_)).trans lintegral_zero
  obtain ⟨h1, h2, h3⟩ := hr
  refine hlaw ?_
  rw [Measure.restrict_apply' measurableSet_Ioi]
  have e : (fun x : ℝ => (x, r)) ⁻¹' B ∩ Set.Ioi 0 = {x : ℝ | 0 < x ∧
      ¬ InOpenInterval Gs r.1 w (Function.update r.2 0 x) (ENNReal.ofReal (t : ℝ))} := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, hB, Set.mem_ofPred_eq, Set.mem_Ioi,
      ENNReal.ofReal_coe_nnreal, and_comm]
  rw [e]
  exact volume_notInOpenInterval_update Gs r.1 w r.2 h1 hG hcov h2 h3 (hw _)
    (NNReal.coe_pos.mpr ht)

/-- **Theorem 1.6, property (i)** for the process (3.26): for each fixed `t ≥ 0`, almost
surely `X_t ∈ VG` and `X` is constant on a neighbourhood of `t` (p. 24, "Property (i)": Lemma
3.7 together with the constancy of `X` on each `[τ_ξ, τ_ξ̂)`).  At `t = 0` the neighbourhood
is `[0, T_{ξ₀})`, which is non-trivial since `E_{ξ₀} > 0` almost surely. -/
theorem almostEverywhereDefined (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hw : ∀ x, 0 < w x)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω))
    (hindep : IndepFun (fun ω => E ω 0) (rest Y E) P)
    (hlaw : P.map (fun ω => E ω 0) ≪ volume.restrict (Set.Ioi 0)) :
    Theorem16.AlmostEverywhereDefined P (process Gs w Y E) := by
  intro t
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · -- `t = 0`: the neighbourhood `[0, T_{ξ₀})`
    filter_upwards [hcons, ae_pos_E0 P hE hlaw] with ω hc hp
    have hh0 : 0 < holding Gs (Y ω) w (E ω) 0 := by
      simp only [holding, Yxi_zero]
      exact ENNReal.ofReal_pos.mpr (div_pos hp (hw _))
    have hsucc : tau Gs (Y ω) w (E ω) (succ Gs (Y ω) 0) = holding Gs (Y ω) w (E ω) 0 := by
      rw [tau_succ _ _ _ _ hc hG hcov (realized_zero _ _), tau_zero, zero_add]
    have h0 : InInterval Gs (Y ω) w (E ω) 0 (0 : ℝ≥0) := inInterval_zero _ _ _ _ hc hG hcov (hw _) hp
    have hX0 : process Gs w Y E 0 ω = some (Yxi Gs (Y ω) 0) := by
      rw [process_of_consistent Gs w Y E hc, hc.X_eq_of_inInterval _ _ _ _ hG hcov h0]
    refine ⟨⟨_, hX0⟩, (holding Gs (Y ω) w (E ω) 0).toReal,
      ENNReal.toReal_pos hh0.ne' (holding_ne_top _ _ _ _ _), fun s hs => ?_⟩
    rw [hX0, process_of_consistent Gs w Y E hc]
    refine hc.X_eq_of_inInterval _ _ _ _ hG hcov
      ⟨realized_zero _ _, by rw [tau_zero]; exact zero_le, ?_⟩
    rw [hsucc]
    rw [Metric.mem_ball, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (NNReal.coe_nonneg s)] at hs
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (NNReal.coe_nonneg s)
      (holding_ne_top _ _ _ _ _)).mpr hs
  · -- `t > 0`: Lemma 3.7
    filter_upwards [hcons, ae_inOpenInterval P Gs w hY hE hG hcov hw hcons hsum hindep hlaw ht]
      with ω hc hin
    obtain ⟨η, hη, h1, h2⟩ := hin
    have hsucc := tau_succ Gs (Y ω) w (E ω) hc hG hcov hη
    have hI : InInterval Gs (Y ω) w (E ω) η t := ⟨hη, h1.le, by rw [hsucc]; exact h2⟩
    have hXt : process Gs w Y E t ω = some (Yxi Gs (Y ω) η) := by
      rw [process_of_consistent Gs w Y E hc, hc.X_eq_of_inInterval _ _ _ _ hG hcov hI]
    refine ⟨⟨_, hXt⟩, ?_⟩
    obtain ⟨b, hb1, hb2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp
      (show (t : ℝ≥0∞) < tau Gs (Y ω) w (E ω) (succ Gs (Y ω) η) by rw [hsucc]; exact h2)
    have hτt : (tau Gs (Y ω) w (E ω) η).toReal < t :=
      ENNReal.toReal_lt_of_lt_ofReal (by rwa [ENNReal.ofReal_coe_nnreal])
    have hτne : tau Gs (Y ω) w (E ω) η ≠ ⊤ := ne_top_of_lt h1
    have htb : (t : ℝ) < b := NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp hb1)
    refine ⟨min (t - (tau Gs (Y ω) w (E ω) η).toReal) (b - t),
      lt_min (sub_pos.mpr hτt) (sub_pos.mpr htb), fun s hs => ?_⟩
    rw [hXt, process_of_consistent Gs w Y E hc]
    rw [Metric.mem_ball, NNReal.dist_eq] at hs
    refine hc.X_eq_of_inInterval _ _ _ _ hG hcov ⟨hη, ?_, ?_⟩
    · have := (abs_lt.mp (lt_of_lt_of_le hs (min_le_left _ _))).1
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.le_ofReal_iff_toReal_le hτne (NNReal.coe_nonneg s)).mpr (by linarith)
    · have := (abs_lt.mp (lt_of_lt_of_le hs (min_le_right _ _))).2
      calc (s : ℝ≥0∞) < b := ENNReal.coe_lt_coe.mpr (NNReal.coe_lt_coe.mp (by linarith))
        _ < _ := hb2

/-- For each fixed `t ≥ 0`, almost surely `t ∈ [τ_η, τ_η̂)` for some `η ∈ Ξ` (Lemma 3.7 for
`t > 0`; `η = ξ₀` for `t = 0`). -/
theorem ae_exists_inInterval (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hw : ∀ x, 0 < w x)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω))
    (hindep : IndepFun (fun ω => E ω 0) (rest Y E) P)
    (hlaw : P.map (fun ω => E ω 0) ≪ volume.restrict (Set.Ioi 0)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ η, InInterval Gs (Y ω) w (E ω) η t := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with rfl | ht
  · filter_upwards [hcons, ae_pos_E0 P hE hlaw] with ω hc hp
    exact ⟨0, inInterval_zero _ _ _ _ hc hG hcov (hw _) hp⟩
  · filter_upwards [hcons, ae_inOpenInterval P Gs w hY hE hG hcov hw hcons hsum hindep hlaw ht]
      with ω hc hin
    obtain ⟨η, hη, h1, h2⟩ := hin
    exact ⟨η, hη, h1.le, by rw [tau_succ _ _ _ _ hc hG hcov hη]; exact h2⟩

/-- **Lemma 3.8, pointwise clause**: for each fixed `t ≥ 0`, almost surely `Xⁿ_t = X_t` for
all sufficiently large `n`. -/
theorem ae_eventually_processN_eq (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hw : ∀ x, 0 < w x)
    (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω))
    (hindep : IndepFun (fun ω => E ω 0) (rest Y E) P)
    (hlaw : P.map (fun ω => E ω 0) ≪ volume.restrict (Set.Ioi 0)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, processN Gs w Y E n t ω = process Gs w Y E t ω := by
  filter_upwards [hcons, ae_exists_inInterval P Gs w hY hE hG hcov hw hcons hsum hindep hlaw t]
    with ω hc hex
  obtain ⟨η, hη⟩ := hex
  rw [process_of_consistent Gs w Y E hc]
  exact eventually_Xn_eq_X_of_inInterval Gs (Y ω) w (E ω) hc hG hcov hη


end probabilistic

/-! ### Convergence in law in `L¹_loc` (Lemma 3.8, as used for property (iv), p. 25) -/

section law

/-- For a second-countable pseudo-metric space with its Borel σ-algebra, a map is measurable
as soon as all the distance functions `ω ↦ dist (F ω) y` are: the open balls form a basis
of the topology, so they generate the Borel σ-algebra. -/
lemma measurable_of_measurable_dist {X : Type*} [PseudoMetricSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {Ω' : Type*} [MeasurableSpace Ω'] {F : Ω' → X} (h : ∀ y, Measurable fun ω => dist (F ω) y) :
    Measurable F := by
  have hb : TopologicalSpace.IsTopologicalBasis {s : Set X | ∃ y r, s = Metric.ball y r} := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨y, r, rfl⟩; exact Metric.isOpen_ball
    · intro a u hau hu
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu a hau
      exact ⟨Metric.ball a ε, ⟨a, ε, rfl⟩, Metric.mem_ball_self hε, hball⟩
  have hgen : (‹MeasurableSpace X› : MeasurableSpace X) =
      MeasurableSpace.generateFrom {s : Set X | ∃ y r, s = Metric.ball y r} :=
    (BorelSpace.measurable_eq (α := X)).trans hb.borel_eq_generateFrom
  refine (measurable_generateFrom ?_).mono le_rfl hgen.le
  rintro _ ⟨y, r, rfl⟩
  exact (h y) measurableSet_Iio

/-- The Borel σ-algebra of the path space `L¹_loc([0,∞), S)` of Definition 3.9. -/
noncomputable instance L1loc.instMeasurableSpace (S : Type u) : MeasurableSpace (L1loc S) :=
  borel _

instance L1loc.instBorelSpace (S : Type u) : BorelSpace (L1loc S) := ⟨rfl⟩

variable {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
  (Gs : ℕ → Set V) (w : V → ℝ) {Y : Ω → ℕ → ℕ → V} {E : Ω → (ℕ →₀ ℕ) → ℝ}
  [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]

/-- The distance from the path of `Xⁿ` to a fixed element of `L¹_loc` is a measurable function
of the sample (Fubini for the jointly measurable set `{(ω, t) : Xⁿ_t(ω) ≠ g(t)}`). -/
lemma measurable_dist_pathClassN (hY : Measurable Y) (hE : Measurable E) (n : ℕ)
    (g : L1loc (Option V)) : Measurable fun ω => dist (pathClassN Gs w Y E n ω) g := by
  have e : (fun ω => dist (pathClassN Gs w Y E n ω) g) = fun ω => (ReflectedWalk.expMeasure
      (Prod.mk ω ⁻¹' {p : Ω × ℝ | g p.2 ≠ Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2)})).toReal := by
    funext ω
    rw [dist_edist, edist_comm, pathClassN, L1loc.edist_mk_right]
    rfl
  rw [e]
  refine ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left ?_)
  have e2 : {p : Ω × ℝ | g p.2 ≠ Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2)} =
      (⋃ o, {p : Ω × ℝ | g p.2 = o} ∩
        {p : Ω × ℝ | Xn Gs (Y p.1) w (E p.1) n (Real.toNNReal p.2) = o})ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff,
      not_exists, not_and]
    constructor
    · intro hne o h1 h2; exact hne (h1.trans h2.symm)
    · intro hp heq; exact hp _ rfl heq.symm
  rw [e2]
  exact (MeasurableSet.iUnion fun o => ((g.measurableSet_preimage_singleton o).preimage
    measurable_snd).inter (measurableSet_prod_Xn Gs w hY hE n o)).compl

/-- The path of `Xⁿ` is a random element of `L¹_loc`. -/
lemma measurable_pathClassN (hY : Measurable Y) (hE : Measurable E) (n : ℕ) :
    Measurable (pathClassN Gs w Y E n) :=
  measurable_of_measurable_dist fun g => measurable_dist_pathClassN Gs w hY hE n g

/-- The distance from the path of `X` to a fixed element of `L¹_loc` is a measurable function
of the sample. -/
lemma measurable_dist_pathClass (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (g : L1loc (Option V)) :
    Measurable fun ω => dist (pathClass Gs w Y E hG hcov ω) g := by
  have e : (fun ω => dist (pathClass Gs w Y E hG hcov ω) g) = fun ω => (ReflectedWalk.expMeasure
      (Prod.mk ω ⁻¹' {p : Ω × ℝ | g p.2 ≠ process Gs w Y E (Real.toNNReal p.2) p.1})).toReal := by
    funext ω
    rw [dist_edist, edist_comm, pathClass, L1loc.edist_mk_right]
    rfl
  rw [e]
  refine ENNReal.measurable_toReal.comp (measurable_measure_prodMk_left ?_)
  have e2 : {p : Ω × ℝ | g p.2 ≠ process Gs w Y E (Real.toNNReal p.2) p.1} =
      (⋃ o, {p : Ω × ℝ | g p.2 = o} ∩
        {p : Ω × ℝ | process Gs w Y E (Real.toNNReal p.2) p.1 = o})ᶜ := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_inter_iff,
      not_exists, not_and]
    constructor
    · intro hne o h1 h2; exact hne (h1.trans h2.symm)
    · intro hp heq; exact hp _ rfl heq.symm
  rw [e2]
  exact (MeasurableSet.iUnion fun o => ((g.measurableSet_preimage_singleton o).preimage
    measurable_snd).inter (measurableSet_prod_process Gs w hY hE hG hcov o)).compl

/-- The path of `X` is a random element of `L¹_loc`. -/
lemma measurable_pathClass (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) : Measurable (pathClass Gs w Y E hG hcov) :=
  measurable_of_measurable_dist fun g => measurable_dist_pathClass Gs w hY hE hG hcov g

variable [IsProbabilityMeasure P]

/-- The law of the path of `Xⁿ` in `L¹_loc([0,∞), VG ∪ {∞})`. -/
noncomputable def lawN (n : ℕ) : ProbabilityMeasure (L1loc (Option V)) :=
  ⟨P.map (pathClassN Gs w Y E n), inferInstance⟩

/-- The law of the path of `X` in `L¹_loc([0,∞), VG ∪ {∞})`. -/
noncomputable def law (hG : Monotone Gs) (hcov : ∀ x, ∃ n, x ∈ Gs n) :
    ProbabilityMeasure (L1loc (Option V)) :=
  ⟨P.map (pathClass Gs w Y E hG hcov), inferInstance⟩

/-- **Lemma 3.8, convergence in law** (p. 25, "By Lemma 3.8, we have `Xⁿ → X` in law with
respect to the metric (3.30)"): the laws of the paths of `Xⁿ` converge weakly, in the space of
probability measures on `L¹_loc([0,∞), VG ∪ {∞})`, to the law of the path of `X`.  From the
almost-sure convergence `ae_tendsto_pathClassN` by dominated convergence. -/
theorem tendsto_lawN (hY : Measurable Y) (hE : Measurable E) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hcons : ∀ᵐ ω ∂P, Consistent Gs (Y ω))
    (hsum : ∀ᵐ ω ∂P, HoldingTimesSummable Gs (Y ω) w (E ω)) :
    Tendsto (fun n => lawN P Gs w (Y := Y) (E := E) n) atTop
      (𝓝 (law P Gs w (Y := Y) (E := E) hG hcov)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hf : ∀ (F : Ω → L1loc (Option V)), Measurable F →
      ∫ ω, f ω ∂(P.map F) = ∫ ω, f (F ω) ∂P := fun F hF =>
    integral_map hF.aemeasurable f.continuous.aestronglyMeasurable
  simp only [lawN, law, ProbabilityMeasure.coe_mk]
  simp only [hf _ (measurable_pathClassN Gs w hY hE _), hf _ (measurable_pathClass Gs w hY hE hG hcov)]
  refine tendsto_integral_of_dominated_convergence (F := fun n ω => f (pathClassN Gs w Y E n ω))
    (f := fun ω => f (pathClass Gs w Y E hG hcov ω)) (fun _ => ‖f‖)
    (fun n => (f.continuous.measurable.comp
      (measurable_pathClassN Gs w hY hE n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _) ?_
  filter_upwards [ae_tendsto_pathClassN P Gs w Y E hG hcov hcons hsum] with ω hω
  exact (f.continuous.tendsto _).comp hω

end law

end ReflectedWalk.PathProperties
