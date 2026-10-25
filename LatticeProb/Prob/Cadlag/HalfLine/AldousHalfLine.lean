import LatticeProb.External.EthierKurtzStopping
import LatticeProb.Prob.ChoiceUniformity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The half-line stopping-increment compactness criterion

The stopping-increment condition along every full sequence of bounded discrete stopping
times implies the two oscillation limits in the cited Ethier–Kurtz sequence criterion.
The past supremum remains inside the expectation throughout the estimate.
-/

namespace LatticeProb

open Filter Set
open scoped Topology ENNReal

/-- The dependent-choice uniformity argument in an arbitrary linear order. -/
theorem exists_eventually_forall_of_forall_choices_order
    {R : Type*} [LinearOrder R] {S : ℕ → Type*} [∀ n, Nonempty (S n)]
    (p : (n : ℕ) → ℕ → S n → R)
    (hanti : ∀ n (s : S n), Antitone (fun k => p n k s))
    (η : R)
    (hchoices : ∀ σ : (n : ℕ) → S n,
      ∃ k N : ℕ, ∀ n, N ≤ n → p n k (σ n) < η) :
    ∃ k N : ℕ, ∀ n, N ≤ n → ∀ s : S n, p n k s < η := by
  classical
  by_contra h
  push Not at h
  choose next hnext hwitness using h
  let index : ℕ → ℕ := fun k =>
    Nat.rec (next 0 0) (fun j previous => next (j + 1) (previous + 1)) k
  have hindex : StrictMono index := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact lt_of_lt_of_le (Nat.lt_succ_self (index k)) (hnext (k + 1) (index k + 1))
  have hbad : ∀ k, ∃ s : S (index k), η ≤ p (index k) k s := by
    intro k
    cases k with
    | zero => exact hwitness 0 0
    | succ k => exact hwitness (k + 1) (index k + 1)
  have hfill : ∀ n : ℕ, ∃ s : S n, ∀ k : ℕ, index k = n → η ≤ p n k s := by
    intro n
    rcases Classical.em (∃ k : ℕ, index k = n) with hn | hn
    · obtain ⟨k, rfl⟩ := hn
      obtain ⟨s, hs⟩ := hbad k
      refine ⟨s, ?_⟩
      intro j hj
      have hjk : j = k := hindex.injective hj
      subst j
      exact hs
    · refine ⟨Classical.ofNonempty, ?_⟩
      intro k hk
      exact (hn ⟨k, hk⟩).elim
  choose σ hσ using hfill
  obtain ⟨K, N, hbound⟩ := hchoices σ
  have hindex_ge : ∀ k, k ≤ index k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k hk => exact Nat.succ_le_of_lt (lt_of_le_of_lt hk (hindex (Nat.lt_succ_self k)))
  let k := max K N
  have hNk : N ≤ index k := le_trans (le_max_right K N) (hindex_ge k)
  have hlarge : η ≤ p (index k) K (σ (index k)) :=
    le_trans (hσ (index k) k rfl) (hanti (index k) (σ (index k)) (le_max_left K N))
  exact (not_lt_of_ge hlarge) (hbound (index k) hNk)

/-- Limits along every full choice sequence give a positive window with a uniform
late-index bound. Monotonicity refers to increasing the window size. -/
theorem exists_pos_eventually_forall_of_tendsto_choices
    {S : ℕ → Type*} [∀ n, Nonempty (S n)]
    (p : ℝ → (n : ℕ) → S n → ℝ≥0∞)
    (hmono : ∀ n s, Monotone (fun d => p d n s))
    (hchoices : ∀ σ : (n : ℕ) → S n,
      Tendsto (fun d => limsup (fun n => p d n (σ n)) atTop) (𝓝[>] 0) (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∃ N : ℕ, ∀ n, N ≤ n → ∀ s : S n, p d n s < ε := by
  let scale : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hpos (k : ℕ) : 0 < scale k := by dsimp [scale]; positivity
  have hscale : Tendsto scale atTop (𝓝[>] 0) := by
    exact tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall hpos⟩
  have hanti : Antitone scale := by
    intro i j hij
    dsimp [scale]
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  obtain ⟨k, N, hk⟩ := exists_eventually_forall_of_forall_choices_order
    (fun n k s => p (scale k) n s)
    (fun n s i j hij => hmono n s (hanti hij)) ε (fun σ => by
      have hlim := (hchoices σ).comp hscale
      obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
      obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt hk)
      exact ⟨k, N, hN⟩)
  exact ⟨scale k, hpos k, N, hk⟩

end LatticeProb

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory TopologicalSpace External
open scoped Topology ENNReal NNReal

noncomputable section

variable {E Ω : Type*} [MetricSpace E] [MeasurableSpace E] [MeasurableSpace Ω]

omit [MeasurableSpace E] in
/-- A truncated distance has expectation at most the threshold plus its tail probability.
No measurability is needed: the event probability is the measure's outer measure. -/
theorem lintegral_truncated_dist_le (P : ProbabilityMeasure Ω) (f g : Ω → E)
    (η : ℝ) :
    (∫⁻ w, ENNReal.ofReal (min (dist (f w) (g w)) 1) ∂P) ≤
      ENNReal.ofReal η + (P : Measure Ω) {w | η ≤ dist (f w) (g w)} := by
  let A := {w | η ≤ dist (f w) (g w)}
  calc
    _ ≤ ∫⁻ w, ENNReal.ofReal η + A.indicator (fun _ => (1 : ℝ≥0∞)) w ∂P := by
      apply lintegral_mono
      intro w
      dsimp only
      by_cases hw : w ∈ A
      · rw [Set.indicator_of_mem hw]
        exact (ENNReal.ofReal_le_ofReal (min_le_right _ _)).trans
          (by simpa only [ENNReal.ofReal_one] using
            (le_add_self : (1 : ℝ≥0∞) ≤ ENNReal.ofReal η + 1))
      · rw [Set.indicator_of_notMem hw, add_zero]
        exact ENNReal.ofReal_le_ofReal ((min_le_left _ _).trans (le_of_not_ge hw))
    _ = ENNReal.ofReal η + ∫⁻ w, A.indicator (fun _ => (1 : ℝ≥0∞)) w ∂P := by
      rw [lintegral_add_left measurable_const, lintegral_const]
      simp only [measure_univ, mul_one]
    _ ≤ _ := add_le_add_right (lintegral_indicator_one_le A) _

omit [MeasurableSpace E] [MeasurableSpace Ω] in
/-- At exponent one every increment is bounded by one. -/
theorem incrementPower_one_le (Y : Ω → D E) (s t : Time) (w : Ω) :
    incrementPower Y 1 s t w ≤ 1 := by
  simpa only [incrementPower, Real.rpow_one, ENNReal.ofReal_one] using
    (ENNReal.ofReal_le_ofReal (min_le_right (dist ((Y w).1 s) ((Y w).1 t)) 1))

/-- A uniform stopping-increment probability bound controls the genuine stopping oscillation.
The past factor is bounded pointwise before its supremum is integrated. -/
theorem stoppingOscillation_le_of_increment_bound (P : ProbabilityMeasure Ω)
    (Y : Ω → D E) {T δ η : ℝ} {b : ℝ≥0∞}
    (hb : ∀ τ : Ω → Time, discreteNaturalStopping Y T τ →
      ∀ u : Time, (u : ℝ) ≤ δ →
        (P : Measure Ω) {w | η ≤ dist ((Y w).1 (τ w + u)) ((Y w).1 (τ w))} ≤ b) :
    stoppingOscillation P Y 1 T δ ≤ ENNReal.ofReal η + b := by
  refine iSup_le fun τ => iSup_le fun hτ => iSup_le fun u => iSup_le fun hu => ?_
  calc
    _ ≤ ∫⁻ w, incrementPower Y 1 (τ w + u) (τ w) w ∂P := by
      apply lintegral_mono
      intro w
      exact iSup_le fun v => iSup_le fun _ =>
        mul_le_of_le_one_right' (incrementPower_one_le Y _ _ w)
    _ ≤ ENNReal.ofReal η +
        (P : Measure Ω) {w | η ≤ dist ((Y w).1 (τ w + u)) ((Y w).1 (τ w))} := by
      simpa only [incrementPower, Real.rpow_one] using
        lintegral_truncated_dist_le P (fun w => (Y w).1 (τ w + u))
          (fun w => (Y w).1 (τ w)) η
    _ ≤ _ := add_le_add_right (hb τ hτ u hu) _

section Sequence

variable {E : Type} [MetricSpace E] [MeasurableSpace E]
    {Ω : ℕ → Type} [m : ∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, ProbabilityMeasure (Ω n)) (Y : ∀ n, Ω n → D E)

/-- The literal stopping-increment hypothesis, quantified over full stopping-time sequences. -/
def stoppingIncrementCondition : Prop :=
  ∀ H : ℝ, 0 < H → ∀ η : ℝ, 0 < η →
    ∀ τ : (n : ℕ) → Ω n → Time, (∀ n, discreteNaturalStopping (Y n) H (τ n)) →
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ δ),
          (P n : Measure (Ω n))
            {w | η ≤ dist ((Y n w).1 (τ n w + u)) ((Y n w).1 (τ n w))}) atTop)
        (𝓝[>] 0) (𝓝 0)

/-- The full-sequence hypothesis gives one positive window and a uniform late-index tail. -/
theorem exists_pos_eventually_stopping_increment_bound
    (h : stoppingIncrementCondition P Y) {H η : ℝ} (hH : 0 < H) (hη : 0 < η)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ d : ℝ, 0 < d ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ τ : Ω n → Time, discreteNaturalStopping (Y n) H τ →
        ∀ u : Time, (u : ℝ) ≤ d →
          (P n : Measure (Ω n))
            {w | η ≤ dist ((Y n w).1 (τ w + u)) ((Y n w).1 (τ w))} ≤ ε := by
  let S (n : ℕ) := {τ : Ω n → Time // discreteNaturalStopping (Y n) H τ}
  haveI (n : ℕ) : Nonempty (S n) :=
    ⟨⟨fun _ => 0, discreteNaturalStopping_zero _ hH.le⟩⟩
  let p (d : ℝ) (n : ℕ) (τ : S n) : ℝ≥0∞ :=
    ⨆ u : Time, ⨆ (_ : (u : ℝ) ≤ d),
      (P n : Measure (Ω n))
        {w | η ≤ dist ((Y n w).1 (τ.1 w + u)) ((Y n w).1 (τ.1 w))}
  obtain ⟨d, hd, N, hN⟩ := LatticeProb.exists_pos_eventually_forall_of_tendsto_choices p
    (fun n τ a b hab => iSup_le fun u => iSup_le fun hu =>
      le_iSup_of_le u (le_iSup_of_le (hu.trans hab) le_rfl))
    (fun σ => h H hH η hη (fun n => (σ n).1) (fun n => (σ n).2)) hε
  refine ⟨d, hd, N, fun n hn τ hτ u hu => ?_⟩
  refine le_trans ?_ (hN n hn ⟨τ, hτ⟩).le
  dsimp only [p]
  exact le_iSup_of_le u (le_iSup_of_le hu le_rfl)

/-- The two sequential oscillation limits required by the cited stopping criterion follow
from the full-sequence stopping-increment hypothesis, with exponent one. -/
theorem tendsto_stoppingOscillation_and_initial_of_stoppingIncrementCondition
    (h : stoppingIncrementCondition P Y) {H : ℝ} (hH : 0 < H) :
    Tendsto (fun δ : ℝ => limsup (fun n => stoppingOscillation (P n) (Y n) 1 H δ) atTop)
        (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun δ : ℝ => limsup (fun n =>
        ∫⁻ w, incrementPower (Y n) 1 δ.toNNReal 0 w ∂P n) atTop)
        (𝓝[>] 0) (𝓝 0) := by
  have hbound (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ d : ℝ, 0 < d ∧ ∀ δ : ℝ, 0 < δ → δ ≤ d →
        limsup (fun n => stoppingOscillation (P n) (Y n) 1 H δ) atTop ≤ ε ∧
          limsup (fun n => ∫⁻ w, incrementPower (Y n) 1 δ.toNNReal 0 w ∂P n)
            atTop ≤ ε := by
    obtain ⟨r, hr, hrpos, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
    have hr' : 0 < r := ENNReal.ofReal_pos.mp hrpos
    let η := r / 2
    have hη : 0 < η := half_pos hr'
    obtain ⟨d, hd, N, hN⟩ :=
      exists_pos_eventually_stopping_increment_bound P Y h hH hη
        (ENNReal.ofReal_pos.mpr hη)
    have hsum : ENNReal.ofReal η + ENNReal.ofReal η ≤ ε := by
      rw [← ENNReal.ofReal_add hη.le hη.le]
      have heq : η + η = r := by dsimp [η]; ring
      rw [heq]
      exact hrε.le
    refine ⟨d, hd, fun δ hδ hδd => ⟨?_, ?_⟩⟩
    · apply (limsup_le_of_le (h := ?_)).trans hsum
      filter_upwards [eventually_ge_atTop N] with n hn
      exact stoppingOscillation_le_of_increment_bound (P n) (Y n)
        (fun τ hτ u hu => hN n hn τ hτ u (hu.trans hδd))
    · apply (limsup_le_of_le (h := ?_)).trans hsum
      filter_upwards [eventually_ge_atTop N] with n hn
      have htail := hN n hn (fun _ => 0) (discreteNaturalStopping_zero _ hH.le)
        δ.toNNReal (by simpa only [Real.coe_toNNReal _ hδ.le] using hδd)
      have hint := lintegral_truncated_dist_le (P n)
        (fun w => (Y n w).1 δ.toNNReal) (fun w => (Y n w).1 0) η
      simp only [zero_add] at htail
      simpa only [incrementPower, Real.rpow_one] using
        hint.trans (add_le_add_right htail _)
  constructor
  · apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨d, hd, hb⟩ := hbound ε hε
    filter_upwards [(eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with δ hδd hδ
    exact (hb δ hδ hδd.le).1
  · apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    obtain ⟨d, hd, hb⟩ := hbound ε hε
    filter_upwards [(eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with δ hδd hδ
    exact (hb δ hδ hδd.le).2

variable [BorelSpace E] [CompleteSpace E] [SeparableSpace E]

/-- Half-line Aldous compactness for separate probability spaces, from the exact cited
Ethier–Kurtz input and the literal full-sequence stopping-increment condition. -/
theorem isCompact_closure_range_map_of_stoppingIncrementCondition
    (hEK : External.EthierKurtzRelativeCompactnessStopping)
    (hY : ∀ n, Measurable (Y n))
    (hmarginal : ∀ η : ℝ, 0 < η → ∀ t : ℚ, 0 ≤ t →
      ∃ K : Set E, IsCompact K ∧ ∀ n,
        ENNReal.ofReal (1 - η) ≤ (P n : Measure (Ω n))
          {w | (Y n w).1 (t : ℝ).toNNReal ∈ K})
    (h : stoppingIncrementCondition P Y) :
    IsCompact (closure (range (fun n => (P n).map (hY n).aemeasurable))) := by
  refine hEK.2 E Ω m P Y hY
    (fun n t => (measurable_eval t).comp (hY n)) hmarginal ?_
  intro H hH
  obtain ⟨hosc, hinit⟩ :=
    tendsto_stoppingOscillation_and_initial_of_stoppingIncrementCondition P Y h hH
  exact ⟨1, zero_lt_one, hosc, hinit⟩

end Sequence

/-- The literal stopping-increment condition holds for an actual constant process
on the one-point probability space. -/
theorem stoppingIncrementCondition_const (a : ℝ) :
    stoppingIncrementCondition (fun _ : ℕ => unitLaw) (fun _ _ => const a) := by
  intro H hH η hη τ hτ
  simp only [const, dist_self, not_le.mpr hη, setOf_false, measure_empty,
    ENNReal.iSup_zero, limsup_const]
  exact tendsto_const_nhds

/-- The proved half-line adapter applies to a genuine constant real process and its law. -/
theorem isCompact_closure_range_constantProcessLaw_of_stoppingIncrementCondition
    (hEK : External.EthierKurtzRelativeCompactnessStopping) (a : ℝ) :
    IsCompact (closure (range (fun _ : ℕ => constantProcessLaw a))) := by
  apply isCompact_closure_range_map_of_stoppingIncrementCondition
    (fun _ : ℕ => unitLaw) (fun _ _ => const a) hEK (fun _ => measurable_const)
  · intro η hη t ht
    refine ⟨{a}, isCompact_singleton, fun n => ?_⟩
    simp only [const, mem_singleton_iff, setOf_true, measure_univ]
    exact (ENNReal.ofReal_le_ofReal (sub_le_self 1 hη.le)).trans_eq
      ENNReal.ofReal_one
  · exact stoppingIncrementCondition_const a

end

end LatticeProb.Cadlag.HalfLine
