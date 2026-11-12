/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39Markov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412fUnion
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF (3.24)–(3.25): from the per-arc conditional bound to the bad-step bound

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1595–1612 and 1624–1628. CONF (3.24) (Lemma 3.7 B for each good arc): a.s.
`P[G_I | 𝓕_k] ≥ 1 − C₀ε_k^α` for `I ∈ 𝓘_k ∖ 𝓘_k^*`. Proof of Lemma 3.10, C:1625–1628: "By (3.23)
and (3.24), `E[#𝓘_k^{**} | 𝓕_k] ≤ C₀ε_k^α #(𝓘_k ∖ 𝓘_k^*)`. By Markov's inequality,
`P[#𝓘_k^{**} > ¼ #(𝓘_k ∖ 𝓘_k^*) | 𝓕_k] ≤ 4C₀ε_k^α`."

* `t39_inter_compl_le_of_condExp`: `P[G | 𝓕] ≥ 1 − c` a.s. gives `P[A ∖ G] ≤ c P[A]` for `A ∈ 𝓕`;
* `t39_condMarkov`: (3.25) in the integrated form used by `t39_tail`: for arcs indexed by a
  finite set `s`, with `𝓕`-measurable presence events `Act_i` (`I_i ∈ 𝓘_k ∖ 𝓘_k^*`) and
  `P[A ∩ Act_i ∖ G_i] ≤ q P[A ∩ Act_i]` for `A ∈ 𝓕`, the event
  `#{i : Act_i} < 4 #{i : Act_i, ¬G_i}` has `P[A ∩ ·] ≤ 4q P[A]` (conditional Markov inequality,
  obtained on each level set of the `𝓕`-measurable count `#{i : Act_i}`).
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set Finset
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- the number of indices `i ∈ s` with `ω ∈ T i`, as an element of `[0, ∞]` -/
noncomputable def t39Count {ι : Type*} (s : Finset ι) (T : ι → Set Ω) (ω : Ω) : ℝ≥0∞ :=
  ∑ i ∈ s, (T i).indicator 1 ω

theorem t39Count_eq_card {ι : Type*} [DecidableEq ι] (s : Finset ι) (T : ι → Set Ω) (ω : Ω)
    [DecidablePred (fun i => ω ∈ T i)] :
    t39Count s T ω = ((s.filter fun i => ω ∈ T i).card : ℝ≥0∞) := by
  simp only [t39Count, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

theorem t39_setLIntegral_count (μ : Measure Ω) {ι : Type*} (s : Finset ι) (T : ι → Set Ω)
    (hT : ∀ i, MeasurableSet[m0] (T i)) (B : Set Ω) :
    ∫⁻ ω in B, t39Count s T ω ∂μ = ∑ i ∈ s, μ (B ∩ T i) := by
  unfold t39Count
  rw [lintegral_finsetSum (f := fun i ω => (T i).indicator 1 ω) _
    fun i _ => measurable_one.indicator (hT i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lintegral_indicator_one (hT i), Measure.restrict_apply (hT i), Set.inter_comm]

/-- **CONF (3.25)** (C:1625–1628), conditional Markov inequality in integrated form -/
theorem t39_condMarkov (μ : Measure Ω) [IsFiniteMeasure μ] (F : MeasurableSpace Ω) (hF : F ≤ m0)
    {ι : Type*} (s : Finset ι) (Act G : ι → Set Ω) (hAct : ∀ i, MeasurableSet[F] (Act i))
    (hG : ∀ i, MeasurableSet[m0] (G i)) (q : ℝ≥0∞)
    (hq : ∀ i (A : Set Ω), MeasurableSet[F] A → μ (A ∩ Act i ∩ (G i)ᶜ) ≤ q * μ (A ∩ Act i))
    (A : Set Ω) (hA : MeasurableSet[F] A) :
    μ (A ∩ {ω | t39Count s Act ω < 4 * t39Count s (fun i => Act i ∩ (G i)ᶜ) ω}) ≤
      4 * q * μ A := by
  classical
  set Y := t39Count s Act
  set X := t39Count s (fun i => Act i ∩ (G i)ᶜ)
  have hYm : Measurable[F] Y :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator (hAct i)
  have hXm : Measurable[m0] X :=
    Finset.measurable_sum _ fun i _ => measurable_const.indicator ((hF _ (hAct i)).inter (hG i).compl)
  have hY : ∀ ω, ∃ y ∈ range (s.card + 1), Y ω = y := by
    intro ω
    refine ⟨(s.filter fun i => ω ∈ Act i).card, Finset.mem_range.2 (Nat.lt_succ_of_le
      (Finset.card_filter_le _ _)), t39Count_eq_card s Act ω⟩
  set Ay : ℕ → Set Ω := fun y => A ∩ {ω | Y ω = y}
  have hAy : ∀ y, MeasurableSet[F] (Ay y) :=
    fun y => hA.inter (hYm (measurableSet_singleton _))
  have hXY : ∀ ω, X ω ≤ Y ω := fun ω =>
    Finset.sum_le_sum fun i _ => Set.indicator_le_indicator_of_subset inter_subset_left
      (fun _ => zero_le) ω
  -- the bound on each level set
  have hlev : ∀ y : ℕ, μ (Ay y ∩ {ω | Y ω < 4 * X ω}) ≤ 4 * q * μ (Ay y) := by
    intro y
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · refine (measure_mono (t := ∅) ?_).trans (by simp)
      rintro ω ⟨⟨_, h0⟩, hlt⟩
      have h0' : Y ω = 0 := by simpa using h0
      have hlt' : Y ω < 4 * X ω := hlt
      have := hXY ω
      rw [h0'] at this hlt'
      rw [nonpos_iff_eq_zero.1 this, mul_zero] at hlt'
      exact (lt_irrefl _ hlt').elim
    have hint : ∫⁻ ω in Ay y, X ω ∂μ ≤ q * y * μ (Ay y) := by
      calc ∫⁻ ω in Ay y, X ω ∂μ = ∑ i ∈ s, μ (Ay y ∩ (Act i ∩ (G i)ᶜ)) :=
            t39_setLIntegral_count μ s _ (fun i => (hF _ (hAct i)).inter (hG i).compl) _
        _ ≤ ∑ i ∈ s, q * μ (Ay y ∩ Act i) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← Set.inter_assoc]; exact hq i _ (hAy y)
        _ = q * ∫⁻ ω in Ay y, Y ω ∂μ := by
            rw [t39_setLIntegral_count μ s _ (fun i => hF _ (hAct i)) _,
              Finset.mul_sum]
        _ = q * y * μ (Ay y) := by
            rw [setLIntegral_congr_fun (hF _ (hAy y)) (g := fun _ => (y : ℝ≥0∞))
              (fun ω hω => hω.2), setLIntegral_const, mul_assoc]
    have hmk := mul_meas_ge_le_lintegral₀ (μ := μ.restrict (Ay y)) (hXm.const_mul 4).aemeasurable
      (y : ℝ≥0∞)
    rw [Measure.restrict_apply' (hF _ (hAy y))] at hmk
    have hsub : Ay y ∩ {ω | Y ω < 4 * X ω} ⊆ {ω | (y : ℝ≥0∞) ≤ 4 * X ω} ∩ Ay y := by
      rintro ω ⟨hω, hlt⟩
      refine ⟨?_, hω⟩
      have : Y ω = y := hω.2
      have hlt' : Y ω < 4 * X ω := hlt
      rw [← this]; exact le_of_lt hlt'
    have hy0 : (y : ℝ≥0∞) ≠ 0 := by exact_mod_cast hy.ne'
    refine (ENNReal.mul_le_mul_iff_right hy0 (ENNReal.natCast_ne_top y)).1 ?_
    calc (y : ℝ≥0∞) * μ (Ay y ∩ {ω | Y ω < 4 * X ω})
        ≤ y * μ ({ω | (y : ℝ≥0∞) ≤ 4 * X ω} ∩ Ay y) := by gcongr
      _ ≤ ∫⁻ ω in Ay y, 4 * X ω ∂μ := hmk
      _ = 4 * ∫⁻ ω in Ay y, X ω ∂μ := lintegral_const_mul 4 hXm
      _ ≤ 4 * (q * y * μ (Ay y)) := by gcongr
      _ = y * (4 * q * μ (Ay y)) := by ring
  have hcov : A ∩ {ω | Y ω < 4 * X ω} ⊆ ⋃ y ∈ range (s.card + 1), Ay y ∩ {ω | Y ω < 4 * X ω} := by
    rintro ω ⟨hA', hlt⟩
    obtain ⟨y, hy, hYy⟩ := hY ω
    exact Set.mem_biUnion hy ⟨⟨hA', hYy⟩, hlt⟩
  have hdisj : PairwiseDisjoint (↑(range (s.card + 1))) Ay := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun ω hi hj => hij ?_
    exact_mod_cast hi.2.symm.trans hj.2
  calc μ (A ∩ {ω | Y ω < 4 * X ω})
      ≤ ∑ y ∈ range (s.card + 1), μ (Ay y ∩ {ω | Y ω < 4 * X ω}) :=
        (measure_mono hcov).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ y ∈ range (s.card + 1), 4 * q * μ (Ay y) := Finset.sum_le_sum fun y _ => hlev y
    _ = 4 * q * μ (⋃ y ∈ range (s.card + 1), Ay y) := by
        rw [← Finset.mul_sum, measure_biUnion_finset hdisj fun y _ => hF _ (hAy y)]
    _ ≤ 4 * q * μ A := by
        gcongr; exact Set.iUnion₂_subset fun y _ => inter_subset_left

end CONF
end LQGMetric
