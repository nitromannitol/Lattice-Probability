/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepCore at commit 31e7483; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# GM Lemma 2.7 (iterating events in disjoint balls): the probabilistic core

Source: GM = Gwynne–Miller, *Existence and uniqueness of the Liouville quantum gravity metric for
`γ ∈ (0,2)`*, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 2.7
(`lem-spatial-ind`, l. 964–971) and its proof (l. 972–1004); MQ = Miller–Qian, arXiv:1812.03913,
`literature/src/1812.03913/lqg_geodesics.tex`, Lemma 4.1 (l. 549–563) and Remark 4.2 (`rmk1`,
l. 590–610: Hölder's inequality turns the RN moment bounds into bounds on probabilities).

This file proves the steps of GM's proof that do not involve the field, in "frozen" form: by the
Markov property (GM l. 974–975) the field on `⋃_z B_{1+s}(z)` is `W` (the harmonic part, determined
by `h|_{ℂ∖U}`) plus independent pieces `Y_z`, mutually independent, and `E_z = {(W, Y_z) ∈ T_z}`.

* `prob_forall_not_le` — GM (2.13) (l. 1000–1002): given the conditional lower bound `p̃` on the
  good event, `P[no E_z] ≤ P[#good < m] + (1 − p̃)^m`.  (GM write `1 − p̃^{#…}`; the correct
  bound is `1 − (1 − p̃)^{#…}`.)
* `mul_prob_card_bad_le` — GM (2.11) (l. 990–994): Markov's inequality for the number of bad
  points.
* `rnDeriv_sq_bound` — MQ Remark 4.2 / GM (2.10) via Cauchy–Schwarz: `ν(S)² ≤ (∫(dν/dμ)²dμ)·μ(S)`;
  `rn_pair_bounds` — both directions from the two moment bounds of `Blueprint.MQLem4_1`.
* `lowerBound_of_rn` — GM l. 996–998: the two RN bounds give `P[E_z | h|_{ℂ∖U}] ≥ p̃` on the
  good event, with `p̃ = (p/4)⁴/c³` (GA-8: through the zero-boundary law, as in MQ Remark 4.2).
* `frozen_union_bound` — GM Lemma 2.7 in frozen form (l. 1003–1004 choice of `n_*`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM

section Core

variable {Ω α ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
  {β : ι → Type*} [∀ i, MeasurableSpace (β i)]

/-- the number of good indices at `w` -/
def goodCount (Good : ι → Set α) (w : α) : ℕ := by
  classical exact (Finset.univ.filter fun i => w ∈ Good i).card

lemma measurable_goodCount {Good : ι → Set α} (hG : ∀ i, MeasurableSet (Good i)) :
    Measurable (goodCount Good) := by
  classical
  have : goodCount Good = fun w => ∑ i, (Good i).indicator (fun _ => (1 : ℕ)) w := by
    funext w
    simp only [goodCount, Finset.card_filter, Set.indicator_apply]
  rw [this]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (hG i)

/-- **GM (2.13)** (l. 1000–1002), frozen form. -/
theorem prob_forall_not_le (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → α}
    {Y : ∀ i, Ω → β i} (hW : Measurable W) (hY : ∀ i, Measurable (Y i))
    (hWY : IndepFun W (fun ω i => Y i ω) P) (hYi : iIndepFun Y P)
    {T : ∀ i, Set (α × β i)} (hT : ∀ i, MeasurableSet (T i))
    {Good : ι → Set α} (hG : ∀ i, MeasurableSet (Good i)) {p : ℝ≥0∞}
    (hp : ∀ i, ∀ᵐ w ∂(P.map W), w ∈ Good i → p ≤ (P.map (Y i)) {b | (w, b) ∈ T i}) (m : ℕ) :
    P {ω | ∀ i, (W ω, Y i ω) ∉ T i} ≤ P {ω | goodCount Good (W ω) < m} + (1 - p) ^ m := by
  classical
  have hYv : Measurable fun ω i => Y i ω := measurable_pi_iff.mpr hY
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hYv.aemeasurable).1 hWY
  have hpi := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hY i).aemeasurable)).1 hYi
  set S : Set (α × ∀ i, β i) := {x | ∀ i, (x.1, x.2 i) ∉ T i} with hSdef
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun x : α × (∀ i, β i) => (x.1, x.2 i)) ⁻¹' (T i)ᶜ := by
      ext x; simp [hSdef]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)) (hT i).compl
  have h1 : P {ω | ∀ i, (W ω, Y i ω) ∉ T i} =
      ∫⁻ w, ∏ i, (P.map (Y i)) {b | (w, b) ∈ T i}ᶜ ∂(P.map W) := by
    have : {ω | ∀ i, (W ω, Y i ω) ∉ T i} = (fun ω => (W ω, fun i => Y i ω)) ⁻¹' S := by
      ext ω; simp [hSdef]
    rw [this, ← Measure.map_apply (hW.prodMk hYv) hS, hlaw, Measure.prod_apply hS, hpi]
    refine lintegral_congr fun w => ?_
    have : Prod.mk w ⁻¹' S = Set.univ.pi fun i => {b | (w, b) ∈ T i}ᶜ := by
      ext y; simp [hSdef]
    rw [this, Measure.pi_pi]
  have hbd : ∀ᵐ w ∂(P.map W), ∏ i, (P.map (Y i)) {b | (w, b) ∈ T i}ᶜ ≤
      {w | goodCount Good w < m}.indicator 1 w + (1 - p) ^ m := by
    filter_upwards [ae_all_iff.2 hp] with w hpw
    have hle1 : ∀ i, (P.map (Y i)) {b | (w, b) ∈ T i}ᶜ ≤ 1 := fun i => by
      exact prob_le_one
    by_cases hc : goodCount Good w < m
    · rw [Set.indicator_of_mem (by exact hc)]
      exact le_add_right (Finset.prod_le_one fun i _ => hle1 i)
    · rw [Set.indicator_of_notMem (by exact hc), zero_add]
      push Not at hc
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ fun i => w ∈ Good i]
      calc _ ≤ (∏ i ∈ Finset.univ.filter fun i => w ∈ Good i, (1 - p)) * 1 := by
            refine mul_le_mul' (Finset.prod_le_prod fun i hi => ?_)
              (Finset.prod_le_one fun i _ => hle1 i)
            have hm : MeasurableSet {b | (w, b) ∈ T i} := measurable_prodMk_left (hT i)
            rw [prob_compl_eq_one_sub hm]
            exact tsub_le_tsub_left (hpw i (Finset.mem_filter.1 hi).2) 1
        _ = (1 - p) ^ goodCount Good w := by simp [goodCount]
        _ ≤ (1 - p) ^ m := pow_le_pow_right_of_le_one' tsub_le_self hc
  rw [h1]
  have hmeas : MeasurableSet {w | goodCount Good w < m} :=
    measurableSet_lt (measurable_goodCount hG) measurable_const
  calc _ ≤ ∫⁻ w, ({w | goodCount Good w < m}.indicator 1 w + (1 - p) ^ m) ∂(P.map W) :=
        lintegral_mono_ae hbd
    _ = (P.map W) {w | goodCount Good w < m} + (1 - p) ^ m := by
        rw [lintegral_add_right _ measurable_const, lintegral_indicator_one hmeas]
        simp
    _ = _ := by rw [Measure.map_apply hW hmeas]; rfl

/-- **GM (2.11)** (l. 990–994): Markov's inequality for the number of bad indices. -/
theorem mul_prob_card_bad_le (P : Measure Ω) {W : Ω → α} (hW : Measurable W)
    {Good : ι → Set α} (hG : ∀ i, MeasurableSet (Good i)) (k : ℕ) :
    (k : ℝ≥0∞) * P {ω | (k : ℝ≥0∞) ≤ ∑ i, (Good i)ᶜ.indicator 1 (W ω)} ≤
      ∑ i, P {ω | W ω ∉ Good i} := by
  have hf : Measurable fun ω => ∑ i, (Good i)ᶜ.indicator (1 : α → ℝ≥0∞) (W ω) :=
    Finset.measurable_sum _ fun i _ => (measurable_const.indicator (hG i).compl).comp hW
  refine (mul_meas_ge_le_lintegral₀ hf.aemeasurable _).trans_eq ?_
  rw [lintegral_finsetSum (Finset.univ)
    (f := fun i ω => (Good i)ᶜ.indicator (1 : α → ℝ≥0∞) (W ω))
    fun i _ => (measurable_const.indicator (hG i).compl).comp hW]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (fun ω => (Good i)ᶜ.indicator (1 : α → ℝ≥0∞) (W ω)) =
      (W ⁻¹' (Good i)ᶜ).indicator 1 := by
    funext ω; by_cases h : W ω ∈ Good i <;> simp [h]
  rw [this, lintegral_indicator_one (hW (hG i).compl)]
  rfl

omit [MeasurableSpace α] in
lemma card_bad_ge {Good : ι → Set α} {w : α} {m : ℕ} (hm : m ≤ Fintype.card ι)
    (hc : goodCount Good w < m) :
    ((Fintype.card ι - m + 1 : ℕ) : ℝ≥0∞) ≤ ∑ i, (Good i)ᶜ.indicator 1 w := by
  classical
  have hsum : (∑ i, (Good i)ᶜ.indicator (1 : α → ℝ≥0∞) w) =
      ((Finset.univ.filter fun i => ¬ w ∈ Good i).card : ℝ≥0∞) := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w ∈ Good i <;> simp [h]
  rw [hsum]
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
    (fun i => w ∈ Good i)
  have : goodCount Good w = (Finset.univ.filter fun i => w ∈ Good i).card := by
    simp only [goodCount]
  rw [Finset.card_univ] at h2
  exact_mod_cast (by omega)

/-- **MQ Remark 4.2 / GM (2.10)**, Cauchy–Schwarz form: `ν(S)² ≤ (∫(dν/dμ)² dμ) μ(S)`. -/
theorem rnDeriv_sq_bound {β : Type*} [MeasurableSpace β] {μ ν : Measure β} [SFinite μ]
    [ν.HaveLebesgueDecomposition μ] (hνμ : ν ≪ μ) {S : Set β} (hS : MeasurableSet S) :
    ν S ^ 2 ≤ (∫⁻ x, ν.rnDeriv μ x ^ (2 : ℝ) ∂μ) * μ S := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h1 : ν S = ∫⁻ x, (ν.rnDeriv μ * S.indicator (1 : β → ℝ≥0∞)) x ∂μ := by
    rw [← Measure.setLIntegral_rnDeriv' hνμ hS, ← lintegral_indicator hS]
    congr 1; funext x; by_cases hx : x ∈ S <;> simp [hx]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq (f := ν.rnDeriv μ)
    (g := S.indicator (1 : β → ℝ≥0∞)) (Measure.measurable_rnDeriv ν μ).aemeasurable
    (measurable_const.indicator hS).aemeasurable
  have h3 : ∫⁻ x, S.indicator (1 : β → ℝ≥0∞) x ^ (2 : ℝ) ∂μ = μ S := by
    rw [← lintegral_indicator_one hS]
    congr 1; funext x; by_cases hx : x ∈ S <;> simp [hx]
  rw [h3, ← h1] at h2
  calc ν S ^ 2 ≤ ((∫⁻ x, ν.rnDeriv μ x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ S ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ zero_le h2 2
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

/-- `P[E_i] = ∫ φ_i(W) dP` with `φ_i(w) = P[(w, Y_i) ∈ T_i]` (freezing `W`). -/
theorem prob_eq_lintegral_section (P : Measure Ω) [IsProbabilityMeasure P] {W : Ω → α}
    {β' : Type*} [MeasurableSpace β'] {Y : Ω → β'} (hW : Measurable W) (hY : Measurable Y)
    (hWY : IndepFun W Y P) {T : Set (α × β')} (hT : MeasurableSet T) :
    P {ω | (W ω, Y ω) ∈ T} = ∫⁻ w, (P.map Y) {b | (w, b) ∈ T} ∂(P.map W) := by
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hW.aemeasurable hY.aemeasurable).1 hWY
  have : {ω | (W ω, Y ω) ∈ T} = (fun ω => (W ω, Y ω)) ⁻¹' T := rfl
  rw [this, ← Measure.map_apply (hW.prodMk hY) hT, hlaw, Measure.prod_apply hT]
  rfl

/-- **GM l. 996–998** (via MQ Remark 4.2): the two RN bounds on the good set and
`P[W ∉ Good] ≤ p/4`, `P[E] ≥ p` give the conditional lower bound `φ ≥ (p/4)⁴/c³` on `Good`. -/
theorem lowerBound_of_rn {μW : Measure α} [IsProbabilityMeasure μW] {φ : α → ℝ≥0∞}
    (hφ1 : ∀ w, φ w ≤ 1) {Good : Set α} (hG : MeasurableSet Good)
    {p c a : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) (hbad : μW Goodᶜ ≤ p / 4)
    (hE : p ≤ ∫⁻ w, φ w ∂μW)
    (hrn : ∀ᵐ w ∂μW, w ∈ Good → φ w ^ 2 ≤ c * a ∧ a ^ 2 ≤ c * φ w) :
    ∀ᵐ w ∂μW, w ∈ Good → (p / 4) ^ 4 / c ^ 3 ≤ φ w := by
  have hca : (p / 4) ^ 2 < c * a := by
    by_contra hle
    push Not at hle
    have hb : ∀ᵐ w ∂μW, φ w ≤ p / 4 + Goodᶜ.indicator 1 w := by
      filter_upwards [hrn] with w hrw
      by_cases hw : w ∈ Good
      · have h := ((hrw hw).1.trans hle)
        refine le_add_right ?_
        by_contra hlt
        push Not at hlt
        rw [pow_two, pow_two] at h
        exact absurd (ENNReal.mul_lt_mul hlt hlt) (not_lt.2 h)
      · rw [Set.indicator_of_mem (show w ∈ Goodᶜ from hw)]
        exact (hφ1 w).trans (le_add_left le_rfl)
    have hint : ∫⁻ w, φ w ∂μW ≤ p / 4 + p / 4 := by
      calc _ ≤ ∫⁻ w, (p / 4 + Goodᶜ.indicator 1 w) ∂μW := lintegral_mono_ae hb
        _ = p / 4 + μW Goodᶜ := by
            rw [lintegral_add_left measurable_const,
              lintegral_indicator_one hG.compl]
            simp
        _ ≤ _ := add_le_add le_rfl hbad
    have h2 : p / 4 + p / 4 < p := by
      have h4 : p / 4 + p / 4 = p / 2 := by
        rw [ENNReal.div_add_div_same, ← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
          ENNReal.mul_div_mul_left _ _ (by norm_num) (by norm_num)]
      rw [h4]
      exact ENNReal.half_lt_self hp0 hpt
    exact absurd (hE.trans hint) (not_le.2 h2)
  filter_upwards [hrn] with w hrw hw
  refine ENNReal.div_le_of_le_mul ?_
  calc (p / 4) ^ 4 = ((p / 4) ^ 2) ^ 2 := by ring
    _ ≤ (c * a) ^ 2 := pow_le_pow_left₀ zero_le hca.le 2
    _ = c ^ 2 * a ^ 2 := by ring
    _ ≤ c ^ 2 * (c * φ w) := by gcongr; exact (hrw hw).2
    _ = φ w * c ^ 3 := by ring

/-- **MQ Remark 4.2** (l. 590–610) in the form used by GM l. 996–998: mutually absolutely
continuous finite measures whose RN derivatives have second moments `≤ c` (the output of
`Blueprint.MQLem4_1` with exponent `2`) satisfy `μg(S)² ≤ c μ₀(S)` and `μ₀(S)² ≤ c μg(S)`. -/
theorem rn_pair_bounds {β : Type*} [MeasurableSpace β] {μ₀ μg : Measure β} [IsFiniteMeasure μ₀]
    [IsFiniteMeasure μg] (h1 : μg ≪ μ₀) (h2 : μ₀ ≪ μg) {c : ℝ≥0∞}
    (hc1 : ∫⁻ x, μg.rnDeriv μ₀ x ^ (2 : ℝ) ∂μ₀ ≤ c)
    (hc2 : ∫⁻ x, μ₀.rnDeriv μg x ^ (2 : ℝ) ∂μg ≤ c) {S : Set β} (hS : MeasurableSet S) :
    μg S ^ 2 ≤ c * μ₀ S ∧ μ₀ S ^ 2 ≤ c * μg S :=
  ⟨(rnDeriv_sq_bound h1 hS).trans (by gcongr), (rnDeriv_sq_bound h2 hS).trans (by gcongr)⟩

end Core

section Frozen

universe u v w x

/-- **GM Lemma 2.7, frozen form** (GM l. 972–1004): `W` (the harmonic part) independent of the
mutually independent pieces `Y_i`; `E_i = {(W, Y_i) ∈ T_i}` with `P[E_i] ≥ p`; for `P_W`-a.e. `w`
in the good set `Good_i` (`𝔐_z ≤ A`, of probability `≥ 1 − min(p/4, (1−q)/4)`) the conditional probability
`φ_i(w) = P[(w, Y_i) ∈ T_i]` and a number `a_i` (the zero-boundary probability `μ₀(S)`) satisfy the
two RN bounds of MQ Remark 4.2 with constant `c`. Then `P[⋃ E_i] ≥ q` once `#ι ≥ n₀(p,q,c)`. -/
theorem frozen_union_bound {p q c : ℝ} (hp : 0 < p) (hq1 : q < 1) :
    ∃ n₀ : ℕ, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {α : Type v} [MeasurableSpace α] {ι : Type w} [Fintype ι] {β : ι → Type x}
      [∀ i, MeasurableSpace (β i)] (W : Ω → α) (Y : ∀ i, Ω → β i), n₀ ≤ Fintype.card ι →
      Measurable W → (∀ i, Measurable (Y i)) → IndepFun W (fun ω i => Y i ω) P →
      iIndepFun Y P → ∀ T : ∀ i, Set (α × β i), (∀ i, MeasurableSet (T i)) →
      ∀ Good : ι → Set α, (∀ i, MeasurableSet (Good i)) →
      (∀ i, P (W ⁻¹' (Good i)ᶜ) ≤ ENNReal.ofReal (min (p / 4) ((1 - q) / 4))) →
      ∀ a : ι → ℝ≥0∞, (∀ i, ∀ᵐ w ∂(P.map W), w ∈ Good i →
        (P.map (Y i)) {b | (w, b) ∈ T i} ^ 2 ≤ ENNReal.ofReal c * a i ∧
          a i ^ 2 ≤ ENNReal.ofReal c * (P.map (Y i)) {b | (w, b) ∈ T i}) →
      (∀ i, ENNReal.ofReal p ≤ P {ω | (W ω, Y i ω) ∈ T i}) →
      ENNReal.ofReal q ≤ P {ω | ∃ i, (W ω, Y i ω) ∈ T i} := by
  set p' := ENNReal.ofReal p
  set c' := ENNReal.ofReal c
  set pt : ℝ≥0∞ := (p' / 4) ^ 4 / c' ^ 3 with hptdef
  have hp'0 : p' ≠ 0 := by simp [p', hp]
  have hpt0 : pt ≠ 0 := (ENNReal.div_pos_iff.2 ⟨pow_ne_zero _ (by simp [hp'0]),
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top⟩).ne'
  have hlt : 1 - pt < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpt0
  have hq2 : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 - q) / 2) := by simp; linarith
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    ((ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt).eventually (Iio_mem_nhds hq2))
  refine ⟨2 * m₀, ?_⟩
  intro Ω _ P _ α _ ι _ β _ W Y hn hW hY hWY hYi T hT Good hG hbad a hrn hpE
  classical
  -- the conditional lower bound `p̃` on the good set (GM l. 996–998)
  have hpt : ∀ i, ∀ᵐ w ∂(P.map W), w ∈ Good i → pt ≤ (P.map (Y i)) {b | (w, b) ∈ T i} := by
    intro i
    have hWYi : IndepFun W (Y i) P := hWY.comp measurable_id (measurable_pi_apply i)
    refine lowerBound_of_rn (μW := P.map W) (φ := fun w => (P.map (Y i)) {b | (w, b) ∈ T i})
      (fun w => prob_le_one) (hG i) hp'0 ENNReal.ofReal_ne_top ?_ ?_ (hrn i)
    · rw [Measure.map_apply hW (hG i).compl]
      refine (hbad i).trans ?_
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_div_of_pos (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · exact (hpE i).trans (prob_eq_lintegral_section P hW (hY i) hWYi (hT i)).le
  have hmain := prob_forall_not_le P hW hY hWY hYi hT hG hpt m₀
  -- the count of bad points (GM (2.11))
  set k := Fintype.card ι - m₀ + 1
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by simp [k]
  have hcount : P {ω | goodCount Good (W ω) < m₀} ≤ ENNReal.ofReal ((1 - q) / 2) := by
    have hsub : {ω | goodCount Good (W ω) < m₀} ⊆
        {ω | (k : ℝ≥0∞) ≤ ∑ i, (Good i)ᶜ.indicator 1 (W ω)} :=
      fun ω hω => card_bad_ge (by omega) hω
    have hM := mul_prob_card_bad_le P hW hG k
    set δ := ENNReal.ofReal ((1 - q) / 4)
    have hsum : ∑ i, P {ω | W ω ∉ Good i} ≤ (Fintype.card ι : ℝ≥0∞) * δ := by
      calc _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ =>
            (hbad i).trans (ENNReal.ofReal_le_ofReal (min_le_right _ _))
        _ = _ := by simp
    have h2k : (Fintype.card ι : ℝ≥0∞) ≤ (k : ℝ≥0∞) * 2 := by
      exact_mod_cast (show Fintype.card ι ≤ k * 2 by omega)
    have h2δ : ENNReal.ofReal ((1 - q) / 2) = 2 * δ := by
      rw [show (1 - q) / 2 = 2 * ((1 - q) / 4) by ring, ENNReal.ofReal_mul (by norm_num)]
      simp [δ]
    have : (k : ℝ≥0∞) * P {ω | (k : ℝ≥0∞) ≤ ∑ i, (Good i)ᶜ.indicator 1 (W ω)} ≤
        (k : ℝ≥0∞) * ENNReal.ofReal ((1 - q) / 2) := by
      calc _ ≤ _ := hM
        _ ≤ _ := hsum
        _ ≤ (k : ℝ≥0∞) * 2 * δ := by gcongr
        _ = _ := by rw [h2δ, mul_assoc]
    exact (measure_mono hsub).trans
      ((ENNReal.mul_le_mul_iff_right hk0 (ENNReal.natCast_ne_top k)).1 this)
  have hall : P {ω | ∀ i, (W ω, Y i ω) ∉ T i} ≤ ENNReal.ofReal (1 - q) := by
    calc _ ≤ _ := hmain
      _ ≤ ENNReal.ofReal ((1 - q) / 2) + ENNReal.ofReal ((1 - q) / 2) :=
          add_le_add hcount (hm₀ m₀ le_rfl).le
      _ = _ := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  have hmeas : MeasurableSet {ω | ∀ i, (W ω, Y i ω) ∉ T i} := by
    have : {ω | ∀ i, (W ω, Y i ω) ∉ T i} = ⋂ i, (fun ω => (W ω, Y i ω)) ⁻¹' (T i)ᶜ := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun i => (hW.prodMk (hY i)) (hT i).compl
  have hc : {ω | ∃ i, (W ω, Y i ω) ∈ T i} = {ω | ∀ i, (W ω, Y i ω) ∉ T i}ᶜ := by
    ext ω; simp
  rw [hc, prob_compl_eq_one_sub hmeas]
  calc ENNReal.ofReal q = 1 - ENNReal.ofReal (1 - q) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]; ring_nf
    _ ≤ _ := tsub_le_tsub_left hall 1

end Frozen

end LQGMetric.GM
