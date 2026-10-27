import LatticeProb.Prob.Percolation.LatticeRadialTail
import LatticeProb.Prob.StochasticO
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable radial bad-point events

The radial bad-point event is measurable for a countable measurable lattice field.
-/

open MeasureTheory LatticeProb Filter
open scoped ENNReal Topology

namespace LatticeProb.Percolation

/-- The event that a radial threshold fails is measurable for a measurable lattice field. -/
theorem measurableSet_radial_bad {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (X : Vertex d → Ω → ℝ) (hX : ∀ x, Measurable (X x))
    (y : Vertex d) (R α : ℝ) :
    MeasurableSet {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} := by
  classical
  have heq : {ω | ∃ x : Vertex d, R ≤ ‖latticeEuclideanEmbedding x -
      latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} =
      ⋃ x : Vertex d, {ω | R ≤ ‖latticeEuclideanEmbedding x -
        latticeEuclideanEmbedding y‖ ∧
        ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  rw [heq]
  apply MeasurableSet.iUnion
  intro x
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (hX x))


/-- A measurable first good index has its upper tail inside each corresponding bad event. -/
theorem exists_measurable_first_good {Ω : Type*} [MeasurableSpace Ω]
    (bad : ℕ → Set Ω) (hbad : ∀ n, MeasurableSet (bad n)) :
    ∃ N : Ω → ℕ, Measurable N ∧
      (∀ ω, (∃ n, ω ∉ bad n) → ω ∉ bad (N ω)) ∧
      (∀ n ω, n < N ω → ω ∈ bad n) := by
  classical
  let q : Ω → ℕ → Prop := fun ω n =>
    ω ∉ bad n ∨ ((∀ k, ω ∈ bad k) ∧ n = 0)
  have hex : ∀ ω, ∃ n, q ω n := by
    intro ω
    by_cases h : ∃ n, ω ∉ bad n
    · obtain ⟨n, hn⟩ := h
      exact ⟨n, Or.inl hn⟩
    · refine ⟨0, Or.inr ⟨?_, rfl⟩⟩
      intro n
      by_contra hn
      exact h ⟨n, hn⟩
  have hq (n : ℕ) : MeasurableSet {ω | q ω n} := by
    have hi : MeasurableSet {ω | ∀ k, ω ∈ bad k} := by
      convert MeasurableSet.iInter hbad using 1
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact (hbad n).compl.union (hi.inter (MeasurableSet.const _))
  let N : Ω → ℕ := fun ω => Nat.find (hex ω)
  refine ⟨N, measurable_find hex hq, ?_, ?_⟩
  · intro ω h
    have hs := Nat.find_spec (hex ω)
    rcases hs with hs | ⟨hs, _⟩
    · exact hs
    · obtain ⟨n, hn⟩ := h
      exact (hn (hs n)).elim
  · intro n ω hn
    by_contra h
    have hle : N ω ≤ n := Nat.find_min' (hex ω) (Or.inl h)
    exact (not_lt_of_ge hle hn)


/-- A measurable index has a radial stretched-exponential tail and selects a good radius
whenever one exists. -/
theorem exists_measurable_radial_index {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A s α : ℝ) (hA : 0 < A) (hs : 0 < s) (hα : 0 < α) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure Ω) (X : Vertex d → Ω → ℝ),
      (∀ x, Measurable (X x)) →
      (∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
        ENNReal.ofReal (A * Real.exp (-(t ^ s) / A))) →
      ∀ y : Vertex d, ∃ N : Ω → ℕ, Measurable N ∧
        (∀ ω, (∃ n : ℕ, ¬∃ x : Vertex d,
          (n : ℝ) + 1 ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ∧
          ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω) →
          ∀ x : Vertex d, (N ω : ℝ) + 1 ≤
            ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
            X x ω < ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α) ∧
        (∀ n : ℕ, μ {ω | n < N ω} ≤
          ENNReal.ofReal (B * Real.exp (-(((n : ℝ) + 1) ^ (α * s)) / B))) := by
  obtain ⟨B, hB, htail⟩ := measure_radial_bad_stretched_exp (d := d) (Ω := Ω)
    A s α hA hs hα
  refine ⟨B, hB, ?_⟩
  intro μ X hX h y
  let bad : ℕ → Set Ω := fun n => {ω | ∃ x : Vertex d,
    (n : ℝ) + 1 ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ∧
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω}
  have hbad (n : ℕ) : MeasurableSet (bad n) :=
    measurableSet_radial_bad X hX y ((n : ℝ) + 1) α
  obtain ⟨N, hNm, hgood, hindex⟩ := exists_measurable_first_good bad hbad
  refine ⟨N, hNm, ?_, ?_⟩
  · intro ω hex x hx
    have hn : ω ∉ bad (N ω) := hgood ω hex
    exact lt_of_not_ge (fun hle => hn ⟨x, hx, hle⟩)
  · intro n
    calc
      μ {ω | n < N ω} ≤ μ (bad n) := measure_mono (fun ω hω => hindex n ω hω)
      _ ≤ _ := htail μ X h y ((n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n))

/-- At almost every sample, some integer radius has no radial bad point. -/
theorem ae_exists_radial_good {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A s α : ℝ) (hA : 0 < A) (hs : 0 < s) (hα : 0 < α)
    (μ : Measure Ω) (X : Vertex d → Ω → ℝ)
    (h : ∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
      ENNReal.ofReal (A * Real.exp (-(t ^ s) / A))) (y : Vertex d) :
    ∀ᵐ ω ∂μ, ∃ n : ℕ, ¬∃ x : Vertex d,
      (n : ℝ) + 1 ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω := by
  obtain ⟨B, hB, htail⟩ := measure_radial_bad_stretched_exp (d := d) (Ω := Ω)
    A s α hA hs hα
  let bad : ℕ → Set Ω := fun n => {ω | ∃ x : Vertex d,
    (n : ℝ) + 1 ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ∧
    ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω}
  have hlim : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal
      (B * Real.exp (-(((n : ℝ) + 1) ^ (α * s)) / B))) Filter.atTop (𝓝 0) := by
    have ha : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hb : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (α * s) / B)
        Filter.atTop Filter.atTop :=
      ((tendsto_rpow_atTop (mul_pos hα hs)).comp ha).atTop_div_const hB
    have hc := Real.tendsto_exp_neg_atTop_nhds_zero.comp hb
    have hd := hc.const_mul B
    have he := ENNReal.tendsto_ofReal hd
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_apply, neg_div] using he
  have hzero : μ (⋂ n, bad n) = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    exact Filter.Eventually.of_forall fun n =>
      (measure_mono (Set.iInter_subset bad n)).trans
        (htail μ X h y ((n : ℝ) + 1) (le_add_of_nonneg_left (Nat.cast_nonneg n)))
  rw [ae_iff]
  have heq : {ω | ¬∃ n : ℕ, ¬∃ x : Vertex d,
      (n : ℝ) + 1 ≤ ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ∧
      ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α ≤ X x ω} =
      ⋂ n, bad n := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, bad]
    push Not
    rfl
  rw [heq]
  exact hzero

/-- A measurable radial scale is almost surely sufficient and has a discrete tail bound. -/
theorem exists_measurable_radial_scale_tail {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A s α : ℝ) (hA : 0 < A) (hs : 0 < s) (hα : 0 < α) :
    ∃ B : ℝ, 0 < B ∧ ∀ (μ : Measure Ω) (X : Vertex d → Ω → ℝ),
      (∀ x, Measurable (X x)) →
      (∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
        ENNReal.ofReal (A * Real.exp (-(t ^ s) / A))) →
      ∀ y : Vertex d, ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 1 ≤ M ω) ∧
        (∀ᵐ ω ∂μ, ∀ x : Vertex d, M ω ≤
          ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
          X x ω < ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α) ∧
        (∀ n : ℕ, μ {ω | (n : ℝ) + 1 < M ω} ≤
          ENNReal.ofReal (B * Real.exp (-(((n : ℝ) + 1) ^ (α * s)) / B))) := by
  obtain ⟨B, hB, hindex⟩ := exists_measurable_radial_index (d := d) (Ω := Ω)
    A s α hA hs hα
  refine ⟨B, hB, ?_⟩
  intro μ X hX h y
  obtain ⟨N, hN, hgood, htail⟩ := hindex μ X hX h y
  let M : Ω → ℝ := fun ω => (N ω : ℝ) + 1
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · intro ω
    exact le_add_of_nonneg_left (Nat.cast_nonneg (N ω))
  · filter_upwards [ae_exists_radial_good A s α hA hs hα μ X h y] with ω hω
    exact hgood ω hω
  · intro n
    apply (measure_mono ?_).trans (htail n)
    intro ω hω
    change (n : ℝ) + 1 < (N ω : ℝ) + 1 at hω
    change n < N ω
    exact_mod_cast (show (n : ℝ) < (N ω : ℝ) by linarith)

private theorem osBound_exp_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hm : Measurable Y) (hn : ∀ ω, 0 ≤ Y ω)
    (ht : OsBound μ 1 1 Y) :
    Integrable (fun ω => Real.exp (Y ω / 32)) μ ∧
      (∫ ω, Real.exp (Y ω / 32) ∂μ) ≤ 2 := by
  have hbig := ht.lintegral_exp_half hm hn
  have hbigint : Integrable (fun ω => Real.exp (Y ω / 2)) μ := by
    refine ⟨?_, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).2 ?_⟩
    · exact (by fun_prop : Measurable (fun ω => Real.exp (Y ω / 2))).aestronglyMeasurable
    · exact lt_of_le_of_lt hbig (ENNReal.ofReal_lt_top)
  have hbigbound : (∫ ω, Real.exp (Y ω / 2) ∂μ) ≤ Real.exp 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).mp
    rw [ofReal_integral_eq_lintegral_ofReal hbigint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact hbig
  have hchord (ω : Ω) : Real.exp (Y ω / 32) ≤
      (15 / 16 : ℝ) + (1 / 16 : ℝ) * Real.exp (Y ω / 2) := by
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Y ω / 2))
      (by norm_num : (0 : ℝ) ≤ 15 / 16) (by norm_num : (0 : ℝ) ≤ 1 / 16)
      (by norm_num : (15 / 16 : ℝ) + 1 / 16 = 1)
    have heq : (1 / 16 : ℝ) * (Y ω / 2) = Y ω / 32 := by ring
    simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, heq] using hc
  have hsmall : Integrable (fun ω => Real.exp (Y ω / 32)) μ := by
    refine (hbigint.const_mul (1 / 16)).add (integrable_const (15 / 16 : ℝ)) |>.mono'
      (by fun_prop : Measurable (fun ω => Real.exp (Y ω / 32))).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply] using (by linarith [hchord ω] :
      Real.exp (Y ω / 32) ≤ (1 / 16 : ℝ) * Real.exp (Y ω / 2) + 15 / 16)
  refine ⟨hsmall, ?_⟩
  have hi := integral_mono hsmall ((integrable_const (15 / 16 : ℝ)).add
    (hbigint.const_mul (1 / 16))) hchord
  change (∫ ω, Real.exp (Y ω / 32) ∂μ) ≤
    ∫ ω, ((15 / 16 : ℝ) + (1 / 16 : ℝ) * Real.exp (Y ω / 2)) ∂μ at hi
  rw [integral_add (integrable_const _) (hbigint.const_mul _), integral_const,
    integral_const_mul] at hi
  have hexp : Real.exp 2 ≤ 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hi
  linarith

private theorem osBound_of_discrete_tail (B p : ℝ) (hB : 0 < B) (hp : 0 < p) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (μ : Measure Ω) (M : Ω → ℝ),
      (∀ ω, 1 ≤ M ω) →
      (∀ n : ℕ, μ {ω | (n : ℝ) + 1 < M ω} ≤
        ENNReal.ofReal (B * Real.exp (-(((n : ℝ) + 1) ^ p) / B))) →
      OsBound μ p θ M := by
  have hf := (tendsto_rpow_atTop hp).eventually (eventually_ge_atTop (B * (B + 1)))
  obtain ⟨Q, hQ⟩ := (eventually_atTop.1 hf)
  let q := max Q 2
  have hq : 2 ≤ q := le_max_right _ _
  have hqp : B * (B + 1) ≤ q ^ p := hQ q (le_max_left _ _)
  refine ⟨2 * q, by positivity, ?_⟩
  intro Ω _ μ M hM htail t ht
  let n := ⌊t * q⌋₊
  have ht0 : 0 ≤ t := le_trans (by norm_num) ht
  have hq0 : 0 ≤ q := by linarith
  have htq : 2 ≤ t * q := by nlinarith
  have hfloor : (n : ℝ) ≤ t * q := Nat.floor_le (mul_nonneg ht0 hq0)
  have hfloor' : t * q < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hp1 : 1 ≤ t ^ p := Real.one_le_rpow ht hp.le
  have hbase : (t * q) ^ p ≤ ((n : ℝ) + 1) ^ p :=
    Real.rpow_le_rpow (mul_nonneg ht0 hq0) hfloor'.le hp.le
  have hpow : t ^ p * (B * (B + 1)) ≤ ((n : ℝ) + 1) ^ p := by
    calc
      _ ≤ t ^ p * q ^ p := mul_le_mul_of_nonneg_left hqp (Real.rpow_nonneg ht0 _)
      _ = (t * q) ^ p := (Real.mul_rpow ht0 hq0).symm
      _ ≤ _ := hbase
  have hbexp : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
  have he : -(((n : ℝ) + 1) ^ p) / B ≤ -t ^ p - B := by
    have hd : t ^ p * (B + 1) ≤ ((n : ℝ) + 1) ^ p / B := by
      apply (le_div_iff₀ hB).mpr
      nlinarith [hpow]
    have hmul : B ≤ t ^ p * B := by nlinarith
    have hle : t ^ p + B ≤ ((n : ℝ) + 1) ^ p / B := by nlinarith
    rw [neg_div]
    linarith [neg_le_neg hle]
  calc
    μ {ω | t * (2 * q) < max (M ω) 0} ≤ μ {ω | (n : ℝ) + 1 < M ω} := by
      apply measure_mono
      intro ω hω
      have hm : 0 ≤ M ω := (zero_le_one.trans (hM ω))
      simp only [Set.mem_setOf_eq, max_eq_left hm] at hω
      change (n : ℝ) + 1 < M ω
      nlinarith
    _ ≤ ENNReal.ofReal (B * Real.exp (-(((n : ℝ) + 1) ^ p) / B)) := htail n
    _ ≤ ENNReal.ofReal (Real.exp (-(t ^ p))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ B * Real.exp (-t ^ p - B) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hB.le
        _ = B / Real.exp B * Real.exp (-t ^ p) := by rw [Real.exp_sub, div_mul_eq_mul_div]; ring
        _ ≤ 1 * Real.exp (-t ^ p) := by
          gcongr
          exact (div_le_one (Real.exp_pos _)).2 hbexp
        _ = _ := one_mul _

/-- A measurable radial threshold with a uniform stretched-exponential moment. -/
theorem exists_radial_scale_exp_moment {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A s α : ℝ) (hA : 0 < A) (hs : 0 < s) (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Vertex d → Ω → ℝ), (∀ x, Measurable (X x)) →
      (∀ x t, 0 < t → μ {ω | t ≤ X x ω} ≤
        ENNReal.ofReal (A * Real.exp (-(t ^ s) / A))) →
      ∀ y : Vertex d, ∃ M : Ω → ℝ, Measurable M ∧ (∀ ω, 1 ≤ M ω) ∧
        Integrable (fun ω => Real.exp ((M ω / C) ^ (α * s))) μ ∧
        (∫ ω, Real.exp ((M ω / C) ^ (α * s)) ∂μ) ≤ 2 ∧
        (∀ᵐ ω ∂μ, ∀ x : Vertex d, M ω ≤
          ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ →
          X x ω < ‖latticeEuclideanEmbedding x - latticeEuclideanEmbedding y‖ ^ α) := by
  let p := α * s
  have hp : 0 < p := mul_pos hα hs
  obtain ⟨B, hB, hscale⟩ := exists_measurable_radial_scale_tail (d := d) (Ω := Ω)
    A s α hA hs hα
  obtain ⟨θ, hθ, hbridge⟩ := osBound_of_discrete_tail B p hB hp
  let C := θ * (32 : ℝ) ^ (1 / p)
  have hC : 0 < C := mul_pos hθ (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C, hC, ?_⟩
  intro μ _ X hX h y
  obtain ⟨M, hM, hM1, hgood, htail⟩ := hscale μ X hX h y
  have hM0 (ω : Ω) : 0 ≤ M ω := (zero_le_one.trans (hM1 ω))
  have ho : OsBound μ p θ M := hbridge μ M hM1 htail
  have hn := ho.normalized_rpow hp hθ
  have hm : Measurable (fun ω => (max (M ω) 0 / θ) ^ p) := by fun_prop
  have hnonneg (ω : Ω) : 0 ≤ (max (M ω) 0 / θ) ^ p :=
    Real.rpow_nonneg (div_nonneg (le_max_right _ _) hθ.le) _
  obtain ⟨hi, hb⟩ := osBound_exp_moment μ _ hm hnonneg hn
  have heq (ω : Ω) : (M ω / C) ^ p = (max (M ω) 0 / θ) ^ p / 32 := by
    rw [max_eq_left (hM0 ω)]
    dsimp [C]
    rw [div_mul_eq_div_div, Real.div_rpow (div_nonneg (hM0 ω) hθ.le)
      (Real.rpow_nonneg (by norm_num) _), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 32)]
    have he : (1 / p) * p = 1 := by field_simp
    rw [he, Real.rpow_one]
  refine ⟨M, hM, hM1, ?_, ?_, hgood⟩
  · change Integrable (fun ω => Real.exp ((M ω / C) ^ p)) μ
    simp_rw [heq]
    exact hi
  · change (∫ ω, Real.exp ((M ω / C) ^ p) ∂μ) ≤ 2
    simp_rw [heq]
    exact hb

end LatticeProb.Percolation
