/-
Birkhoff's pointwise ergodic theorem.

Mathlib 4.32 has the Birkhoff sums and nothing else: no maximal ergodic theorem
and no pointwise theorem.  `LatticeProb.maximal_ergodic` supplied the first;
this file builds the second on it.

The route.  From the maximal ergodic theorem comes the maximal inequality: the
measure of the set where some Birkhoff average of a function exceeds `c` is at
most `‖f‖₁ / c`.  For a bounded `f` the upper and lower Birkhoff limits are
bounded measurable and invariant, and the maximal ergodic theorem applied on the
invariant set where the lower limit is below `α` and the upper limit above `β`
forces that set to be null, so the two limits agree almost everywhere.  For an
integrable `f`, truncation gives a bounded `g` with `‖f - g‖₁` as small as
wanted, and the maximal inequality turns that into an almost sure bound on the
gap between the two limits of `f`, which is therefore zero.
-/
import Mathlib
import LatticeProb.Prob.MaximalErgodic

noncomputable section

namespace LatticeProb

open MeasureTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {f : Ω → ℝ}

/-! ### The maximal inequality -/

/-- The set where some Birkhoff sum of `f` exceeds `c` times its length. -/
def maximalSet (T : Ω → Ω) (f : Ω → ℝ) (c : ℝ) : Set Ω :=
  ⋃ N : ℕ, {x | 0 < maxBirkhoff T (fun y => f y - c) N x}

theorem measurableSet_maximalSet (hT : Measurable T) (hfm : Measurable f) (c : ℝ) :
    MeasurableSet (maximalSet T f c) := by
  refine MeasurableSet.iUnion fun N => ?_
  exact measurableSet_lt measurable_const
    (measurable_maxBirkhoff hT (hfm.sub measurable_const) N)

omit [MeasurableSpace Ω] in
theorem monotone_maximalSet_aux' (T : Ω → Ω) (g : Ω → ℝ) :
    Monotone fun N : ℕ => {x | 0 < maxBirkhoff T g N x} := by
  intro M N h x hx
  exact lt_of_lt_of_le hx (maxBirkhoff_mono T _ h x)

omit [MeasurableSpace Ω] in
theorem monotone_maximalSet_aux (T : Ω → Ω) (f : Ω → ℝ) (c : ℝ) :
    Monotone fun N : ℕ => {x | 0 < maxBirkhoff T (fun y => f y - c) N x} := by
  intro M N h x hx
  exact lt_of_lt_of_le hx (maxBirkhoff_mono T _ h x)

/-- **The maximal inequality.**  `c` times the measure of the set where some
Birkhoff average exceeds `c` is at most the `L¹` norm of `f`. -/
theorem maximal_inequality [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {c : ℝ} (_hc : 0 < c) :
    c * (μ (maximalSet T f c)).toReal ≤ ∫ x, |f x| ∂μ := by
  set g : Ω → ℝ := fun y => f y - c with hg
  have hgm : Measurable g := hfm.sub measurable_const
  have hgi : Integrable g μ := hf.sub (integrable_const c)
  set E : ℕ → Set Ω := fun N => {x | 0 < maxBirkhoff T g N x} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxBirkhoff hT.measurable hgm N)
  have hstep : ∀ N, c * (μ (E N)).toReal ≤ ∫ x, |f x| ∂μ := by
    intro N
    have h0 := maximal_ergodic hT hgm hgi N
    have hsplit : ∫ x in E N, g x ∂μ
        = (∫ x in E N, f x ∂μ) - c * (μ (E N)).toReal := by
      rw [hg]
      rw [integral_sub hf.integrableOn (integrable_const c), setIntegral_const,
        smul_eq_mul, measureReal_def]
      ring
    rw [hsplit] at h0
    have h1 : ∫ x in E N, f x ∂μ ≤ ∫ x in E N, |f x| ∂μ :=
      setIntegral_mono_on hf.integrableOn hf.abs.integrableOn (hEm N)
        (fun x _ => le_abs_self _)
    have h2 : ∫ x in E N, |f x| ∂μ ≤ ∫ x, |f x| ∂μ :=
      setIntegral_le_integral hf.abs (Filter.Eventually.of_forall fun x => abs_nonneg _)
    linarith
  have hmono : Monotone E := monotone_maximalSet_aux T f c
  have hlim : Tendsto (fun N => μ (E N)) atTop (𝓝 (μ (maximalSet T f c))) := by
    rw [maximalSet]
    exact tendsto_measure_iUnion_atTop hmono
  have hlimR : Tendsto (fun N => (μ (E N)).toReal) atTop
      (𝓝 ((μ (maximalSet T f c)).toReal)) :=
    (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hlim
  refine le_of_tendsto (hlimR.const_mul c) ?_
  filter_upwards with N using hstep N

/-! ### The Birkhoff averages and their two limits -/

/-- The Birkhoff average `S_n / n`. -/
def bAvg (T : Ω → Ω) (f : Ω → ℝ) (n : ℕ) (x : Ω) : ℝ := birkhoffSum T f n x / n

theorem measurable_bAvg (hT : Measurable T) (hfm : Measurable f) (n : ℕ) :
    Measurable (bAvg T f n) :=
  (Finset.measurable_sum _ fun k _ => hfm.comp (hT.iterate k)).div measurable_const

omit [MeasurableSpace Ω] in
theorem abs_bAvg_le {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (n : ℕ) (x : Ω) :
    |bAvg T f n x| ≤ C := by
  cases n with
  | zero => simpa [bAvg, birkhoffSum] using hC
  | succ n =>
      have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      rw [bAvg, abs_div, abs_of_pos hn, div_le_iff₀ hn]
      calc |birkhoffSum T f (n + 1) x| ≤ ∑ k ∈ Finset.range (n + 1), |f (T^[k] x)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range (n + 1), C := Finset.sum_le_sum fun k _ => hf _
        _ = C * ((n + 1 : ℕ) : ℝ) := by
            rw [Finset.sum_const, Finset.card_range]; push_cast; ring

omit [MeasurableSpace Ω] in
theorem isBoundedUnder_le_of {a : ℕ → ℝ} {C : ℝ} (h : ∀ n, a n ≤ C) :
    IsBoundedUnder (· ≤ ·) atTop a :=
  ⟨C, Filter.eventually_map.mpr (Filter.Eventually.of_forall h)⟩

omit [MeasurableSpace Ω] in
theorem isBoundedUnder_ge_of {a : ℕ → ℝ} {C : ℝ} (h : ∀ n, C ≤ a n) :
    IsBoundedUnder (· ≥ ·) atTop a :=
  ⟨C, Filter.eventually_map.mpr (Filter.Eventually.of_forall h)⟩

/-- Two bounded sequences whose difference tends to zero have the same upper
limit. -/
theorem limsup_le_limsup_of_sub {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C) (hb : ∀ n, |b n| ≤ C)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    limsup a atTop ≤ limsup b atTop := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hs2
  have hbA : IsBoundedUnder (· ≤ ·) atTop b :=
    isBoundedUnder_le_of fun n => (abs_le.mp (hb n)).2
  have hbE : ∀ᶠ n in atTop, b n < s := eventually_lt_of_limsup_lt hs1 hbA
  have haB : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_ge_of fun n => (abs_le.mp (ha n)).1
  have haF : ∃ᶠ n in atTop, t < a n :=
    frequently_lt_of_lt_limsup haB.isCoboundedUnder_le ht2
  have hd : ∀ᶠ n in atTop, |a n - b n| < t - s := by
    have hpos : (0 : ℝ) < t - s := by linarith
    have := NormedAddGroup.tendsto_nhds_zero.mp h (t - s) hpos
    simpa using this
  obtain ⟨n, hn1, hn2, hn3⟩ := (haF.and_eventually (hbE.and hd)).exists
  have hlt : a n < t := by
    have h4 := (abs_lt.mp hn3).2
    linarith
  linarith

theorem limsup_eq_of_sub {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C) (hb : ∀ n, |b n| ≤ C)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    limsup a atTop = limsup b atTop := by
  refine le_antisymm (limsup_le_limsup_of_sub ha hb h) (limsup_le_limsup_of_sub hb ha ?_)
  have : (fun n => b n - a n) = fun n => -(a n - b n) := by funext n; ring
  rw [this]
  simpa using h.neg

/-- The upper Birkhoff limit. -/
def bLimsup (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) : ℝ := limsup (fun n => bAvg T f n x) atTop

/-- The lower Birkhoff limit. -/
def bLiminf (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) : ℝ := liminf (fun n => bAvg T f n x) atTop

theorem measurable_bLimsup (hT : Measurable T) (hfm : Measurable f) :
    Measurable (bLimsup T f) :=
  Measurable.limsup fun n => measurable_bAvg hT hfm n

theorem measurable_bLiminf (hT : Measurable T) (hfm : Measurable f) :
    Measurable (bLiminf T f) :=
  Measurable.liminf fun n => measurable_bAvg hT hfm n

omit [MeasurableSpace Ω] in
theorem bLiminf_le_bLimsup {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x : Ω) :
    bLiminf T f x ≤ bLimsup T f x := by
  refine liminf_le_limsup ?_ ?_
  · exact isBoundedUnder_le_of fun n => (abs_le.mp (abs_bAvg_le hC hf n x)).2
  · exact isBoundedUnder_ge_of fun n => (abs_le.mp (abs_bAvg_le hC hf n x)).1

omit [MeasurableSpace Ω] in
/-- The upper Birkhoff limit is invariant. -/
theorem bLimsup_comp {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x : Ω) :
    bLimsup T f (T x) = bLimsup T f x := by
  set a : ℕ → ℝ := fun n => bAvg T f n (T x) with ha
  set b : ℕ → ℝ := fun n => bAvg T f (n + 1) x with hb
  have habs_a : ∀ n, |a n| ≤ C := fun n => abs_bAvg_le hC hf n (T x)
  have habs_b : ∀ n, |b n| ≤ C := fun n => abs_bAvg_le hC hf (n + 1) x
  have hkey : ∀ n : ℕ, 1 ≤ n → a n - b n = (b n - f x) / n := by
    intro n hn
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hS : birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
      rw [birkhoffSum_succ']; ring
    rw [ha, hb]
    simp only [bAvg, hS]
    push_cast
    field_simp
    ring
  have hsub : Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, 1 ≤ n → |a n - b n| ≤ (2 * C) / n := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      rw [hkey n hn, abs_div, abs_of_pos hn0]
      have h1 := habs_b n
      have h2 := hf x
      have habs : |b n - f x| ≤ 2 * C := by
        have h3 := abs_add_le (b n) (-(f x))
        rw [abs_neg] at h3
        have h4 : b n - f x = b n + -(f x) := by ring
        rw [h4]
        linarith
      gcongr
    refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C / (n : ℝ)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simpa using hbound n hn
    · exact tendsto_const_div_atTop_nhds_zero_nat (2 * C)
  rw [bLimsup, bLimsup, ← limsup_nat_add (fun n => bAvg T f n x) 1]
  exact limsup_eq_of_sub habs_a habs_b hsub

omit [MeasurableSpace Ω] in
theorem liminf_le_liminf_of_sub {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C) (hb : ∀ n, |b n| ≤ C)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    liminf b atTop ≤ liminf a atTop := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs1, hs2⟩ := exists_between hcon
  obtain ⟨t, ht1, ht2⟩ := exists_between hs2
  have hbB : IsBoundedUnder (· ≥ ·) atTop b :=
    isBoundedUnder_ge_of fun n => (abs_le.mp (hb n)).1
  have hbE : ∀ᶠ n in atTop, t < b n := eventually_lt_of_lt_liminf ht2 hbB
  have haB : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_le_of fun n => (abs_le.mp (ha n)).2
  have haF : ∃ᶠ n in atTop, a n < s :=
    frequently_lt_of_liminf_lt haB.isCoboundedUnder_ge hs1
  have hd : ∀ᶠ n in atTop, |a n - b n| < t - s := by
    have hpos : (0 : ℝ) < t - s := by linarith
    have := NormedAddGroup.tendsto_nhds_zero.mp h (t - s) hpos
    simpa using this
  obtain ⟨n, hn1, hn2, hn3⟩ := (haF.and_eventually (hbE.and hd)).exists
  have h4 := (abs_lt.mp hn3).1
  linarith

omit [MeasurableSpace Ω] in
theorem liminf_eq_of_sub {a b : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C) (hb : ∀ n, |b n| ≤ C)
    (h : Tendsto (fun n => a n - b n) atTop (𝓝 0)) :
    liminf a atTop = liminf b atTop := by
  refine le_antisymm (liminf_le_liminf_of_sub hb ha ?_) (liminf_le_liminf_of_sub ha hb h)
  have he : (fun n => b n - a n) = fun n => -(a n - b n) := by funext n; ring
  rw [he]
  simpa using h.neg

omit [MeasurableSpace Ω] in
/-- The lower Birkhoff limit is invariant. -/
theorem bLiminf_comp {C : ℝ} (hC : 0 ≤ C) (hf : ∀ x, |f x| ≤ C) (x : Ω) :
    bLiminf T f (T x) = bLiminf T f x := by
  set a : ℕ → ℝ := fun n => bAvg T f n (T x) with ha
  set b : ℕ → ℝ := fun n => bAvg T f (n + 1) x with hb
  have habs_a : ∀ n, |a n| ≤ C := fun n => abs_bAvg_le hC hf n (T x)
  have habs_b : ∀ n, |b n| ≤ C := fun n => abs_bAvg_le hC hf (n + 1) x
  have hkey : ∀ n : ℕ, 1 ≤ n → a n - b n = (b n - f x) / n := by
    intro n hn
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hS : birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
      rw [birkhoffSum_succ']; ring
    rw [ha, hb]
    simp only [bAvg, hS]
    push_cast
    field_simp
    ring
  have hsub : Tendsto (fun n => a n - b n) atTop (𝓝 0) := by
    have hbound : ∀ n : ℕ, 1 ≤ n → |a n - b n| ≤ (2 * C) / n := by
      intro n hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := by omega
        exact_mod_cast this
      rw [hkey n hn, abs_div, abs_of_pos hn0]
      have h1 := habs_b n
      have h2 := hf x
      have habs : |b n - f x| ≤ 2 * C := by
        have h3 := abs_add_le (b n) (-(f x))
        rw [abs_neg] at h3
        have h4 : b n - f x = b n + -(f x) := by ring
        rw [h4]
        linarith
      gcongr
    refine squeeze_zero_norm' (a := fun n : ℕ => 2 * C / (n : ℝ)) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simpa using hbound n hn
    · exact tendsto_const_div_atTop_nhds_zero_nat (2 * C)
  rw [bLiminf, bLiminf, ← liminf_nat_add (fun n => bAvg T f n x) 1]
  exact liminf_eq_of_sub habs_a habs_b hsub

/-! ### Restricting to an invariant set -/

theorem measurePreserving_restrict (hT : MeasurePreserving T μ μ) {A : Set Ω}
    (hA : MeasurableSet A) (hinv : T ⁻¹' A = A) :
    MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
  refine ⟨hT.measurable, ?_⟩
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hT.measurable hs, Measure.restrict_apply (hT.measurable hs),
    Measure.restrict_apply hs]
  conv_lhs => rw [← hinv]
  rw [← Set.preimage_inter, ← Measure.map_apply hT.measurable (hs.inter hA), hT.map_eq]

omit [MeasurableSpace Ω] in
theorem birkhoffSum_sub_const (T : Ω → Ω) (f : Ω → ℝ) (c : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => f y - c) n x = birkhoffSum T f n x - n * c := by
  simp only [birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

omit [MeasurableSpace Ω] in
theorem birkhoffSum_const_sub (T : Ω → Ω) (f : Ω → ℝ) (c : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => c - f y) n x = n * c - birkhoffSum T f n x := by
  simp only [birkhoffSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- If every point of an invariant set has some strictly positive Birkhoff sum,
the integral of the function over that set is nonnegative. -/
theorem integral_nonneg_of_covering [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    {g : Ω → ℝ} (hgm : Measurable g) (hgi : Integrable g μ)
    {A : Set Ω} (hAm : MeasurableSet A) (hinv : T ⁻¹' A = A)
    (hcov : ∀ x ∈ A, ∃ n, 0 < birkhoffSum T g n x) :
    0 ≤ ∫ x in A, g x ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict A) := inferInstance
  have hTν : MeasurePreserving T (μ.restrict A) (μ.restrict A) :=
    measurePreserving_restrict hT hAm hinv
  have hgν : Integrable g (μ.restrict A) := hgi.restrict
  set E : ℕ → Set Ω := fun N => {x | 0 < maxBirkhoff T g N x} with hE
  have hEm : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxBirkhoff hT.measurable hgm N)
  have hmono : Monotone E := monotone_maximalSet_aux' T g
  have hstep : ∀ N, 0 ≤ ∫ x in E N, g x ∂(μ.restrict A) := fun N =>
    maximal_ergodic hTν hgm hgν N
  have hcover : A ⊆ ⋃ N, E N := by
    intro x hx
    obtain ⟨n, hn⟩ := hcov x hx
    exact Set.mem_iUnion.mpr ⟨n, lt_of_lt_of_le hn
      (birkhoffSum_le_maxBirkhoff T g le_rfl x)⟩
  have hae : ∀ᵐ x ∂(μ.restrict A), x ∈ ⋃ N, E N := by
    rw [ae_iff]
    have hms : MeasurableSet {a : Ω | a ∉ ⋃ N, E N} := (MeasurableSet.iUnion hEm).compl
    have hempty : {a : Ω | a ∉ ⋃ N, E N} ∩ A = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      exact fun hnot hA => hnot (hcover hA)
    rw [Measure.restrict_apply hms, hempty, measure_empty]
  have hfull : ∫ x in ⋃ N, E N, g x ∂(μ.restrict A) = ∫ x, g x ∂(μ.restrict A) := by
    rw [Measure.restrict_eq_self_of_ae_mem hae]
  have hlim := tendsto_setIntegral_of_monotone hEm hmono hgν.integrableOn
  rw [hfull] at hlim
  refine ge_of_tendsto hlim ?_
  exact Filter.Eventually.of_forall hstep

/-! ### The two limits agree, for a bounded function -/

/-- The invariant set where the lower limit is below `α` and the upper limit
above `β`. -/
def gapSet (T : Ω → Ω) (f : Ω → ℝ) (α β : ℝ) : Set Ω :=
  {x | bLiminf T f x < α ∧ β < bLimsup T f x}

theorem measure_gapSet_eq_zero [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x, |f x| ≤ C) {α β : ℝ} (hab : α < β) : μ (gapSet T f α β) = 0 := by
  set A := gapSet T f α β with hA
  have hAm : MeasurableSet A :=
    (measurableSet_lt (measurable_bLiminf hT.measurable hfm) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_bLimsup hT.measurable hfm))
  have hinv : T ⁻¹' A = A := by
    ext x
    simp only [hA, gapSet, Set.mem_preimage, Set.mem_setOf_eq,
      bLimsup_comp hC hfb, bLiminf_comp hC hfb]
  have hcob : ∀ x : Ω, IsCoboundedUnder (· ≤ ·) atTop (fun n => bAvg T f n x) := fun x =>
    (isBoundedUnder_ge_of fun n => (abs_le.mp (abs_bAvg_le hC hfb n x)).1).isCoboundedUnder_le
  have hcob' : ∀ x : Ω, IsCoboundedUnder (· ≥ ·) atTop (fun n => bAvg T f n x) := fun x =>
    (isBoundedUnder_le_of fun n => (abs_le.mp (abs_bAvg_le hC hfb n x)).2).isCoboundedUnder_ge
  have hcov1 : ∀ x ∈ A, ∃ n, 0 < birkhoffSum T (fun y => f y - β) n x := by
    intro x hx
    have hfreq : ∃ᶠ n in atTop, β < bAvg T f n x :=
      frequently_lt_of_lt_limsup (hcob x) hx.2
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    refine ⟨n, ?_⟩
    rw [birkhoffSum_sub_const]
    rw [bAvg, lt_div_iff₀ hn0] at hn1
    linarith
  have hcov2 : ∀ x ∈ A, ∃ n, 0 < birkhoffSum T (fun y => α - f y) n x := by
    intro x hx
    have hfreq : ∃ᶠ n in atTop, bAvg T f n x < α :=
      frequently_lt_of_liminf_lt (hcob' x) hx.1
    obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually (eventually_ge_atTop 1)).exists
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    refine ⟨n, ?_⟩
    rw [birkhoffSum_const_sub]
    rw [bAvg, div_lt_iff₀ hn0] at hn1
    linarith
  have h1 : 0 ≤ ∫ x in A, (f x - β) ∂μ :=
    integral_nonneg_of_covering hT (hfm.sub measurable_const)
      (hf.sub (integrable_const β)) hAm hinv hcov1
  have h2 : 0 ≤ ∫ x in A, (α - f x) ∂μ :=
    integral_nonneg_of_covering hT (measurable_const.sub hfm)
      ((integrable_const α).sub hf) hAm hinv hcov2
  have e1 : ∫ x in A, (f x - β) ∂μ = (∫ x in A, f x ∂μ) - β * (μ A).toReal := by
    rw [integral_sub hf.integrableOn (integrable_const β), setIntegral_const, smul_eq_mul,
      measureReal_def]
    ring
  have e2 : ∫ x in A, (α - f x) ∂μ = α * (μ A).toReal - ∫ x in A, f x ∂μ := by
    rw [integral_sub (integrable_const α) hf.integrableOn, setIntegral_const, smul_eq_mul,
      measureReal_def]
    ring
  rw [e1] at h1
  rw [e2] at h2
  have hnn : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hle : (μ A).toReal ≤ 0 := by nlinarith
  have hzero : (μ A).toReal = 0 := le_antisymm hle hnn
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzero with h | h
  · exact h
  · exact absurd h (measure_ne_top μ A)

/-- **Birkhoff's theorem, bounded case:** the upper and lower Birkhoff limits of
a bounded measurable function agree almost everywhere. -/
theorem ae_bLiminf_eq_bLimsup_of_bounded [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {C : ℝ} (hC : 0 ≤ C)
    (hfb : ∀ x, |f x| ≤ C) :
    ∀ᵐ x ∂μ, bLiminf T f x = bLimsup T f x := by
  have hnull : μ (⋃ q : {p : ℚ × ℚ // p.1 < p.2},
      gapSet T f ((q : ℚ × ℚ).1 : ℝ) ((q : ℚ × ℚ).2 : ℝ)) = 0 :=
    measure_iUnion_null fun q =>
      measure_gapSet_eq_zero hT hfm hf hC hfb (by exact_mod_cast q.2)
  have hsub : {x | ¬ bLiminf T f x = bLimsup T f x} ⊆
      ⋃ q : {p : ℚ × ℚ // p.1 < p.2},
        gapSet T f ((q : ℚ × ℚ).1 : ℝ) ((q : ℚ × ℚ).2 : ℝ) := by
    intro x hx
    have hlt : bLiminf T f x < bLimsup T f x :=
      lt_of_le_of_ne (bLiminf_le_bLimsup hC hfb x) hx
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlt
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
    exact Set.mem_iUnion.mpr ⟨⟨(a, b), by exact_mod_cast hb1⟩, ha1, hb2⟩
  rw [ae_iff]
  exact measure_mono_null hsub hnull

/-! ### From the bounded case to `L¹` -/

omit [MeasurableSpace Ω] in
theorem cauchySeq_bAvg_of_bounded_ae {g : Ω → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hgb : ∀ x, |g x| ≤ C) {x : Ω}
    (hx : bLiminf T g x = bLimsup T g x) :
    CauchySeq fun n => bAvg T g n x := by
  have hconv : Tendsto (fun n => bAvg T g n x) atTop (𝓝 (bLimsup T g x)) := by
    refine tendsto_of_liminf_eq_limsup hx rfl ?_ ?_
    · exact isBoundedUnder_le_of fun n => (abs_le.mp (abs_bAvg_le hC hgb n x)).2
    · exact isBoundedUnder_ge_of fun n => (abs_le.mp (abs_bAvg_le hC hgb n x)).1
  exact hconv.cauchySeq

/-- The set where the Birkhoff averages fail to be eventually `ε`-close to one
another. -/
def oscSet (T : Ω → Ω) (f : Ω → ℝ) (ε : ℝ) : Set Ω :=
  {x | ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ N ≤ n ∧ ε < |bAvg T f m x - bAvg T f n x|}

omit [MeasurableSpace Ω] in
theorem not_cauchySeq_subset_iUnion_oscSet (T : Ω → Ω) (f : Ω → ℝ) :
    {x | ¬ CauchySeq fun n => bAvg T f n x} ⊆ ⋃ k : ℕ, oscSet T f (1 / (k + 1)) := by
  intro x hx
  simp only [Set.mem_setOf_eq, Metric.cauchySeq_iff] at hx
  push Not at hx
  obtain ⟨ε, hε, hx⟩ := hx
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine Set.mem_iUnion.mpr ⟨k, fun N => ?_⟩
  obtain ⟨m, hm, n, hn, hmn⟩ := hx N
  exact ⟨m, n, hm, hn, lt_of_lt_of_le hk (by rwa [Real.dist_eq] at hmn)⟩

omit [MeasurableSpace Ω] in
/-- Splitting `f` into a bounded part and a remainder splits the oscillation. -/
theorem oscSet_subset {g r : Ω → ℝ} (hfgr : ∀ x, f x = g x + r x) {ε : ℝ} (hε : 0 < ε) :
    oscSet T f ε ⊆ {x | ¬ CauchySeq fun n => bAvg T g n x}
      ∪ {x | ∃ n : ℕ, ε / 4 < |bAvg T r n x|} := by
  intro x hx
  by_contra hcon
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hcon
  obtain ⟨hg, hr⟩ := hcon
  have hrb : ∀ n : ℕ, |bAvg T r n x| ≤ ε / 4 := by
    intro n
    by_contra hn
    exact hr ⟨n, lt_of_not_ge hn⟩
  have hsplit : ∀ n : ℕ, bAvg T f n x = bAvg T g n x + bAvg T r n x := by
    intro n
    simp only [bAvg, birkhoffSum]
    rw [← add_div]
    congr 1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hfgr _
  rw [Metric.cauchySeq_iff] at hg
  obtain ⟨N, hN⟩ := hg (ε / 2) (by linarith)
  obtain ⟨m, n, hm, hn, hmn⟩ := hx N
  have h1 := hN m hm n hn
  rw [Real.dist_eq] at h1
  rw [hsplit m, hsplit n] at hmn
  have h2 := hrb m
  have h3 := hrb n
  have h4 : |bAvg T g m x + bAvg T r m x - (bAvg T g n x + bAvg T r n x)|
      ≤ |bAvg T g m x - bAvg T g n x| + |bAvg T r m x| + |bAvg T r n x| := by
    have e : bAvg T g m x + bAvg T r m x - (bAvg T g n x + bAvg T r n x)
        = (bAvg T g m x - bAvg T g n x) + (bAvg T r m x + -(bAvg T r n x)) := by ring
    rw [e]
    refine le_trans (abs_add_le _ _) ?_
    have h5 := abs_add_le (bAvg T r m x) (-(bAvg T r n x))
    rw [abs_neg] at h5
    linarith
  linarith

/-! ### Truncation -/

/-- `f` clipped to `[-M, M]`. -/
def clip (M : ℝ) (f : Ω → ℝ) : Ω → ℝ := fun x => max (-M) (min M (f x))

theorem measurable_clip (M : ℝ) (hfm : Measurable f) : Measurable (clip M f) :=
  measurable_const.max (measurable_const.min hfm)

omit [MeasurableSpace Ω] in
theorem abs_clip_le {M : ℝ} (hM : 0 ≤ M) (x : Ω) : |clip M f x| ≤ M := by
  rw [clip, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

omit [MeasurableSpace Ω] in
theorem abs_sub_clip_le {M : ℝ} (hM : 0 ≤ M) (x : Ω) : |f x - clip M f x| ≤ |f x| := by
  rcases le_total M (f x) with h | h
  · have h1 : min M (f x) = M := min_eq_left h
    have h2 : max (-M) M = M := max_eq_right (by linarith)
    rw [clip, h1, h2, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total (f x) (-M) with h' | h'
    · have h1 : min M (f x) = f x := min_eq_right h
      have h2 : max (-M) (f x) = -M := max_eq_left h'
      rw [clip, h1, h2, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have h1 : min M (f x) = f x := min_eq_right h
      have h2 : max (-M) (f x) = f x := max_eq_right h'
      rw [clip, h1, h2]
      simp [abs_nonneg]

theorem tendsto_integral_abs_sub_clip (hfm : Measurable f) (hf : Integrable f μ) :
    Tendsto (fun k : ℕ => ∫ x, |f x - clip (k : ℝ) f x| ∂μ) atTop (𝓝 0) := by
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable
      (fun x => |f x - clip (k : ℝ) f x|) μ :=
    fun k => ((hfm.sub (measurable_clip _ hfm)).abs).aestronglyMeasurable
  have hbound : ∀ k : ℕ, ∀ᵐ x ∂μ, ‖|f x - clip (k : ℝ) f x|‖ ≤ |f x| := by
    intro k
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_abs]
    exact abs_sub_clip_le (by positivity) x
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun k : ℕ => |f x - clip (k : ℝ) f x|) atTop (𝓝 0) := by
    filter_upwards with x
    have heq : ∀ k : ℕ, |f x| ≤ (k : ℝ) → |f x - clip (k : ℝ) f x| = 0 := by
      intro k hk
      have h1 : f x ≤ (k : ℝ) := le_trans (le_abs_self _) hk
      have h2 : -(k : ℝ) ≤ f x := by
        have := neg_abs_le (f x); linarith
      rw [clip, min_eq_right h1, max_eq_right h2, sub_self, abs_zero]
    obtain ⟨K, hK⟩ := exists_nat_ge |f x|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop K] with k hk
    exact (heq k (le_trans hK (by exact_mod_cast hk))).symm
  have := tendsto_integral_of_dominated_convergence (fun x => |f x|) hmeas hf.abs hbound hlim
  simpa using this

/-! ### Birkhoff's pointwise ergodic theorem -/

omit [MeasurableSpace Ω] in
theorem subset_maximalSet_abs (T : Ω → Ω) (r : Ω → ℝ) {c : ℝ} (hc : 0 < c) :
    {x | ∃ n : ℕ, c < |bAvg T r n x|} ⊆ maximalSet T (fun y => |r y|) c := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hn1 : 1 ≤ n := by
    by_contra h
    push Not at h
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    simp only [bAvg, birkhoffSum, Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      div_zero, abs_zero] at hn
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hle : |bAvg T r n x| ≤ bAvg T (fun y => |r y|) n x := by
    rw [bAvg, bAvg, abs_div, abs_of_pos hn0]
    gcongr
    exact Finset.abs_sum_le_sum_abs _ _
  have hgt : c < bAvg T (fun y => |r y|) n x := lt_of_lt_of_le hn hle
  rw [bAvg, lt_div_iff₀ hn0] at hgt
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  have hpos : 0 < birkhoffSum T (fun y => |r y| - c) n x := by
    rw [birkhoffSum_sub_const]
    linarith
  exact lt_of_lt_of_le hpos (birkhoffSum_le_maxBirkhoff T _ le_rfl x)

theorem measure_oscSet_eq_zero [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) {ε : ℝ} (hε : 0 < ε) :
    μ (oscSet T f ε) = 0 := by
  have hkey : ∀ k : ℕ, (ε / 4) * (μ (oscSet T f ε)).toReal
      ≤ ∫ x, |f x - clip (k : ℝ) f x| ∂μ := by
    intro k
    set g : Ω → ℝ := clip (k : ℝ) f with hgdef
    set r : Ω → ℝ := fun x => f x - g x with hrdef
    have hgm : Measurable g := measurable_clip _ hfm
    have hrm : Measurable r := hfm.sub hgm
    have hgb : ∀ x, |g x| ≤ (k : ℝ) := fun x => abs_clip_le (by positivity) x
    have hgi : Integrable g μ :=
      Integrable.of_bound hgm.aestronglyMeasurable (k : ℝ)
        (Filter.Eventually.of_forall fun x => by simpa using hgb x)
    have hri : Integrable r μ := hf.sub hgi
    have hgcauchy : μ {x | ¬ CauchySeq fun n => bAvg T g n x} = 0 := by
      rw [← ae_iff]
      filter_upwards [ae_bLiminf_eq_bLimsup_of_bounded hT hgm hgi
        (by positivity : (0:ℝ) ≤ (k : ℝ)) hgb] with x hx
      exact cauchySeq_bAvg_of_bounded_ae (by positivity) hgb hx
    have hsub := oscSet_subset (T := T) (f := f) (g := g) (r := r)
      (fun x => by rw [hrdef]; ring) hε
    have hsub2 : {x | ∃ n : ℕ, ε / 4 < |bAvg T r n x|}
        ⊆ maximalSet T (fun y => |r y|) (ε / 4) :=
      subset_maximalSet_abs T r (by linarith)
    have hmono : μ (oscSet T f ε) ≤ μ (maximalSet T (fun y => |r y|) (ε / 4)) := by
      refine le_trans (measure_mono hsub) ?_
      refine le_trans (measure_union_le _ _) ?_
      rw [hgcauchy, zero_add]
      exact measure_mono hsub2
    have hmax := maximal_inequality hT hrm.abs hri.abs (c := ε / 4) (by linarith)
    have h1 : (μ (oscSet T f ε)).toReal
        ≤ (μ (maximalSet T (fun y => |r y|) (ε / 4))).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _) hmono
    have h2 : ∫ x, |(|r x|)| ∂μ = ∫ x, |r x| ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show |(|r x|)| = |r x|
      exact abs_abs _
    rw [h2] at hmax
    have hεpos : (0 : ℝ) < ε / 4 := by linarith
    calc (ε / 4) * (μ (oscSet T f ε)).toReal
        ≤ (ε / 4) * (μ (maximalSet T (fun y => |r y|) (ε / 4))).toReal :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hεpos)
      _ ≤ ∫ x, |r x| ∂μ := hmax
      _ = ∫ x, |f x - clip (k : ℝ) f x| ∂μ := rfl
  have hlim : Tendsto (fun k : ℕ => ∫ x, |f x - clip (k : ℝ) f x| ∂μ) atTop (𝓝 0) :=
    tendsto_integral_abs_sub_clip hfm hf
  have hzero : (ε / 4) * (μ (oscSet T f ε)).toReal ≤ 0 :=
    ge_of_tendsto' hlim fun k => hkey k
  have hnn : (0 : ℝ) ≤ (μ (oscSet T f ε)).toReal := ENNReal.toReal_nonneg
  have hle0 : (μ (oscSet T f ε)).toReal ≤ 0 := by nlinarith
  have := le_antisymm hle0 hnn
  rcases (ENNReal.toReal_eq_zero_iff _).mp this with h | h
  · exact h
  · exact absurd h (measure_ne_top μ _)

theorem ae_cauchySeq_bAvg [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, CauchySeq fun n => bAvg T f n x := by
  rw [ae_iff]
  refine measure_mono_null (not_cauchySeq_subset_iUnion_oscSet T f) ?_
  refine measure_iUnion_null fun k => measure_oscSet_eq_zero hT hfm hf ?_
  positivity

/-- **Birkhoff's pointwise ergodic theorem.**  For a measure-preserving
transformation of a finite measure space and an integrable function, the
Birkhoff averages converge almost everywhere. -/
theorem ae_tendsto_bAvg [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ∃ L : ℝ, Tendsto (fun n => bAvg T f n x) atTop (𝓝 L) := by
  filter_upwards [ae_cauchySeq_bAvg hT hfm hf] with x hx
  exact cauchySeq_tendsto_of_complete hx

/-- **Birkhoff's theorem with a named limit.**  The Birkhoff averages converge
almost everywhere to `bLimsup T f`, which is measurable. -/
theorem ae_tendsto_bLimsup [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T f n x) atTop (𝓝 (bLimsup T f x)) := by
  filter_upwards [ae_cauchySeq_bAvg hT hfm hf] with x hx
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hx
  have : bLimsup T f x = L := hL.limsup_eq
  rw [this]
  exact hL

/-- The Birkhoff limit is invariant almost everywhere. -/
theorem ae_bLimsup_comp [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hfm : Measurable f) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, bLimsup T f (T x) = bLimsup T f x := by
  have hshift : ∀ᵐ x ∂μ, Tendsto (fun n => bAvg T f n (T x)) atTop
      (𝓝 (bLimsup T f (T x))) :=
    hT.quasiMeasurePreserving.ae (ae_tendsto_bLimsup hT hfm hf)
  filter_upwards [ae_tendsto_bLimsup hT hfm hf, hshift] with x hx hTx
  -- `bAvg n (T x) = ((n+1)/n) * bAvg (n+1) x - f x / n`
  have hkey : ∀ n : ℕ, 1 ≤ n →
      bAvg T f n (T x)
        = (((n : ℝ) + 1) / (n : ℝ)) * bAvg T f (n + 1) x - f x / (n : ℝ) := by
    intro n hn
    have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hS : birkhoffSum T f n (T x) = birkhoffSum T f (n + 1) x - f x := by
      rw [birkhoffSum_succ']; ring
    simp only [bAvg, hS]
    push_cast
    field_simp
  have hlim2 : Tendsto (fun n : ℕ =>
      (((n : ℝ) + 1) / (n : ℝ)) * bAvg T f (n + 1) x - f x / (n : ℝ)) atTop
      (𝓝 (1 * bLimsup T f x - 0)) := by
    refine Tendsto.sub (Tendsto.mul ?_ (hx.comp (tendsto_add_atTop_nat 1))) ?_
    · have h1 : ∀ n : ℕ, 1 ≤ n → ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
        intro n hn
        have hn0 : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
      have h2 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
        have h3 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n : ℝ)) atTop (𝓝 ((1 : ℝ) + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
        simpa using h3
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (h1 n hn).symm
    · simpa using tendsto_const_div_atTop_nhds_zero_nat (f x)
  have hlim3 : Tendsto (fun n => bAvg T f n (T x)) atTop (𝓝 (bLimsup T f x)) := by
    rw [show bLimsup T f x = 1 * bLimsup T f x - 0 by ring]
    refine hlim2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hkey n hn).symm
  exact tendsto_nhds_unique hTx hlim3

end LatticeProb

end
