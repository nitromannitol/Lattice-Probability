/-
The Gaussian maximal estimate for Brownian motion.

`LatticeProb/Prob/BrownianTail.lean` has the tail of the value at a single
time.  What an application needs is the tail of the whole path: the chance that
a Brownian path ever leaves a band of width `a` before time `T` is again
Gaussian in `a ^ 2 / T`, with constants that do not depend on anything.

The route is Ottaviani's maximal inequality on a dyadic grid, so no reflection
principle and no continuous-time martingale theory is needed.  Three steps.

The increments of the process over the grid are independent, so the event that
the path first passes the level `2 α` at a grid point `t k` is independent of
the event that the increment from `t k` to the last grid point is smaller than
`α`: the first is measurable for the increments before `k`, the second is a sum
of the increments after `k`.  Ottaviani's inequality then bounds the chance of
ever passing `2 α` on the grid by `2 x / (1 - 2 x)` with
`x = exp (- α ^ 2 / (2 T))`, and a case split on whether `4 x` exceeds `1`
turns that into `4 x` with no side condition.

A path which leaves the band at some real time before `T` leaves half the band
at a dyadic time, by uniform continuity; the dyadic events increase with the
level, so their limit carries the bound.

Finally the bound is transported to a process with only almost surely continuous
paths and no measurability: a pre-Brownian motion has a measurable modification
with continuous paths, and two modifications with continuous paths agree at
every time almost surely.
-/
import Mathlib
import LatticeProb.Prob.Dyadic
import LatticeProb.Prob.Ottaviani
import LatticeProb.Prob.BrownianTail

open MeasureTheory ProbabilityTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-! ### Two elementary facts used for the first passage sets -/

theorem measurableSet_abs_lt {Ω : Type*} {mm : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : Measurable f) (c : ℝ) : MeasurableSet {ω | |f ω| < c} :=
  measurableSet_lt hf.abs measurable_const

/-- The set on which `|S k|` first reaches `c` at the index `k`. -/
theorem measurableSet_firstPassage {Ω : Type*} {mm : MeasurableSpace Ω} {S : ℕ → Ω → ℝ} {k : ℕ}
    (hS : ∀ j, j ≤ k → Measurable (S j)) (c : ℝ) :
    MeasurableSet ({ω | c ≤ |S k ω|} ∩ ⋂ j ∈ Finset.range k, {ω | |S j ω| < c}) := by
  refine MeasurableSet.inter (measurableSet_le measurable_const ((hS k le_rfl).abs)) ?_
  refine MeasurableSet.biInter (Finset.range k).countable_toSet (fun j hj => ?_)
  exact measurableSet_abs_lt (hS j (le_of_lt (Finset.mem_range.1 hj))) c

/-- Telescoping over `Finset.Ico`. -/
theorem sum_Ico_sub_telescope {M : Type*} [AddCommGroup M] (f : ℕ → M) {a b : ℕ} (hab : a ≤ b) :
    ∑ i ∈ Finset.Ico a b, (f (i + 1) - f i) = f b - f a := by
  rw [Finset.sum_Ico_eq_sub _ hab, Finset.sum_range_sub f, Finset.sum_range_sub f]
  abel

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The tails of a single value and of an increment -/

/-- **The two-sided Gaussian tail at a single time.**  The one-sided bound of
`LatticeProb.measure_ge_le_exp` applied to `B` and to `-B`. -/
theorem measure_abs_ge_le_exp (hB : IsPreBrownianReal B P)
    {T : ℝ≥0} (hT : 0 < T) {a : ℝ} (ha : 0 < a) :
    P {ω | a ≤ |B T ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
  have h1 : {ω : Ω | a ≤ |B T ω|} ⊆ {ω : Ω | a ≤ B T ω} ∪ {ω : Ω | a ≤ (-B) T ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases abs_cases (B T ω) with ⟨he, _⟩ | ⟨he, _⟩
    · left
      simp only [Set.mem_setOf_eq]
      rw [he] at hω
      exact hω
    · right
      simp only [Set.mem_setOf_eq, Pi.neg_apply]
      rw [he] at hω
      exact hω
  have h2 := measure_ge_le_exp hB hT ha
  have h3 := measure_ge_le_exp hB.neg hT ha
  calc P {ω : Ω | a ≤ |B T ω|}
      ≤ P ({ω : Ω | a ≤ B T ω} ∪ {ω : Ω | a ≤ (-B) T ω}) := measure_mono h1
    _ ≤ P {ω : Ω | a ≤ B T ω} + P {ω : Ω | a ≤ (-B) T ω} := measure_union_le _ _
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * T)))) := by
        rw [two_mul]
        exact add_le_add h2 h3

/-- **The Gaussian tail of an increment** over a time span at most `R`. -/
theorem measure_abs_sub_ge_le (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t)
    {a R : ℝ} (ha : 0 < a) (hR : (t : ℝ) - (s : ℝ) ≤ R) :
    P {ω | a ≤ |B t ω - B s ω|} ≤ 2 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (2 * R)))) := by
  rcases eq_or_lt_of_le hst with rfl | hlt
  · have hempty : {ω : Ω | a ≤ |B s ω - B s ω|} = (∅ : Set Ω) := by
      ext ω
      simp only [sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      exact ha
    rw [hempty, measure_empty]
    exact zero_le
  · have hu : (0 : ℝ≥0) < t - s := tsub_pos_of_lt hlt
    have hshift := measure_abs_ge_le_exp (hB.shift s) hu ha
    have hts : s + (t - s) = t := add_tsub_cancel_of_le hst
    have hset : {ω : Ω | a ≤ |B (s + (t - s)) ω - B s ω|} = {ω : Ω | a ≤ |B t ω - B s ω|} := by
      rw [hts]
    rw [hset] at hshift
    refine le_trans hshift ?_
    have hcoe : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := NNReal.coe_sub hst
    have hpos : (0 : ℝ) < ((t - s : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr hu
    have hmono : Real.exp (-(a ^ 2 / (2 * ((t - s : ℝ≥0) : ℝ))))
        ≤ Real.exp (-(a ^ 2 / (2 * R))) := by
      apply Real.exp_le_exp.mpr
      have h1 : a ^ 2 / (2 * R) ≤ a ^ 2 / (2 * ((t - s : ℝ≥0) : ℝ)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [hcoe]
        linarith
      linarith
    exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hmono) 2


/-! ### The maximal estimate on a finite grid -/

/-- The arithmetic that turns Ottaviani's bound into a bound with no side condition:
`(1 - 2 x) p ≤ 2 x` and `p ≤ 1` force `p ≤ 4 x`, whatever `x` is. -/
theorem le_four_mul_of_one_sub_two_mul_le {x p : ℝ≥0∞} (hp : p ≤ 1)
    (h : (1 - 2 * x) * p ≤ 2 * x) : p ≤ 4 * x := by
  rcases le_or_gt (2 * x) 1 with hx | hx
  · have hsplit : ((1 : ℝ≥0∞) - 2 * x) + 2 * x = 1 := tsub_add_cancel_of_le hx
    calc p = (((1 : ℝ≥0∞) - 2 * x) + 2 * x) * p := by rw [hsplit, one_mul]
      _ = (1 - 2 * x) * p + 2 * x * p := by rw [add_mul]
      _ ≤ 2 * x + 2 * x * 1 := add_le_add h (mul_le_mul_right hp (2 * x))
      _ = 4 * x := by rw [mul_one]; ring
  · exact le_trans hp (le_trans hx.le (mul_le_mul_left (by norm_num) x))

/-- **The Gaussian maximal estimate on a finite grid.**  For a monotone family of times
whose span is at most `T`, the chance that `|B (t k) - B (t 0)|` ever reaches `2 α` is at
most `4 exp (- α ^ 2 / (2 T))`.  Ottaviani's inequality is applied to the increments of the
process along the grid, which are independent. -/
theorem measure_grid_max_le [IsProbabilityMeasure P]
    (hB : IsPreBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (N : ℕ) (t : ℕ → ℝ≥0) (hmono : Monotone t)
    {T α : ℝ} (hα : 0 < α) (hspan : (t N : ℝ) - (t 0 : ℝ) ≤ T) :
    P {ω | ∃ k ≤ N, 2 * α ≤ |B (t k) ω - B (t 0) ω|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(α ^ 2 / (2 * T)))) := by
  classical
  set x := ENNReal.ofReal (Real.exp (-(α ^ 2 / (2 * T)))) with hx
  set D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω with hD
  have hDm : ∀ i, Measurable (D i) := fun i => (hm _).sub (hm _)
  have hind : iIndepFun D P := hB.hasIndepIncrements.nat hmono
  set m : ℕ → MeasurableSpace Ω := fun i => MeasurableSpace.comap (D i) inferInstance with hmdef
  have hle : ∀ i, m i ≤ (inferInstance : MeasurableSpace Ω) := fun i => (hDm i).comap_le
  have hiIndep : iIndep m P := hind
  have hIndepk : ∀ k : ℕ, Indep (⨆ i ∈ Set.Iio k, m i) (⨆ i ∈ Set.Ici k, m i) P := fun k =>
    indep_iSup_of_disjoint hle hiIndep (Set.Iio_disjoint_Ici le_rfl)
  have hmeas_sum : ∀ (I : Set ℕ) (s : Finset ℕ), (∀ i ∈ s, i ∈ I) →
      Measurable[⨆ i ∈ I, m i] (fun ω => ∑ i ∈ s, D i ω) := by
    intro I s hs
    refine Finset.measurable_sum s (fun i hi => ?_)
    exact Measurable.mono (measurable_iff_comap_le.2 le_rfl) (le_biSup m (hs i hi)) le_rfl
  set S : ℕ → Ω → ℝ := fun j ω => B (t j) ω - B (t 0) ω with hS
  have hSsum : ∀ j, (fun ω => ∑ i ∈ Finset.range j, D i ω) = S j := by
    intro j
    funext ω
    exact Finset.sum_range_sub (fun i => B (t i) ω) j
  have hSmeas : ∀ k j, j ≤ k → Measurable[⨆ i ∈ Set.Iio k, m i] (S j) := by
    intro k j hjk
    rw [← hSsum j]
    exact hmeas_sum _ _ (fun i hi => lt_of_lt_of_le (Finset.mem_range.1 hi) hjk)
  set A : ℕ → Set Ω := fun k =>
    {ω | 2 * α ≤ |S k ω|} ∩ ⋂ j ∈ Finset.range k, {ω | |S j ω| < 2 * α} with hA
  set G : ℕ → Set Ω := fun k => {ω | |B (t N) ω - B (t k) ω| < α} with hG
  have hAmeas : ∀ k, MeasurableSet[⨆ i ∈ Set.Iio k, m i] (A k) := fun k =>
    measurableSet_firstPassage (mm := ⨆ i ∈ Set.Iio k, m i) (hSmeas k) (2 * α)
  have hGmeas : ∀ k, k ≤ N → MeasurableSet[⨆ i ∈ Set.Ici k, m i] (G k) := by
    intro k hk
    have heq : (fun ω => ∑ i ∈ Finset.Ico k N, D i ω) = fun ω => B (t N) ω - B (t k) ω := by
      funext ω
      exact sum_Ico_sub_telescope (fun i => B (t i) ω) hk
    have hmeas : Measurable[⨆ i ∈ Set.Ici k, m i] (fun ω => B (t N) ω - B (t k) ω) := by
      rw [← heq]
      exact hmeas_sum _ _ (fun i hi => (Finset.mem_Ico.1 hi).1)
    exact measurableSet_abs_lt (mm := ⨆ i ∈ Set.Ici k, m i) hmeas α
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    (iSup₂_le fun i (_ : i ∈ Set.Iio k) => hle i) _ (hAmeas k)
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_abs_lt ((hm _).sub (hm _)) α
  have hindep : ∀ k, k ≤ N → P (A k ∩ G k) = P (A k) * P (G k) := by
    intro k hk
    exact ((hIndepk k).indepSet_of_measurableSet (hAmeas k) (hGmeas k hk)).measure_inter_eq_mul
  have hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (A j) (A k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    rintro ω ⟨hωj, hωj'⟩ ⟨hωk, hωk'⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hωj' hωk' hωj hωk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact absurd hωj (not_le.2 (hωk' j (Finset.mem_range.2 h)))
    · exact absurd hωk (not_le.2 (hωj' k (Finset.mem_range.2 h)))
  have hM : {ω | ∃ k ≤ N, 2 * α ≤ |S k ω|} ⊆ ⋃ k ∈ Finset.range (N + 1), A k := by
    rintro ω ⟨k, hkN, hk⟩
    have hex : ∃ j, 2 * α ≤ |S j ω| := ⟨k, hk⟩
    have hk0 : 2 * α ≤ |S (Nat.find hex) ω| := Nat.find_spec hex
    have hk0le : Nat.find hex ≤ k := Nat.find_le hk
    refine Set.mem_biUnion (Finset.mem_range.2 (Nat.lt_succ_of_le (le_trans hk0le hkN))) ?_
    refine ⟨hk0, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro j hj
    exact not_le.1 (Nat.find_min hex (Finset.mem_range.1 hj))
  have hsub : ∀ k, k ≤ N → A k ∩ G k ⊆ {ω | α ≤ |S N ω|} := by
    rintro k hk ω ⟨⟨hωA, -⟩, hωG⟩
    have hωG' : |B (t N) ω - B (t k) ω| < α := hωG
    simp only [Set.mem_setOf_eq] at hωA ⊢
    have hdiff : S N ω - S k ω = B (t N) ω - B (t k) ω := by simp [hS]
    have h1 : |S k ω| - |S N ω - S k ω| ≤ |S N ω| := by
      have h0 := abs_sub_abs_le_abs_sub (S k ω) (S N ω)
      have h2 : |S k ω - S N ω| = |S N ω - S k ω| := abs_sub_comm _ _
      linarith [h0, h2.symm.le, h2.le]
    rw [hdiff] at h1
    linarith [hωG']
  -- the two Gaussian inputs
  have hspank : ∀ k, k ≤ N → ((t N : ℝ) - (t k : ℝ)) ≤ T := by
    intro k hk
    have h0 : (t 0 : ℝ) ≤ (t k : ℝ) := NNReal.coe_le_coe.2 (hmono (Nat.zero_le k))
    linarith
  have hGle : ∀ k, k ≤ N → (1 : ℝ≥0∞) - 2 * x ≤ P (G k) := by
    intro k hk
    have hcompl : (G k)ᶜ = {ω | α ≤ |B (t N) ω - B (t k) ω|} := by
      ext ω
      simp only [hG, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
    have h1 : P ((G k)ᶜ) ≤ 2 * x := by
      rw [hcompl]
      exact measure_abs_sub_ge_le hB (hmono hk) hα (hspank k hk)
    have h2 : P (G k) + P ((G k)ᶜ) = 1 := by
      rw [measure_add_measure_compl (hGm k), measure_univ]
    rw [tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = P (G k) + P ((G k)ᶜ) := h2.symm
      _ ≤ P (G k) + 2 * x := add_le_add_right h1 _
  have hE : P {ω | α ≤ |S N ω|} ≤ 2 * x :=
    measure_abs_sub_ge_le hB (hmono (Nat.zero_le N)) hα hspan
  have hott := ottaviani hAm hGm hdisj hindep hGle hsub hM
  exact le_four_mul_of_one_sub_two_mul_le prob_le_one (le_trans hott hE)

/-! ### From the grid to the whole path -/

theorem measure_exists_abs_sub_ge_le [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    P {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω - B 0 ω|}
      ≤ 4 * ENNReal.ofReal (Real.exp (-(a ^ 2 / (32 * (T : ℝ))))) := by
  classical
  set grid : ℕ → ℕ → ℝ≥0 := fun n k => Real.toNNReal ((k : ℝ) / 2 ^ n) with hgrid
  set NN : ℕ → ℕ := fun n => ⌊(T : ℝ) * 2 ^ n⌋₊ with hNN
  set E : ℕ → Set Ω := fun n =>
    {ω | ∃ k ≤ NN n, 2 * (a / 4) ≤ |B (grid n k) ω - B (grid n 0) ω|} with hE
  have hgrid0 : ∀ n, grid n 0 = 0 := by
    intro n
    simp [hgrid]
  have hgmono : ∀ n, Monotone (grid n) := by
    intro n i j hij
    apply Real.toNNReal_le_toNNReal
    gcongr
  have hgle : ∀ n k, k ≤ NN n → ((grid n k : ℝ)) ≤ (T : ℝ) := by
    intro n k hk
    have h1 : (k : ℝ) ≤ (T : ℝ) * 2 ^ n := (Nat.le_floor_iff (by positivity)).1 hk
    have h2 : (k : ℝ) / 2 ^ n ≤ (T : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      exact h1
    calc ((grid n k : ℝ)) = max ((k : ℝ) / 2 ^ n) 0 := by
          simp [hgrid, Real.coe_toNNReal']
      _ ≤ (T : ℝ) := max_le h2 (by positivity)
  have hspan : ∀ n, ((grid n (NN n) : ℝ) - (grid n 0 : ℝ)) ≤ (T : ℝ) := by
    intro n
    rw [hgrid0 n]
    simpa using hgle n (NN n) le_rfl
  have hEbound : ∀ n, P (E n) ≤ 4 * ENNReal.ofReal (Real.exp (-((a / 4) ^ 2 / (2 * (T : ℝ))))) :=
    fun n => measure_grid_max_le hB.toIsPreBrownianReal hm (NN n) (grid n) (hgmono n) (by positivity) (hspan n)
  have hexp : (a / 4) ^ 2 / (2 * (T : ℝ)) = a ^ 2 / (32 * (T : ℝ)) := by
    rw [div_pow]
    rw [div_div]
    norm_num
    ring
  have hEmono : Monotone E := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rintro ω ⟨k, hk, hka⟩
    refine ⟨2 * k, ?_, ?_⟩
    · have h1 : (k : ℝ) ≤ (T : ℝ) * 2 ^ n := (Nat.le_floor_iff (by positivity)).1 hk
      refine (Nat.le_floor_iff (by positivity)).2 ?_
      push_cast
      calc (2 : ℝ) * k ≤ 2 * ((T : ℝ) * 2 ^ n) := by linarith
        _ = (T : ℝ) * 2 ^ (n + 1) := by ring
    · have hgg : grid (n + 1) (2 * k) = grid n k := by
        simp only [hgrid]
        congr 1
        push_cast
        ring
      rw [hgg, hgrid0 n, hgrid0 (n + 1)] at *
      exact hka
  have hinc : {ω | ∃ s : ℝ≥0, s ≤ T ∧ a ≤ |B s ω - B 0 ω|} ≤ᵐ[P] ⋃ n, E n := by
    filter_upwards [hB.cont] with ω hcont hω
    obtain ⟨s, hs, hsa⟩ := hω
    have hcont' : Continuous (fun r : ℝ≥0 => B r ω - B 0 ω) := hcont.sub continuous_const
    obtain ⟨n, k, hk, hka⟩ :=
      dyadic_witness (B := fun r ω => B r ω - B 0 ω) (T := T) (a := a) (ω := ω) hcont'
        ⟨s, hs, hsa⟩
    refine Set.mem_iUnion.2 ⟨n, k, ?_, ?_⟩
    · refine (Nat.le_floor_iff (by positivity)).2 ?_
      rw [← div_le_iff₀ (by positivity : (0:ℝ) < 2 ^ n)]
      exact hk
    · rw [hgrid0 n]
      have h2 : (2 : ℝ) * (a / 4) = a / 2 := by ring
      rw [h2]
      exact hka
  refine le_trans (measure_mono_ae hinc) ?_
  rw [hEmono.measure_iUnion]
  refine iSup_le fun n => ?_
  rw [← hexp]
  exact hEbound n

/-! ### Dropping the measurability hypothesis -/

/-- Two processes on `ℝ≥0` which are modifications of each other and have almost surely
continuous paths agree at every time almost surely: they are indistinguishable.  A countable
dense set of times carries the almost sure agreement, and continuity spreads it. -/
theorem ae_forall_eq_of_modification {C : ℝ≥0 → Ω → ℝ} (hmod : ∀ t, B t =ᵐ[P] C t)
    (hBc : ∀ᵐ ω ∂P, Continuous fun t => B t ω) (hCc : ∀ᵐ ω ∂P, Continuous fun t => C t ω) :
    ∀ᵐ ω ∂P, ∀ t, B t ω = C t ω := by
  obtain ⟨s, hs_count, hs_dense⟩ := TopologicalSpace.exists_countable_dense (ℝ≥0)
  have key : ∀ᵐ ω ∂P, ∀ t ∈ s, B t ω = C t ω := by
    rw [MeasureTheory.ae_ball_iff hs_count]
    intro t _
    filter_upwards [hmod t] with ω hω using hω
  filter_upwards [key, hBc, hCc] with ω hω hcB hcC
  intro t
  have heq : (fun t => B t ω) = (fun t => C t ω) :=
    Continuous.ext_on hs_dense hcB hcC (fun u hu => hω u hu)
  exact congrFun heq t

end LatticeProb

end
