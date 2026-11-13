import LatticeProb.Prob.AkcogluKrengelAE.AnchoredBoxErgodicHolds
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAll
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicAllFlip
import LatticeProb.Prob.AkcogluKrengelAE.RectangleErgodicFull

/-!
# The rectangle pointwise ergodic theorem for arbitrary corners

For a measure-preserving additive `ℤᵈ`-action on an ergodic probability space, a bounded measurable
`h` and real `a ≤ b`, the averages `N⁻ᵈ ∑_{x ∈ ∏ᵢ [⌈N aᵢ⌉, ⌈N bᵢ⌉)} h (τ x ω)` converge a.e. to
`∏ᵢ (bᵢ - aᵢ) ∫h`; no sign condition is put on `a`.

In each coordinate the indicator of `[⌈N a⌉, ⌈N b⌉)` is the difference of the signed indicators of
the intervals between `0` and `⌈N b⌉` and between `0` and `⌈N a⌉`; expanding the product writes the
rectangle as a signed sum of `2ᵈ` orthant boxes `signedBox`.  Reflecting the negative
coordinates (`reflectActionS`) and shifting by a fixed vector turns an orthant box into a box
`∏ᵢ [0, mᵢ)` of the reflected action, read at a fixed shifted point.  The box averages of an
ergodic action converge a.e. to the mean along every family of side lengths tending to infinity
(`ae_tendsto_boxAvg_univ_integral`), which gives the limit of each orthant box.

## Main results

* `ae_tendsto_boxAvg_univ_integral`: the box ergodic theorem along arbitrary side lengths;
* `sum_rectBox_eq_signed_sum_signedBox`: the orthant decomposition of a rectangle;
* `rectangleErgodicAll_holds`, `rectangleErgodicAllReduction_holds`, `rectangleErgodicFull_holds`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- **The box ergodic theorem along arbitrary side lengths.**  For an ergodic action, `d ≥ 1`, and
side lengths `m N i → ∞` in every coordinate, the box averages converge a.e. to the mean. -/
theorem ae_tendsto_boxAvg_univ_integral {μ : Measure Ω} [IsProbabilityMeasure μ]
    {σ : Site d → Ω → Ω} (hσ : ∀ z, MeasurePreserving (σ z) μ μ)
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω))
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z, σ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1)
    (hd : 0 < d) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    {m : ℕ → Fin d → ℕ} (hm : ∀ i, Tendsto (fun N => m N i) atTop atTop) :
    ∀ᵐ ω ∂μ, Tendsto (fun N => boxAvg σ h Finset.univ (m N) ω) atTop
      (𝓝 (∫ ω, h ω ∂μ)) := by
  obtain ⟨G, hGm, _hGb, hGconv, hinv⟩ :=
    exists_ae_tendsto_boxAvg hσ hσadd hh hM hb Finset.univ
  have hGinv : ∀ z, G ∘ σ z = G :=
    comp_eq_of_comp_unit_eq hd hσadd fun j => hinv j (Finset.mem_univ j)
  obtain ⟨a, ha⟩ := exists_ae_eq_const_of_ae_invariant (fun z => (hσ z).measurable) hσadd herg
    hGm (Eventually.of_forall fun ω z => congrFun (hGinv z) ω)
  have hGint : ∫ ω, G ω ∂μ = ∫ ω, h ω ∂μ := by
    have hconv : ∀ᵐ ω ∂μ, Tendsto (fun N => gridAvg σ h Finset.univ N ω) atTop
        (𝓝 (G ω)) := by
      have hc := hGconv (fun N _ => N) (fun i _ => tendsto_id)
      simpa only [boxAvg_univ_const_eq_gridAvg] using hc
    have h1 : Tendsto (fun N : ℕ => ∫ ω, gridAvg σ h Finset.univ N ω ∂μ) atTop
        (𝓝 (∫ ω, G ω ∂μ)) :=
      tendsto_integral_of_dominated_convergence (fun _ : Ω => M)
        (fun N => (measurable_gridAvg hσ hh Finset.univ N).aestronglyMeasurable)
        (integrable_const M)
        (fun N => by
          filter_upwards with ω
          rw [Real.norm_eq_abs]
          exact abs_gridAvg_le σ h hM hb Finset.univ N ω) hconv
    have hEq : (fun N : ℕ => ∫ ω, gridAvg σ h Finset.univ N ω ∂μ) =ᶠ[atTop]
        fun _ : ℕ => ∫ ω, h ω ∂μ :=
      eventually_atTop.mpr ⟨1, fun n hn => integral_gridAvg_univ_eq_integral hσ hh hb hn⟩
    exact (tendsto_nhds_unique tendsto_const_nhds (Tendsto.congr' hEq h1)).symm
  have hai : a = ∫ ω, h ω ∂μ := by
    rw [← hGint, integral_congr_ae ha]
    simp
  filter_upwards [hGconv m (fun i _ => hm i), ha] with ω hω hGa
  rwa [hGa, hai] at hω

/-- The integer interval between `0` and `⌈N t⌉`: `[0, ⌈N t⌉)` for `t ≥ 0`, `[⌈N t⌉, 0)` for
`t < 0`. -/
noncomputable def signedInterval (N : ℕ) (t : ℝ) : Finset ℤ :=
  if 0 ≤ t then Finset.Ico 0 ⌈(N : ℝ) * t⌉ else Finset.Ico ⌈(N : ℝ) * t⌉ 0

/-- The sign `1` for `t ≥ 0` and `-1` for `t < 0`. -/
noncomputable def signOf (t : ℝ) : ℝ := if 0 ≤ t then 1 else -1

theorem signOf_mul_abs (t : ℝ) : signOf t * |t| = t := by
  unfold signOf
  split_ifs with ht
  · rw [one_mul, abs_of_nonneg ht]
  · rw [abs_of_neg (not_le.1 ht)]; ring

/-- The indicator of `[⌈N a⌉, ⌈N b⌉)` is the difference of the signed indicators of the intervals
between `0` and `⌈N b⌉` and between `0` and `⌈N a⌉`. -/
theorem ite_Ico_ceil_eq_sub_signedInterval (N : ℕ) {a b : ℝ} (hab : a ≤ b) (x : ℤ) :
    (if x ∈ Finset.Ico ⌈(N : ℝ) * a⌉ ⌈(N : ℝ) * b⌉ then (1 : ℝ) else 0) =
      signOf b * (if x ∈ signedInterval N b then 1 else 0) -
        signOf a * (if x ∈ signedInterval N a then 1 else 0) := by
  have hA : ⌈(N : ℝ) * a⌉ ≤ ⌈(N : ℝ) * b⌉ :=
    Int.ceil_mono (mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg N))
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ ⌈(N : ℝ) * t⌉ := fun t ht =>
    Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) ht)
  have hneg : ∀ t : ℝ, t < 0 → ⌈(N : ℝ) * t⌉ ≤ 0 := fun t ht =>
    Int.ceil_le.2 (by
      rw [Int.cast_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) ht.le)
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have := hpos a ha
    simp only [signOf, signedInterval, if_pos ha, if_pos hb, Finset.mem_Ico]
    split_ifs <;> first | omega | norm_num
  · have := hneg a (not_le.1 ha)
    by_cases hb : 0 ≤ b
    · have := hpos b hb
      simp only [signOf, signedInterval, if_neg ha, if_pos hb, Finset.mem_Ico]
      split_ifs <;> first | omega | norm_num
    · have := hneg b (not_le.1 hb)
      simp only [signOf, signedInterval, if_neg ha, if_neg hb, Finset.mem_Ico]
      split_ifs <;> first | omega | norm_num

/-- The orthant box `∏ᵢ` of the integer intervals between `0` and `⌈N cᵢ⌉`. -/
noncomputable def signedBox (c : Fin d → ℝ) (N : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => signedInterval N (c i)

theorem mem_signedBox {c : Fin d → ℝ} {N : ℕ} {x : Site d} :
    x ∈ signedBox c N ↔ ∀ i, x i ∈ signedInterval N (c i) :=
  Fintype.mem_piFinset

/-- **The rectangle is the signed sum of its `2ᵈ` orthant corner boxes**, pointwise. -/
theorem indicator_rectBox_eq_sum_signedBox (a b : Fin d → ℝ) (N : ℕ) (x : Site d)
    (hab : ∀ i, a i ≤ b i) :
    (if x ∈ rectBox a b N then (1 : ℝ) else 0) =
      ∑ S : Finset (Fin d), (-1) ^ S.card * ((∏ i, signOf (corner a b S i)) *
        (if x ∈ signedBox (corner a b S) N then (1 : ℝ) else 0)) := by
  classical
  let F : Fin d → ℝ := fun i =>
    signOf (b i) * (if x i ∈ signedInterval N (b i) then 1 else 0)
  let G : Fin d → ℝ := fun i =>
    signOf (a i) * (if x i ∈ signedInterval N (a i) then 1 else 0)
  have hrect : (if x ∈ rectBox a b N then (1 : ℝ) else 0) = ∏ i, (F i - G i) := by
    have h1 : (if x ∈ rectBox a b N then (1 : ℝ) else 0) =
        ∏ i, (if x i ∈ Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉ then (1 : ℝ) else 0) := by
      rw [Fintype.prod_boole]
      by_cases h : ∀ i, x i ∈ Finset.Ico ⌈(N : ℝ) * a i⌉ ⌈(N : ℝ) * b i⌉
      · rw [if_pos h, if_pos (by simpa only [mem_rectBox] using h)]
      · rw [if_neg h, if_neg (by simpa only [mem_rectBox] using h)]
    rw [h1]
    exact Finset.prod_congr rfl fun i _ => ite_Ico_ceil_eq_sub_signedInterval N (hab i) (x i)
  rw [hrect, Finset.prod_sub F G Finset.univ, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hfactor : (∏ i, (if i ∈ S then G i else F i)) =
      (∏ i ∈ Finset.univ \ S, F i) * ∏ i ∈ S, G i := by
    have hfilter1 : Finset.univ.filter (fun i => i ∈ S) = S := by ext i; simp
    have hfilter2 : Finset.univ.filter (fun i => ¬ i ∈ S) = Finset.univ \ S := by
      ext i; simp [Finset.mem_sdiff]
    rw [Finset.prod_ite, hfilter1, hfilter2, mul_comm]
  have hbox : (∏ i, (if i ∈ S then G i else F i)) =
      (∏ i, signOf (corner a b S i)) *
        (if x ∈ signedBox (corner a b S) N then (1 : ℝ) else 0) := by
    have hc : (∏ i, (if i ∈ S then G i else F i)) = ∏ i, (signOf (corner a b S i) *
        (if x i ∈ signedInterval N (corner a b S i) then (1 : ℝ) else 0)) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i ∈ S <;> simp [F, G, corner, hi]
    rw [hc, Finset.prod_mul_distrib, Fintype.prod_boole]
    congr 1
    by_cases h : ∀ i, x i ∈ signedInterval N (corner a b S i)
    · rw [if_pos h, if_pos (mem_signedBox.2 h)]
    · rw [if_neg h, if_neg (fun hx => h (mem_signedBox.1 hx))]
  rw [mul_assoc, ← hfactor, hbox]

/-- **The orthant decomposition of a rectangle sum.** -/
theorem sum_rectBox_eq_signed_sum_signedBox (f : Site d → ℝ) (a b : Fin d → ℝ) (N : ℕ)
    (hab : ∀ i, a i ≤ b i) :
    ∑ x ∈ rectBox a b N, f x = ∑ S : Finset (Fin d), (-1) ^ S.card *
      ((∏ i, signOf (corner a b S i)) * ∑ x ∈ signedBox (corner a b S) N, f x) := by
  classical
  let U : Finset (Site d) := rectBox a b N ∪
    Finset.univ.biUnion fun S : Finset (Fin d) => signedBox (corner a b S) N
  have hR : rectBox a b N ⊆ U := Finset.subset_union_left
  have hB : ∀ S, signedBox (corner a b S) N ⊆ U := fun S =>
    (Finset.subset_biUnion_of_mem (fun S : Finset (Fin d) => signedBox (corner a b S) N)
      (Finset.mem_univ S)).trans Finset.subset_union_right
  have hsum : ∀ B ⊆ U, ∑ x ∈ B, f x = ∑ x ∈ U, (if x ∈ B then (1 : ℝ) else 0) * f x := by
    intro B hBU
    simp_rw [boole_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hBU]
  rw [hsum _ hR]
  simp_rw [fun x => indicator_rectBox_eq_sum_signedBox a b N x hab, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hsum _ (hB S), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- The coordinates in which `c` is negative. -/
noncomputable def negSet (c : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => c i < 0

/-- The unit shift in the coordinates in which `c` is negative. -/
noncomputable def negShift (c : Fin d → ℝ) (i : Fin d) : ℤ :=
  if c i < 0 then 1 else 0

/-- The side lengths of the orthant box: `⌈N cᵢ⌉` for `cᵢ ≥ 0` and `⌊N (-cᵢ)⌋` for `cᵢ < 0`. -/
noncomputable def signedLength (c : Fin d → ℝ) (N : ℕ) (i : Fin d) : ℕ :=
  if 0 ≤ c i then (⌈(N : ℝ) * c i⌉).toNat else ⌊(N : ℝ) * -c i⌋₊

theorem natCast_signedLength_of_neg {c : Fin d → ℝ} {i : Fin d} (hci : c i < 0) (N : ℕ) :
    ((signedLength c N i : ℕ) : ℤ) = -⌈(N : ℝ) * c i⌉ := by
  rw [signedLength, if_neg (not_le.2 hci),
    Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg N) (neg_nonneg.2 hci.le)),
    mul_neg, Int.floor_neg]

theorem natCast_signedLength_of_nonneg {c : Fin d → ℝ} {i : Fin d} (hci : 0 ≤ c i) (N : ℕ) :
    ((signedLength c N i : ℕ) : ℤ) = ⌈(N : ℝ) * c i⌉ := by
  rw [signedLength, if_pos hci,
    Int.toNat_of_nonneg (Int.ceil_nonneg (mul_nonneg (Nat.cast_nonneg N) hci))]

/-- Reflecting the negative coordinates and shifting by `negShift c` maps the orthant box onto the
box `∏ᵢ [0, signedLengthᵢ)`. -/
theorem sum_signedBox_eq_sum_intBox (c : Fin d → ℝ) (N : ℕ) (F : Site d → ℝ) :
    ∑ x ∈ signedBox c N, F x =
      ∑ y ∈ intBox Finset.univ (signedLength c N),
        F (flipSubset (negSet c) (y + negShift c)) := by
  have hP : ∀ i, i ∈ negSet c ↔ c i < 0 := fun i => by simp [negSet]
  have hint : ∀ y : Site d, y ∈ intBox Finset.univ (signedLength c N) ↔
      ∀ i, 0 ≤ y i ∧ y i < ((signedLength c N i : ℕ) : ℤ) := fun y => by
    simp [intBox, Fintype.mem_piFinset, Finset.mem_Ico]
  refine Finset.sum_nbij' (fun x => flipSubset (negSet c) x - negShift c)
    (fun y => flipSubset (negSet c) (y + negShift c)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [hint]
    intro i
    have hxi := mem_signedBox.1 hx i
    by_cases hci : c i < 0
    · simp only [signedInterval, if_neg (not_le.2 hci), Finset.mem_Ico] at hxi
      simp only [Pi.sub_apply, flipSubset, negShift, (hP i).2 hci, if_true, hci,
        natCast_signedLength_of_neg hci]
      omega
    · simp only [signedInterval, if_pos (not_lt.1 hci), Finset.mem_Ico] at hxi
      have hni : i ∉ negSet c := fun h => hci ((hP i).1 h)
      simp only [Pi.sub_apply, flipSubset, negShift, hni, if_false, hci,
        natCast_signedLength_of_nonneg (not_lt.1 hci)]
      omega
  · intro y hy
    rw [hint] at hy
    rw [mem_signedBox]
    intro i
    have hyi := hy i
    by_cases hci : c i < 0
    · rw [natCast_signedLength_of_neg hci] at hyi
      simp only [signedInterval, if_neg (not_le.2 hci), Finset.mem_Ico, flipSubset, negShift,
        Pi.add_apply, (hP i).2 hci, if_true, hci]
      omega
    · rw [natCast_signedLength_of_nonneg (not_lt.1 hci)] at hyi
      have hni : i ∉ negSet c := fun h => hci ((hP i).1 h)
      simp only [signedInterval, if_pos (not_lt.1 hci), Finset.mem_Ico, flipSubset, negShift,
        Pi.add_apply, hni, if_false, hci]
      omega
  · intro x _
    simp only [sub_add_cancel, flipSubset_involutive]
  · intro y _
    simp only [flipSubset_involutive, add_sub_cancel_right]
  · intro x _
    simp only [sub_add_cancel, flipSubset_involutive]

/-- The orthant side lengths tend to infinity in every coordinate with `cᵢ ≠ 0`. -/
theorem tendsto_signedLength {c : Fin d → ℝ} {i : Fin d} (hci : c i ≠ 0) :
    Tendsto (fun N => signedLength c N i) atTop atTop := by
  rcases lt_or_gt_of_ne hci with hneg | hpos
  · have h1 : Tendsto (fun N : ℕ => ⌈(N : ℝ) * -c i⌉.toNat - 1) atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp (tendsto_ceil_toNat_atTop (neg_pos.2 hneg))
    refine tendsto_atTop_mono (fun N => ?_) h1
    have hz := natCast_signedLength_of_neg hneg N
    have hc1 : ⌈(N : ℝ) * -c i⌉ ≤ ⌊(N : ℝ) * -c i⌋ + 1 := Int.ceil_le_floor_add_one _
    have hc2 : ⌊(N : ℝ) * -c i⌋ = -⌈(N : ℝ) * c i⌉ := by rw [mul_neg, Int.floor_neg]
    omega
  · have h1 := tendsto_ceil_toNat_atTop hpos
    refine h1.congr fun N => ?_
    simp only [signedLength, if_pos hpos.le]

/-- The normalised orthant side lengths: `signedLength / N → |cᵢ|`. -/
theorem tendsto_signedLength_div (c : Fin d → ℝ) (i : Fin d) :
    Tendsto (fun N : ℕ => ((signedLength c N i : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 |c i|) := by
  by_cases hci : 0 ≤ c i
  · rw [abs_of_nonneg hci]
    refine (tendsto_ceil_toNat_div hci).congr fun N => ?_
    simp only [signedLength, if_pos hci]
  · have hneg : 0 ≤ -c i := neg_nonneg.2 (not_le.1 hci).le
    rw [abs_of_neg (not_le.1 hci)]
    have h1 := (tendsto_nat_floor_mul_div_atTop hneg).comp tendsto_natCast_atTop_atTop
    refine h1.congr fun N => ?_
    simp only [Function.comp_apply, signedLength, if_neg hci, mul_comm (-c i)]

/-- **The orthant-box ergodic theorem.**  For an ergodic action, `d ≥ 1`, and any `c`, the
normalised sums over `signedBox c N` converge a.e. to `(∏ᵢ |cᵢ|) ∫h`. -/
theorem ae_tendsto_signedBox {μ : Measure Ω} [IsProbabilityMeasure μ]
    {τ : Site d → Ω → Ω} (hτ : ∀ z, MeasurePreserving (τ z) μ μ)
    (hadd : ∀ z w ω, τ (z + w) ω = τ z (τ w ω))
    (herg : ∀ A : Set Ω, MeasurableSet A → (∀ z, τ z ⁻¹' A = A) → μ A = 0 ∨ μ A = 1)
    (hd : 0 < d) {h : Ω → ℝ} (hh : Measurable h) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |h x| ≤ M)
    (c : Fin d → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
        ∑ x ∈ signedBox c N, h (τ x ω)) atTop (𝓝 ((∏ i, |c i|) * ∫ ω, h ω ∂μ)) := by
  by_cases hzero : ∃ i, c i = 0
  · obtain ⟨i, hi⟩ := hzero
    have hemp : ∀ N : ℕ, signedBox c N = ∅ := by
      intro N
      rw [Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := mem_signedBox.1 hx i
      simp [signedInterval, hi] at this
    have hprod : (∏ i, |c i|) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    filter_upwards with ω
    simp only [hemp, Finset.sum_empty, mul_zero, hprod, zero_mul]
    exact tendsto_const_nhds
  push_neg at hzero
  obtain ⟨hτ', hadd', herg'⟩ := reflectActionS_props hτ hadd herg (negSet c)
  set τ' := reflectActionS τ (negSet c) with hτ'def
  have hbox := ae_tendsto_boxAvg_univ_integral hτ' hadd' herg' hd hh hM hb
    (m := fun N => signedLength c N) (fun i => tendsto_signedLength (hzero i))
  have hshift := (hτ' (negShift c)).quasiMeasurePreserving.ae hbox
  have hscale : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
      ∏ i, ((signedLength c N i : ℕ) : ℝ)) atTop (𝓝 (∏ i, |c i|)) := by
    have hlim := tendsto_finset_prod Finset.univ fun i _ => tendsto_signedLength_div c i
    refine hlim.congr' ?_
    filter_upwards with N
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Real.rpow_neg (Nat.cast_nonneg N), Real.rpow_natCast, div_eq_mul_inv, mul_comm]
  filter_upwards [hshift] with ω hω
  have heq : ∀ N : ℕ, (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ signedBox c N, h (τ x ω) =
      ((N : ℝ) ^ (-(d : ℝ)) * ∏ i, ((signedLength c N i : ℕ) : ℝ)) *
        boxAvg τ' h Finset.univ (signedLength c N) (τ' (negShift c) ω) := by
    intro N
    have hsum : ∑ x ∈ signedBox c N, h (τ x ω) =
        ∑ w ∈ boxGridSet Finset.univ (signedLength c N),
          h (τ' (natToSite w) (τ' (negShift c) ω)) := by
      rw [sum_signedBox_eq_sum_intBox c N (fun x => h (τ x ω)),
        sum_boxGridSet_eq_sum_intBox Finset.univ (signedLength c N)
          (fun y => h (τ' y (τ' (negShift c) ω)))]
      refine Finset.sum_congr rfl fun y _ => ?_
      show h (τ' (y + negShift c) ω) = _
      rw [hadd']
    rw [hsum, sum_boxGridSet_eq_boxAvg_mul τ' h Finset.univ (signedLength c N)
      (τ' (negShift c) ω)]
    ring
  simp_rw [heq]
  exact hscale.mul hω

/-- **The rectangle pointwise ergodic theorem for arbitrary corners `a ≤ b`.** -/
theorem rectangleErgodicAll_holds (d : ℕ) : RectangleErgodicAll d := by
  intro Ω _ μ _ τ hτ hadd herg h hh hbdd a b hab
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact rectangleErgodic_holds 0 μ τ hτ hadd herg h hh hbdd a b (fun i => i.elim0) hab
  obtain ⟨M, hM, hb⟩ := hbdd
  have hall : ∀ᵐ ω ∂μ, ∀ S : Finset (Fin d),
      Tendsto (fun N : ℕ => (N : ℝ) ^ (-(d : ℝ)) *
          ∑ x ∈ signedBox (corner a b S) N, h (τ x ω)) atTop
        (𝓝 ((∏ i, |corner a b S i|) * ∫ ω, h ω ∂μ)) := by
    rw [Filter.eventually_all]
    exact fun S => ae_tendsto_signedBox hτ hadd herg hd hh hM hb (corner a b S)
  filter_upwards [hall] with ω hω
  have hfun : ∀ N : ℕ, (N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ rectBox a b N, h (τ x ω) =
      ∑ S : Finset (Fin d), (-1) ^ S.card * ((∏ i, signOf (corner a b S i)) *
        ((N : ℝ) ^ (-(d : ℝ)) * ∑ x ∈ signedBox (corner a b S) N, h (τ x ω))) := by
    intro N
    rw [sum_rectBox_eq_signed_sum_signedBox (fun x => h (τ x ω)) a b N hab, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    ring
  have hlim : (∑ S : Finset (Fin d), (-1) ^ S.card * ((∏ i, signOf (corner a b S i)) *
      ((∏ i, |corner a b S i|) * ∫ ω, h ω ∂μ))) = (∏ i, (b i - a i)) * ∫ ω, h ω ∂μ := by
    rw [← signed_sum_corner_eq_prod_sub a b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [← mul_assoc (∏ i, signOf (corner a b S i)), ← Finset.prod_mul_distrib]
    simp only [signOf_mul_abs]
    ring
  simp_rw [hfun]
  rw [← hlim]
  exact tendsto_finsetSum Finset.univ fun S _ =>
    ((hω S).const_mul (∏ i, signOf (corner a b S i))).const_mul ((-1) ^ S.card)

/-- The arbitrary-corner reduction holds, its conclusion being proved. -/
theorem rectangleErgodicAllReduction_holds (d : ℕ) : RectangleErgodicAllReduction d :=
  fun _ => rectangleErgodicAll_holds d

/-- `RectangleErgodicFull` holds: it is `RectangleErgodicAll` with the average named. -/
theorem rectangleErgodicFull_holds (d : ℕ) : RectangleErgodicFull d := by
  intro Ω _ μ _ τ hτ hadd herg h hh hbdd a b hab
  exact rectangleErgodicAll_holds d μ τ hτ hadd herg h hh hbdd a b hab

end LatticeProb
