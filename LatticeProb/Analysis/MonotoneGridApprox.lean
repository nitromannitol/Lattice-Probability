import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Grid approximation of monotone functions and of integrals over initial segments

Elementary real analysis; no external input.

* `abs_sub_le_of_monotoneOn_cell`: two functions monotone on a cell `[s, t]` differ at a point `x` of the cell
  by at most the larger endpoint discrepancy plus the increment of `g` across the cell.
* `abs_sub_le_of_grid`: on `[0, T]`, if two monotone functions are `η`-close on the uniform grid `k T / m`
  and the increments of `g` over the grid cells are at most `κ`, then `|f - g| ≤ η + κ` on `[0, T]`.
* `abs_setIntegral_sub_le_of_grid`: for finite measures `μ, ν` on `ℝ` whose distribution functions
  `t ↦ μ [0, t]` and `t ↦ ν [0, t]` are `δ`-close on `[0, T]`, and a measurable `w` bounded by `W` with
  oscillation at most `κ` on mesh `T / m`, the integrals of `w` over `[0, s]` differ by at most
  `κ (μ [0, T] + ν [0, T]) + (2 m + 1) W δ`. The proof replaces `w` by a step function constant on the
  cells `{u | ⌈u m / T⌉₊ = k}`, `k = 0, …, m`; the cell `{0}` carries the atom at `0`.
-/

open MeasureTheory Set

namespace LatticeProb

/-- Two functions monotone on a cell `[s, t]` differ at a point `x` of the cell by at most the larger of the
endpoint discrepancies `|f s - g s|`, `|f t - g t|` plus the increment `g t - g s`. -/
theorem abs_sub_le_of_monotoneOn_cell {f g : ℝ → ℝ} {s t x : ℝ} (hf : MonotoneOn f (Set.Icc s t))
    (hg : MonotoneOn g (Set.Icc s t)) (hx : x ∈ Set.Icc s t) :
    |f x - g x| ≤ max |f s - g s| |f t - g t| + (g t - g s) := by
  obtain ⟨hsx, hxt⟩ := hx
  have hst : s ≤ t := hsx.trans hxt
  have hfx1 : f s ≤ f x := hf ⟨le_rfl, hst⟩ ⟨hsx, hxt⟩ hsx
  have hfx2 : f x ≤ f t := hf ⟨hsx, hxt⟩ ⟨hst, le_rfl⟩ hxt
  have hgx1 : g s ≤ g x := hg ⟨le_rfl, hst⟩ ⟨hsx, hxt⟩ hsx
  have hgx2 : g x ≤ g t := hg ⟨hsx, hxt⟩ ⟨hst, le_rfl⟩ hxt
  have hA : f t - g t ≤ max |f s - g s| |f t - g t| := (le_abs_self _).trans (le_max_right _ _)
  have hB : -(f s - g s) ≤ max |f s - g s| |f t - g t| := (neg_le_abs _).trans (le_max_left _ _)
  rw [abs_le]
  constructor <;> linarith

/-- Grid approximation: on `[0, T]`, two monotone functions that are `η`-close at the grid points
`j T / m`, `j ≤ m`, and whose increments over the grid cells are at most `κ`, satisfy `|f - g| ≤ η + κ`. -/
theorem abs_sub_le_of_grid {f g : ℝ → ℝ} {T η κ : ℝ} {m : ℕ} (hm : 0 < m) (hT : 0 ≤ T)
    (hf : MonotoneOn f (Set.Icc 0 T)) (hg : MonotoneOn g (Set.Icc 0 T))
    (hgrid : ∀ j : ℕ, j ≤ m → |f (j * T / m) - g (j * T / m)| ≤ η)
    (hosc : ∀ j : ℕ, j < m → g ((j + 1) * T / m) - g (j * T / m) ≤ κ) :
    ∀ x ∈ Set.Icc 0 T, |f x - g x| ≤ η + κ := by
  intro x hx
  obtain ⟨hx0, hxT⟩ := hx
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨j, hjm, hj1, hj2⟩ :
      ∃ j : ℕ, j < m ∧ (j : ℝ) * T / m ≤ x ∧ x ≤ ((j : ℝ) + 1) * T / m := by
    rcases hT.eq_or_lt with hT0 | hTpos
    · subst hT0
      have hx' : x = 0 := le_antisymm hxT hx0
      subst hx'
      exact ⟨0, hm, by simp, by simp⟩
    · have hy0 : 0 ≤ x * m / T := div_nonneg (mul_nonneg hx0 hm'.le) hTpos.le
      have hym : x * m / T ≤ m := by
        rw [div_le_iff₀ hTpos]; nlinarith
      set n := ⌊x * m / T⌋₊ with hn
      have hjm : min n (m - 1) < m := lt_of_le_of_lt (min_le_right _ _) (by omega)
      have hjy : ((min n (m - 1) : ℕ) : ℝ) ≤ x * m / T :=
        le_trans (Nat.cast_le.2 (min_le_left _ _)) (Nat.floor_le hy0)
      have hyj : x * m / T ≤ ((min n (m - 1) : ℕ) : ℝ) + 1 := by
        rcases le_total n (m - 1) with h | h
        · rw [min_eq_left h]; exact (Nat.lt_floor_add_one _).le
        · rw [min_eq_right h, Nat.cast_pred hm]
          linarith
      refine ⟨min n (m - 1), hjm, ?_, ?_⟩
      · have h1 := (le_div_iff₀ hTpos).1 hjy
        rw [div_le_iff₀ hm']
        linarith
      · rw [le_div_iff₀ hm']
        exact (div_le_iff₀ hTpos).1 hyj
  have hjm1 : j + 1 ≤ m := hjm
  have hjm' : (j : ℝ) + 1 ≤ m := by exact_mod_cast hjm1
  have hsub : Set.Icc ((j : ℝ) * T / m) (((j : ℝ) + 1) * T / m) ⊆ Set.Icc 0 T := by
    intro u hu
    exact ⟨le_trans (div_nonneg (mul_nonneg (Nat.cast_nonneg j) hT) hm'.le) hu.1,
      le_trans hu.2 ((div_le_iff₀ hm').2 (by nlinarith [mul_le_mul_of_nonneg_right hjm' hT]))⟩
  have h1 := abs_sub_le_of_monotoneOn_cell (hf.mono hsub) (hg.mono hsub) ⟨hj1, hj2⟩
  have hA := hgrid j hjm.le
  have hB := hgrid (j + 1) hjm1
  push_cast at hB
  have hC := hosc j hjm
  have hmax := max_le hA hB
  linarith

/-! ### Cells of the ceiling index `⌈u m / T⌉₊` -/

private lemma ceil_eq_succ_iff {m : ℕ} {T : ℝ} (hm : 0 < m) (hT : 0 < T) (u : ℝ) (j : ℕ) :
    ⌈u * m / T⌉₊ = j + 1 ↔ (j : ℝ) * T / m < u ∧ u ≤ ((j : ℝ) + 1) * T / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.ceil_eq_iff (by omega : j + 1 ≠ 0), Nat.add_sub_cancel]
  push_cast
  rw [lt_div_iff₀ hT, div_le_iff₀ hT, div_lt_iff₀ hm', le_div_iff₀ hm']

private lemma ceil_eq_zero_iff {m : ℕ} {T : ℝ} (hm : 0 < m) (hT : 0 < T) (u : ℝ) :
    ⌈u * m / T⌉₊ = 0 ↔ u ≤ 0 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Nat.ceil_eq_zero, div_le_iff₀ hT, zero_mul]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

private lemma ceil_le_m {m : ℕ} {T : ℝ} (hm : 0 < m) (hT : 0 < T) {u : ℝ} (hu : u ∈ Set.Icc 0 T) :
    ⌈u * m / T⌉₊ ≤ m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply Nat.ceil_le.2
  rw [div_le_iff₀ hT]
  nlinarith [hu.2]

private lemma grid_mem {m k : ℕ} {T : ℝ} (hm : 0 < m) (hT : 0 < T) (hk : k ≤ m) :
    (k : ℝ) * T / m ∈ Set.Icc 0 T := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
  refine ⟨div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT.le) hm'.le, ?_⟩
  rw [div_le_iff₀ hm']
  nlinarith

private lemma abs_sub_ceil_cell_le {m : ℕ} {T : ℝ} (hm : 0 < m) (hT : 0 < T) {u : ℝ} (hu0 : 0 ≤ u) :
    |u - (⌈u * m / T⌉₊ : ℝ) * T / m| ≤ T / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hT0 : T ≠ 0 := hT.ne'
  have hm0 : (m : ℝ) ≠ 0 := hm'.ne'
  have hy0 : 0 ≤ u * m / T := div_nonneg (mul_nonneg hu0 hm'.le) hT.le
  have h1 : u * m / T ≤ (⌈u * m / T⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈u * m / T⌉₊ : ℝ) < u * m / T + 1 := Nat.ceil_lt_add_one hy0
  have key : u - (⌈u * m / T⌉₊ : ℝ) * T / m = (u * m / T - ⌈u * m / T⌉₊) * (T / m) := by
    field_simp
  rw [key, abs_mul, abs_of_nonneg (div_nonneg hT.le hm'.le)]
  have hab : |u * m / T - (⌈u * m / T⌉₊ : ℝ)| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith
  calc |u * m / T - (⌈u * m / T⌉₊ : ℝ)| * (T / m) ≤ 1 * (T / m) :=
        mul_le_mul_of_nonneg_right hab (div_nonneg hT.le hm'.le)
    _ = T / m := one_mul _

/-! ### Mass of a grid cell -/

private lemma Ioc_inter_Icc_zero {a b s : ℝ} (ha : 0 ≤ a) :
    Ioc a b ∩ Icc 0 s = Ioc (min s a) (min s b) := by
  ext u
  simp only [mem_inter_iff, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨h1, h2⟩, _, h4⟩
    exact ⟨lt_of_le_of_lt (min_le_right _ _) h1, le_min h4 h2⟩
  · rintro ⟨h1, h2⟩
    have hu_s : u ≤ s := le_trans h2 (min_le_left _ _)
    have hu_b : u ≤ b := le_trans h2 (min_le_right _ _)
    rcases le_total a s with has | has
    · rw [min_eq_right has] at h1
      exact ⟨⟨h1, hu_b⟩, (ha.trans_lt h1).le, hu_s⟩
    · rw [min_eq_left has] at h1
      exact absurd h1 (not_lt.2 hu_s)

private lemma measureReal_Ioc_eq_sub {μ : Measure ℝ} [IsFiniteMeasure μ] {p q : ℝ} (hp : 0 ≤ p)
    (hpq : p ≤ q) : μ.real (Ioc p q) = μ.real (Icc 0 q) - μ.real (Icc 0 p) := by
  have hU : Icc 0 q = Icc 0 p ∪ Ioc p q := (Icc_union_Ioc_eq_Icc hp hpq).symm
  have hD : Disjoint (Icc 0 p) (Ioc p q) :=
    Set.disjoint_left.2 fun x hx hy => absurd hy.1 (not_lt.2 hx.2)
  rw [hU, measureReal_union hD measurableSet_Ioc]
  ring

/-! ### Integrals of step functions and the grid estimate -/

private lemma integrableOn_of_abs_le {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hf : Measurable f) {C : ℝ} (hC : ∀ x ∈ S, |f x| ≤ C) :
    IntegrableOn f S μ := by
  refine Integrable.mono' (integrable_const C) hf.aestronglyMeasurable ?_
  exact ae_restrict_of_forall_mem hS fun x hx => by simpa [Real.norm_eq_abs] using hC x hx

private lemma setIntegral_grid_step {ρ : Measure ℝ} [IsFiniteMeasure ρ] {S : Set ℝ} {m : ℕ} {T : ℝ}
    (c : ℕ → ℝ) (hcellM : ∀ k : ℕ, MeasurableSet ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ)) :
    ∫ u in S, (∑ k ∈ Finset.range (m + 1),
        ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ).indicator (fun _ => c k) u) ∂ρ
      = ∑ k ∈ Finset.range (m + 1), c k * ρ.real (S ∩ {u : ℝ | ⌈u * m / T⌉₊ = k}) := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [setIntegral_indicator (hcellM k), setIntegral_const, smul_eq_mul]
    ring
  · intro k _
    exact (integrable_const (c k)).indicator (hcellM k)

private lemma abs_setIntegral_sub_approx_le {ρ : Measure ℝ} [IsFiniteMeasure ρ] {w wm : ℝ → ℝ}
    {S : Set ℝ} {κ W : ℝ} (hS : MeasurableSet S) (hw : Measurable w) (hwm : Measurable wm)
    (hwW : ∀ x ∈ S, |w x| ≤ W) (hwmW : ∀ x ∈ S, |wm x| ≤ W) (happrox : ∀ x ∈ S, |w x - wm x| ≤ κ) :
    |∫ u in S, w u ∂ρ - ∫ u in S, wm u ∂ρ| ≤ κ * ρ.real S := by
  rw [← integral_sub (integrableOn_of_abs_le hS hw hwW) (integrableOn_of_abs_le hS hwm hwmW)]
  have h := norm_setIntegral_le_of_norm_le_const (μ := ρ) (s := S) (f := fun u => w u - wm u)
    (C := κ) (measure_lt_top ρ S) (fun x hx => by simpa [Real.norm_eq_abs] using happrox x hx)
  rw [Real.norm_eq_abs] at h
  exact h

private lemma abs_sum_grid_le {c e : ℕ → ℝ} {m : ℕ} {W δ : ℝ} (hW0 : 0 ≤ W)
    (hc : ∀ k ∈ Finset.range (m + 1), |c k| ≤ W) (he0 : |e 0| ≤ δ)
    (he : ∀ j, j < m → |e (j + 1)| ≤ 2 * δ) :
    |∑ k ∈ Finset.range (m + 1), c k * e k| ≤ (2 * m + 1) * W * δ := by
  rw [Finset.sum_range_succ']
  have h1 : ∑ j ∈ Finset.range m, |c (j + 1) * e (j + 1)| ≤ ∑ _j ∈ Finset.range m, (2 * W * δ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjm : j < m := Finset.mem_range.1 hj
    rw [abs_mul]
    calc |c (j + 1)| * |e (j + 1)| ≤ W * (2 * δ) :=
          mul_le_mul (hc (j + 1) (Finset.mem_range.2 (by omega))) (he j hjm) (abs_nonneg _) hW0
      _ = 2 * W * δ := by ring
  have h2 : |c 0 * e 0| ≤ W * δ := by
    rw [abs_mul]
    exact mul_le_mul (hc 0 (Finset.mem_range.2 (by omega))) he0 (abs_nonneg _) hW0
  calc |∑ j ∈ Finset.range m, c (j + 1) * e (j + 1) + c 0 * e 0|
      ≤ |∑ j ∈ Finset.range m, c (j + 1) * e (j + 1)| + |c 0 * e 0| := abs_add_le _ _
    _ ≤ ∑ j ∈ Finset.range m, |c (j + 1) * e (j + 1)| + W * δ :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) h2
    _ ≤ ∑ _j ∈ Finset.range m, (2 * W * δ) + W * δ := by linarith
    _ = (2 * m + 1) * W * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- Integrals over initial segments: a bounded measurable `w` with oscillation at most `κ` on mesh `T / m` and
distribution functions `t ↦ μ [0,t]`, `t ↦ ν [0,t]` that are `δ`-close on `[0, T]` satisfy the estimate below. -/
theorem abs_setIntegral_sub_le_of_grid {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {w : ℝ → ℝ}
    (hw : Measurable w) {T W κ δ : ℝ} {m : ℕ} (hm : 0 < m) (hT : 0 < T)
    (hW : ∀ x ∈ Set.Icc 0 T, |w x| ≤ W)
    (hosc : ∀ x ∈ Set.Icc 0 T, ∀ y ∈ Set.Icc 0 T, |x - y| ≤ T / m → |w x - w y| ≤ κ)
    (hcdf : ∀ t ∈ Set.Icc 0 T, |(μ (Set.Icc 0 t)).toReal - (ν (Set.Icc 0 t)).toReal| ≤ δ) :
    ∀ s ∈ Set.Icc 0 T, |∫ u in Set.Icc 0 s, w u ∂μ - ∫ u in Set.Icc 0 s, w u ∂ν|
      ≤ κ * ((μ (Set.Icc 0 T)).toReal + (ν (Set.Icc 0 T)).toReal) + (2 * m + 1) * W * δ := by
  intro s hs
  obtain ⟨hs0, hsT⟩ := hs
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hT0 : (0 : ℝ) ≤ T := hT.le
  have hTm : 0 ≤ T / m := div_nonneg hT0 hm'.le
  have hκ : 0 ≤ κ := by
    have h := hosc 0 ⟨le_rfl, hT0⟩ 0 ⟨le_rfl, hT0⟩ (by rw [sub_self, abs_zero]; exact hTm)
    simpa using h
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) (hcdf 0 ⟨le_rfl, hT0⟩)
  have hW0 : 0 ≤ W := le_trans (abs_nonneg _) (hW 0 ⟨le_rfl, hT0⟩)
  obtain ⟨wm, hwm⟩ : ∃ wm : ℝ → ℝ, ∀ u, wm u = ∑ k ∈ Finset.range (m + 1),
      ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ).indicator (fun _ => w (k * T / m)) u :=
    ⟨fun u => ∑ k ∈ Finset.range (m + 1),
      ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ).indicator (fun _ => w (k * T / m)) u, fun u => rfl⟩
  have hwmfun : wm = fun u => ∑ k ∈ Finset.range (m + 1),
      ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ).indicator (fun _ => w (k * T / m)) u := funext hwm
  have hceilM : Measurable (fun u : ℝ => ⌈u * m / T⌉₊) :=
    Nat.measurable_ceil.comp ((measurable_id.mul_const _).div_const _)
  have hcellM : ∀ k : ℕ, MeasurableSet ({u : ℝ | ⌈u * m / T⌉₊ = k} : Set ℝ) := fun k =>
    hceilM (measurableSet_singleton k)
  have hwmM : Measurable wm := by
    rw [hwmfun]
    exact Finset.measurable_sum _ fun k _ => measurable_const.indicator (hcellM k)
  have hwm_eq : ∀ u ∈ Set.Icc 0 T, wm u = w ((⌈u * m / T⌉₊ : ℝ) * T / m) := by
    intro u hu
    rw [hwm u, Finset.sum_eq_single (⌈u * m / T⌉₊)]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hnot
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (ceil_le_m hm hT hu))) hnot
  have hgridW : ∀ u ∈ Set.Icc 0 T, (⌈u * m / T⌉₊ : ℝ) * T / m ∈ Set.Icc 0 T := fun u hu =>
    grid_mem hm hT (ceil_le_m hm hT hu)
  have hwmW : ∀ x ∈ Set.Icc 0 s, |wm x| ≤ W := fun x hx => by
    have hxT : x ∈ Set.Icc 0 T := ⟨hx.1, hx.2.trans hsT⟩
    rw [hwm_eq x hxT]
    exact hW _ (hgridW x hxT)
  have happrox : ∀ x ∈ Set.Icc 0 s, |w x - wm x| ≤ κ := fun x hx => by
    have hxT : x ∈ Set.Icc 0 T := ⟨hx.1, hx.2.trans hsT⟩
    rw [hwm_eq x hxT]
    exact hosc x hxT _ (hgridW x hxT) (abs_sub_ceil_cell_le hm hT hx.1)
  have hwW : ∀ x ∈ Set.Icc 0 s, |w x| ≤ W := fun x hx => hW x ⟨hx.1, hx.2.trans hsT⟩
  have hSM : MeasurableSet (Set.Icc 0 s) := measurableSet_Icc
  -- the error of replacing `w` by its step function
  have hEμ := abs_setIntegral_sub_approx_le (ρ := μ) hSM hw hwmM hwW hwmW happrox
  have hEν := abs_setIntegral_sub_approx_le (ρ := ν) hSM hw hwmM hwW hwmW happrox
  -- masses of the cells inside `[0, s]`
  have hcellZero : Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = 0} = Set.Icc 0 0 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨⟨h0, _⟩, hc⟩
      exact ⟨h0, (ceil_eq_zero_iff hm hT u).1 hc⟩
    · rintro ⟨h0, h1⟩
      exact ⟨⟨h0, le_trans h1 hs0⟩, (ceil_eq_zero_iff hm hT u).2 h1⟩
  have hcellSucc : ∀ j : ℕ, Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = j + 1}
      = Set.Ioc ((j : ℝ) * T / m) (((j : ℝ) + 1) * T / m) ∩ Set.Icc 0 s := by
    intro j
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioc]
    rw [ceil_eq_succ_iff hm hT]
    tauto
  have hD : ∀ u ∈ Set.Icc 0 T, |μ.real (Set.Icc 0 u) - ν.real (Set.Icc 0 u)| ≤ δ := fun u hu => hcdf u hu
  have he0 : |μ.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = 0})
      - ν.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = 0})| ≤ δ := by
    rw [hcellZero]
    exact hD 0 ⟨le_rfl, hT0⟩
  have hej : ∀ j : ℕ, j < m → |μ.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = j + 1})
      - ν.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = j + 1})| ≤ 2 * δ := by
    intro j hj
    have ha : (0 : ℝ) ≤ (j : ℝ) * T / m := div_nonneg (mul_nonneg (Nat.cast_nonneg j) hT0) hm'.le
    have hab : (j : ℝ) * T / m ≤ ((j : ℝ) + 1) * T / m := by
      apply div_le_div_of_nonneg_right _ hm'.le
      nlinarith
    have hjm' : (j : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hj
    have hp : 0 ≤ min s ((j : ℝ) * T / m) := le_min hs0 ha
    have hpq : min s ((j : ℝ) * T / m) ≤ min s (((j : ℝ) + 1) * T / m) := min_le_min_left _ hab
    have hp' : min s ((j : ℝ) * T / m) ∈ Set.Icc 0 T := ⟨hp, (min_le_left _ _).trans hsT⟩
    have hq' : min s (((j : ℝ) + 1) * T / m) ∈ Set.Icc 0 T :=
      ⟨le_min hs0 (div_nonneg (mul_nonneg (by positivity) hT0) hm'.le), (min_le_left _ _).trans hsT⟩
    rw [hcellSucc j, Ioc_inter_Icc_zero ha,measureReal_Ioc_eq_sub hp hpq,
      measureReal_Ioc_eq_sub (μ := ν) hp hpq]
    have h1 := hD _ hq'
    have h2 := hD _ hp'
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- the step-function part
  have hstep : ∫ u in Set.Icc 0 s, wm u ∂μ - ∫ u in Set.Icc 0 s, wm u ∂ν
      = ∑ k ∈ Finset.range (m + 1), (w (k * T / m)) *
          (μ.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = k})
            - ν.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = k})) := by
    simp only [hwmfun]
    rw [setIntegral_grid_step (ρ := μ) (fun k : ℕ => w (k * T / m)) hcellM,
      setIntegral_grid_step (ρ := ν) (fun k : ℕ => w (k * T / m)) hcellM, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => (mul_sub _ _ _).symm
  have hZ : |∫ u in Set.Icc 0 s, wm u ∂μ - ∫ u in Set.Icc 0 s, wm u ∂ν| ≤ (2 * m + 1) * W * δ := by
    rw [hstep]
    exact abs_sum_grid_le (c := fun k : ℕ => w (k * T / m))
      (e := fun k : ℕ => μ.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = k})
        - ν.real (Set.Icc 0 s ∩ {u : ℝ | ⌈u * m / T⌉₊ = k})) hW0
      (fun k hk => hW _ (grid_mem hm hT (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))) he0 hej
  -- assembly
  have hfinal : ∫ u in Set.Icc 0 s, w u ∂μ - ∫ u in Set.Icc 0 s, w u ∂ν
      = (∫ u in Set.Icc 0 s, w u ∂μ - ∫ u in Set.Icc 0 s, wm u ∂μ)
        - (∫ u in Set.Icc 0 s, w u ∂ν - ∫ u in Set.Icc 0 s, wm u ∂ν)
        + (∫ u in Set.Icc 0 s, wm u ∂μ - ∫ u in Set.Icc 0 s, wm u ∂ν) := by ring
  rw [hfinal]
  have hμle : κ * μ.real (Set.Icc 0 s) ≤ κ * μ.real (Set.Icc 0 T) :=
    mul_le_mul_of_nonneg_left (measureReal_mono (Set.Icc_subset_Icc le_rfl hsT)) hκ
  have hνle : κ * ν.real (Set.Icc 0 s) ≤ κ * ν.real (Set.Icc 0 T) :=
    mul_le_mul_of_nonneg_left (measureReal_mono (Set.Icc_subset_Icc le_rfl hsT)) hκ
  obtain ⟨a1, a2⟩ := abs_le.1 hEμ
  obtain ⟨b1, b2⟩ := abs_le.1 hEν
  obtain ⟨c1, c2⟩ := abs_le.1 hZ
  show _ ≤ κ * (μ.real (Set.Icc 0 T) + ν.real (Set.Icc 0 T)) + (2 * m + 1) * W * δ
  rw [mul_add]
  exact abs_le.2 ⟨by linarith, by linarith⟩

end LatticeProb
