/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Perc.Peierls at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Perc.DualityMain
import LatticeProb.Bonanno.LQGMetric.Perc.Paths
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Peierls bound for finite-range dependent site percolation on a rectangle of boxes

Statements (the combinatorial and probabilistic facts behind "standard percolation technique",
"Peierls argument", "percolation of good boxes" in DDDF arXiv:1904.08021 Prop. 4.18 step 1,
Ding–Gwynne arXiv:1807.01072 Lemma 3.11, Ding–Dunlap arXiv:1812.06921 Prop. 4.2,
Ding–Zhang–Zeitouni arXiv:1807.00422 Lemma 3.7):

(a) duality (`LQGMetric.percGoodLR_or_percBadTB`, file `Perc/DualityMain`): in a `K × L`
    rectangle of boxes either a left–right crossing by `4`-connected good boxes or a
    top–bottom crossing by `*`-connected bad boxes;
(b) counting (`LQGMetric.card_percChainsFrom_le`, file `Perc/Paths`): at most `8 ^ n`
    `*`-paths with `n` steps from a given box;
(c) Peierls (`LQGMetric.perc_peierls`, this file): if each box of the rectangle is bad with
    probability `≤ ε`, the badness events of boxes pairwise at `ℓ^∞`-distance `> r` satisfy the
    product bound (finite-range dependence), `ε ≤ θ ^ (r+1)²` and `8 θ ≤ 1/2`, then
    `P(no left–right good crossing) ≤ K (8 θ) ^ L`.

Proof of (c), following Ding–Gwynne (`metric-comparison-final.tex` lines 1267–1278) and
Ding–Dunlap (`tightness-gg.tex` lines 2693–2740): by (a), no good crossing gives a simple
top–bottom `*`-path of bad boxes with `k ≥ L` boxes, starting at one of the `K` top boxes;
among its `k` boxes, a residue class modulo `r + 1` of both coordinates contains at least
`k / (r+1)²` of them, which are pairwise at `ℓ^∞`-distance `> r` (Ding–Dunlap partition `𝒢`
into `M` classes, line 2697; Ding–Zhang–Zeitouni `ℓ/(2κ+1)²`, `LBM_LGDarXiv.tex` line 1010), so
the path is all bad with probability `≤ ε ^ (k/(r+1)²) ≤ θ ^ k`; a union bound over the
`≤ K 8^(k-1)` paths and the geometric series in `k` give the claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ENNReal

namespace LQGMetric

/-- `x, y` are at `ℓ^∞`-distance `> r`. -/
def PercFar (r : ℕ) (x y : ℤ × ℤ) : Prop :=
  (r : ℤ) < x.1 - y.1 ∨ (r : ℤ) < y.1 - x.1 ∨ (r : ℤ) < x.2 - y.2 ∨ (r : ℤ) < y.2 - x.2

lemma percFar_of_emod {r : ℕ} {x y : ℤ × ℤ} (hne : x ≠ y)
    (h1 : x.1 % ((r : ℤ) + 1) = y.1 % ((r : ℤ) + 1))
    (h2 : x.2 % ((r : ℤ) + 1) = y.2 % ((r : ℤ) + 1)) : PercFar r x y := by
  obtain ⟨k1, hk1⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h1)
  obtain ⟨k2, hk2⟩ := Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h2)
  have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  unfold PercFar
  by_cases e1 : x.1 = y.1
  · have e2 : x.2 ≠ y.2 := fun e2 => hne (Prod.ext e1 e2)
    have hk : k2 ≠ 0 := by rintro rfl; apply e2; linarith
    rcases lt_or_gt_of_ne hk with hk | hk
    · have : k2 ≤ -1 := by omega
      right; right; right; nlinarith
    · have : 1 ≤ k2 := by omega
      right; right; left; nlinarith
  · have hk : k1 ≠ 0 := by rintro rfl; apply e1; linarith
    rcases lt_or_gt_of_ne hk with hk | hk
    · have : k1 ≤ -1 := by omega
      right; left; nlinarith
    · have : 1 ≤ k1 := by omega
      left; nlinarith

section Bound

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {K L : ℤ} (B : ℤ × ℤ → Set Ω)
  (r : ℕ) {ε θ : ℝ≥0∞}

/-- A fixed duplicate-free list of boxes of the rectangle is entirely bad with probability at
most `θ ^ length`. -/
lemma perc_list_bound (hθ1 : θ ≤ 1) (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ x, percInGrid K L x → μ (B x) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ x ∈ F, percInGrid K L x) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x))
    (l : List (ℤ × ℤ)) (hl : l.Nodup) (hgrid : ∀ y ∈ l, percInGrid K L y) :
    μ {ω | ∀ y ∈ l, ω ∈ B y} ≤ θ ^ l.length := by
  classical
  set s := l.toFinset with hsdef
  have hs : s.card = l.length := List.toFinset_card_of_nodup hl
  set c : ℤ × ℤ → ℤ × ℤ := fun x => (x.1 % ((r : ℤ) + 1), x.2 % ((r : ℤ) + 1)) with hcdef
  set t : Finset (ℤ × ℤ) := Finset.Ico 0 ((r : ℤ) + 1) ×ˢ Finset.Ico 0 ((r : ℤ) + 1) with htdef
  have hr0 : (0 : ℤ) < (r : ℤ) + 1 := by positivity
  have hct : ∀ x ∈ s, c x ∈ t := by
    intro x _
    simp only [hcdef, htdef, Finset.mem_product, Finset.mem_Ico]
    exact ⟨⟨Int.emod_nonneg _ hr0.ne', Int.emod_lt_of_pos _ hr0⟩,
      ⟨Int.emod_nonneg _ hr0.ne', Int.emod_lt_of_pos _ hr0⟩⟩
  have htcard : t.card = (r + 1) ^ 2 := by
    rw [htdef, Finset.card_product, Int.card_Ico]
    have : ((r : ℤ) + 1 - 0).toNat = r + 1 := by omega
    rw [this, sq]
  have htne : t.Nonempty := ⟨(0, 0), by simp [htdef]⟩
  obtain ⟨z, -, hz⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hct htne
    (b := (l.length : ℚ) / ((r + 1) ^ 2 : ℚ)) (by
      rw [htcard, nsmul_eq_mul, hs]
      push_cast
      rw [mul_div_cancel₀]
      positivity)
  set F := s.filter (fun x => c x = z) with hFdef
  have hm : l.length ≤ (r + 1) ^ 2 * F.card := by
    rw [div_le_iff₀ (by positivity)] at hz
    exact_mod_cast (by linarith : (l.length : ℚ) ≤ (r + 1) ^ 2 * (F.card : ℚ))
  have hFs : ∀ x ∈ F, x ∈ l := fun x hx =>
    List.mem_toFinset.mp (Finset.mem_filter.mp hx).1
  calc μ {ω | ∀ y ∈ l, ω ∈ B y} ≤ μ (⋂ x ∈ F, B x) := by
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_iInter]
        exact fun x hx => hω x (hFs x hx)
    _ ≤ ∏ x ∈ F, μ (B x) := by
        refine hind F (fun x hx => hgrid x (hFs x hx)) fun x hx y hy hxy => ?_
        have hx' := (Finset.mem_filter.mp hx).2
        have hy' := (Finset.mem_filter.mp hy).2
        rw [← hy'] at hx'
        simp only [hcdef, Prod.mk.injEq] at hx'
        exact percFar_of_emod hxy hx'.1 hx'.2
    _ ≤ ε ^ F.card := Finset.prod_le_pow_card _ _ _ fun x hx => hε x (hgrid x (hFs x hx))
    _ ≤ (θ ^ ((r + 1) ^ 2)) ^ F.card := pow_le_pow_left₀ bot_le hεθ _
    _ = θ ^ ((r + 1) ^ 2 * F.card) := (pow_mul _ _ _).symm
    _ ≤ θ ^ l.length := pow_le_pow_right_of_le_one' hθ1 hm

end Bound

/-- Geometric tail: for `q ≤ 1/2`, `∑_{i < k} q^(a+i) + 2 q^(a+k) ≤ 2 q^a`. -/
lemma perc_geom_aux {q : ℝ≥0∞} (hq : q ≤ 2⁻¹) (a : ℕ) :
    ∀ k : ℕ, ∑ i ∈ Finset.range k, q ^ (a + i) + 2 * q ^ (a + k) ≤ 2 * q ^ a := by
  have h2q : 2 * q ≤ 1 := by
    calc 2 * q ≤ 2 * 2⁻¹ := by gcongr
      _ = 1 := ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_assoc]
    refine le_trans ?_ ih
    gcongr
    calc q ^ (a + k) + 2 * q ^ (a + (k + 1)) = q ^ (a + k) + (2 * q) * q ^ (a + k) := by
          rw [← add_assoc, pow_succ]; ring
      _ ≤ q ^ (a + k) + 1 * q ^ (a + k) := by gcongr
      _ = 2 * q ^ (a + k) := by ring

/-- **Peierls bound** for finite-range dependent site percolation on the `K × L` rectangle of
boxes. `B x` is the event that the box `x` is bad. If each box is bad with probability `≤ ε`,
the badness events of any family of boxes pairwise at `ℓ^∞`-distance `> r` satisfy the product
bound, `ε ≤ θ ^ (r+1)²` and `8 θ ≤ 1/2`, then the probability that there is no left–right
crossing of the rectangle by `4`-connected good boxes is at most `K (8 θ) ^ L`. -/
theorem perc_peierls {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (K L : ℕ) (hK : 1 ≤ K)
    (hL : 1 ≤ L) (B : ℤ × ℤ → Set Ω) (r : ℕ) {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hεθ : ε ≤ θ ^ ((r + 1) ^ 2))
    (hε : ∀ x, percInGrid K L x → μ (B x) ≤ ε)
    (hind : ∀ F : Finset (ℤ × ℤ), (∀ x ∈ F, percInGrid K L x) →
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → PercFar r x y) → μ (⋂ x ∈ F, B x) ≤ ∏ x ∈ F, μ (B x)) :
    μ {ω | ¬ PercGoodLR K L (fun x => ω ∉ B x)} ≤ K * (8 * θ) ^ L := by
  classical
  have h21 : (2⁻¹ : ℝ≥0∞) ≤ 1 := ENNReal.inv_le_one.mpr (by norm_num)
  have hθ8 : θ ≤ 8 * θ := le_mul_of_one_le_left bot_le (by norm_num)
  have hθ1 : θ ≤ 1 := hθ8.trans (hθ.trans h21)
  set top : Finset (ℤ × ℤ) := (Finset.range K).image (fun i : ℕ => ((i : ℤ), (L : ℤ) - 1))
    with htop
  set N := Finset.Ico (L - 1) (K * L) with hN
  set A : ℤ × ℤ → ℕ → Finset (List (ℤ × ℤ)) := fun x n =>
    (percChainsFrom x n).filter (fun l => l.Nodup ∧ ∀ y ∈ l, percInGrid K L y) with hA
  have hsub : {ω | ¬ PercGoodLR K L (fun x => ω ∉ B x)} ⊆
      ⋃ x ∈ top, ⋃ n ∈ N, ⋃ l ∈ A x n, {ω | ∀ y ∈ l, ω ∈ B y} := by
    intro ω hω
    obtain ⟨l, hnd, hch, ⟨x, hx, hx2⟩, hbad, hlen⟩ :=
      percBadTB_exists_list (percBadTB_of_not_percGoodLR (by omega) (by omega) hω)
    obtain ⟨t, rfl⟩ : ∃ t, l = x :: t := by
      cases l with
      | nil => simp at hx
      | cons y t => simp only [List.head?_cons, Option.some.injEq] at hx; exact ⟨t, by rw [hx]⟩
    have hxg := (hbad x (by simp)).1
    have hlenle : (x :: t).length ≤ K * L := by
      have hs : (x :: t).toFinset ⊆ Finset.Ico (0 : ℤ) K ×ˢ Finset.Ico (0 : ℤ) L := by
        intro y hy
        have := (hbad y (List.mem_toFinset.mp hy)).1
        simp only [percInGrid] at this
        simp only [Finset.mem_product, Finset.mem_Ico]
        omega
      have := Finset.card_le_card hs
      rw [List.toFinset_card_of_nodup hnd, Finset.card_product, Int.card_Ico, Int.card_Ico]
        at this
      simpa using this
    simp only [Set.mem_iUnion]
    refine ⟨x, ?_, t.length, ?_, x :: t, ?_, ?_⟩
    · obtain ⟨x1, x2⟩ := x
      simp only [percInGrid] at hxg
      simp only [htop, Finset.mem_image, Finset.mem_range, Prod.mk.injEq]
      refine ⟨x1.toNat, by omega, by omega, by simp at hx2; omega⟩
    · simp only [hN, Finset.mem_Ico]
      simp only [List.length_cons] at hlen hlenle
      omega
    · simp only [hA, Finset.mem_filter]
      exact ⟨mem_percChainsFrom _ x t hch rfl, hnd, fun y hy => (hbad y hy).1⟩
    · intro y hy
      have := (hbad y hy).2
      simpa using this
  have hgeom : ∑ n ∈ N, θ * (8 * θ) ^ n ≤ (8 * θ) ^ L := by
    rw [← Finset.mul_sum, hN, Finset.sum_Ico_eq_sum_range]
    have h := perc_geom_aux hθ (L - 1) (K * L - (L - 1))
    have h' := le_trans le_self_add h
    calc θ * ∑ i ∈ Finset.range (K * L - (L - 1)), (8 * θ) ^ (L - 1 + i)
        ≤ θ * (2 * (8 * θ) ^ (L - 1)) := by gcongr
      _ ≤ 8 * θ * (8 * θ) ^ (L - 1) := by
          rw [← mul_assoc, mul_comm θ 2]
          gcongr
          norm_num
      _ = (8 * θ) ^ L := by
          rw [← pow_succ']
          congr 1
          omega
  calc μ {ω | ¬ PercGoodLR K L (fun x => ω ∉ B x)}
      ≤ μ (⋃ x ∈ top, ⋃ n ∈ N, ⋃ l ∈ A x n, {ω | ∀ y ∈ l, ω ∈ B y}) := measure_mono hsub
    _ ≤ ∑ x ∈ top, ∑ n ∈ N, ∑ l ∈ A x n, μ {ω | ∀ y ∈ l, ω ∈ B y} := by
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        refine (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        exact measure_biUnion_finset_le _ _
    _ ≤ ∑ x ∈ top, ∑ n ∈ N, ∑ l ∈ A x n, θ ^ (n + 1) := by
        gcongr with x _ n _ l hl
        obtain ⟨hl1, hl2, hl3⟩ := Finset.mem_filter.mp hl
        rw [← length_of_mem_percChainsFrom n x l hl1]
        exact perc_list_bound μ B r hθ1 hεθ hε hind l hl2 hl3
    _ ≤ ∑ x ∈ top, ∑ n ∈ N, (8 : ℝ≥0∞) ^ n * θ ^ (n + 1) := by
        gcongr with x _ n _
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        exact_mod_cast (Finset.card_filter_le _ _).trans (card_percChainsFrom_le x n)
    _ = top.card * ∑ n ∈ N, θ * (8 * θ) ^ n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [mul_pow, pow_succ]
        ring
    _ ≤ K * (8 * θ) ^ L := by
        gcongr
        exact_mod_cast Finset.card_image_le.trans (by simp)

end LQGMetric
