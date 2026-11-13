/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CadlagJumpPartitionFatou at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Topology.Order.Cadlag
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Pathwise Fatou lemma for the squared jumps of a càdlàg path

For a càdlàg path `Z : ℝ≥0 → ℝ` and the dyadic partitions `t^n_i = T i / 2^n` of `[0, T]`,
the sum of the squared jumps `(Z s − Z s⁻)²` over any finite set of times `s ∈ (0, T]` is
bounded by `liminf_n ∑_i (Z t^n_{i+1} − Z t^n_i)²`.

Each fixed time `s` lies in exactly one half-open cell `(t^n_i, t^n_{i+1}]`; its right endpoint
converges to `s` from the right and its left endpoint from the left, so by càdlàg-ness the
cell increment converges to the jump at `s`.  Finitely many distinct times eventually occupy
distinct cells, and all the remaining cell increments are nonnegative.  Everything is
deterministic; the `ℝ≥0∞`-valued formulation avoids any integrability side condition.

This is the analytic input of the energy budget proving the nonvertex-time continuity of the
full-energy potential paths (manuscript `p:prop:purejump`, nonvertex half); nothing
probabilistic appears here.
-/

set_option autoImplicit false

open Filter Topology Set
open scoped NNReal ENNReal

namespace ReflectedGMS.CadlagJumpPartitionFatou

/-- The dyadic partition point `T * i / 2 ^ n` of `[0, T]`. -/
noncomputable def dyadicPoint (T : ℝ≥0) (n i : ℕ) : ℝ≥0 := T * (i : ℝ≥0) / (2 : ℝ≥0) ^ n

/-- The sum of squared increments of `Z` over the dyadic partition of `[0, T]` with mesh
`T / 2 ^ n`. -/
noncomputable def partitionSquareSum (Z : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ n), (Z (dyadicPoint T n (i + 1)) - Z (dyadicPoint T n i)) ^ 2

/-- The squared jump of `Z` at `s`, as an extended nonnegative real. -/
noncomputable def jumpSq (Z : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal ((Z s - Function.leftLim Z s) ^ 2)

/-- The index of the half-open cell `(t^n_i, t^n_{i+1}]` containing `s`. -/
noncomputable def cellIndex (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) : ℕ :=
  ⌈s * (2 : ℝ≥0) ^ n / T⌉₊ - 1

theorem partitionSquareSum_nonneg (Z : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    0 ≤ partitionSquareSum Z T n :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem dyadicPoint_succ (T : ℝ≥0) (n i : ℕ) :
    dyadicPoint T n (i + 1) = dyadicPoint T n i + T / (2 : ℝ≥0) ^ n := by
  unfold dyadicPoint
  rw [Nat.cast_succ, mul_add, mul_one, add_div]

theorem two_pow_pos_nnreal (n : ℕ) : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n

/-- The mesh of the dyadic partition tends to zero. -/
theorem tendsto_mesh (T : ℝ≥0) :
    Tendsto (fun n : ℕ => T / (2 : ℝ≥0) ^ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((1 : ℝ≥0) / 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h' := h.const_mul T
  rw [mul_zero] at h'
  refine h'.congr fun n => ?_
  rw [div_pow, one_pow, mul_one_div]

section Cell

variable {T : ℝ≥0} (hT : 0 < T) {n : ℕ} {s : ℝ≥0} (hs : s ∈ Ioc 0 T)
include hT hs

theorem cellIndex_succ : cellIndex T n s + 1 = ⌈s * (2 : ℝ≥0) ^ n / T⌉₊ := by
  unfold cellIndex
  have hpos : 0 < ⌈s * (2 : ℝ≥0) ^ n / T⌉₊ := by
    rw [Nat.lt_ceil, Nat.cast_zero]
    exact div_pos (mul_pos hs.1 (two_pow_pos_nnreal n)) hT
  omega

theorem cellIndex_lt : cellIndex T n s < 2 ^ n := by
  have h1 : cellIndex T n s + 1 ≤ 2 ^ n := by
    rw [cellIndex_succ hT hs, Nat.ceil_le, Nat.cast_pow, Nat.cast_ofNat,
      div_le_iff₀ hT]
    calc s * (2 : ℝ≥0) ^ n ≤ T * (2 : ℝ≥0) ^ n :=
          mul_le_mul_of_nonneg_right hs.2 (two_pow_pos_nnreal n).le
      _ = _ := mul_comm _ _
  omega

theorem le_dyadicPoint_cellIndex_succ : s ≤ dyadicPoint T n (cellIndex T n s + 1) := by
  rw [cellIndex_succ hT hs, dyadicPoint, le_div_iff₀ (two_pow_pos_nnreal n)]
  have h := Nat.le_ceil (s * (2 : ℝ≥0) ^ n / T)
  rw [div_le_iff₀ hT] at h
  calc s * (2 : ℝ≥0) ^ n ≤ ↑⌈s * (2 : ℝ≥0) ^ n / T⌉₊ * T := h
    _ = _ := mul_comm _ _

theorem dyadicPoint_cellIndex_succ_lt :
    dyadicPoint T n (cellIndex T n s + 1) < s + T / (2 : ℝ≥0) ^ n := by
  rw [cellIndex_succ hT hs, dyadicPoint, div_lt_iff₀ (two_pow_pos_nnreal n), add_mul,
    div_mul_cancel₀ _ (two_pow_pos_nnreal n).ne']
  have h : (⌈s * (2 : ℝ≥0) ^ n / T⌉₊ : ℝ≥0) < s * (2 : ℝ≥0) ^ n / T + 1 :=
    Nat.ceil_lt_add_one zero_le
  calc T * ↑⌈s * (2 : ℝ≥0) ^ n / T⌉₊ < T * (s * (2 : ℝ≥0) ^ n / T + 1) :=
        mul_lt_mul_of_pos_left h hT
    _ = s * (2 : ℝ≥0) ^ n + T := by
        rw [mul_add, mul_one, mul_comm T, div_mul_cancel₀ _ hT.ne']

theorem dyadicPoint_cellIndex_lt : dyadicPoint T n (cellIndex T n s) < s := by
  have h := dyadicPoint_cellIndex_succ_lt hT hs (n := n)
  rw [dyadicPoint_succ] at h
  exact lt_of_add_lt_add_right h

theorem le_dyadicPoint_cellIndex_add : s ≤ dyadicPoint T n (cellIndex T n s) + T / (2 : ℝ≥0) ^ n := by
  rw [← dyadicPoint_succ]
  exact le_dyadicPoint_cellIndex_succ hT hs

end Cell

/-- The right endpoint of the cell of `s` converges to `s` from the right. -/
theorem tendsto_dyadicPoint_cellIndex_succ {T : ℝ≥0} (hT : 0 < T) {s : ℝ≥0}
    (hs : s ∈ Ioc 0 T) :
    Tendsto (fun n => dyadicPoint T n (cellIndex T n s + 1)) atTop (𝓝[≥] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have hlim : Tendsto (fun n : ℕ => s + T / (2 : ℝ≥0) ^ n) atTop (𝓝 s) := by
      simpa using (tendsto_mesh T).const_add s
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun n => le_dyadicPoint_cellIndex_succ hT hs)
      (fun n => (dyadicPoint_cellIndex_succ_lt hT hs).le)
  · exact le_dyadicPoint_cellIndex_succ hT hs

/-- The left endpoint of the cell of `s` converges to `s` from the left. -/
theorem tendsto_dyadicPoint_cellIndex {T : ℝ≥0} (hT : 0 < T) {s : ℝ≥0}
    (hs : s ∈ Ioc 0 T) :
    Tendsto (fun n => dyadicPoint T n (cellIndex T n s)) atTop (𝓝[<] s) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have hlim : Tendsto (fun n : ℕ => s - T / (2 : ℝ≥0) ^ n) atTop (𝓝 s) := by
      simpa using (tendsto_const_nhds (x := s)).sub (tendsto_mesh T)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
      (fun n => tsub_le_iff_right.2 (le_dyadicPoint_cellIndex_add hT hs))
      (fun n => (dyadicPoint_cellIndex_lt hT hs).le)
  · exact dyadicPoint_cellIndex_lt hT hs

/-- The increment of a càdlàg path over the cell of `s` converges to the jump at `s`. -/
theorem tendsto_cell_increment {Z : ℝ≥0 → ℝ} (hZ : IsCadlag Z) {T : ℝ≥0} (hT : 0 < T)
    {s : ℝ≥0} (hs : s ∈ Ioc 0 T) :
    Tendsto (fun n => Z (dyadicPoint T n (cellIndex T n s + 1)) -
        Z (dyadicPoint T n (cellIndex T n s))) atTop
      (𝓝 (Z s - Function.leftLim Z s)) := by
  have hright : Tendsto (fun n => Z (dyadicPoint T n (cellIndex T n s + 1))) atTop (𝓝 (Z s)) := by
    have hc : ContinuousWithinAt Z (Ici s) s :=
      (continuousWithinAt_Ioi_iff_Ici).1 (hZ.isRightContinuous s)
    exact hc.tendsto.comp (tendsto_dyadicPoint_cellIndex_succ hT hs)
  have hleft : Tendsto (fun n => Z (dyadicPoint T n (cellIndex T n s))) atTop
      (𝓝 (Function.leftLim Z s)) :=
    (hZ.tendsto_nhdsLT_leftLim s).comp (tendsto_dyadicPoint_cellIndex hT hs)
  exact hright.sub hleft

/-- Two distinct times eventually lie in distinct cells. -/
theorem eventually_cellIndex_ne {T : ℝ≥0} (hT : 0 < T) {s s' : ℝ≥0} (hs : s ∈ Ioc 0 T)
    (hs' : s' ∈ Ioc 0 T) (hne : s ≠ s') :
    ∀ᶠ n in atTop, cellIndex T n s ≠ cellIndex T n s' := by
  -- reduce to the case `s < s'`
  have key : ∀ {a b : ℝ≥0}, a ∈ Ioc 0 T → b ∈ Ioc 0 T → a < b →
      ∀ᶠ n in atTop, cellIndex T n a ≠ cellIndex T n b := by
    intro a b ha hb hab
    have hpos : 0 < b - a := tsub_pos_of_lt hab
    filter_upwards [(tendsto_mesh T).eventually (gt_mem_nhds hpos)] with n hn heq
    -- `b ≤ t_{i+1} < a + mesh`, contradiction with `mesh < b − a`
    have h1 := le_dyadicPoint_cellIndex_succ hT hb (n := n)
    have h2 := dyadicPoint_cellIndex_succ_lt hT ha (n := n)
    rw [heq] at h2
    have : b < a + T / (2 : ℝ≥0) ^ n := lt_of_le_of_lt h1 h2
    have h3 : b - a < T / (2 : ℝ≥0) ^ n := (tsub_lt_iff_left hab.le).2 this
    exact absurd h3 (not_lt.2 hn.le)
  rcases lt_or_gt_of_ne hne with h | h
  · exact key hs hs' h
  · exact (key hs' hs h).mono fun n hn => hn.symm

/-- On a finite set of distinct times the cell index is eventually injective. -/
theorem eventually_injOn_cellIndex {T : ℝ≥0} (hT : 0 < T) {ι : Type*} (F : Finset ι)
    (s : ι → ℝ≥0) (hinj : Set.InjOn s F) (hmem : ∀ i ∈ F, s i ∈ Ioc 0 T) :
    ∀ᶠ n in atTop, Set.InjOn (fun i => cellIndex T n (s i)) F := by
  classical
  have h : ∀ p ∈ F ×ˢ F, ∀ᶠ n in atTop, p.1 ≠ p.2 → cellIndex T n (s p.1) ≠ cellIndex T n (s p.2) := by
    intro p hp
    rw [Finset.mem_product] at hp
    by_cases hpe : p.1 = p.2
    · exact Eventually.of_forall fun n hne => absurd hpe hne
    · have hne : s p.1 ≠ s p.2 := fun h => hpe (hinj hp.1 hp.2 h)
      exact (eventually_cellIndex_ne hT (hmem _ hp.1) (hmem _ hp.2) hne).mono fun n hn _ => hn
  filter_upwards [(Finset.eventually_all (F ×ˢ F)).2 h] with n hn
  intro i hi j hj hij
  by_contra hne
  exact hn (i, j) (Finset.mem_product.2 ⟨hi, hj⟩) hne hij

/-- **Pathwise Fatou lemma, finite form.**  The sum of squared jumps of a càdlàg path over
finitely many distinct times in `(0, T]` is at most the `liminf` of the dyadic partition
square sums. -/
theorem sum_jumpSq_le_liminf {Z : ℝ≥0 → ℝ} (hZ : IsCadlag Z) (T : ℝ≥0) {ι : Type*}
    (F : Finset ι) (s : ι → ℝ≥0) (hinj : Set.InjOn s F) (hmem : ∀ i ∈ F, s i ∈ Ioc 0 T) :
    ∑ i ∈ F, jumpSq Z (s i) ≤
      liminf (fun n => ENNReal.ofReal (partitionSquareSum Z T n)) atTop := by
  classical
  rcases F.eq_empty_or_nonempty with hF | ⟨i₀, hi₀⟩
  · simp [hF]
  have hT : 0 < T := lt_of_lt_of_le (hmem i₀ hi₀).1 (hmem i₀ hi₀).2
  -- the cell increments attached to the times of `F`
  let a : ℕ → ℝ≥0∞ := fun n => ∑ i ∈ F,
    ENNReal.ofReal ((Z (dyadicPoint T n (cellIndex T n (s i) + 1)) -
      Z (dyadicPoint T n (cellIndex T n (s i)))) ^ 2)
  have hlim : Tendsto a atTop (𝓝 (∑ i ∈ F, jumpSq Z (s i))) := by
    refine tendsto_finsetSum F fun i hi => ?_
    exact ENNReal.tendsto_ofReal ((tendsto_cell_increment hZ hT (hmem i hi)).pow 2)
  have hle : ∀ᶠ n in atTop, a n ≤ ENNReal.ofReal (partitionSquareSum Z T n) := by
    filter_upwards [eventually_injOn_cellIndex hT F s hinj hmem] with n hn
    rw [partitionSquareSum, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    have himage : (∑ i ∈ F, ENNReal.ofReal ((Z (dyadicPoint T n (cellIndex T n (s i) + 1)) -
        Z (dyadicPoint T n (cellIndex T n (s i)))) ^ 2)) =
        ∑ j ∈ F.image (fun i => cellIndex T n (s i)),
          ENNReal.ofReal ((Z (dyadicPoint T n (j + 1)) - Z (dyadicPoint T n j)) ^ 2) :=
      (Finset.sum_image (f := fun j => ENNReal.ofReal
        ((Z (dyadicPoint T n (j + 1)) - Z (dyadicPoint T n j)) ^ 2)) hn).symm
    show (∑ i ∈ F, ENNReal.ofReal ((Z (dyadicPoint T n (cellIndex T n (s i) + 1)) -
        Z (dyadicPoint T n (cellIndex T n (s i)))) ^ 2)) ≤ _
    rw [himage]
    refine Finset.sum_le_sum_of_subset ?_
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    exact Finset.mem_range.2 (cellIndex_lt hT (hmem i hi))
  rw [← hlim.liminf_eq]
  exact liminf_le_liminf hle

/-- **Pathwise Fatou lemma, countable form.**  A family `a` of extended nonnegative reals
indexed by a countable type, each nonzero member of which is bounded by the squared jump at
a time `s i ∈ (0, T]`, the nonzero members having distinct times, sums to at most the
`liminf` of the dyadic partition square sums. -/
theorem tsum_le_liminf_of_jumpSq {Z : ℝ≥0 → ℝ} (hZ : IsCadlag Z) (T : ℝ≥0) {ι : Type*}
    [Countable ι] (s : ι → ℝ≥0) (a : ι → ℝ≥0∞)
    (hle : ∀ i, a i ≠ 0 → a i ≤ jumpSq Z (s i))
    (hinj : Set.InjOn s {i | a i ≠ 0}) (hmem : ∀ i, a i ≠ 0 → s i ∈ Ioc 0 T) :
    ∑' i, a i ≤ liminf (fun n => ENNReal.ofReal (partitionSquareSum Z T n)) atTop := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  have hsplit : ∑ i ∈ F, a i = ∑ i ∈ F.filter (fun i => a i ≠ 0), a i :=
    (Finset.sum_filter_ne_zero F).symm
  rw [hsplit]
  calc ∑ i ∈ F.filter (fun i => a i ≠ 0), a i ≤
        ∑ i ∈ F.filter (fun i => a i ≠ 0), jumpSq Z (s i) :=
        Finset.sum_le_sum fun i hi => hle i (Finset.mem_filter.1 hi).2
    _ ≤ _ := by
        refine sum_jumpSq_le_liminf hZ T _ s ?_ ?_
        · intro i hi j hj hij
          exact hinj (Finset.mem_filter.1 hi).2 (Finset.mem_filter.1 hj).2 hij
        · intro i hi
          exact hmem i (Finset.mem_filter.1 hi).2

end ReflectedGMS.CadlagJumpPartitionFatou
