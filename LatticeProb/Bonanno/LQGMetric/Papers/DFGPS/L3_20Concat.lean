/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_20Concat at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
`internalEDist_le_tsum_of_chain`: if `xₙ → u ∈ Y` and `d(xₙ, xₙ₊₁; Y) ≤ cₙ`, then
`d(x₀, u; Y) ≤ Σ cₙ`. Proof: concatenate paths `γₙ` from `xₙ` to `xₙ₊₁` inside `Y` on the
intervals `[1 − 2^{-n}, 1 − 2^{-n-1}]` (finite concatenations `catN n`, constant `xₙ` after
`1 − 2^{-n}`), pass to the uniform limit (the tails `Σ_{i ≥ n} len γᵢ → 0`), and use lower
semicontinuity of length (`curveLength_le_liminf_of_tendstoUniformlyOn`).

Used for the closed squares of DFGPS Lemma 3.20 (second display, T:2322–2325): a point on the
boundary of a closed square is joined to the centre through nested open dyadic sub-squares.
Own elementary argument (standard infinite concatenation of paths); proposed DEVIATIONS entry
DFA7-2.
-/

noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
namespace L320

open MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-- breakpoints `1 − 2^{-n}` -/
def brk (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

lemma brk_succ (n : ℕ) : brk (n + 1) = brk n + (1 / 2 : ℝ) ^ (n + 1) := by
  unfold brk; rw [pow_succ]; ring

lemma brk_mono {n m : ℕ} (h : n ≤ m) : brk n ≤ brk m := by
  unfold brk
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) h
  linarith

lemma brk_lt_one (n : ℕ) : brk n < 1 := by
  unfold brk; have : (0 : ℝ) < (1 / 2) ^ n := by positivity
  linarith

lemma brk_nonneg (n : ℕ) : 0 ≤ brk n := by
  unfold brk; have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith

lemma two_pow_mul_half_pow (n : ℕ) : (2 : ℝ) ^ (n + 1) * (1 / 2) ^ (n + 1) = 1 := by
  rw [← mul_pow]; norm_num

/-- finite concatenations -/
def catN (x : ℕ → X) (γ : ∀ n, Path (x n) (x (n + 1))) : ℕ → ℝ → X
  | 0 => fun _ => x 0
  | n + 1 => fun t => if t ≤ brk n then catN x γ n t
      else (γ n).extend ((2 : ℝ) ^ (n + 1) * (t - brk n))

variable (x : ℕ → X) (γ : ∀ n, Path (x n) (x (n + 1)))

lemma catN_of_ge : ∀ (n : ℕ) (t : ℝ), brk n ≤ t → catN x γ n t = x n
  | 0, _, _ => rfl
  | n + 1, t, ht => by
    have hlt : brk n < t := by rw [brk_succ] at ht; have := pow_pos (by norm_num : (0:ℝ) < 1/2) (n+1); linarith
    simp only [catN, if_neg (not_le.2 hlt)]
    refine Path.extend_of_one_le _ ?_
    rw [brk_succ] at ht
    have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    calc (1 : ℝ) = 2 ^ (n + 1) * (1 / 2) ^ (n + 1) := (two_pow_mul_half_pow n).symm
      _ ≤ 2 ^ (n + 1) * (t - brk n) := by gcongr; linarith

lemma continuous_catN : ∀ n, Continuous (catN x γ n)
  | 0 => continuous_const
  | n + 1 => by
    refine Continuous.if_le (continuous_catN n) ((γ n).continuous_extend.comp (by fun_prop))
      continuous_id continuous_const ?_
    intro t ht
    rw [show t = brk n from ht, catN_of_ge x γ n (brk n) le_rfl, sub_self, mul_zero,
      Path.extend_zero]

lemma catN_mem {Y : Set X} (h0 : x 0 ∈ Y) (hγ : ∀ n t, γ n t ∈ Y) : ∀ n t, catN x γ n t ∈ Y
  | 0, _ => h0
  | n + 1, t => by
    show (if t ≤ brk n then catN x γ n t
      else (γ n).extend ((2 : ℝ) ^ (n + 1) * (t - brk n))) ∈ Y
    split_ifs
    · exact catN_mem h0 hγ n t
    · rw [Path.extend]; exact hγ n _

lemma catN_stable {n : ℕ} {t : ℝ} (ht : t ≤ brk n) : ∀ m, n ≤ m → catN x γ m t = catN x γ n t := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    simp only [catN, if_pos (ht.trans (brk_mono hnm))]; exact ih

lemma edist_catN {n : ℕ} : ∀ m, n ≤ m → ∀ t, brk n ≤ t →
    edist (x n) (catN x γ m t) ≤ ∑ i ∈ Finset.Ico n m, pathLength (γ i) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro t ht; rw [catN_of_ge x γ n t ht, edist_self]; exact bot_le
  | succ m hnm ih =>
    intro t ht
    rw [Finset.sum_Ico_succ_top hnm]
    simp only [catN]
    split_ifs with h
    · exact (ih t ht).trans le_self_add
    · have h1 := ih (brk m) (brk_mono hnm)
      rw [catN_of_ge x γ m (brk m) le_rfl] at h1
      refine (edist_triangle _ (x m) _).trans (add_le_add h1 ?_)
      rw [Path.extend]
      exact edist_le_pathLength_apply (γ m) _

lemma curveLength_const_on {P : ℝ → X} {a b : ℝ} {c : X} (h : ∀ t ∈ Icc a b, P t = c) :
    curveLength P a b = 0 := by
  rw [curveLength_congr (Q := fun _ => c) h]
  exact eVariationOn.constant_on (by rintro _ ⟨s, -, rfl⟩ _ ⟨s', -, rfl⟩; rfl)

lemma curveLength_catN : ∀ n, curveLength (catN x γ n) 0 1 ≤ ∑ i ∈ Finset.range n, pathLength (γ i)
  | 0 => by
    rw [curveLength_const_on (P := catN x γ 0) (c := x 0) (fun t _ => rfl)]; exact bot_le
  | n + 1 => by
    rw [Finset.sum_range_succ,
      ← curveLength_add _ (brk_nonneg n) (brk_lt_one n).le]
    refine add_le_add ?_ ?_
    · rw [curveLength_congr (Q := catN x γ n) (fun t ht => by
        simp only [catN, if_pos ht.2])]
      refine le_trans ?_ (curveLength_catN n)
      exact curveLength_mono _ le_rfl (brk_lt_one n).le
    · set φ : ℝ → ℝ := fun t => (2 : ℝ) ^ (n + 1) * (t - brk n)
      rw [curveLength_congr (Q := (γ n).extend ∘ φ) (fun t ht => by
        simp only [catN, Function.comp_apply, φ]
        split_ifs with h
        · have : t = brk n := le_antisymm h ht.1
          rw [this, catN_of_ge x γ n (brk n) le_rfl, sub_self, mul_zero, Path.extend_zero]
        · rfl)]
      rw [curveLength_comp_of_continuousOn_monotoneOn _ (brk_lt_one n).le (by fun_prop)
        (fun s _ t _ hst => by simp only [φ]; gcongr)]
      have h0 : φ (brk n) = 0 := by simp [φ]
      have h1 : 1 ≤ φ 1 := by
        simp only [φ, brk, sub_sub_cancel]
        rw [pow_succ, mul_comm ((2 : ℝ) ^ n) 2, mul_assoc, ← mul_pow,
          show (2 : ℝ) * (1/2) = 1 by norm_num, one_pow]
        norm_num
      rw [h0, ← curveLength_add _ zero_le_one h1,
        curveLength_const_on (c := x (n + 1)) (fun t ht => Path.extend_of_one_le _ ht.1),
        add_zero]
      rfl

/-- the infinite concatenation, ending at `u` -/
def catL (u : X) (t : ℝ) : X := by
  classical
  exact if h : ∃ n, t ≤ brk n then catN x γ (Nat.find h) t else u

lemma catL_eq (u : X) {n : ℕ} {t : ℝ} (ht : t ≤ brk n) : catL x γ u t = catN x γ n t := by
  classical
  have h : ∃ n, t ≤ brk n := ⟨n, ht⟩
  simp only [catL, dif_pos h]
  exact (catN_stable x γ (Nat.find_spec h) n (Nat.find_min' h ht)).symm

lemma catL_one (u : X) : catL x γ u 1 = u := by
  classical
  have h : ¬ ∃ n, (1 : ℝ) ≤ brk n := fun ⟨n, hn⟩ => (brk_lt_one n).not_ge hn
  simp only [catL, dif_neg h]

variable {x γ}

lemma edist_catN_catL (u : X) (hx : Tendsto x atTop (𝓝 u)) (n : ℕ) (t : ℝ) :
    edist (catN x γ n t) (catL x γ u t) ≤ ∑' i, pathLength (γ (i + n)) := by
  classical
  by_cases ht : t ≤ brk n
  · rw [catL_eq x γ u ht, edist_self]; exact bot_le
  push Not at ht
  rw [catN_of_ge x γ n t ht.le]
  have htail : ∀ m, n ≤ m →
      ∑ i ∈ Finset.Ico n m, pathLength (γ i) ≤ ∑' i, pathLength (γ (i + n)) := by
    intro m hm
    rw [Finset.sum_Ico_eq_sum_range]
    calc _ = ∑ k ∈ Finset.range (m - n), pathLength (γ (k + n)) := by
          refine Finset.sum_congr rfl fun k _ => ?_; rw [add_comm]
      _ ≤ _ := ENNReal.sum_le_tsum _
  by_cases hex : ∃ m, t ≤ brk m
  · obtain ⟨m, hm⟩ := hex
    have hm' : t ≤ brk (max m n) := hm.trans (brk_mono (le_max_left _ _))
    rw [catL_eq x γ u hm']
    exact (edist_catN x γ (max m n) (le_max_right _ _) t ht.le).trans
      (htail _ (le_max_right _ _))
  · have hL : catL x γ u t = u := by simp only [catL, dif_neg hex]
    rw [hL]
    have hlim : Tendsto (fun m => edist (x n) (x m)) atTop (𝓝 (edist (x n) u)) :=
      tendsto_const_nhds.edist hx
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hm => ?_⟩)
    have := edist_catN x γ m hm (brk m) (brk_mono hm)
    rw [catN_of_ge x γ m (brk m) le_rfl] at this
    exact this.trans (htail m hm)

theorem internalEDist_le_tsum_of_paths {Y : Set X} {u : X} (hu : u ∈ Y)
    (hx : Tendsto x atTop (𝓝 u)) (hγY : ∀ n t, γ n t ∈ Y)
    (hfin : ∑' n, pathLength (γ n) ≠ ∞) :
    internalEDist Y (x 0) u ≤ ∑' n, pathLength (γ n) := by
  classical
  have hunif : TendstoUniformlyOn (catN x γ) (catL x γ u) atTop (Icc 0 1) := by
    rw [EMetric.tendstoUniformlyOn_iff]
    intro ε hε
    have := ENNReal.tendsto_sum_nat_add (fun i => pathLength (γ i)) hfin
    filter_upwards [this.eventually (gt_mem_nhds hε)] with n hn t _
    rw [edist_comm]; exact (edist_catN_catL u hx n t).trans_lt hn
  have hcont : ContinuousOn (catL x γ u) (Icc 0 1) :=
    hunif.continuousOn (Frequently.of_forall fun n => (continuous_catN x γ n).continuousOn)
  have hlen : curveLength (catL x γ u) 0 1 ≤ ∑' n, pathLength (γ n) := by
    refine (curveLength_le_liminf_of_tendstoUniformlyOn hunif).trans ?_
    refine liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
    exact (curveLength_catN x γ n).trans (ENNReal.sum_le_tsum _)
  obtain ⟨p, hp, hpr⟩ := exists_path_of_curve zero_le_one hcont
  have h0 : catL x γ u 0 = x 0 := catL_eq x γ u (n := 0) (by simp [brk])
  have h1 : catL x γ u 1 = u := catL_one x γ u
  have hx0 : x 0 ∈ Y := by have := hγY 0 0; rwa [Path.source] at this
  have hY : ∀ t, p t ∈ Y := by
    intro t
    obtain ⟨s, -, hs'⟩ := hpr ⟨t, rfl⟩
    rw [← hs']
    by_cases hs1 : ∃ m, s ≤ brk m
    · obtain ⟨m, hm⟩ := hs1
      rw [catL_eq x γ u hm]
      exact catN_mem x γ hx0 hγY m s
    · simp only [catL, dif_neg hs1]; exact hu
  calc internalEDist Y (x 0) u = internalEDist Y (catL x γ u 0) (catL x γ u 1) := by rw [h0, h1]
    _ ≤ pathLength p := internalEDist_le_pathLength p hY
    _ = curveLength (catL x γ u) 0 1 := hp
    _ ≤ _ := hlen

/-- **Chain bound**: if `xₙ → u ∈ Y` and `d(xₙ, xₙ₊₁; Y) ≤ cₙ` with `Σ cₙ < ∞`, then
`d(x₀, u; Y) ≤ Σ cₙ`. -/
theorem internalEDist_le_tsum_of_chain {Y : Set X} {x : ℕ → X} {u : X} (hu : u ∈ Y)
    (hx : Tendsto x atTop (𝓝 u)) {c : ℕ → ℝ≥0∞} (hc : ∑' n, c n ≠ ∞)
    (hstep : ∀ n, internalEDist Y (x n) (x (n + 1)) ≤ c n) :
    internalEDist Y (x 0) u ≤ ∑' n, c n := by
  refine ENNReal.le_of_forall_pos_le_add fun η hη _ => ?_
  obtain ⟨δ, hδ0, hδsum⟩ :=
    ENNReal.exists_pos_sum_of_countable (ENNReal.coe_ne_zero.2 hη.ne') ℕ
  have hch : ∀ n, ∃ p : Path (x n) (x (n + 1)), (∀ t, p t ∈ Y) ∧
      pathLength p ≤ c n + δ n := by
    intro n
    have hlt : internalEDist Y (x n) (x (n + 1)) < c n + δ n :=
      (hstep n).trans_lt (ENNReal.lt_add_right (ENNReal.ne_top_of_tsum_ne_top hc n)
        (ENNReal.coe_ne_zero.2 (hδ0 n).ne'))
    obtain ⟨p, hp⟩ := iInf_lt_iff.1 hlt
    exact ⟨p.1, p.2, hp.le⟩
  choose γ hγY hγL using hch
  have hsum : ∑' n, pathLength (γ n) ≤ ∑' n, c n + η := by
    calc ∑' n, pathLength (γ n) ≤ ∑' n, (c n + δ n) := ENNReal.tsum_le_tsum hγL
      _ = ∑' n, c n + ∑' n, (δ n : ℝ≥0∞) := ENNReal.tsum_add
      _ ≤ _ := by gcongr
  exact (internalEDist_le_tsum_of_paths hu hx hγY
    (ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hc, ENNReal.coe_ne_top⟩) hsum)).trans hsum

end L320
end LQGMetric.DFGPS
