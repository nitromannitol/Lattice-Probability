/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412eConcat at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Infinite concatenation of curves with summable lengths (for `hfin`, DEC-86 (3))

DEC-86 item (3) builds a finite-length path from `𝕫` to a point `x ∈ ∂B_r(z)` by concatenating
countably many curves `γ_k` (on `[1 − 2^{-k}, 1 − 2^{-k-1}]`) whose lengths are summable and
whose initial points converge to `x`. This file proves the generic statement in a metric space:
the concatenation `p412eCat γ q` is continuous on `[0, 1]`, ends at `q`, and its length is at
most `∑ len γ_k` (lower semicontinuity of length, `curveLength_le_liminf`). Own elementary
argument (standard; DEC-86 (3)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open LQGMetric.MetricGeometry
open scoped ENNReal

namespace LQGMetric.GM

/-- the dyadic times `u_n = 1 − 2^{-n}` -/
def p412eU (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ n

theorem p412eU_mono : Monotone p412eU := fun m n h => by
  unfold p412eU
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num) h
  linarith

theorem p412eU_zero : p412eU 0 = 0 := by simp [p412eU]

theorem p412eU_lt_one (n : ℕ) : p412eU n < 1 := by
  unfold p412eU; have : (0 : ℝ) < (1 / 2) ^ n := by positivity
  linarith

theorem p412eU_nonneg (n : ℕ) : 0 ≤ p412eU n := p412eU_zero ▸ p412eU_mono (Nat.zero_le n)

theorem p412e_exists_idx {t : ℝ} (ht : t < 1) : ∃ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) < 1 - t := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (sub_pos.2 ht) (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n)) hn⟩

open Classical in
/-- the index `k` with `t ∈ [u_k, u_{k+1})` -/
def p412eIdx (t : ℝ) : ℕ := if ht : t < 1 then Nat.find (p412e_exists_idx ht) else 0

theorem p412eIdx_eq {t : ℝ} {k : ℕ} (h1 : p412eU k ≤ t) (h2 : t < p412eU (k + 1)) :
    p412eIdx t = k := by
  classical
  have ht : t < 1 := h2.trans (p412eU_lt_one _)
  unfold p412eIdx
  rw [dif_pos ht, Nat.find_eq_iff]
  unfold p412eU at h1 h2
  refine ⟨by linarith, fun n hn => ?_⟩
  have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    (Nat.succ_le_of_lt hn)
  rw [Nat.succ_eq_add_one] at this
  push_neg; linarith

theorem p412eIdx_spec {t : ℝ} (h0 : 0 ≤ t) (ht : t < 1) :
    p412eU (p412eIdx t) ≤ t ∧ t < p412eU (p412eIdx t + 1) := by
  classical
  have hk : p412eIdx t = Nat.find (p412e_exists_idx ht) := by unfold p412eIdx; rw [dif_pos ht]
  have hs := Nat.find_spec (p412e_exists_idx ht)
  rw [← hk] at hs
  refine ⟨?_, by unfold p412eU; linarith⟩
  rcases hk' : p412eIdx t with _ | j
  · simpa [p412eU_zero] using h0
  · have hmin := Nat.find_min (p412e_exists_idx ht) (m := j) (by omega)
    push_neg at hmin
    unfold p412eU; linarith

/-- the affine reparametrization `[u_k, u_{k+1}] → [0, 1]` -/
def p412ePhi (k : ℕ) (t : ℝ) : ℝ := 2 - 2 ^ (k + 1) * (1 - t)

theorem p412ePhi_lo (k : ℕ) : p412ePhi k (p412eU k) = 0 := by
  unfold p412ePhi p412eU
  have : (2 : ℝ) ^ (k + 1) * (1 / 2) ^ k = 2 := by
    rw [pow_succ, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
  rw [sub_sub_cancel, this]; ring

theorem p412ePhi_hi (k : ℕ) : p412ePhi k (p412eU (k + 1)) = 1 := by
  unfold p412ePhi p412eU
  have : (2 : ℝ) ^ (k + 1) * (1 / 2) ^ (k + 1) = 1 := by rw [← mul_pow]; norm_num
  rw [sub_sub_cancel, this]; ring

theorem p412ePhi_mono (k : ℕ) : Monotone (p412ePhi k) := fun s t h => by
  unfold p412ePhi
  have : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  nlinarith

theorem p412ePhi_mapsTo (k : ℕ) : MapsTo (p412ePhi k) (Icc (p412eU k) (p412eU (k + 1))) (Icc 0 1) :=
  fun t ht => ⟨p412ePhi_lo k ▸ p412ePhi_mono k ht.1, p412ePhi_hi k ▸ p412ePhi_mono k ht.2⟩

variable {X : Type*} [MetricSpace X]

/-- the concatenation of the curves `γ k` on `[u_k, u_{k+1}]`, with value `q` at `1` -/
def p412eCat (γ : ℕ → ℝ → X) (q : X) (t : ℝ) : X :=
  if t < 1 then γ (p412eIdx t) (p412ePhi (p412eIdx t) t) else q

theorem p412eCat_eqOn {γ : ℕ → ℝ → X} {q : X} (hj : ∀ k, γ k 1 = γ (k + 1) 0) (k : ℕ) :
    EqOn (p412eCat γ q) (γ k ∘ p412ePhi k) (Icc (p412eU k) (p412eU (k + 1))) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with h | h
  · subst h
    have hi : p412eIdx (p412eU (k + 1)) = k + 1 :=
      p412eIdx_eq le_rfl (p412eU_mono.strictMono_of_injective (fun a b hab => by
        unfold p412eU at hab
        have := pow_right_injective₀ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) (by linarith :
          (1 / 2 : ℝ) ^ a = (1 / 2) ^ b)
        exact this) (Nat.lt_succ_self _))
    simp only [p412eCat, if_pos (p412eU_lt_one _), hi, Function.comp_apply, p412ePhi_hi,
      p412ePhi_lo, hj]
  · simp only [p412eCat, if_pos (h.trans (p412eU_lt_one _)), p412eIdx_eq ht.1 h,
      Function.comp_apply]

theorem p412eCat_contOn_piece {γ : ℕ → ℝ → X} {q : X} (hc : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    (hj : ∀ k, γ k 1 = γ (k + 1) 0) (k : ℕ) :
    ContinuousOn (p412eCat γ q) (Icc (p412eU k) (p412eU (k + 1))) := by
  refine ContinuousOn.congr ?_ (p412eCat_eqOn hj k)
  exact (hc k).comp (by unfold p412ePhi; fun_prop) (p412ePhi_mapsTo k)

theorem p412eCat_contOn_init {γ : ℕ → ℝ → X} {q : X} (hc : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    (hj : ∀ k, γ k 1 = γ (k + 1) 0) (n : ℕ) :
    ContinuousOn (p412eCat γ q) (Icc 0 (p412eU n)) := by
  induction n with
  | zero => rw [p412eU_zero, Icc_self]; exact continuousOn_singleton _ _
  | succ n ih =>
    rw [← Icc_union_Icc_eq_Icc (p412eU_nonneg n) (p412eU_mono (Nat.le_succ n))]
    exact ih.union_of_isClosed (p412eCat_contOn_piece hc hj n) isClosed_Icc isClosed_Icc

theorem p412eCat_len_piece {γ : ℕ → ℝ → X} {q : X} (hc : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    (hj : ∀ k, γ k 1 = γ (k + 1) 0) (k : ℕ) :
    curveLength (p412eCat γ q) (p412eU k) (p412eU (k + 1)) = curveLength (γ k) 0 1 := by
  rw [curveLength_congr (p412eCat_eqOn hj k),
    curveLength_comp_of_continuousOn_monotoneOn _ (p412eU_mono (Nat.le_succ k))
      (by unfold p412ePhi; fun_prop) ((p412ePhi_mono k).monotoneOn _), p412ePhi_lo, p412ePhi_hi]

theorem p412e_tendsto_U : Tendsto p412eU atTop (𝓝 1) := by
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))
  rw [sub_zero] at this; exact this

/-- **Infinite concatenation** (own elementary argument, DEC-86 (3)) -/
theorem p412e_concat {γ : ℕ → ℝ → X} {q : X} (hc : ∀ k, ContinuousOn (γ k) (Icc 0 1))
    (hj : ∀ k, γ k 1 = γ (k + 1) 0) (hp : Tendsto (fun k => γ k 0) atTop (𝓝 q))
    (hs : ∑' k, curveLength (γ k) 0 1 ≠ ∞) :
    ContinuousOn (p412eCat γ q) (Icc 0 1) ∧ p412eCat γ q 0 = γ 0 0 ∧ p412eCat γ q 1 = q ∧
      curveLength (p412eCat γ q) 0 1 ≤ ∑' k, curveLength (γ k) 0 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1, p412eCat γ q t = q ∨ ∃ k, ∃ s ∈ Icc (0 : ℝ) 1, p412eCat γ q t = γ k s := by
  have hcat0 : p412eCat γ q 0 = γ 0 0 := by
    have h := p412eCat_eqOn (q := q) hj 0 ⟨le_of_eq p412eU_zero, p412eU_nonneg 1⟩
    rw [h, Function.comp_apply]; congr 1; norm_num [p412ePhi]
  have hcat1 : p412eCat γ q 1 = q := by simp [p412eCat]
  -- the tail `len γ_k + d(γ_k(0), q)` tends to `0`
  have htail : Tendsto (fun k => curveLength (γ k) 0 1 + edist (γ k 0) q) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs).add (tendsto_iff_edist_tendsto_0.1 hp)
    simpa using this
  -- continuity at `1`
  have hat1 : ContinuousWithinAt (p412eCat γ q) (Icc 0 1) 1 := by
    rw [ContinuousWithinAt, hcat1, EMetric.tendsto_nhds]
    intro ε hε
    by_cases hεt : ε = ∞
    · exact Eventually.of_forall fun t => hεt ▸ edist_lt_top _ _
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((ENNReal.tendsto_nhds_zero.1 htail) (ε / 2)
      (ENNReal.half_pos hε.ne'))
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds (p412eU_lt_one N))]
      with t ht htN
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; rw [hcat1, edist_self]; exact hε
    obtain ⟨hk1, hk2⟩ := p412eIdx_spec ht.1 h1
    set k := p412eIdx t
    have hkN : N ≤ k := by
      by_contra hlt; push_neg at hlt
      have := p412eU_mono (Nat.succ_le_of_lt hlt)
      exact absurd (htN.trans hk2) (not_lt.2 this)
    have hmem := p412ePhi_mapsTo k ⟨hk1, hk2.le⟩
    have heq : p412eCat γ q t = γ k (p412ePhi k t) := by simp [p412eCat, h1, k]
    rw [heq]
    calc edist (γ k (p412ePhi k t)) q ≤ edist (γ k 0) (γ k (p412ePhi k t)) + edist (γ k 0) q := by
          rw [edist_comm (γ k 0)]; exact edist_triangle _ _ _
      _ ≤ curveLength (γ k) 0 1 + edist (γ k 0) q := by
          gcongr
          exact (edist_le_curveLength _ hmem.1).trans (curveLength_mono _ le_rfl hmem.2)
      _ ≤ ε / 2 := hN k hkN
      _ < ε := ENNReal.half_lt_self hε.ne' hεt
  -- continuity on `[0, 1)`
  have hcont : ContinuousOn (p412eCat γ q) (Icc 0 1) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1; exact hat1
    obtain ⟨-, hk2⟩ := p412eIdx_spec ht.1 h1
    refine ((p412eCat_contOn_init (q := q) hc hj (p412eIdx t + 1)) t
      ⟨ht.1, hk2.le⟩).mono_of_mem_nhdsWithin ?_
    exact mem_nhdsWithin.2 ⟨Iio _, isOpen_Iio, hk2, fun y hy => ⟨hy.2.1, hy.1.le⟩⟩
  refine ⟨hcont, hcat0, hcat1, ?_, ?_⟩
  · -- length: lower semicontinuity along `t ↦ Cat (min t u_n)`
    have hlim : ∀ t ∈ Icc (0 : ℝ) 1,
        Tendsto (fun n => (p412eCat γ q ∘ fun s => min s (p412eU n)) t) atTop
          (𝓝 (p412eCat γ q t)) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · subst h1
        have hU : Tendsto p412eU atTop (𝓝[Icc 0 1] 1) :=
          tendsto_nhdsWithin_iff.2 ⟨p412e_tendsto_U,
            Eventually.of_forall fun n => ⟨p412eU_nonneg n, (p412eU_lt_one n).le⟩⟩
        refine (hat1.tendsto.comp hU).congr fun n => ?_
        simp [min_eq_right (p412eU_lt_one n).le]
      · obtain ⟨N, hN⟩ := eventually_atTop.1 ((p412e_tendsto_U).eventually (Ioi_mem_nhds h1))
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        simp [min_eq_left (hN n hn).le]
    refine (curveLength_le_liminf hlim).trans (liminf_le_of_frequently_le' (Frequently.of_forall
      fun n => ?_))
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
      (fun a _ b _ hab => min_le_min_right _ hab), min_eq_left (p412eU_nonneg n),
      min_eq_right (p412eU_lt_one n).le]
    have hsum := sum_curveLength_eq (p412eCat γ q) p412eU_mono n
    rw [p412eU_zero] at hsum
    rw [← hsum]
    simp only [p412eCat_len_piece hc hj]
    exact ENNReal.sum_le_tsum _
  · intro t ht
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · left; rw [h1, hcat1]
    · right
      obtain ⟨hk1, hk2⟩ := p412eIdx_spec ht.1 h1
      exact ⟨p412eIdx t, _, p412ePhi_mapsTo _ ⟨hk1, hk2.le⟩, by simp [p412eCat, h1]⟩

end LQGMetric.GM
