/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9Det2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P9Det

/-!
# DG Proposition 3.9, the deterministic bound (P2-DG105j)

Ding–Gwynne, arXiv:1807.01072, proof of Proposition 3.9 (DG:1362–1389), deterministic part:
for `z ∈ 𝕊 = c + [0,L]²` the hubs of the dyadic squares `S_j^z ∋ z` of levels `k₀ ≤ k ≤ k₀ + J`
form a chain (DG (eqn-dyadic-seq-diam), summed in (eqn-dist-to-X)); the last square is inside an
admissible ball around `z` (DG:1371–1373, via Lemma 3.8); the hubs of level `k₀` are joined
through rows and columns of squares (DG:1384–1386). `p39_det`:
`D^ε(z, w; Q) ≤ 2 + 2 Σ_{i<J} (2M_{k₀+i+1} + M_{k₀+i+2}) + (4 L 2^{k₀}) · 4 M_{k₀+1}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DG

variable {μ : Measure ℂ} {ε : ℝ} {Q : Set ℂ} {c : ℂ} {L : ℝ} {k₀ : ℕ} {Mf : ℕ → ℝ}
  {KH KV : ℕ → ℕ → ℕ → Set ℂ}

/-- the index of the dyadic square of level `k` containing a point at offset `t ≥ 0` -/
def p39Idx (k : ℕ) (t : ℝ) : ℕ := ⌊t / p39d k⌋₊

lemma p39Idx_le {k : ℕ} {t : ℝ} (ht : 0 ≤ t) : (p39Idx k t : ℝ) * p39d k ≤ t := by
  have h := Nat.floor_le (div_nonneg ht (p39d_pos k).le)
  unfold p39Idx
  calc (⌊t / p39d k⌋₊ : ℝ) * p39d k ≤ t / p39d k * p39d k :=
        mul_le_mul_of_nonneg_right h (p39d_pos k).le
    _ = t := div_mul_cancel₀ t (p39d_pos k).ne'

lemma p39Idx_lt {k : ℕ} (t : ℝ) : t < ((p39Idx k t : ℝ) + 1) * p39d k := by
  have h := Nat.lt_floor_add_one (t / p39d k)
  unfold p39Idx
  calc t = t / p39d k * p39d k := (div_mul_cancel₀ t (p39d_pos k).ne').symm
    _ < _ := mul_lt_mul_of_pos_right h (p39d_pos k)

lemma p39Idx_succ {k : ℕ} {t : ℝ} (ht : 0 ≤ t) :
    ∃ i ≤ 1, p39Idx (k + 1) t = 2 * p39Idx k t + i := by
  have e : t / p39d (k + 1) = 2 * (t / p39d k) := by
    rw [p39d_succ]; field_simp
  have hx : 0 ≤ t / p39d k := div_nonneg ht (p39d_pos k).le
  unfold p39Idx
  rw [e]
  have h1 : 2 * ⌊t / p39d k⌋₊ ≤ ⌊2 * (t / p39d k)⌋₊ :=
    Nat.le_floor (by push_cast; nlinarith [Nat.floor_le hx])
  have h2 : ⌊2 * (t / p39d k)⌋₊ < 2 * ⌊t / p39d k⌋₊ + 2 :=
    (Nat.floor_lt (by positivity)).2 (by push_cast; nlinarith [Nat.lt_floor_add_one (t / p39d k)])
  exact ⟨⌊2 * (t / p39d k)⌋₊ - 2 * ⌊t / p39d k⌋₊, by omega, by omega⟩

/-- the hub of the level-`k` square containing `z` -/
def p39HubAt (KH KV : ℕ → ℕ → ℕ → Set ℂ) (c : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  p39Hub KH KV k (p39Idx k (z.re - c.re)) (p39Idx k (z.im - c.im))

/-- the square `c + [0,L]²` -/
def p39Sq (c : ℂ) (L : ℝ) : Set ℂ := Icc c.re (c.re + L) ×ℂ Icc c.im (c.im + L)

lemma p39_ok_at {k : ℕ} (hk : k₀ ≤ k) {z : ℂ} (hz : z ∈ p39Sq c L) :
    P39Ok L k₀ k (p39Idx k (z.re - c.re)) (p39Idx k (z.im - c.im)) := by
  simp only [p39Sq, Complex.mem_reProdIm, mem_Icc] at hz
  exact ⟨hk, (p39Idx_le (by linarith)).trans (by linarith),
    (p39Idx_le (by linarith)).trans (by linarith)⟩

/-- **DG (eqn-dist-to-X)**, the chain of hubs along `S_0^z ⊃ S_1^z ⊃ ⋯` -/
theorem p39_chain (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {z : ℂ} (hz : z ∈ p39Sq c L) (J : ℕ) :
    (dgLGD μ ε Q (p39HubAt KH KV c k₀ z) (p39HubAt KH KV c (k₀ + J) z) : ℝ≥0∞) ≤
      ENNReal.ofReal (Mf (k₀ + 1)) + ∑ i ∈ Finset.range J, (2 * ENNReal.ofReal (Mf (k₀ + i + 1)) +
        ENNReal.ofReal (Mf (k₀ + i + 1 + 1))) := by
  have hz' := hz
  simp only [p39Sq, Complex.mem_reProdIm, mem_Icc] at hz'
  induction J with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]
    have h0 := p39_ok_at (k := k₀ + 0) le_rfl hz
    obtain ⟨hk, ha, hb⟩ := h0
    have hm := (p39_hub_mem H ⟨hk, ha, hb⟩).2
    exact (H.2 (k₀ + 0 + 1) _ _ (by omega) (p39_ok0 ha) (p39_ok0 hb)).dist hm hm
  | succ J ih =>
    obtain ⟨i, hi, ei⟩ := p39Idx_succ (k := k₀ + J) (t := z.re - c.re) (by linarith)
    obtain ⟨j, hj, ej⟩ := p39Idx_succ (k := k₀ + J) (t := z.im - c.im) (by linarith)
    have hs := p39_step H hi hj (p39_ok_at (k := k₀ + J) (by omega) hz)
      (ei ▸ ej ▸ p39_ok_at (k := k₀ + J + 1) (by omega) hz)
    rw [Finset.sum_range_succ, ← add_assoc (ENNReal.ofReal (Mf (k₀ + 1)))]
    refine (p39_tri _ (p39HubAt KH KV c (k₀ + J) z) _).trans (add_le_add ih ?_)
    unfold p39HubAt
    rw [← add_assoc, ei, ej]
    refine hs.trans (le_of_eq ?_)
    ring

lemma p39_symm' (z w : ℂ) : (dgLGD μ ε Q w z : ℝ≥0∞) ≤ dgLGD μ ε Q z w :=
  ENat.toENNReal_le.2 (p39_symm z w)

/-- a row of squares of level `k` (DG:1384) -/
theorem p39_row (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k b : ℕ} (hk : k₀ ≤ k)
    (hb : (b : ℝ) * p39d k ≤ L) : ∀ a : ℕ, (a : ℝ) * p39d k ≤ L →
      (dgLGD μ ε Q (p39Hub KH KV k 0 b) (p39Hub KH KV k a b) : ℝ≥0∞) ≤
        ((a : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) := by
  have hL : 0 ≤ L := le_trans (by positivity) hb
  intro a
  induction a with
  | zero =>
    intro ha
    have hm := (p39_hub_mem H ⟨hk, ha, hb⟩).2
    have hd := (H.2 (k + 1) _ _ (by omega) (p39_ok0 ha) (p39_ok0 hb)).dist hm hm
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact hd.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  | succ a ih =>
    intro ha
    have ha0 : (a : ℝ) * p39d k ≤ L := le_trans (by
      gcongr; linarith) ha
    calc (dgLGD μ ε Q (p39Hub KH KV k 0 b) (p39Hub KH KV k (a + 1) b) : ℝ≥0∞)
        ≤ dgLGD μ ε Q (p39Hub KH KV k 0 b) (p39Hub KH KV k a b) +
          dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k (a + 1) b) := p39_tri _ _ _
      _ ≤ ((a : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) +
          4 * ENNReal.ofReal (Mf (k + 1)) :=
          add_le_add (ih ha0) (p39_right H ⟨hk, ha0, hb⟩ ⟨hk, ha, hb⟩)
      _ = (((a + 1 : ℕ) : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) := by
          push_cast; ring

/-- a column of squares of level `k` (DG:1384) -/
theorem p39_col (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a : ℕ} (hk : k₀ ≤ k)
    (ha : (a : ℝ) * p39d k ≤ L) : ∀ b : ℕ, (b : ℝ) * p39d k ≤ L →
      (dgLGD μ ε Q (p39Hub KH KV k a 0) (p39Hub KH KV k a b) : ℝ≥0∞) ≤
        ((b : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) := by
  intro b
  induction b with
  | zero =>
    intro hb
    have hm := (p39_hub_mem H ⟨hk, ha, hb⟩).2
    have hd := (H.2 (k + 1) _ _ (by omega) (p39_ok0 ha) (p39_ok0 hb)).dist hm hm
    simp only [Nat.cast_zero, zero_add, one_mul]
    exact hd.trans (le_mul_of_one_le_left (by positivity) (by norm_num))
  | succ b ih =>
    intro hb
    have hb0 : (b : ℝ) * p39d k ≤ L := le_trans (by
      gcongr; linarith) hb
    calc (dgLGD μ ε Q (p39Hub KH KV k a 0) (p39Hub KH KV k a (b + 1)) : ℝ≥0∞)
        ≤ dgLGD μ ε Q (p39Hub KH KV k a 0) (p39Hub KH KV k a b) +
          dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k a (b + 1)) := p39_tri _ _ _
      _ ≤ ((b : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) +
          4 * ENNReal.ofReal (Mf (k + 1)) :=
          add_le_add (ih hb0) (p39_up H ⟨hk, ha, hb0⟩ ⟨hk, ha, hb⟩)
      _ = (((b + 1 : ℕ) : ℝ≥0∞) + 1) * (4 * ENNReal.ofReal (Mf (k + 1))) := by
          push_cast; ring

lemma p39_idx_bound {k a : ℕ} (ha : (a : ℝ) * p39d k ≤ L) : (a : ℝ) ≤ L / p39d k :=
  (le_div_iff₀ (p39d_pos k)).2 ha

/-- the hubs of level `k` are joined through rows and columns (DG:1384–1386) -/
theorem p39_top (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {k a b a' b' : ℕ}
    (h : P39Ok L k₀ k a b) (h' : P39Ok L k₀ k a' b') :
    (dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k a' b') : ℝ≥0∞) ≤
      ENNReal.ofReal (4 * (L / p39d k) + 4) * (4 * ENNReal.ofReal (Mf (k + 1))) := by
  obtain ⟨hk, ha, hb⟩ := h
  obtain ⟨-, ha', hb'⟩ := h'
  have hL : 0 ≤ L := le_trans (by positivity) ha
  have h0 : ((0 : ℕ) : ℝ) * p39d k ≤ L := by simpa using hL
  set T := 4 * ENNReal.ofReal (Mf (k + 1))
  have e1 : (dgLGD μ ε Q (p39Hub KH KV k 0 0) (p39Hub KH KV k a b) : ℝ≥0∞) ≤
      ((a : ℝ≥0∞) + 1) * T + ((b : ℝ≥0∞) + 1) * T :=
    (p39_tri _ (p39Hub KH KV k a 0) _).trans
      (add_le_add (p39_row H hk h0 a ha) (p39_col H hk ha b hb))
  have e2 : (dgLGD μ ε Q (p39Hub KH KV k 0 0) (p39Hub KH KV k a' b') : ℝ≥0∞) ≤
      ((a' : ℝ≥0∞) + 1) * T + ((b' : ℝ≥0∞) + 1) * T :=
    (p39_tri _ (p39Hub KH KV k a' 0) _).trans
      (add_le_add (p39_row H hk h0 a' ha') (p39_col H hk ha' b' hb'))
  have hc : ((a + b + a' + b' + 4 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (4 * (L / p39d k) + 4) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    have := p39_idx_bound ha; have := p39_idx_bound hb
    have := p39_idx_bound ha'; have := p39_idx_bound hb'
    push_cast; linarith
  calc (dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k a' b') : ℝ≥0∞)
      ≤ dgLGD μ ε Q (p39Hub KH KV k a b) (p39Hub KH KV k 0 0) +
        dgLGD μ ε Q (p39Hub KH KV k 0 0) (p39Hub KH KV k a' b') := p39_tri _ _ _
    _ ≤ (((a : ℝ≥0∞) + 1) * T + ((b : ℝ≥0∞) + 1) * T) +
        (((a' : ℝ≥0∞) + 1) * T + ((b' : ℝ≥0∞) + 1) * T) :=
        add_le_add ((p39_symm' _ _).trans e1) e2
    _ = ((a + b + a' + b' + 4 : ℕ) : ℝ≥0∞) * T := by push_cast; ring
    _ ≤ _ := by gcongr

/-- the last square of the chain lies in an admissible ball around `z` (DG:1371–1373) -/
theorem p39_bot (H : P39Hyp μ ε Q c L k₀ Mf KH KV) {K : ℕ} (hK : k₀ ≤ K) {z : ℂ}
    (hz : z ∈ p39Sq c L) {ρ : ℝ} (hρ : 2 * p39d K < ρ) (hB : Metric.ball z ρ ⊆ closure Q)
    (hm : μ (Metric.ball z ρ) ≤ ENNReal.ofReal ε) :
    (dgLGD μ ε Q z (p39HubAt KH KV c K z) : ℝ≥0∞) ≤ 1 ∧
      (dgLGD μ ε Q (p39HubAt KH KV c K z) z : ℝ≥0∞) ≤ 1 := by
  have hz' := hz
  simp only [p39Sq, Complex.mem_reProdIm, mem_Icc] at hz'
  obtain ⟨-, ha, hb⟩ := p39_ok_at hK hz
  have hmem := p39_hub_mem H (p39_ok_at hK hz)
  have hre := (H.2 (K + 1) _ _ (by omega) (p39_ok0 ha) (p39_ok0 hb)).re_mem hmem.2
  have him := (H.1 (K + 1) _ _ (by omega) (p39_ok0 ha) (p39_ok0 hb)).im_mem hmem.1
  rw [p39_c2] at hre him
  have e1 : p39d (K + 1) = p39d K / 2 := p39d_succ K
  have l1 := p39Idx_le (k := K) (t := z.re - c.re) (by linarith)
  have l2 := p39Idx_le (k := K) (t := z.im - c.im) (by linarith)
  have u1 := p39Idx_lt (k := K) (z.re - c.re)
  have u2 := p39Idx_lt (k := K) (z.im - c.im)
  have hδ := p39d_pos K
  have hn : ‖p39HubAt KH KV c K z - z‖ < ρ := by
    unfold p39HubAt
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    rw [Complex.sub_re, Complex.sub_im]
    have r1 : |(p39Hub KH KV K (p39Idx K (z.re - c.re)) (p39Idx K (z.im - c.im))).re - z.re| ≤
        p39d K := abs_le.2 ⟨by nlinarith [hre.1, hre.2],
      by nlinarith [hre.1, hre.2]⟩
    have r2 : |(p39Hub KH KV K (p39Idx K (z.re - c.re)) (p39Idx K (z.im - c.im))).im - z.im| ≤
        p39d K := abs_le.2 ⟨by nlinarith [him.1, him.2],
      by nlinarith [him.1, him.2]⟩
    linarith
  have hr : 0 < ρ := lt_trans (by positivity) hρ
  have hzB : z ∈ Metric.ball z ρ := Metric.mem_ball_self hr
  have hhB : p39HubAt KH KV c K z ∈ Metric.ball z ρ := by rw [Metric.mem_ball, dist_eq_norm]; exact hn
  exact ⟨p39_ball hr hB hm hzB hhB, p39_ball hr hB hm hhB hzB⟩

/-- **DG Proposition 3.9, deterministic bound** (DG:1362–1389) -/
theorem p39_det (H : P39Hyp μ ε Q c L k₀ Mf KH KV) (J : ℕ) {ρ : ℝ}
    (hρ : 2 * p39d (k₀ + J) < ρ)
    (hB : ∀ z ∈ p39Sq c L, Metric.ball z ρ ⊆ closure Q ∧
      μ (Metric.ball z ρ) ≤ ENNReal.ofReal ε) :
    ∀ z ∈ p39Sq c L, ∀ w ∈ p39Sq c L, (dgLGD μ ε Q z w : ℝ≥0∞) ≤
      2 + 2 * (ENNReal.ofReal (Mf (k₀ + 1)) + ∑ i ∈ Finset.range J,
        (2 * ENNReal.ofReal (Mf (k₀ + i + 1)) + ENNReal.ofReal (Mf (k₀ + i + 1 + 1)))) +
      ENNReal.ofReal (4 * (L / p39d k₀) + 4) * (4 * ENNReal.ofReal (Mf (k₀ + 1))) := by
  intro z hz w hw
  set S := ENNReal.ofReal (Mf (k₀ + 1)) + ∑ i ∈ Finset.range J,
        (2 * ENNReal.ofReal (Mf (k₀ + i + 1)) + ENNReal.ofReal (Mf (k₀ + i + 1 + 1)))
  have bz := p39_bot H (by omega) hz hρ (hB z hz).1 (hB z hz).2
  have bw := p39_bot H (by omega) hw hρ (hB w hw).1 (hB w hw).2
  have cz := p39_chain H hz J
  have cw := p39_chain H hw J
  have t := p39_top H (p39_ok_at (k := k₀) le_rfl hz) (p39_ok_at (k := k₀) le_rfl hw)
  calc (dgLGD μ ε Q z w : ℝ≥0∞)
      ≤ dgLGD μ ε Q z (p39HubAt KH KV c (k₀ + J) z) +
        dgLGD μ ε Q (p39HubAt KH KV c (k₀ + J) z) (p39HubAt KH KV c k₀ z) +
        dgLGD μ ε Q (p39HubAt KH KV c k₀ z) (p39HubAt KH KV c k₀ w) +
        dgLGD μ ε Q (p39HubAt KH KV c k₀ w) w := p39_tri4 _ _ _ _ _
    _ ≤ dgLGD μ ε Q z (p39HubAt KH KV c (k₀ + J) z) +
        dgLGD μ ε Q (p39HubAt KH KV c (k₀ + J) z) (p39HubAt KH KV c k₀ z) +
        dgLGD μ ε Q (p39HubAt KH KV c k₀ z) (p39HubAt KH KV c k₀ w) +
        (dgLGD μ ε Q (p39HubAt KH KV c k₀ w) (p39HubAt KH KV c (k₀ + J) w) +
          dgLGD μ ε Q (p39HubAt KH KV c (k₀ + J) w) w) := by
        gcongr; exact p39_tri _ _ _
    _ ≤ 1 + S + ENNReal.ofReal (4 * (L / p39d k₀) + 4) * (4 * ENNReal.ofReal (Mf (k₀ + 1))) +
        (S + 1) := by
        exact add_le_add (add_le_add (add_le_add bz.1 ((p39_symm' _ _).trans cz)) t)
          (add_le_add cw bw.2)
    _ = _ := by ring

end DG
end LQGMetric
