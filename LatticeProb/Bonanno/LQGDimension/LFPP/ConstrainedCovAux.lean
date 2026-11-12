/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ConstrainedCovAux at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.GraphCov
import LatticeProb.Bonanno.LQGDimension.LFPP.ConstrainedCovMeas

/-!
# Algebra of `logCov` on edge-indexed combinations, and subdivision of a chord

* `logCov` of `wc M W V` in either slot as a finite sum; differences of two combinations with
  the same vertices are combinations with the difference of the weights; total variation.
* **Subdivision**: the uniform measure on a chord `[x, y]` (one edge of weight `1`) and the
  same chord cut into `M` edges of weight `1/M` have the same `logCov` against any
  combination of nondegenerate segments, in either slot.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.ConstrCov

open Blueprint.Draft GraphCov

/-! ## `logCov` of `wc` combinations -/

lemma logCov_wc_left (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) (X : SegComb) :
    (wc M W V).logCov X = ∑ i ∈ Finset.range M,
      W i * (X.map fun p' => p'.1 * segLogPair (V i) (V (i + 1)) p'.2.1 p'.2.2).sum := by
  unfold SegComb.logCov wc
  rw [List.map_map, list_sum_map_range_real]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp]
  rw [← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun p' _ => ?_
  ring

lemma logCov_wc_right (X : SegComb) (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) :
    X.logCov (wc M W V) = (X.map fun p => p.1 * ∑ j ∈ Finset.range M,
      W j * segLogPair p.2.1 p.2.2 (V j) (V (j + 1))).sum := by
  unfold SegComb.logCov wc
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [List.map_map, list_sum_map_range_real, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Function.comp]
  ring

lemma logCov_sub_left (a b X : SegComb) : (a.sub b).logCov X = a.logCov X - b.logCov X := by
  unfold SegComb.sub; rw [logCov_append_left, logCov_neg_left]; ring

lemma logCov_sub_right (X a b : SegComb) : X.logCov (a.sub b) = X.logCov a - X.logCov b := by
  unfold SegComb.sub; rw [logCov_append_right, logCov_neg_right]; ring

lemma logCov_wc_sub_left (M : ℕ) (W W' : ℕ → ℝ) (V : ℕ → ℂ) (X : SegComb) :
    ((wc M W V).sub (wc M W' V)).logCov X = (wc M (fun i => W i - W' i) V).logCov X := by
  rw [logCov_sub_left, logCov_wc_left, logCov_wc_left, logCov_wc_left, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma list_sum_map_sub' {α : Type*} (l : List α) (F G : α → ℝ) :
    (l.map fun a => F a - G a).sum = (l.map F).sum - (l.map G).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma logCov_wc_sub_right (X : SegComb) (M : ℕ) (W W' : ℕ → ℝ) (V : ℕ → ℂ) :
    X.logCov ((wc M W V).sub (wc M W' V)) = X.logCov (wc M (fun i => W i - W' i) V) := by
  rw [logCov_sub_right, logCov_wc_right, logCov_wc_right, logCov_wc_right, ← list_sum_map_sub']
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Total variation `Σ |wᵢ|` of a segment combination. -/
def tv (c : SegComb) : ℝ := (c.map fun p => |p.1|).sum

lemma tv_sub (a b : SegComb) : tv (a.sub b) = tv a + tv b := by
  unfold tv SegComb.sub
  rw [List.map_append, List.sum_append, List.map_map]
  congr 2
  refine List.map_congr_left fun p _ => ?_
  simp

lemma tv_wc (M : ℕ) (W : ℕ → ℝ) (V : ℕ → ℂ) :
    tv (wc M W V) = ∑ i ∈ Finset.range M, |W i| := by
  unfold tv wc
  rw [List.map_map, ← list_sum_map_range_real]
  rfl

lemma tv_wc_prob {M : ℕ} {W : ℕ → ℝ} (V : ℕ → ℂ) (hW : ∀ i < M, 0 ≤ W i)
    (hs : ∑ i ∈ Finset.range M, W i = 1) : tv (wc M W V) = 1 := by
  rw [tv_wc, ← hs]
  exact Finset.sum_congr rfl fun i hi => abs_of_nonneg (hW i (Finset.mem_range.1 hi))

lemma abs_logCov_wc_sub_left_le {M : ℕ} {W W' : ℕ → ℝ} {V : ℕ → ℂ} {X : SegComb} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ i < M, ∀ p' ∈ X, |segLogPair (V i) (V (i + 1)) p'.2.1 p'.2.2| ≤ K) :
    |((wc M W V).sub (wc M W' V)).logCov X| ≤
      (∑ i ∈ Finset.range M, |W i - W' i|) * tv X * K := by
  rw [logCov_wc_sub_left]
  calc _ ≤ tv (wc M (fun i => W i - W' i) V) * tv X * K := by
        refine abs_logCov_le _ _ hK0 fun p hp p' hp' => ?_
        unfold wc at hp
        rw [List.mem_map] at hp
        obtain ⟨i, hi, rfl⟩ := hp
        exact hK i (List.mem_range.1 hi) p' hp'
    _ = _ := by rw [tv_wc]

lemma abs_logCov_wc_sub_right_le {X : SegComb} {M : ℕ} {W W' : ℕ → ℝ} {V : ℕ → ℂ} {K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ p ∈ X, ∀ j < M, |segLogPair p.2.1 p.2.2 (V j) (V (j + 1))| ≤ K) :
    |X.logCov ((wc M W V).sub (wc M W' V))| ≤
      tv X * (∑ i ∈ Finset.range M, |W i - W' i|) * K := by
  rw [logCov_wc_sub_right]
  calc _ ≤ tv X * tv (wc M (fun i => W i - W' i) V) * K := by
        refine abs_logCov_le _ _ hK0 fun p hp p' hp' => ?_
        unfold wc at hp'
        rw [List.mem_map] at hp'
        obtain ⟨j, hj, rfl⟩ := hp'
        exact hK p hp j (List.mem_range.1 hj)
    _ = _ := by rw [tv_wc]

/-! ## Subdivision of a chord -/

/-- The point with parameter `t` on the chord from `x` to `y`. -/
def chordPt (x y : ℂ) (t : ℝ) : ℂ := x + (t : ℂ) * (y - x)

lemma chordPt_zero (x y : ℂ) : chordPt x y 0 = x := by simp [chordPt]

lemma chordPt_one (x y : ℂ) : chordPt x y 1 = y := by simp [chordPt]

lemma chordPt_piece (x y : ℂ) {M : ℕ} (_hM : 0 < M) (i : ℕ) (t : ℝ) :
    chordPt x y ((i : ℝ) / M) + (t : ℂ) * (chordPt x y (((i : ℝ) + 1) / M) -
      chordPt x y ((i : ℝ) / M)) = chordPt x y (((i : ℝ) + t) / M) := by
  unfold chordPt; push_cast; ring

/-- Log-domination between a segment and a nondegenerate segment (second variable). -/
lemma logDom_seg_seg (a b x y : ℂ) (hxy : x ≠ y) :
    LogDom (fun s t => -Real.log ‖(a + (s : ℂ) * (b - a)) - chordPt x y t‖) := by
  have hv : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hv' : 0 < ‖y - x‖ := norm_pos_iff.2 hv
  set w : ℝ → ℂ := fun s => (a + (s : ℂ) * (b - a)) - x
  set c : ℝ → ℝ := fun s => ((w s).re * (y - x).re + (w s).im * (y - x).im) /
    ((y - x).re ^ 2 + (y - x).im ^ 2)
  have hlow : ∀ s t : ℝ, ‖y - x‖ * |t - c s| ≤ ‖(a + (s : ℂ) * (b - a)) - chordPt x y t‖ := by
    intro s t
    have h := HeatKernel.proj_lower (w s) (y - x) hv t
    have e : w s - (t : ℂ) * (y - x) = (a + (s : ℂ) * (b - a)) - chordPt x y t := by
      simp only [w, chordPt]; ring
    rwa [e] at h
  have hwb : ∀ s ∈ Icc (0:ℝ) 1, ‖w s‖ ≤ 2 * ‖a‖ + ‖b‖ + ‖x‖ := by
    intro s hs
    simp only [w]
    have h1 : ‖(s : ℂ) * (b - a)‖ ≤ ‖b‖ + ‖a‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖b - a‖ ≤ 1 * ‖b - a‖ := by gcongr; exact hs.2
        _ ≤ ‖b‖ + ‖a‖ := by rw [one_mul]; exact norm_sub_le _ _
    calc ‖a + (s : ℂ) * (b - a) - x‖ ≤ ‖a + (s : ℂ) * (b - a)‖ + ‖x‖ := norm_sub_le _ _
      _ ≤ ‖a‖ + ‖(s : ℂ) * (b - a)‖ + ‖x‖ := by gcongr; exact norm_add_le _ _
      _ ≤ 2 * ‖a‖ + ‖b‖ + ‖x‖ := by linarith
  refine logDom_curve (P := fun s => a + (s : ℂ) * (b - a)) (Q := chordPt x y)
    (by fun_prop) (by unfold chordPt; fun_prop) hv' c
    (K := (2 * ‖a‖ + ‖b‖ + ‖x‖) / ‖y - x‖)
    (Cu := 2 * ‖a‖ + ‖b‖ + ‖x‖ + ‖y - x‖) ?_ (fun s _ t _ => hlow s t) ?_
  · intro s hs
    have h := hlow s 0
    have e : (a + (s : ℂ) * (b - a)) - chordPt x y 0 = w s := by simp [w, chordPt]
    rw [e, zero_sub, abs_neg] at h
    rw [le_div_iff₀ hv', mul_comm]
    exact h.trans (hwb s hs)
  · intro s hs t ht
    have e : (a + (s : ℂ) * (b - a)) - chordPt x y t = w s - (t : ℂ) * (y - x) := by
      simp only [w, chordPt]; ring
    rw [e]
    calc ‖w s - (t : ℂ) * (y - x)‖ ≤ ‖w s‖ + ‖(t : ℂ) * (y - x)‖ := norm_sub_le _ _
      _ ≤ (2 * ‖a‖ + ‖b‖ + ‖x‖) + ‖y - x‖ := by
          gcongr
          · exact hwb s hs
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
            calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht.2
              _ = ‖y - x‖ := one_mul _

/-- Subdividing the second segment of `segLogPair`. -/
lemma segLogPair_subdiv_right {M : ℕ} (hM : 0 < M) (a b x y : ℂ) (hxy : x ≠ y) :
    segLogPair a b x y = ∑ j ∈ Finset.range M, (1 / (M : ℝ)) *
      segLogPair a b (chordPt x y ((j : ℝ) / M)) (chordPt x y (((j : ℝ) + 1) / M)) := by
  set h : ℝ → ℝ → ℝ := fun s t => -Real.log ‖(a + (s : ℂ) * (b - a)) - chordPt x y t‖ with hh
  have hd : LogDom h := logDom_seg_seg a b x y hxy
  have hL : segLogPair a b x y = ∫ s in (0:ℝ)..1, ∫ t in (0:ℝ)..1, h s t := rfl
  have hR : ∀ j : ℕ, (1 / (M : ℝ)) *
      segLogPair a b (chordPt x y ((j : ℝ) / M)) (chordPt x y (((j : ℝ) + 1) / M)) =
      ∫ s in (0:ℝ)..1, ∫ t in (j : ℝ) / M..((j : ℝ) + 1) / M, h s t := by
    intro j
    unfold segLogPair
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← piece_integral hM (h s) j]
    congr 1
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hh]
    rw [chordPt_piece x y hM j t]
  rw [Finset.sum_congr rfl fun j _ => hR j, ← intervalIntegral.integral_finsetSum
    (fun j hj => hd.ii_integral (by positivity) (by gcongr; linarith)
      (by
        have hj' : (j : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 hj
        rw [div_le_one (by exact_mod_cast hM)]; exact hj')), hL]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  exact (sum_pieces hM (h s) (hd.ii hs)).symm

/-- Log-domination between a chord (first variable) and a nondegenerate segment. -/
lemma logDom_chord_seg (x y a' b' : ℂ) (hab : a' ≠ b') :
    LogDom (fun s t => -Real.log ‖chordPt x y s - (a' + (t : ℂ) * (b' - a'))‖) :=
  logDom_seg_seg x y a' b' hab

/-- Subdividing the first segment of `segLogPair`. -/
lemma segLogPair_subdiv_left {M : ℕ} (hM : 0 < M) (x y a' b' : ℂ) (hab : a' ≠ b') :
    segLogPair x y a' b' = ∑ i ∈ Finset.range M, (1 / (M : ℝ)) *
      segLogPair (chordPt x y ((i : ℝ) / M)) (chordPt x y (((i : ℝ) + 1) / M)) a' b' := by
  set h : ℝ → ℝ → ℝ := fun s t => -Real.log ‖chordPt x y s - (a' + (t : ℂ) * (b' - a'))‖
    with hh
  have hd : LogDom h := logDom_chord_seg x y a' b' hab
  set g : ℝ → ℝ := fun s => ∫ t in (0:ℝ)..1, h s t with hg
  have hL : segLogPair x y a' b' = ∫ s in (0:ℝ)..1, g s := rfl
  have hR : ∀ i : ℕ, (1 / (M : ℝ)) *
      segLogPair (chordPt x y ((i : ℝ) / M)) (chordPt x y (((i : ℝ) + 1) / M)) a' b' =
      ∫ s in (i : ℝ) / M..((i : ℝ) + 1) / M, g s := by
    intro i
    rw [← piece_integral hM g i]
    congr 1
    unfold segLogPair
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hg, hh]
    rw [chordPt_piece x y hM i s]
  rw [Finset.sum_congr rfl fun i _ => hR i, hL]
  exact (sum_pieces hM g (hd.ii_integral le_rfl zero_le_one le_rfl)).symm

lemma swap_sum_list (s : Finset ℕ) (c : ℕ → ℝ) (X : SegComb) (S : ℕ → ℝ × ℂ × ℂ → ℝ) :
    ∑ i ∈ s, c i * (X.map fun p' => p'.1 * S i p').sum =
      (X.map fun p' => p'.1 * ∑ i ∈ s, c i * S i p').sum := by
  induction X with
  | nil => simp
  | cons q X ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The chord `[x, y]` as `M` edges of weight `1/M`. -/
def chordM (M : ℕ) (x y : ℂ) : SegComb :=
  wc M (fun _ => 1 / (M : ℝ)) (fun i => chordPt x y ((i : ℝ) / M))

lemma logCov_chord_left {M : ℕ} (hM : 0 < M) (x y : ℂ) (X : SegComb)
    (hX : ∀ p ∈ X, p.2.1 ≠ p.2.2) :
    SegComb.logCov [((1 : ℝ), x, y)] X = (chordM M x y).logCov X := by
  rw [chordM, logCov_wc_left]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [swap_sum_list]
  unfold SegComb.logCov
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
  congr 1
  refine List.map_congr_left fun p' hp' => ?_
  rw [segLogPair_subdiv_left hM x y p'.2.1 p'.2.2 (hX p' hp')]

lemma logCov_chord_right {M : ℕ} (hM : 0 < M) (X : SegComb) (x y : ℂ) (hxy : x ≠ y) :
    X.logCov [((1 : ℝ), x, y)] = X.logCov (chordM M x y) := by
  rw [chordM, logCov_wc_right]
  unfold SegComb.logCov
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_one,
    Nat.cast_add, Nat.cast_one]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  rw [segLogPair_subdiv_right hM p.2.1 p.2.2 x y hxy]

end LQGDimension.ConstrCov
