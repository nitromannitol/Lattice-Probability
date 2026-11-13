/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.InwardMap.LatticeMap at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.InwardMap.Basic




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.Exponent.InwardMap

private theorem affine_lipschitz (c d : ℝ) (hc : 0 ≤ c) (hcK : c ≤ 5/4) :
    LipschitzWith (5/4 : NNReal) (fun t : ℝ => c*t+d) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Real.dist_eq, NNReal.coe_div, NNReal.coe_ofNat]
  have h : |(c*x+d)-(c*y+d)| = c*|x-y| := by
    rw [show (c*x+d)-(c*y+d) = c*(x-y) by ring, abs_mul, abs_of_nonneg hc]
  rw [h]
  exact mul_le_mul_of_nonneg_right hcK (abs_nonneg _)

 

def latticeCoord (a t : ℝ) : ℝ :=
  max (min (max (min (t+32*a) ((1-64*a)*t-64*a)) ((1+64*a)*t))
      ((1-64*a)*t+64*a))
    (t-32*a)

theorem latticeCoord_lipschitz (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    LipschitzWith (5/4 : NNReal) (latticeCoord a) := by
  have hc : 0 ≤ 1-64*a ∧ 1-64*a ≤ 5/4 ∧
      0 ≤ 1+64*a ∧ 1+64*a ≤ 5/4 := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have h1 := affine_lipschitz 1 (32*a) (by norm_num) (by norm_num)
  have h2 := affine_lipschitz (1-64*a) (-64*a) hc.1 hc.2.1
  have h3 := affine_lipschitz (1+64*a) 0 hc.2.2.1 hc.2.2.2
  have h4 := affine_lipschitz (1-64*a) (64*a) hc.1 hc.2.1
  have h5 := affine_lipschitz 1 (-32*a) (by norm_num) (by norm_num)
  have h := (((h1.min h2).max h3).min h4).max h5
  simp only [max_self] at h
  convert h using 1
  funext t
  simp only [latticeCoord, one_mul, add_zero, sub_eq_add_neg, ← neg_mul]

private theorem latticeCoord_leftOuter (a t : ℝ) (ha0 : 0 ≤ a)
    (ht : t ≤ -(3/2 : ℝ)) : latticeCoord a t = t+32*a := by
  have h01 : t+32*a ≤ (1-64*a)*t-64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ -(3/2:ℝ)-t by linarith)]
  have h02 : (1+64*a)*t ≤ t+32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ (1/2:ℝ)-t by linarith)]
  have h03 : t+32*a ≤ (1-64*a)*t+64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ (1/2:ℝ)-t by linarith)]
  have h04 : t-32*a ≤ t+32*a := by linarith
  unfold latticeCoord
  rw [min_eq_left h01, max_eq_left h02, min_eq_left h03, max_eq_left h04]

private theorem latticeCoord_leftInner (a t : ℝ) (ha0 : 0 ≤ a)
    (ht0 : -(3/2 : ℝ) ≤ t) (ht1 : t ≤ -(1/2 : ℝ)) :
    latticeCoord a t = (1-64*a)*t-64*a := by
  have h10 : (1-64*a)*t-64*a ≤ t+32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(3/2:ℝ) by linarith)]
  have h12 : (1+64*a)*t ≤ (1-64*a)*t-64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ -(1/2:ℝ)-t by linarith)]
  have h13 : (1-64*a)*t-64*a ≤ (1-64*a)*t+64*a := by linarith
  have h14 : t-32*a ≤ (1-64*a)*t-64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ -(1/2:ℝ)-t by linarith)]
  unfold latticeCoord
  rw [min_eq_right h10, max_eq_left h12, min_eq_left h13, max_eq_left h14]

private theorem latticeCoord_center (a t : ℝ) (ha0 : 0 ≤ a)
    (ht0 : -(1/2 : ℝ) ≤ t) (ht1 : t ≤ (1/2 : ℝ)) :
    latticeCoord a t = (1+64*a)*t := by
  have h10 : (1-64*a)*t-64*a ≤ t+32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(3/2:ℝ) by linarith)]
  have h12 : (1-64*a)*t-64*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(1/2:ℝ) by linarith)]
  have h23 : (1+64*a)*t ≤ (1-64*a)*t+64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ (1/2:ℝ)-t by linarith)]
  have h24 : t-32*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(1/2:ℝ) by linarith)]
  unfold latticeCoord
  rw [min_eq_right h10, max_eq_right h12, min_eq_left h23, max_eq_left h24]

private theorem latticeCoord_rightInner (a t : ℝ) (ha0 : 0 ≤ a)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t ≤ (3/2 : ℝ)) :
    latticeCoord a t = (1-64*a)*t+64*a := by
  have h10 : (1-64*a)*t-64*a ≤ t+32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(3/2:ℝ) by linarith)]
  have h12 : (1-64*a)*t-64*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(1/2:ℝ) by linarith)]
  have h32 : (1-64*a)*t+64*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t-(1/2:ℝ) by linarith)]
  have h34 : t-32*a ≤ (1-64*a)*t+64*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ (3/2:ℝ)-t by linarith)]
  unfold latticeCoord
  rw [min_eq_right h10, max_eq_right h12, min_eq_right h32, max_eq_left h34]

private theorem latticeCoord_rightOuter (a t : ℝ) (ha0 : 0 ≤ a)
    (ht : (3/2 : ℝ) ≤ t) : latticeCoord a t = t-32*a := by
  have h10 : (1-64*a)*t-64*a ≤ t+32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(3/2:ℝ) by linarith)]
  have h12 : (1-64*a)*t-64*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t+(1/2:ℝ) by linarith)]
  have h32 : (1-64*a)*t+64*a ≤ (1+64*a)*t := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t-(1/2:ℝ) by linarith)]
  have h34 : (1-64*a)*t+64*a ≤ t-32*a := by
    nlinarith [mul_nonneg ha0 (show 0 ≤ t-(3/2:ℝ) by linarith)]
  unfold latticeCoord
  rw [min_eq_right h10, max_eq_right h12, min_eq_right h32, max_eq_right h34]

theorem latticeCoord_eq_inwardCoord (a t : ℝ) (ha0 : 0 ≤ a) :
    latticeCoord a t = inwardCoord a t := by
  by_cases h0 : t ≤ -(3/2 : ℝ)
  · rw [latticeCoord_leftOuter a t ha0 h0]
    simp [inwardCoord, h0]
  by_cases h1 : t ≤ -(1/2 : ℝ)
  · rw [latticeCoord_leftInner a t ha0 (le_of_lt (lt_of_not_ge h0)) h1]
    simp only [inwardCoord, ite_eq_right h0, ite_eq_left h1]
    ring
  by_cases h2 : t ≤ (1/2 : ℝ)
  · rw [latticeCoord_center a t ha0 (le_of_lt (lt_of_not_ge h1)) h2]
    simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
  by_cases h3 : t ≤ (3/2 : ℝ)
  · rw [latticeCoord_rightInner a t ha0 (le_of_lt (lt_of_not_ge h2)) h3]
    simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2, ite_eq_left h3]
    ring
  · rw [latticeCoord_rightOuter a t ha0 (le_of_lt (lt_of_not_ge h3))]
    simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2, ite_eq_right h3]

theorem inwardCoord_lipschitz (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    LipschitzWith (5/4 : NNReal) (inwardCoord a) := by
  have heq : inwardCoord a = latticeCoord a := by
    funext t
    exact (latticeCoord_eq_inwardCoord a t ha0).symm
  rw [heq]
  exact latticeCoord_lipschitz a ha0 ha

private theorem strictMono_min {f g : ℝ → ℝ} (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (fun t => min (f t) (g t)) := by
  intro x y hxy
  exact lt_min (lt_of_le_of_lt (min_le_left _ _) (hf hxy))
    (lt_of_le_of_lt (min_le_right _ _) (hg hxy))

private theorem strictMono_max {f g : ℝ → ℝ} (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (fun t => max (f t) (g t)) := by
  intro x y hxy
  exact max_lt_iff.mpr ⟨(hf hxy).trans_le (le_max_left _ _),
    (hg hxy).trans_le (le_max_right _ _)⟩

private theorem affine_strictMono (c d : ℝ) (hc : 0 < c) :
    StrictMono (fun t : ℝ => c*t+d) := by
  intro x y hxy
  have hm := mul_lt_mul_of_pos_left hxy hc
  linarith

theorem latticeCoord_strictMono (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    StrictMono (latticeCoord a) := by
  have hc : 0 < 1-64*a ∧ 0 < 1+64*a := by
    constructor <;> nlinarith
  have h1 := affine_strictMono 1 (32*a) (by norm_num)
  have h2 := affine_strictMono (1-64*a) (-64*a) hc.1
  have h3 := affine_strictMono (1+64*a) 0 hc.2
  have h4 := affine_strictMono (1-64*a) (64*a) hc.1
  have h5 := affine_strictMono 1 (-32*a) (by norm_num)
  have h := strictMono_max (strictMono_min (strictMono_max (strictMono_min h1 h2)
    h3) h4) h5
  convert h using 1
  funext t
  simp only [latticeCoord, one_mul, add_zero, sub_eq_add_neg, ← neg_mul]

theorem inwardCoord_strictMono (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    StrictMono (inwardCoord a) := by
  have heq : inwardCoord a = latticeCoord a := by
    funext t
    exact (latticeCoord_eq_inwardCoord a t ha0).symm
  rw [heq]
  exact latticeCoord_strictMono a ha0 ha

theorem inwardCoord_displacement (a t : ℝ) (ha0 : 0 ≤ a) :
    -32*a ≤ inwardCoord a t - t ∧ inwardCoord a t - t ≤ 32*a := by
  by_cases h0 : t ≤ -(3/2 : ℝ)
  · simp only [inwardCoord, ite_eq_left h0]
    constructor <;> linarith
  by_cases h1 : t ≤ -(1/2 : ℝ)
  · have hp0 : 0 ≤ a*(t+(3/2:ℝ)) :=
      mul_nonneg ha0 (by linarith [lt_of_not_ge h0] : 0 ≤ t+(3/2:ℝ))
    have hp1 : 0 ≤ a*(-(1/2:ℝ)-t) :=
      mul_nonneg ha0 (by linarith : 0 ≤ -(1/2:ℝ)-t)
    simp only [inwardCoord, ite_eq_right h0, ite_eq_left h1]
    constructor <;> nlinarith
  by_cases h2 : t ≤ (1/2 : ℝ)
  · have hp0 : 0 ≤ a*(t+(1/2:ℝ)) :=
      mul_nonneg ha0 (by linarith [lt_of_not_ge h1] : 0 ≤ t+(1/2:ℝ))
    have hp1 : 0 ≤ a*((1/2:ℝ)-t) :=
      mul_nonneg ha0 (by linarith : 0 ≤ (1/2:ℝ)-t)
    simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1, ite_eq_left h2]
    constructor <;> nlinarith
  by_cases h3 : t ≤ (3/2 : ℝ)
  · have hp0 : 0 ≤ a*(t-(1/2:ℝ)) :=
      mul_nonneg ha0 (by linarith [lt_of_not_ge h2] : 0 ≤ t-(1/2:ℝ))
    have hp1 : 0 ≤ a*((3/2:ℝ)-t) :=
      mul_nonneg ha0 (by linarith : 0 ≤ (3/2:ℝ)-t)
    simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2, ite_eq_left h3]
    constructor <;> nlinarith
  · simp only [inwardCoord, ite_eq_right h0, ite_eq_right h1,
      ite_eq_right h2, ite_eq_right h3]
    constructor <;> linarith

theorem inwardCoord_surjective (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1/256) :
    Function.Surjective (inwardCoord a) := by
  intro y
  let lo : ℝ := y - 32*a - 1
  let hi : ℝ := y + 32*a + 1
  have hlo : inwardCoord a lo ≤ y := by
    have h := (inwardCoord_displacement a lo ha0).2
    dsimp [lo] at h
    linarith
  have hhi : y ≤ inwardCoord a hi := by
    have h := (inwardCoord_displacement a hi ha0).1
    dsimp [hi] at h
    linarith
  exact intermediate_value_univ lo hi (inwardCoord_lipschitz a ha0 ha).continuous
    ⟨hlo, hhi⟩

end SupercriticalLQGUniqueness.Exponent.InwardMap
