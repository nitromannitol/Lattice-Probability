/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3SmallN at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3Energy

 









set_option autoImplicit false
noncomputable section

open Finset
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

 
def sqWalk (R r : ℤ) (t : ℕ) : ℤ × ℤ :=
  if (t : ℤ) ≤ R - r then (R - t, 0)
  else if (t : ℤ) ≤ R - r + r then (r, t - (R - r))
  else if (t : ℤ) ≤ R - r + 3 * r then (r - (t - (R - r) - r), r)
  else if (t : ℤ) ≤ R - r + 5 * r then (-r, r - (t - (R - r) - 3 * r))
  else if (t : ℤ) ≤ R - r + 7 * r then (-r + (t - (R - r) - 5 * r), -r)
  else (r, -r + (t - (R - r) - 7 * r))

theorem sqWalk_adj (R r : ℤ) (hr : 1 ≤ r) (hrR : r ≤ R) (t : ℕ) :
    latticeAdjacent (sqWalk R r t) (sqWalk R r (t + 1)) := by
  unfold sqWalk
  push_cast
  split_ifs <;> simp only [latticeAdjacent, and_true, true_and] <;> omega

 
def stepOf (d : ℤ × ℤ) : Bool × Bool :=
  if d = (1, 0) then (true, true) else if d = (-1, 0) then (false, false)
  else if d = (0, 1) then (true, false) else (false, true)

theorem stepVec_stepOf (z w : ℤ × ℤ) (h : latticeAdjacent z w) : z + stepVec (stepOf (w - z)) = w := by
  obtain ⟨z1, z2⟩ := z; obtain ⟨w1, w2⟩ := w
  simp only [latticeAdjacent] at h
  unfold stepOf
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
    simp [stepVec, Prod.ext_iff] <;> omega

 
def stepsOf (W : ℕ → ℤ × ℤ) (N : ℕ) : Fin N → Bool × Bool := fun i => stepOf (W (i + 1) - W i)

theorem wpos_stepsOf (W : ℕ → ℤ × ℤ) (hW : ∀ t, latticeAdjacent (W t) (W (t + 1))) (N : ℕ) :
    ∀ k ≤ N, wpos (W 0) (stepsOf W N) k = W k := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wpos_succ, ih (by omega)]
    have : ext (stepsOf W N) k = stepOf (W (k + 1) - W k) := by
      simp [ext, stepsOf, show k < N by omega]
    rw [this, stepVec_stepOf _ _ (hW k)]

 
theorem outer_radius_ge_small (n : ℕ) (hn : 4 ≤ n) :
    2 ^ (n - 1) + 3 ≤ dgffOuterRadius n := by
  unfold dgffOuterRadius
  apply Nat.le_floor
  have h1 : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) = 2 ^ n / Real.sqrt 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [h1]
  have hs : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [le_div_iff₀ hs]
  have h3 : Real.sqrt 2 ≤ 1.415 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : (2 : ℝ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h8 : (8 : ℝ) ≤ 2 ^ (n - 1) := by
    have : (2 : ℝ) ^ 3 ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  rw [h2]
  push_cast
  nlinarith

theorem inner_radius_small (n : ℕ) : (dgffInnerRadius n : ℤ) = 2 ^ (n - 1) := by
  unfold dgffInnerRadius; push_cast; rfl

section SqWalk

variable (R r : ℤ) (hr : 1 ≤ r) (hrR : r ≤ R)
include hr hrR

theorem sqWalk_zero : sqWalk R r 0 = (R, 0) := by
  unfold sqWalk; rw [if_pos (by push_cast; omega)]; simp

theorem sqWalk_box (t : ℕ) (ht : (t : ℤ) ≤ R - r + 8 * r) :
    |(sqWalk R r t).1| ≤ R ∧ |(sqWalk R r t).2| ≤ r := by
  unfold sqWalk
  split_ifs <;> simp only [abs_le] <;> omega

theorem sqWalk_shell (t : ℕ) (h1 : R - r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + 8 * r) :
    |(sqWalk R r t).1| ≤ r ∧ |(sqWalk R r t).2| ≤ r ∧
      (r ≤ |(sqWalk R r t).1| ∨ r ≤ |(sqWalk R r t).2|) := by
  unfold sqWalk
  split_ifs <;> simp only [abs_le, le_abs] <;> omega

theorem sqWalk_side1 (t : ℕ) (h1 : R - r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + r) :
    (sqWalk R r t).1 = r := by
  unfold sqWalk; split_ifs <;> simp only <;> omega

theorem sqWalk_side2 (t : ℕ) (h1 : R - r + r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + 3 * r) :
    (sqWalk R r t).2 = r := by
  unfold sqWalk; split_ifs <;> simp only <;> omega

theorem sqWalk_side3 (t : ℕ) (h1 : R - r + 3 * r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + 5 * r) :
    (sqWalk R r t).1 = -r := by
  unfold sqWalk; split_ifs <;> simp only <;> omega

theorem sqWalk_side4 (t : ℕ) (h1 : R - r + 5 * r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + 7 * r) :
    (sqWalk R r t).2 = -r := by
  unfold sqWalk; split_ifs <;> simp only <;> omega

theorem sqWalk_side5 (t : ℕ) (h1 : R - r + 7 * r ≤ (t : ℤ)) (h2 : (t : ℤ) ≤ R - r + 8 * r) :
    (sqWalk R r t).1 = r := by
  unfold sqWalk; split_ifs <;> simp only <;> omega

theorem sqWalk_start (t : ℕ) (h : (t : ℤ) = R - r) : sqWalk R r t = (r, 0) := by
  unfold sqWalk; rw [if_pos (by omega)]; ext <;> simp <;> omega

theorem sqWalk_end (t : ℕ) (h : (t : ℤ) = R - r + 8 * r) : sqWalk R r t = (r, 0) := by
  unfold sqWalk
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]
  ext <;> simp <;> omega

end SqWalk

 
theorem small_mass (n : ℕ) (hn : 4 ≤ n) :
    ∃ y : DGFFSite n, ∃ N : ℕ, N ≤ 9 * 2 ^ n ∧ dgffConductance ≤ (boxConductances n).boundary y ∧
      ENNReal.ofReal ((1 / 4 : ℝ) ^ N) ≤ pathMass n (ExcursionEncircles n) y := by
  obtain ⟨R, hRdef⟩ : ∃ R : ℤ, R = interiorRadius n := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℤ, r = 2 ^ (n - 1) + 2 := ⟨_, rfl⟩
  have hpow : (2 : ℤ) ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
  have h8 : (8 : ℤ) ≤ 2 ^ (n - 1) := by
    have : (2 : ℤ) ^ 3 ≤ 2 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at this; exact this
  have hR : R = 2 ^ n - 1 := by rw [hRdef]; rfl
  have hr1 : 1 ≤ r := by omega
  have hrR : r ≤ R := by omega
  obtain ⟨W, hW⟩ : ∃ W : ℕ → ℤ × ℤ, W = sqWalk R r := ⟨_, rfl⟩
  have hWadj : ∀ t, latticeAdjacent (W t) (W (t + 1)) := by
    rw [hW]; exact sqWalk_adj R r hr1 hrR
  obtain ⟨A, hA⟩ : ∃ A : ℕ, (A : ℤ) = R - r := ⟨(R - r).toNat, by omega⟩
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r' : ℤ) = r := ⟨r.toNat, by omega⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = A + 8 * r' := ⟨_, rfl⟩
  have hW0 : W 0 = (R, 0) := by rw [hW]; exact sqWalk_zero R r hr1 hrR
  have hy0 : (R, (0 : ℤ)) ∈ interiorSites n := by
    rw [mem_interior_iff, ← hRdef]; simp only; omega
  have hsq : ∀ i ≤ 8 * r', |(W (A + i)).1| ≤ r ∧ |(W (A + i)).2| ≤ r ∧
      (r ≤ |(W (A + i)).1| ∨ r ≤ |(W (A + i)).2|) := by
    intro i hi
    have hi' : (i : ℤ) ≤ 8 * r := by rw [← hr']; exact_mod_cast hi
    rw [hW]; exact sqWalk_shell R r hr1 hrR _ (by push_cast; omega) (by push_cast; omega)
  
  have hWA : W A = (r, 0) := by rw [hW]; exact sqWalk_start R r hr1 hrR A hA
  have hWAe : W (A + 8 * r') = (r, 0) := by
    rw [hW]; exact sqWalk_end R r hr1 hrR _ (by push_cast; omega)
  have hchain : (seg W A (8 * r')).IsChain latticeAdjacent := seg_isChain W hWadj A _
  have hcl : IsClosed (seg W A (8 * r')) := ⟨seg_ne_nil _ _ _, by
    rw [seg_head?, seg_getLast?, hWA, hWAe]⟩
  have hwind : wind (0, 0) (seg W A (8 * r')) = -1 := by
    unfold wind
    rw [stepSum_seg]
    have e : ∑ a ∈ range (8 * r'), crossVal (0, 0) (W (A + a)) (W (A + a + 1)) =
        ∑ k ∈ Ico A (A + 8 * r'), crossVal (0, 0) (W k) (W (k + 1)) := by
      rw [sum_Ico_eq_sum_range]; simp
    rw [e, ← sum_Ico_consecutive _ (show A ≤ A + r' by omega) (show A + r' ≤ A + 8 * r' by omega),
      ← sum_Ico_consecutive _ (show A + r' ≤ A + 3 * r' by omega)
        (show A + 3 * r' ≤ A + 8 * r' by omega),
      ← sum_Ico_consecutive _ (show A + 3 * r' ≤ A + 5 * r' by omega)
        (show A + 5 * r' ≤ A + 8 * r' by omega),
      ← sum_Ico_consecutive _ (show A + 5 * r' ≤ A + 7 * r' by omega)
        (show A + 7 * r' ≤ A + 8 * r' by omega)]
    have z1 : ∑ k ∈ Ico A (A + r'), crossVal (0, 0) (W k) (W (k + 1)) = 0 := by
      apply sum_eq_zero; intro k hk; rw [mem_Ico] at hk
      have hk' : (A : ℤ) ≤ k ∧ (k : ℤ) + 1 ≤ A + r' := by constructor <;> omega
      apply crossVal_eq_zero_of_right
      · rw [hW, sqWalk_side1 R r hr1 hrR k (by omega) (by omega)]; show (0 : ℤ) + 1 ≤ r; omega
      · rw [hW, sqWalk_side1 R r hr1 hrR (k + 1) (by push_cast; omega) (by push_cast; omega)]
        show (0 : ℤ) + 1 ≤ r; omega
    have z2 : ∑ k ∈ Ico (A + r') (A + 3 * r'), crossVal (0, 0) (W k) (W (k + 1)) = -1 := by
      rw [sum_Ico_crossVal_above W hWadj (0, 0) _ _ (by omega) (fun k h1 h2 => by
        have hk' : ((A + r' : ℕ) : ℤ) ≤ k ∧ (k : ℤ) < ((A + 3 * r' : ℕ) : ℤ) := by
          constructor <;> omega
        push_cast at hk'
        rw [hW, sqWalk_side2 R r hr1 hrR k (by omega) (by omega)]
        show (0 : ℤ) < r; omega)]
      have e1 : (W (A + 3 * r')).1 = -r := by
        rw [hW]; exact sqWalk_side3 R r hr1 hrR _ (by push_cast; omega) (by push_cast; omega)
      have e2 : (W (A + r')).1 = r := by
        rw [hW]; exact sqWalk_side1 R r hr1 hrR _ (by push_cast; omega) (by push_cast; omega)
      simp only [rightInd, e1, e2]
      rw [if_neg (by omega), if_pos (by omega)]
      norm_num
    have z3 : ∑ k ∈ Ico (A + 3 * r') (A + 5 * r'), crossVal (0, 0) (W k) (W (k + 1)) = 0 := by
      apply sum_eq_zero; intro k hk; rw [mem_Ico] at hk
      have hk' : ((A + 3 * r' : ℕ) : ℤ) ≤ k ∧ (k : ℤ) + 1 ≤ ((A + 5 * r' : ℕ) : ℤ) := by
        constructor <;> omega
      push_cast at hk'
      apply crossVal_eq_zero_of_left
      · rw [hW, sqWalk_side3 R r hr1 hrR k (by omega) (by omega)]; show -r ≤ (0 : ℤ); omega
      · rw [hW, sqWalk_side3 R r hr1 hrR (k + 1) (by push_cast; omega) (by push_cast; omega)]
        show -r ≤ (0 : ℤ); omega
    have z4 : ∑ k ∈ Ico (A + 5 * r') (A + 7 * r'), crossVal (0, 0) (W k) (W (k + 1)) = 0 := by
      apply sum_eq_zero; intro k hk; rw [mem_Ico] at hk
      have hk' : ((A + 5 * r' : ℕ) : ℤ) ≤ k ∧ (k : ℤ) + 1 ≤ ((A + 7 * r' : ℕ) : ℤ) := by
        constructor <;> omega
      push_cast at hk'
      apply crossVal_eq_zero_of_below
      rw [hW, sqWalk_side4 R r hr1 hrR k (by omega) (by omega)]; show -r ≤ (0 : ℤ); omega
    have z5 : ∑ k ∈ Ico (A + 7 * r') (A + 8 * r'), crossVal (0, 0) (W k) (W (k + 1)) = 0 := by
      apply sum_eq_zero; intro k hk; rw [mem_Ico] at hk
      have hk' : ((A + 7 * r' : ℕ) : ℤ) ≤ k ∧ (k : ℤ) + 1 ≤ ((A + 8 * r' : ℕ) : ℤ) := by
        constructor <;> omega
      push_cast at hk'
      apply crossVal_eq_zero_of_right
      · rw [hW, sqWalk_side5 R r hr1 hrR k (by omega) (by omega)]; show (0 : ℤ) + 1 ≤ r; omega
      · rw [hW, sqWalk_side5 R r hr1 hrR (k + 1) (by push_cast; omega) (by push_cast; omega)]
        show (0 : ℤ) + 1 ≤ r; omega
    rw [z1, z2, z3, z4, z5]; norm_num
  obtain ⟨l', h1, h2, h3, h4, h5⟩ := exists_simple_loop (0, 0) _ _ le_rfl hchain hcl
    (by rw [hwind]; norm_num)
  have hinner := inner_radius_small n
  have hout : (2 ^ (n - 1) + 3 : ℤ) ≤ (dgffOuterRadius n : ℤ) := by
    have := outer_radius_ge_small n hn; exact_mod_cast this
  obtain ⟨p, hp, hmap⟩ := aroundPath_of_loop_gen n r r (by rw [hinner]; omega) (by omega)
    (by rw [← hRdef]; exact hrR) l' h1 h2 h3 h5 (by
      intro v hv
      obtain ⟨i, hi, rfl⟩ := mem_seg.mp (h4 v hv)
      exact hsq i hi)
  
  have hcont : ContEvent n N (R, 0) (stepsOf W N) := by
    have hpos := wpos_stepsOf W hWadj N
    rw [hW0] at hpos
    refine ⟨fun k hk => ?_, p, hp, fun v hv => ?_⟩
    · rw [hpos k hk]
      have hk' : (k : ℤ) ≤ R - r + 8 * r := by
        have : (k : ℤ) ≤ N := by exact_mod_cast hk
        rw [hN] at this; push_cast at this; omega
      obtain ⟨a, b⟩ := (show |(W k).1| ≤ R ∧ |(W k).2| ≤ r by
        rw [hW]; exact sqWalk_box R r hr1 hrR k hk')
      rw [mem_interior_iff, ← hRdef]
      rw [abs_le] at a b
      omega
    · have hv' : v.1 ∈ l'.dropLast := by rw [← hmap]; exact List.mem_map_of_mem hv
      obtain ⟨i, hi, hiv⟩ := mem_seg.mp (h4 v.1 (List.dropLast_subset l' hv'))
      exact ⟨A + i, by omega, by rw [hpos (A + i) (by omega)]; exact hiv⟩
  refine ⟨⟨(R, 0), hy0⟩, N, ?_, ?_, ?_⟩
  · have : (N : ℤ) ≤ 9 * 2 ^ n := by rw [hN]; push_cast; omega
    exact_mod_cast this
  · exact boundary_ge_of_right n _ hRdef
  · have hge := pathMass_enc_ge n N ⟨(R, 0), hy0⟩
    refine le_trans ?_ hge
    apply ENNReal.ofReal_le_ofReal
    have hc : (1 : ℝ) ≤ ((univ.filter fun ω : Fin N → Bool × Bool =>
        ContEvent n N (R, 0) ω).card : ℝ) := by
      have : 1 ≤ (univ.filter fun ω : Fin N → Bool × Bool => ContEvent n N (R, 0) ω).card :=
        card_pos.mpr ⟨stepsOf W N, by rw [mem_filter]; exact ⟨mem_univ _, hcont⟩⟩
      exact_mod_cast this
    rw [show ((1 : ℝ) / 4) ^ N = 1 / 4 ^ N by rw [one_div, inv_pow, one_div]]
    exact div_le_div_of_nonneg_right hc (by positivity)

end SupercriticalLQGUniqueness.B2.QPos.P3
