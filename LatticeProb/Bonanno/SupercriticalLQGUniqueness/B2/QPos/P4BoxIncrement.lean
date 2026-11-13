/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4BoxIncrement at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Telescope

 









set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 
def incrConst : ℝ := 2 * 48 ^ 2 * 2064

theorem incrConst_pos : 0 < incrConst := by unfold incrConst; norm_num

 
theorem green_le_tele (z : ℤ × ℤ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (i : ℕ) (a c : ℤ × ℤ)
    (ha : a ∈ sqBox z (7 * ℓ + 1)) (hc : c ∉ sqBox z (4 ^ i * (8 * ℓ))) :
    green (sqBox z (4 ^ (i + 1) * (8 * ℓ))) a c ≤ 2064 := by
  have hstrip : ∀ e ∈ sqBox z (4 ^ (i + 1) * (8 * ℓ)), |e.1 - z.1| < 4 ^ (i + 1) * (8 * ℓ) :=
    fun e he => (mem_sqBox.mp he).1
  rw [mem_sqBox] at ha
  rw [mem_sqBox] at hc
  have h4 : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  have hrpos : 0 < 4 ^ i * ℓ := by positivity
  have hfar : ((4 ^ i * ℓ : ℕ) : ℝ) ≤ |((c.1 - a.1 : ℤ) : ℝ)| ∨
      ((4 ^ i * ℓ : ℕ) : ℝ) ≤ |((c.2 - a.2 : ℤ) : ℝ)| := by
    have hl : (0 : ℤ) ≤ ℓ := by positivity
    have key : ∀ u v w : ℤ, (4 ^ i * (8 * ℓ) : ℤ) ≤ |u - w| → |v - w| < 7 * ℓ + 1 →
        ((4 ^ i * ℓ : ℕ) : ℤ) ≤ |u - v| := by
      intro u v w h1 h2
      push_cast
      have h7 : (7 : ℤ) * ℓ ≤ 4 ^ i * (7 * ℓ) := by nlinarith
      rw [abs_lt] at h2
      rcases le_abs'.mp h1 with h1 | h1
      · rw [le_abs']; left; nlinarith
      · rw [le_abs']; right; nlinarith
    by_cases h1 : |c.1 - z.1| < 4 ^ i * (8 * ℓ)
    · have h2 : ¬ |c.2 - z.2| < 4 ^ i * (8 * ℓ) := fun h => hc ⟨h1, h⟩
      push_neg at h2
      right
      have := key c.2 a.2 z.2 h2 ha.2
      exact_mod_cast this
    · push_neg at h1
      left
      have := key c.1 a.1 z.1 h1 ha.1
      exact_mod_cast this
  have hg := green_le_far _ z.1 _ hstrip a c (4 ^ i * ℓ) hrpos hfar
  have hratio : 2 * ((4 ^ (i + 1) * (8 * ℓ) : ℤ) : ℝ) ^ 2 / ((4 ^ i * ℓ : ℕ) : ℝ) ^ 2 = 2048 := by
    push_cast
    have : (0 : ℝ) < (4 : ℝ) ^ i * ℓ := by positivity
    field_simp
    ring
  linarith

 
theorem incr_concentric_step (z : ℤ × ℤ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (i : ℕ) {x y : ℤ × ℤ}
    (hx1 : |x.1 - z.1| ≤ 6 * ℓ) (hx2 : |x.2 - z.2| ≤ 6 * ℓ)
    (hy1 : |y.1 - z.1| ≤ 6 * ℓ) (hy2 : |y.2 - z.2| ≤ 6 * ℓ)
    (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d) :
    incr (sqBox z (4 ^ (i + 1) * (8 * ℓ))) x y - incr (sqBox z (4 ^ i * (8 * ℓ))) x y ≤
      48 * (48 * 2064 * Real.sqrt (d / ℓ)) * Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ)) := by
  set Q : ℕ → Finset (ℤ × ℤ) := fun k => sqBox z (4 ^ k * (8 * ℓ))
  have h4 : (1 : ℤ) ≤ 4 ^ i := one_le_pow₀ (by norm_num)
  have hl : (0 : ℤ) ≤ ℓ := by positivity
  have hsub : Q i ⊆ Q (i + 1) := by
    apply sqBox_mono
    rw [pow_succ]
    nlinarith
  have hxQ : x ∈ Q i := by
    rw [mem_sqBox]; constructor <;> nlinarith
  have hyQ : y ∈ Q i := by
    rw [mem_sqBox]; constructor <;> nlinarith
  apply incr_step_le (Q i) (Q (i + 1)) hsub z.1 (4 ^ i * (8 * ℓ))
    (fun c hc => (mem_sqBox.mp hc).1) hxQ hyQ _ d hd1 hd2
  · have : 1 ≤ 4 ^ i := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  · intro c h1 h2
    rw [mem_sqBox]
    push_cast at h1 h2
    constructor
    · have := abs_sub_le c.1 x.1 z.1
      nlinarith [abs_nonneg (c.1 - x.1)]
    · have := abs_sub_le c.2 x.2 z.2
      nlinarith [abs_nonneg (c.2 - x.2)]
  · intro c h1 h2
    rw [mem_sqBox]
    push_cast at h1 h2
    constructor
    · have := abs_sub_le c.1 y.1 z.1
      nlinarith [abs_nonneg (c.1 - y.1)]
    · have := abs_sub_le c.2 y.2 z.2
      nlinarith [abs_nonneg (c.2 - y.2)]
  · 
    intro c hc
    rw [green_symm _ c x, green_symm _ c y]
    have hV : sqBox z (7 * ℓ) ⊆ Q (i + 1) := by
      apply sqBox_mono
      rw [pow_succ]
      nlinarith
    refine green_diff_le (Q (i + 1)) (sqBox z (7 * ℓ)) (sqBox z (7 * ℓ + 1)) hV
      (sqBox_mono (by linarith)) ?_ ?_ ?_ ?_ ?_ d hd1 hd2 ℓ hℓ ?_ ?_
    · intro a ha s
      rw [mem_sqBox] at ha ⊢
      have hs1 : |(stepVec s).1| ≤ 1 := by rcases s with ⟨_ | _, _ | _⟩ <;> simp [stepVec]
      have hs2 : |(stepVec s).2| ≤ 1 := by rcases s with ⟨_ | _, _ | _⟩ <;> simp [stepVec]
      simp only [Prod.fst_add, Prod.snd_add]
      constructor
      · have := abs_add_le (a.1 - z.1) (stepVec s).1
        rw [show a.1 - z.1 + (stepVec s).1 = a.1 + (stepVec s).1 - z.1 by ring] at this
        linarith [ha.1]
      · have := abs_add_le (a.2 - z.2) (stepVec s).2
        rw [show a.2 - z.2 + (stepVec s).2 = a.2 + (stepVec s).2 - z.2 by ring] at this
        linarith [ha.2]
    · intro hcV
      apply hc
      exact sqBox_mono (by nlinarith) hcV
    · intro a ha
      exact green_le_tele z ℓ hℓ i a c ha hc
    · rw [mem_sqBox]; constructor <;> linarith
    · rw [mem_sqBox]; constructor <;> linarith
    · intro c h1 h2
      rw [mem_sqBox]
      constructor
      · have := abs_sub_le c.1 x.1 z.1; linarith
      · have := abs_sub_le c.2 x.2 z.2; linarith
    · intro c h1 h2
      rw [mem_sqBox]
      constructor
      · have := abs_sub_le c.1 y.1 z.1; linarith
      · have := abs_sub_le c.2 y.2 z.2; linarith

 
theorem incr_concentric_le (z : ℤ × ℤ) (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (N : ℕ) {x y : ℤ × ℤ}
    (hx1 : |x.1 - z.1| ≤ 6 * ℓ) (hx2 : |x.2 - z.2| ≤ 6 * ℓ)
    (hy1 : |y.1 - z.1| ≤ 6 * ℓ) (hy2 : |y.2 - z.2| ≤ 6 * ℓ)
    (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d) :
    incr (sqBox z (4 ^ N * (8 * ℓ))) x y - incr (sqBox z (8 * ℓ)) x y ≤
      incrConst * d / ℓ := by
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (show 0 < ℓ by omega)
  have hd0 : (0 : ℝ) ≤ d := by positivity
  
  have hstep : ∀ i : ℕ,
      incr (sqBox z (4 ^ (i + 1) * (8 * ℓ))) x y - incr (sqBox z (4 ^ i * (8 * ℓ))) x y ≤
        48 ^ 2 * 2064 * ((d : ℝ) / ℓ) * (1 / 2) ^ i := by
    intro i
    refine (incr_concentric_step z ℓ hℓ i hx1 hx2 hy1 hy2 d hd1 hd2).trans ?_
    have hroot : Real.sqrt (d / ℓ) * Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ)) ≤
        ((d : ℝ) / ℓ) * (1 / 2) ^ i := by
      have e1 : ((d : ℝ) / (4 ^ i * (2 * ℓ) : ℕ)) = ((d : ℝ) / ℓ) * (1 / 4) ^ i * (1 / 2) := by
        push_cast
        rw [one_div_pow]
        field_simp
      have e2 : ((d : ℝ) / (4 ^ i * (2 * ℓ) : ℕ)) ≤ ((d : ℝ) / ℓ) * ((1 / 2) ^ i) ^ 2 := by
        rw [e1, ← pow_mul, show ((1 : ℝ) / 2) ^ (i * 2) = (1 / 4) ^ i by
          rw [mul_comm, pow_mul]; norm_num]
        have : (0 : ℝ) ≤ ((d : ℝ) / ℓ) * (1 / 4) ^ i := by positivity
        linarith
      have e3 : Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ)) ≤ Real.sqrt (d / ℓ) * (1 / 2) ^ i := by
        calc Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ))
            ≤ Real.sqrt (((d : ℝ) / ℓ) * ((1 / 2) ^ i) ^ 2) := Real.sqrt_le_sqrt e2
          _ = Real.sqrt (d / ℓ) * (1 / 2) ^ i := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      have e4 : Real.sqrt (d / ℓ) * Real.sqrt (d / ℓ) = (d : ℝ) / ℓ :=
        Real.mul_self_sqrt (by positivity)
      calc Real.sqrt (d / ℓ) * Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ))
          ≤ Real.sqrt (d / ℓ) * (Real.sqrt (d / ℓ) * (1 / 2) ^ i) := by
            gcongr
        _ = ((d : ℝ) / ℓ) * (1 / 2) ^ i := by rw [← mul_assoc, e4]
    calc 48 * (48 * 2064 * Real.sqrt (d / ℓ)) * Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ))
        = 48 ^ 2 * 2064 * (Real.sqrt (d / ℓ) * Real.sqrt (d / (4 ^ i * (2 * ℓ) : ℕ))) := by
          ring
      _ ≤ 48 ^ 2 * 2064 * (((d : ℝ) / ℓ) * (1 / 2) ^ i) := by gcongr
      _ = 48 ^ 2 * 2064 * ((d : ℝ) / ℓ) * (1 / 2) ^ i := by ring
  
  have hsum : ∀ N : ℕ, incr (sqBox z (4 ^ N * (8 * ℓ))) x y - incr (sqBox z (8 * ℓ)) x y ≤
      ∑ i ∈ range N, 48 ^ 2 * 2064 * ((d : ℝ) / ℓ) * (1 / 2) ^ i := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ]
      have := hstep N
      linarith
  have hgeom : ∑ i ∈ range N, 48 ^ 2 * 2064 * ((d : ℝ) / ℓ) * (1 / 2) ^ i ≤
      2 * (48 ^ 2 * 2064 * ((d : ℝ) / ℓ)) := by
    rw [← Finset.mul_sum]
    have hg : ∑ i ∈ range N, ((1 : ℝ) / 2) ^ i ≤ 2 := by
      have := sum_geometric_two_le N
      simpa [one_div] using this
    have h0 : (0 : ℝ) ≤ 48 ^ 2 * 2064 * ((d : ℝ) / ℓ) := by positivity
    nlinarith
  refine (hsum N).trans (hgeom.trans (le_of_eq ?_))
  unfold incrConst
  ring

end SupercriticalLQGUniqueness.B2.QPos.P4
