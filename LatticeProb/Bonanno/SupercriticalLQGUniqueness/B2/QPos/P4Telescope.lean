/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P4Telescope at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4Gradient
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4LocalGreen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P4GreenBridge

 















set_option autoImplicit false
noncomputable section

open Finset

namespace SupercriticalLQGUniqueness.B2.QPos.P4

open P3

 
def sqBox (z : ℤ × ℤ) (r : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.Ioo (z.1 - r) (z.1 + r)) ×ˢ (Finset.Ioo (z.2 - r) (z.2 + r))

theorem mem_sqBox {z c : ℤ × ℤ} {r : ℤ} : c ∈ sqBox z r ↔ |c.1 - z.1| < r ∧ |c.2 - z.2| < r := by
  unfold sqBox
  rw [Finset.mem_product, Finset.mem_Ioo, Finset.mem_Ioo, abs_lt, abs_lt]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem sqBox_mono {z : ℤ × ℤ} {r r' : ℤ} (h : r ≤ r') : sqBox z r ⊆ sqBox z r' := by
  intro c hc
  rw [mem_sqBox] at hc ⊢
  exact ⟨by linarith [hc.1], by linarith [hc.2]⟩

 

theorem incr_step_le (U U' : Finset (ℤ × ℤ)) (hUU' : U ⊆ U') (z1 R : ℤ)
    (hstrip : ∀ c ∈ U, |c.1 - z1| < R) {x y : ℤ × ℤ} (hx : x ∈ U) (hy : y ∈ U)
    {M : ℝ} (hM : ∀ c, c ∉ U → |green U' c x - green U' c y| ≤ M)
    (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d) (m : ℕ) (hm : 2 ≤ m)
    (hbx : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ U)
    (hby : ∀ c : ℤ × ℤ, |c.1 - y.1| < m → |c.2 - y.2| < m → c ∈ U) :
    incr U' x y - incr U x y ≤ 48 * M * Real.sqrt (d / m) := by
  set F : ℤ × ℤ → ℝ := fun c =>
    (green U' c x - green U' c y) - (green U c x - green U c y) with hF
  have hharm : ∀ a ∈ U, F a = avg F a := by
    intro a ha
    have haU' : a ∈ U' := hUU' ha
    have e1 := green_eq haU' x
    have e2 := green_eq haU' y
    have e3 := green_eq ha x
    have e4 := green_eq ha y
    have hp1 : pt U' x a = pt U x a := by
      unfold pt; simp [hx, hUU' hx]
    have hp2 : pt U' y a = pt U y a := by
      unfold pt; simp [hy, hUU' hy]
    simp only [hF]
    rw [avg_sub, avg_sub, avg_sub, e1, e2, e3, e4, hp1, hp2]
    ring
  have hout : ∀ c, c ∉ U → |F c| ≤ M := by
    intro c hc
    simp only [hF]
    rw [green_of_not_mem_left hc, green_of_not_mem_left hc, sub_zero, sub_zero]
    exact hM c hc
  have hglob := abs_le_of_harmonic U z1 R hstrip hharm hout
  have hgrad := harmonic_diff_sqrt U hharm hglob d hd1 hd2 m hm hbx hby
  have hid : F x - F y = incr U' x y - incr U x y := by
    simp only [hF, incr]
    ring
  rw [← hid]
  exact (le_abs_self _).trans hgrad

 

theorem green_diff_le (U' V Vb : Finset (ℤ × ℤ)) (hVU' : V ⊆ U') (hVVb : V ⊆ Vb)
    (hVb : ∀ a ∈ V, ∀ s : Bool × Bool, a + stepVec s ∈ Vb)
    {w : ℤ × ℤ} (hw : w ∉ V) {M : ℝ} (hM : ∀ a ∈ Vb, green U' a w ≤ M)
    {x y : ℤ × ℤ} (hx : x ∈ V) (hy : y ∈ V)
    (d : ℕ) (hd1 : |x.1 - y.1| ≤ d) (hd2 : |x.2 - y.2| ≤ d) (m : ℕ) (hm : 2 ≤ m)
    (hbx : ∀ c : ℤ × ℤ, |c.1 - x.1| < m → |c.2 - x.2| < m → c ∈ V)
    (hby : ∀ c : ℤ × ℤ, |c.1 - y.1| < m → |c.2 - y.2| < m → c ∈ V) :
    |green U' x w - green U' y w| ≤ 48 * M * Real.sqrt (d / m) := by
  classical
  set H : ℤ × ℤ → ℝ := fun a => if a ∈ Vb then green U' a w else 0 with hHdef
  have hharm : ∀ a ∈ V, H a = avg H a := by
    intro a ha
    have hab : a ∈ Vb := hVVb ha
    have haw : a ≠ w := fun h => hw (h ▸ ha)
    have e := green_eq (hVU' ha) w
    have hpt : pt U' w a = 0 := by unfold pt; rw [if_neg (fun h => haw h.1)]
    rw [hpt, zero_add] at e
    simp only [hHdef, if_pos hab]
    rw [e]
    unfold avg
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    dsimp only
    rw [if_pos (hVb a ha s)]
  have hM0 : 0 ≤ M := (green_nonneg U' x w).trans (hM x (hVVb hx))
  have hglob : ∀ c, |H c| ≤ M := by
    intro c
    simp only [hHdef]
    split_ifs with hc
    · rw [abs_of_nonneg (green_nonneg U' c w)]; exact hM c hc
    · rw [abs_zero]; exact hM0
  have hgrad := harmonic_diff_sqrt V hharm hglob d hd1 hd2 m hm hbx hby
  have hHx : H x = green U' x w := by simp only [hHdef, if_pos (hVVb hx)]
  have hHy : H y = green U' y w := by simp only [hHdef, if_pos (hVVb hy)]
  rw [← hHx, ← hHy]
  exact hgrad

end SupercriticalLQGUniqueness.B2.QPos.P4
