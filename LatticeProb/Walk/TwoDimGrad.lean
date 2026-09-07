/-
The two-dimensional kernel factorizes in the rotated coordinates, and the
mixed same-parity shift reduces to the one-dimensional gradient.

Put `s = x + y` and `t = x - y`.  A step of the simple walk on `ℤ²` changes
`(s,t)` by one of `(±1, ±1)`, so `s` and `t` are INDEPENDENT one-dimensional
walks of the same length, and

    p_m(x,y) = p^1_m(x+y) · p^1_m(x-y) .

The mixed shift `z ↦ z + (1,1)` is `s ↦ s + 2`, `t ↦ t`, so it moves ONE factor,
and the total variation distance it produces is exactly the one-dimensional
two-step gradient.  The parity constraint `s ≡ t (mod 2)` cutting out the image
of the rotation costs nothing, because both factors already live on the parity
class of `m`.

This is the smallest genuine case of the same-parity gradient of
`ssec:green-estimates`, and it is the case the standard-basis coordinate
schedule cannot reach.
-/
import Mathlib
import LatticeProb.Walk.OneDimGrad

noncomputable section

namespace LatticeProb

open Finset

/-! ### The two-dimensional recursion and the factorization -/

theorem srwHeat_two_succ (m : ℕ) (x y : ℤ) :
    srwHeat 2 (m + 1) ![x, y]
      = (srwHeat 2 m ![x - 1, y] + srwHeat 2 m ![x + 1, y]
          + srwHeat 2 m ![x, y - 1] + srwHeat 2 m ![x, y + 1]) / 4 := by
  rw [srwHeat_succ_eq_sum_dir]
  have h0t : (![x, y] : Site 2) + dirVec ((0, true) : Dir 2) = ![x + 1, y] := by
    funext i; fin_cases i <;> simp [dirVec]
  have h0f : (![x, y] : Site 2) + dirVec ((0, false) : Dir 2) = ![x - 1, y] := by
    funext i; fin_cases i <;> simp [dirVec, sub_eq_add_neg]
  have h1t : (![x, y] : Site 2) + dirVec ((1, true) : Dir 2) = ![x, y + 1] := by
    funext i; fin_cases i <;> simp [dirVec]
  have h1f : (![x, y] : Site 2) + dirVec ((1, false) : Dir 2) = ![x, y - 1] := by
    funext i; fin_cases i <;> simp [dirVec, sub_eq_add_neg]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fintype.sum_bool]
  rw [h0t, h0f, h1t, h1f]
  norm_num
  ring

theorem vec2_eq_zero_iff (x y : ℤ) : (![x, y] : Site 2) = 0 ↔ (x = 0 ∧ y = 0) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩
    funext i; fin_cases i <;> simp

/-- **The two-dimensional kernel factorizes in the rotated coordinates**:
`p_m(x,y) = p^1_m(x+y) p^1_m(x-y)`.  The two rotated coordinates are
independent one-dimensional walks of the same length, because a step of the
plane walk changes them by one of `(±1,±1)` uniformly. -/
theorem srwHeat_two_factor : ∀ (m : ℕ) (x y : ℤ),
    srwHeat 2 m ![x, y] = S1 m (x + y) * S1 m (x - y) := by
  intro m
  induction m with
  | zero =>
      intro x y
      rw [srwHeat_zero, S1_zero, S1_zero]
      by_cases h : x = 0 ∧ y = 0
      · obtain ⟨rfl, rfl⟩ := h
        rw [if_pos ((vec2_eq_zero_iff 0 0).mpr ⟨rfl, rfl⟩)]
        norm_num
      · rw [if_neg (fun hc => h ((vec2_eq_zero_iff x y).mp hc))]
        have hne : ¬ (x + y = 0 ∧ x - y = 0) := by
          rintro ⟨ha, hb⟩
          exact h ⟨by omega, by omega⟩
        rcases not_and_or.mp hne with hc | hc
        · rw [if_neg hc]; ring
        · rw [if_neg hc]; ring
  | succ m ih =>
      intro x y
      rw [srwHeat_two_succ, ih, ih, ih, ih, S1_succ, S1_succ]
      have e1 : x - 1 + y = x + y - 1 := by ring
      have e2 : x - 1 - y = x - y - 1 := by ring
      have e3 : x + 1 + y = x + y + 1 := by ring
      have e4 : x + 1 - y = x - y + 1 := by ring
      have e5 : x + (y - 1) = x + y - 1 := by ring
      have e6 : x - (y - 1) = x - y + 1 := by ring
      have e7 : x + (y + 1) = x + y + 1 := by ring
      have e8 : x - (y + 1) = x - y - 1 := by ring
      rw [e1, e2, e3, e4, e5, e6, e7, e8]
      ring

/-! ### The mixed same-parity gradient in the plane -/

theorem vec2_eta (w : Site 2) : (![w 0, w 1] : Site 2) = w := by
  funext i; fin_cases i <;> simp

theorem vec2_add_one_one (w : Site 2) :
    w + (![1, 1] : Site 2) = ![w 0 + 1, w 1 + 1] := by
  funext i; fin_cases i <;> simp

/-- **The mixed same-parity gradient of the plane walk.**
`∑_z |p_m(z) - p_m(z + (1,1))| ≤ C m^{-1/2}`, the two-dimensional case of
`eq:rw-tv-gradient`.  The shift moves exactly one of the two rotated
coordinates, so the sum is the one-dimensional two-step gradient times the total
mass of the other coordinate. -/
theorem exists_tsum_srwHeat_two_grad_le :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      ∑' w : Site 2, |srwHeat 2 m w - srwHeat 2 m (w + ![1, 1])|
        ≤ C / Real.sqrt (m : ℝ) := by
  classical
  obtain ⟨C, hC, hgrad⟩ := exists_tsum_abs_S1_shift_le
  refine ⟨C, hC, fun m hm => ?_⟩
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
  -- the summand in the rotated coordinates
  have hterm : ∀ w : Site 2, |srwHeat 2 m w - srwHeat 2 m (w + ![1, 1])|
      = S1 m (w 0 - w 1) * |S1 m (w 0 + w 1) - S1 m (w 0 + w 1 + 2)| := by
    intro w
    rw [← vec2_eta w, vec2_add_one_one, srwHeat_two_factor, srwHeat_two_factor]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have e1 : w 0 + 1 + (w 1 + 1) = w 0 + w 1 + 2 := by ring
    have e2 : w 0 + 1 - (w 1 + 1) = w 0 - w 1 := by ring
    rw [e1, e2, ← sub_mul, abs_mul, abs_of_nonneg (S1_nonneg m (w 0 - w 1))]
    ring
  refine Real.tsum_le_of_sum_le (fun w => abs_nonneg _) fun F => ?_
  rw [Finset.sum_congr rfl fun w _ => hterm w]
  -- the rotation is injective, so the sum is below a product of two sums
  set G : Finset (ℤ × ℤ) := F.image (fun w : Site 2 => (w 0 + w 1, w 0 - w 1)) with hG
  have hinj : ∀ a ∈ F, ∀ b ∈ F,
      ((a 0 + a 1, a 0 - a 1) : ℤ × ℤ) = (b 0 + b 1, b 0 - b 1) → a = b := by
    intro a _ b _ h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    funext i
    fin_cases i
    · show a 0 = b 0; omega
    · show a 1 = b 1; omega
  have hsum : ∑ w ∈ F, S1 m (w 0 - w 1) * |S1 m (w 0 + w 1) - S1 m (w 0 + w 1 + 2)|
      = ∑ p ∈ G, S1 m p.2 * |S1 m p.1 - S1 m (p.1 + 2)| := by
    rw [hG, Finset.sum_image hinj]
  rw [hsum]
  have hsub : G ⊆ (G.image Prod.fst) ×ˢ (G.image Prod.snd) := fun p hp =>
    Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hnn : ∀ p : ℤ × ℤ, 0 ≤ S1 m p.2 * |S1 m p.1 - S1 m (p.1 + 2)| :=
    fun p => mul_nonneg (S1_nonneg _ _) (abs_nonneg _)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p).trans ?_
  rw [Finset.sum_product]
  have hrow : ∀ s ∈ G.image Prod.fst,
      ∑ t ∈ G.image Prod.snd, S1 m t * |S1 m s - S1 m (s + 2)|
        ≤ |S1 m s - S1 m (s + 2)| := by
    intro s _
    rw [← Finset.sum_mul]
    have h1 := sum_finset_S1_le m (G.image Prod.snd)
    nlinarith [abs_nonneg (S1 m s - S1 m (s + 2)), h1,
      Finset.sum_nonneg (fun t (_ : t ∈ G.image Prod.snd) => S1_nonneg m t)]
  refine (Finset.sum_le_sum hrow).trans ?_
  exact (Summable.sum_le_tsum _ (fun s _ => abs_nonneg _)
    (summable_abs_S1_shift m)).trans (hgrad m hm)

end LatticeProb
