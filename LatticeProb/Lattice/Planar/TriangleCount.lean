import LatticeProb.Lattice.Planar.Basic

/-!
# Counting the planar l1 triangle

The triangle is the integer l1 ball intersected with the right-hand cone.
Its upper and lower wings give exact even and odd cardinalities.
-/

namespace LatticeProb.Lattice.Planar

open Finset

/-- The nonnegative wing, parametrized by height and horizontal displacement. -/
def triangleWing (L : ℕ) : Finset Site :=
  ((range (L / 2 + 1)).sigma fun k => range (L - 2 * k + 1)).image
    (fun p => ((p.1 + p.2 : ℕ), (p.1 : ℤ)))

/-- Reflection in the horizontal axis. -/
def triangleReflect (z : Site) : Site := (z.1, -z.2)

/-- The closed l1 triangle of radius `L` in the right-hand cone. -/
def triangle (L : ℕ) : Finset Site :=
  triangleWing L ∪ (triangleWing L).image triangleReflect

/-- The wing parametrization is exactly the nonnegative half of the source triangle. -/
theorem mem_triangleWing (L : ℕ) (z : Site) :
    z ∈ triangleWing L ↔ 0 ≤ z.2 ∧ z.2 ≤ z.1 ∧ z.1 + z.2 ≤ L := by
  simp only [triangleWing, mem_image, mem_sigma, mem_range]
  constructor
  · rintro ⟨⟨k, t⟩, ⟨hk, ht⟩, rfl⟩
    dsimp at hk ht ⊢
    omega
  · rintro ⟨hy, hxy, hL⟩
    refine ⟨⟨z.2.toNat, (z.1 - z.2).toNat⟩, ⟨?_, ?_⟩, ?_⟩
    · dsimp
      have := Int.toNat_of_nonneg hy
      omega
    · dsimp
      have := Int.toNat_of_nonneg hy
      have := Int.toNat_of_nonneg (sub_nonneg.mpr hxy)
      omega
    · apply Prod.ext <;> simp only
      · have := Int.toNat_of_nonneg hy
        have := Int.toNat_of_nonneg (sub_nonneg.mpr hxy)
        push_cast
        omega
      · exact Int.toNat_of_nonneg hy

/-- Full literal membership characterization in integer coordinates. -/
theorem mem_triangle (L : ℕ) (z : Site) :
    z ∈ triangle L ↔ |z.1| + |z.2| ≤ (L : ℤ) ∧ |z.2| ≤ z.1 := by
  simp only [triangle, mem_union, mem_image]
  constructor
  · rintro (hz | ⟨w, hw, rfl⟩)
    · obtain ⟨hy, hxy, hL⟩ := (mem_triangleWing L z).mp hz
      rw [abs_of_nonneg hy, abs_of_nonneg (le_trans hy hxy)]
      exact ⟨hL, hxy⟩
    · obtain ⟨hy, hxy, hL⟩ := (mem_triangleWing L w).mp hw
      simpa only [triangleReflect, abs_neg, abs_of_nonneg hy,
        abs_of_nonneg (le_trans hy hxy)] using And.intro hL hxy
  · rintro ⟨hL, hxy⟩
    have hx : 0 ≤ z.1 := le_trans (abs_nonneg _) hxy
    rw [abs_of_nonneg hx] at hL
    by_cases hy : 0 ≤ z.2
    · left
      apply (mem_triangleWing L z).mpr
      simpa only [abs_of_nonneg hy] using And.intro hy (And.intro hxy hL)
    · right
      refine ⟨triangleReflect z, ?_, ?_⟩
      · apply (mem_triangleWing L _).mpr
        simp only [triangleReflect]
        rw [abs_of_neg (lt_of_not_ge hy)] at hL hxy
        exact ⟨by omega, hxy, hL⟩
      · simp only [triangleReflect, neg_neg]

private theorem wing_injective : Function.Injective
    (fun p : Sigma fun _ : ℕ => ℕ => (((p.1 + p.2 : ℕ) : ℤ), (p.1 : ℤ))) := by
  intro a b h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp at h₁ h₂
  have hk : a.1 = b.1 := by exact_mod_cast h₂
  have ht : a.2 = b.2 := by exact_mod_cast (show (a.2 : ℤ) = b.2 by omega)
  exact Sigma.ext hk (heq_of_eq ht)

/-- The cardinality of a wing is the sum of its horizontal row lengths. -/
theorem card_triangleWing (L : ℕ) :
    (triangleWing L).card = ∑ k ∈ range (L / 2 + 1), (L - 2 * k + 1) := by
  rw [triangleWing, card_image_of_injective _ wing_injective, card_sigma]
  simp only [card_range]

private theorem row_sum (n c : ℕ) :
    (∑ k ∈ range (n + 1), (2 * n - 2 * k + c)) = (n + 1) * (n + c) := by
  have hsum := sum_range_id_mul_two (n + 1)
  have hpoint : ∀ k ∈ range (n + 1),
      2 * n - 2 * k + c = 2 * n + c - 2 * k := by
    intro k hk
    simp only [mem_range] at hk
    omega
  rw [sum_congr rfl hpoint]
  rw [sum_tsub_distrib _ (by
    intro k hk
    simp only [mem_range] at hk
    omega), sum_const, ← mul_sum]
  simp only [card_range, smul_eq_mul]
  have : (n + 1) - 1 = n := by omega
  rw [this] at hsum
  have heq : (n + 1) * (2 * n + c) =
      2 * (∑ i ∈ range (n + 1), i) + (n + 1) * (n + c) := by
    nlinarith
  rw [heq, Nat.add_sub_cancel_left]

/-- Even-radius wings are squares in cardinality. -/
theorem card_triangleWing_even (m : ℕ) :
    (triangleWing (2 * m)).card = (m + 1) ^ 2 := by
  rw [card_triangleWing]
  simp only [Nat.mul_div_right, show 0 < 2 by omega]
  rw [row_sum m 1]
  ring

/-- Odd-radius wings have consecutive side lengths in cardinality. -/
theorem card_triangleWing_odd (m : ℕ) :
    (triangleWing (2 * m + 1)).card = (m + 1) * (m + 2) := by
  rw [card_triangleWing]
  have hd : (2 * m + 1) / 2 = m := by omega
  rw [hd]
  have hp : ∀ k ∈ range (m + 1),
      2 * m + 1 - 2 * k + 1 = 2 * m - 2 * k + 2 := by
    intro k hk
    simp only [mem_range] at hk
    omega
  rw [sum_congr rfl hp, row_sum m 2]

private theorem reflection_injective : Function.Injective triangleReflect := by
  intro a b h
  have := congrArg triangleReflect h
  simpa only [triangleReflect, neg_neg] using this

/-- The two wings overlap precisely on the horizontal axis segment. -/
theorem triangleWing_inter_reflect (L : ℕ) :
    triangleWing L ∩ (triangleWing L).image triangleReflect =
      (range (L + 1)).image (fun x : ℕ => ((x : ℤ), (0 : ℤ))) := by
  ext z
  simp only [mem_inter, mem_image]
  constructor
  · rintro ⟨hz, w, hw, heq⟩
    obtain ⟨hy, hxy, hL⟩ := (mem_triangleWing L z).mp hz
    obtain ⟨hwy, _, _⟩ := (mem_triangleWing L w).mp hw
    have he := congrArg Prod.snd heq
    simp only [triangleReflect] at he
    have hz0 : z.2 = 0 := by omega
    refine ⟨z.1.toNat, ?_, ?_⟩
    · simp only [mem_range]
      omega
    · apply Prod.ext
      · exact Int.toNat_of_nonneg (by omega)
      · exact hz0.symm
  · rintro ⟨x, hx, rfl⟩
    have hw : ((x : ℤ), (0 : ℤ)) ∈ triangleWing L := by
      apply (mem_triangleWing L _).mpr
      simp only [mem_range] at hx
      constructor
      · omega
      constructor <;> omega
    exact ⟨hw, _, hw, rfl⟩

/-- Adding the axis overlap recovers twice the wing cardinality. -/
theorem card_triangle_add_axis (L : ℕ) :
    (triangle L).card + (L + 1) = 2 * (triangleWing L).card := by
  have h := card_union_add_card_inter (triangleWing L)
    ((triangleWing L).image triangleReflect)
  rw [triangleWing_inter_reflect, card_image_of_injective _ reflection_injective] at h
  have hi : Function.Injective (fun x : ℕ => ((x : ℤ), (0 : ℤ))) := by
    intro x y hxy
    have he : (x : ℤ) = y := congrArg Prod.fst hxy
    exact_mod_cast he
  rw [card_image_of_injective _ hi, card_range] at h
  change (triangle L).card + (L + 1) = _ at h
  omega

/-- Exact cardinality at an even radius. -/
theorem card_triangle_even (m : ℕ) :
    (triangle (2 * m)).card = 2 * m ^ 2 + 2 * m + 1 := by
  have h := card_triangle_add_axis (2 * m)
  rw [card_triangleWing_even] at h
  nlinarith

/-- Exact cardinality at an odd radius. -/
theorem card_triangle_odd (m : ℕ) :
    (triangle (2 * m + 1)).card = 2 * (m + 1) ^ 2 := by
  have h := card_triangle_add_axis (2 * m + 1)
  rw [card_triangleWing_odd] at h
  nlinarith

/-- The radius-zero triangle consists of one lattice site. -/
theorem card_triangle_zero : (triangle 0).card = 1 := by
  convert card_triangle_even 0 using 1
  norm_num

/-- The radius-one triangle has two sites. -/
theorem card_triangle_one : (triangle 1).card = 2 := by
  simpa only [Nat.mul_zero, Nat.zero_add, zero_add, one_pow, mul_one]
    using card_triangle_odd 0

/-- The radius-two triangle has five sites. -/
theorem card_triangle_two : (triangle 2).card = 5 := by
  convert card_triangle_even 1 using 1
  norm_num

end LatticeProb.Lattice.Planar
