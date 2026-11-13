import LatticeProb.Sandpile.Toppling

/-!
# Radius bound for a cubical FdBR configuration

Let `w ≥ 0` be a function on `ℤ^d` whose positive set is the box of radius `r`,
and let `s0 = (2d - 2) + N δ₀`. If `s0 + Δw < 2d` everywhere, then
`((N + 2d - 2)^(1/d) - 3) / 2 ≤ r`.

The excess `e = s0 + Δw - (2d - 2)` sums to `N` over the box of radius `r + 1`,
because `Δw` sums to zero there. Each value of `e` is at most `1`. For `d ≥ 2`,
`e` vanishes at the `2^d` corners of that box, which gives `N + 2d - 2 ≤ (2r+3)^d`.
For `d = 1` the count of the box alone gives the same bound.
-/

namespace LatticeProb.Sandpile

open LatticeProb

/-- The box of radius `r` in `ℤ^d`, as a finite set. -/
def radiusBox (d r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(r : ℤ)) (r : ℤ)

/-- The corners of the box of radius `r`: every coordinate is `±(r + 1)`. -/
def cornerBox (d r : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun _ : Fin d => ({-((r : ℤ) + 1), (r : ℤ) + 1} : Finset ℤ)

theorem mem_radiusBox {d r : ℕ} {x : Site d} :
    x ∈ radiusBox d r ↔ ∀ i, |x i| ≤ (r : ℤ) := by
  simp [radiusBox, Fintype.mem_piFinset, abs_le]

theorem mem_cornerBox {d r : ℕ} {x : Site d} :
    x ∈ cornerBox d r ↔ ∀ i, x i = -((r : ℤ) + 1) ∨ x i = (r : ℤ) + 1 := by
  simp [cornerBox, Fintype.mem_piFinset]

theorem card_radiusBox (d r : ℕ) : (radiusBox d r).card = (2 * r + 1) ^ d := by
  rw [radiusBox, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem card_cornerBox (d r : ℕ) : (cornerBox d r).card = 2 ^ d := by
  have hne : -((r : ℤ) + 1) ≠ (r : ℤ) + 1 := by omega
  rw [cornerBox, Fintype.card_piFinset]
  simp only [Finset.card_pair hne, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem radiusBox_subset_succ (d r : ℕ) : radiusBox d r ⊆ radiusBox d (r + 1) := by
  intro y hy
  rw [mem_radiusBox] at hy ⊢
  intro j
  exact (hy j).trans (by omega)

theorem cornerBox_subset (d r : ℕ) : cornerBox d r ⊆ radiusBox d (r + 1) := by
  intro x hx
  rw [mem_cornerBox] at hx
  rw [mem_radiusBox]
  intro i
  rw [abs_le]
  rcases hx i with h | h <;> omega

theorem mem_radiusBox_succ_add_unit {d r : ℕ} {y : Site d} (hy : y ∈ radiusBox d r)
    (i : Fin d) : y + unit i ∈ radiusBox d (r + 1) := by
  rw [mem_radiusBox] at hy ⊢
  intro j
  have hj := abs_le.mp (hy j)
  rw [abs_le]
  by_cases h : j = i
  · subst h
    simp only [Pi.add_apply, unit, Pi.single_eq_same]
    omega
  · simp only [Pi.add_apply, unit, Pi.single_apply, h, ite_false, add_zero]
    omega

theorem mem_radiusBox_succ_sub_unit {d r : ℕ} {y : Site d} (hy : y ∈ radiusBox d r)
    (i : Fin d) : y - unit i ∈ radiusBox d (r + 1) := by
  rw [mem_radiusBox] at hy ⊢
  intro j
  have hj := abs_le.mp (hy j)
  rw [abs_le]
  by_cases h : j = i
  · subst h
    simp only [Pi.sub_apply, unit, Pi.single_eq_same]
    omega
  · simp only [Pi.sub_apply, unit, Pi.single_apply, h, ite_false, sub_zero]
    omega

/-- Translating the summand by a vector `u` that maps the box of radius `r` into the
box of radius `r + 1` leaves the sum over the box of radius `r + 1` unchanged, when the
summand vanishes outside the box of radius `r`. -/
theorem sum_radiusBox_succ_add {d r : ℕ} (f : Site d → ℤ)
    (hf : ∀ y, y ∉ radiusBox d r → f y = 0) (u : Site d)
    (hu : ∀ y ∈ radiusBox d r, y - u ∈ radiusBox d (r + 1)) :
    ∑ x ∈ radiusBox d (r + 1), f (x + u) = ∑ x ∈ radiusBox d (r + 1), f x := by
  refine Finset.sum_bij_ne_zero (fun x _ _ => x + u) ?_ ?_ ?_ ?_
  · intro x _ hne
    have hK : x + u ∈ radiusBox d r := by
      by_contra h
      exact hne (hf _ h)
    exact radiusBox_subset_succ d r hK
  · intro a _ _ b _ _ hab
    exact add_right_cancel hab
  · intro b hb hne
    have hbK : b ∈ radiusBox d r := by
      by_contra h
      exact hne (hf _ h)
    exact ⟨b - u, hu b hbK, by rw [sub_add_cancel]; exact hne, sub_add_cancel b u⟩
  · intro a _ _
    rfl

/-- The discrete Laplacian sums to zero over the box of radius `r + 1` when it
vanishes outside the box of radius `r`. -/
theorem sum_radiusBox_lap {d r : ℕ} (w : Site d → ℤ)
    (hw : ∀ y, y ∉ radiusBox d r → w y = 0) :
    ∑ x ∈ radiusBox d (r + 1), lap w x = 0 := by
  have hshift : ∀ i : Fin d, ∑ x ∈ radiusBox d (r + 1),
      (w (x + unit i) + w (x - unit i)) = 2 * ∑ x ∈ radiusBox d (r + 1), w x := by
    intro i
    rw [Finset.sum_add_distrib]
    have h1 := sum_radiusBox_succ_add w hw (unit i)
      (fun y hy => mem_radiusBox_succ_sub_unit hy i)
    have h2 := sum_radiusBox_succ_add w hw (-unit i)
      (fun y hy => by rw [sub_neg_eq_add]; exact mem_radiusBox_succ_add_unit hy i)
    simp only [sub_eq_add_neg]
    rw [h1, h2]
    ring
  simp only [lap, nbrSumZ]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp only [hshift, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← Finset.mul_sum]
  ring

theorem add_unit_apply_of_ne {d : ℕ} {x : Site d} {i j : Fin d} (h : j ≠ i) :
    (x + unit i) j = x j := by
  simp [unit, h]

theorem sub_unit_apply_of_ne {d : ℕ} {x : Site d} {i j : Fin d} (h : j ≠ i) :
    (x - unit i) j = x j := by
  simp [unit, h]

/-- A point whose `j`-th coordinate is that of a corner lies outside the box of radius `r`. -/
theorem not_mem_radiusBox_of_corner {d r : ℕ} {x y : Site d} (hx : x ∈ cornerBox d r)
    (j : Fin d) (hyj : y j = x j) : y ∉ radiusBox d r := by
  intro hy
  rw [mem_radiusBox] at hy
  have h1 := abs_le.mp (hy j)
  rw [mem_cornerBox] at hx
  rcases hx j with h | h <;> omega

theorem lap_eq_zero_of_mem_corner {d r : ℕ} {w : Site d → ℤ}
    (hw : ∀ y, y ∉ radiusBox d r → w y = 0) (hd : 2 ≤ d) {x : Site d}
    (hx : x ∈ cornerBox d r) : lap w x = 0 := by
  have hcard : 1 < Fintype.card (Fin d) := by
    rw [Fintype.card_fin]
    omega
  have hsum : ∀ i : Fin d, w (x + unit i) + w (x - unit i) = 0 := by
    intro i
    obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
    rw [hw _ (not_mem_radiusBox_of_corner hx j (add_unit_apply_of_ne hj)),
      hw _ (not_mem_radiusBox_of_corner hx j (sub_unit_apply_of_ne hj)), add_zero]
  have h0 : w x = 0 := hw x (not_mem_radiusBox_of_corner hx ⟨0, by omega⟩ rfl)
  have hnbr : nbrSumZ w x = 0 := by
    unfold nbrSumZ
    exact Finset.sum_eq_zero fun i _ => hsum i
  simp only [lap, hnbr, h0, mul_zero, sub_zero]

theorem corner_ne_zero {d r : ℕ} {x : Site d} (hx : x ∈ cornerBox d r) (hd : 1 ≤ d) :
    x ≠ 0 := by
  intro h
  rw [mem_cornerBox] at hx
  have h0 := hx ⟨0, by omega⟩
  rw [h, Pi.zero_apply] at h0
  omega

theorem two_mul_sub_two_le_pow {d : ℕ} (h : 2 ≤ d) : (2 : ℤ) * d - 2 ≤ 2 ^ d := by
  induction d, h using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
    rw [pow_succ]
    push_cast
    linarith

/-- The radius bound for an FdBR configuration with `N` chips at the origin on the
background `2d - 2`, when the positive set of `w` is the box of radius `r`. -/
theorem fdbr_radius_bound {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (s0 : Site d → ℤ)
    (hs0 : ∀ x, s0 x = (2 * (d : ℤ) - 2) + (N : ℤ) * dirac 0 x)
    (w : Site d → ℤ) (hw0 : ∀ x, 0 ≤ w x) (r : ℕ)
    (hsupp : {x : Site d | 0 < w x} = {x : Site d | ∀ i : Fin d, |x i| ≤ (r : ℤ)})
    (hstab : ∀ x, s0 x + lap w x < 2 * (d : ℤ)) :
    (((N : ℝ) + 2 * (d : ℝ) - 2) ^ (1 / (d : ℝ)) - 3) / 2 ≤ (r : ℝ) := by
  have hw : ∀ y, y ∉ radiusBox d r → w y = 0 := by
    intro y hy
    have hnpos : ¬ (0 < w y) := by
      intro hpos
      apply hy
      rw [mem_radiusBox]
      have hmem : y ∈ {x : Site d | 0 < w x} := hpos
      rw [hsupp] at hmem
      exact hmem
    exact le_antisymm (not_lt.mp hnpos) (hw0 y)
  have hsumB : ∑ x ∈ radiusBox d (r + 1), (s0 x + lap w x - (2 * (d : ℤ) - 2)) = (N : ℤ) := by
    have h1 : ∀ x, s0 x + lap w x - (2 * (d : ℤ) - 2) = (N : ℤ) * dirac 0 x + lap w x :=
      fun x => by rw [hs0 x]; ring
    have h0mem : (0 : Site d) ∈ radiusBox d (r + 1) :=
      mem_radiusBox.mpr fun i => by simp only [Pi.zero_apply, abs_zero]; positivity
    have hdirac : ∑ x ∈ radiusBox d (r + 1), dirac (0 : Site d) x = 1 := by
      simp [dirac, h0mem]
    simp only [h1]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdirac, sum_radiusBox_lap w hw]
    ring
  have he_le : ∀ x, s0 x + lap w x - (2 * (d : ℤ) - 2) ≤ 1 := fun x => by
    have := hstab x
    omega
  have hBcard : ((radiusBox d (r + 1)).card : ℤ) = (2 * (r : ℤ) + 3) ^ d := by
    rw [card_radiusBox, show 2 * (r + 1) + 1 = 2 * r + 3 by ring]
    push_cast
    ring
  have hcount : (N : ℤ) + 2 * (d : ℤ) - 2 ≤ (2 * (r : ℤ) + 3) ^ d := by
    rcases Nat.lt_or_ge d 2 with h2 | h2
    · obtain rfl : d = 1 := by omega
      have hle : ∑ x ∈ radiusBox 1 (r + 1), (s0 x + lap w x - (2 * ((1 : ℕ) : ℤ) - 2))
          ≤ ∑ _x ∈ radiusBox 1 (r + 1), (1 : ℤ) :=
        Finset.sum_le_sum fun x _ => he_le x
      rw [hsumB, Finset.sum_const, nsmul_eq_mul, mul_one] at hle
      rw [pow_one]
      have hB1 : ((radiusBox 1 (r + 1)).card : ℤ) = 2 * (r : ℤ) + 3 := by
        rw [hBcard, pow_one]
      push_cast
      linarith
    · have hC0 : ∀ x ∈ cornerBox d r, s0 x + lap w x - (2 * (d : ℤ) - 2) = 0 := by
        intro x hx
        rw [hs0 x, lap_eq_zero_of_mem_corner hw h2 hx,
          dirac_of_ne (corner_ne_zero hx hd)]
        ring
      have hsplit := Finset.sum_sdiff (cornerBox_subset d r)
        (f := fun x => s0 x + lap w x - (2 * (d : ℤ) - 2))
      have hCzero : ∑ x ∈ cornerBox d r, (s0 x + lap w x - (2 * (d : ℤ) - 2)) = 0 :=
        Finset.sum_eq_zero hC0
      have hbound : ∑ x ∈ radiusBox d (r + 1) \ cornerBox d r,
          (s0 x + lap w x - (2 * (d : ℤ) - 2))
          ≤ ((radiusBox d (r + 1) \ cornerBox d r).card : ℤ) := by
        have hle : ∑ x ∈ radiusBox d (r + 1) \ cornerBox d r,
            (s0 x + lap w x - (2 * (d : ℤ) - 2))
            ≤ ∑ _x ∈ radiusBox d (r + 1) \ cornerBox d r, (1 : ℤ) :=
          Finset.sum_le_sum fun x _ => he_le x
        rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
        exact hle
      have hcardsplit := Finset.card_sdiff_add_card_eq_card (cornerBox_subset d r)
      have hcz : ((radiusBox d (r + 1) \ cornerBox d r).card : ℤ)
          + ((cornerBox d r).card : ℤ) = ((radiusBox d (r + 1)).card : ℤ) := by
        exact_mod_cast hcardsplit
      rw [card_cornerBox] at hcz
      push_cast at hcz
      have h2d := two_mul_sub_two_le_pow h2
      rw [hsumB] at hsplit
      linarith
  have hX : (N : ℝ) + 2 * (d : ℝ) - 2 ≤ (2 * (r : ℝ) + 3) ^ d := by
    have h := (Int.cast_le (R := ℝ)).mpr hcount
    push_cast at h
    linarith
  have hX0 : 0 ≤ (N : ℝ) + 2 * (d : ℝ) - 2 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hd0 : d ≠ 0 := by omega
  have hpow : ((2 * (r : ℝ) + 3) ^ d) ^ ((d : ℝ)⁻¹) = 2 * (r : ℝ) + 3 :=
    Real.pow_rpow_inv_natCast (by positivity) hd0
  have hle := Real.rpow_le_rpow hX0 hX (by positivity : (0 : ℝ) ≤ (d : ℝ)⁻¹)
  rw [hpow] at hle
  rw [one_div]
  linarith

end LatticeProb.Sandpile
