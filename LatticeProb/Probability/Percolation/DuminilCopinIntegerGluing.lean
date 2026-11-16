import LatticeProb.Probability.Percolation.VerticalJoinedProbability

/-!
# Gluing inclusive rectangle crossings

Harris' inequality combines joined square crossings into a crossing of the
surrounding rectangle for the independent critical bond law.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Site := LatticeModels.Site 2
private abbrev μ := Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
  bernoulliMeasure True False half)

private theorem shifted_leftSide (n : ℕ) :
    (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (leftSide (3 * n) (2 * n) : Set Site) = outerLeft n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter, mem_rectangle_iff] at hy
    simp only [outerLeft, Set.mem_ofPred_eq, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    omega
  · intro hx
    refine ⟨x - ![-(n : ℤ), -(n : ℤ)], ?_, sub_add_cancel _ _⟩
    simp only [outerLeft, Set.mem_ofPred_eq] at hx
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter, mem_rectangle_iff,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul, Nat.cast_ofNat]
    omega

private theorem shifted_rightSide (n : ℕ) :
    (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (rightSide (3 * n) (2 * n) : Set Site) = outerRight n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter, mem_rectangle_iff,
      Nat.cast_mul, Nat.cast_ofNat] at hy
    simp only [outerRight, Set.mem_ofPred_eq, Pi.add_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    omega
  · intro hx
    refine ⟨x - ![-(n : ℤ), -(n : ℤ)], ?_, sub_add_cancel _ _⟩
    simp only [outerRight, Set.mem_ofPred_eq] at hx
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter, mem_rectangle_iff,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul, Nat.cast_ofNat]
    omega

/-- Translation identifies the surrounding crossing probability with the inclusive rectangle. -/
theorem surrounding_crossing_probability (n : ℕ) :
    μ.real (crossingIn (surroundingRectangle n) (outerLeft n) (outerRight n)) =
      crossingProb half (3 * n) (2 * n) := by
  rw [← shifted_leftSide n, ← shifted_rightSide n, surroundingRectangle,
    crossingIn_probability_shift, crossingIn_probability]
  rfl

private theorem square_subset_centered (n : ℕ) : (rectangle n n : Set Site) ⊆ centeredSquare n := by
  intro x hx
  rw [Finset.mem_coe, centeredSquare, mem_centered_square]
  simp only [Finset.mem_coe, mem_rectangle_iff] at hx
  omega

private theorem mem_surrounding (n : ℕ) (x : Site) :
    x ∈ surroundingRectangle n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := by
  constructor
  · intro h
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp h
    simp only [mem_rectangle_iff] at hy
    simp only [Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Nat.cast_mul,
      Nat.cast_ofNat] at *
    omega
  · intro hx
    refine Finset.mem_image.mpr ⟨x - ![-(n : ℤ), -(n : ℤ)], ?_, sub_add_cancel _ _⟩
    simp only [mem_rectangle_iff, Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Nat.cast_mul, Nat.cast_ofNat]
    omega

private theorem square_subset_surrounding (n : ℕ) :
    (rectangle n n : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  rw [Finset.mem_coe, mem_surrounding]
  simp only [Finset.mem_coe, mem_rectangle_iff] at hx
  omega

private theorem centered_subset_surrounding (n : ℕ) :
    (centeredSquare n : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  rw [Finset.mem_coe, centeredSquare, mem_centered_square] at hx
  rw [Finset.mem_coe, mem_surrounding]
  omega

private theorem reflected_subset_surrounding (n : ℕ) :
    ((centeredSquare n).image (reflX n) : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [centeredSquare, mem_centered_square] at hy
  rw [Finset.mem_coe, mem_surrounding]
  simp only [reflX_apply_zero, reflX_apply_one]
  omega

/-- Two vertical joined crossings and a horizontal crossing cross the surrounding rectangle. -/
theorem crossing_of_vertical_joined_crossings (n : ℕ)
    {η : (LatticeModels.zdGraph 2).edgeSet → Prop}
    (hL : η ∈ joinedCrossingIn (rectangle n n) (centeredSquare n)
      (bottomSide n n) (topSide n n) (outerLeft n))
    (hR : η ∈ joinedCrossingIn (rectangle n n) ((centeredSquare n).image (reflX n))
      (bottomSide n n) (topSide n n) (outerRight n))
    (hH : η ∈ crossing n n) :
    η ∈ crossingIn (surroundingRectangle n) (outerLeft n) (outerRight n) := by
  let ω := extend (LatticeModels.zdGraph 2) η
  change ω ∈ joinedCrossing _ _ _ _ _ at hL hR
  have hH' : ω ∈ lrCrossing n n := (mem_crossing_iff n n η).mp hH
  change ω ∈ openCrossing _ _ _ at hH' ⊢
  obtain ⟨a, ha, b, hb, l, hl, hab, hal⟩ := hL
  obtain ⟨a', ha', b', hb', r, hr, hab', har⟩ := hR
  obtain ⟨c, hc, d, hd, hcd⟩ := hH'
  have hω : ω ⊆ (LatticeModels.zdGraph 2).edgeSet := extend_subset _ _
  obtain ⟨P, hPS, hPω⟩ := exists_walk_of_mem_openConnIn hω hab
  obtain ⟨P', hP'S, hP'ω⟩ := exists_walk_of_mem_openConnIn hω hab'
  obtain ⟨Q, hQS, hQω⟩ := exists_walk_of_mem_openConnIn hω hcd
  have hbox : ∀ {x y : Site} (P : (LatticeModels.zdGraph 2).Walk x y),
      (∀ z ∈ P.support, z ∈ (rectangle n n : Finset Site)) →
      ∀ z ∈ P.support, (0 : ℤ) ≤ z 0 ∧ z 0 ≤ n ∧ 0 ≤ z 1 ∧ z 1 ≤ n := by
    intro x y P h z hz
    exact mem_rectangle_iff.mp (h z hz)
  simp only [Finset.mem_coe, leftSide, rightSide, bottomSide, topSide,
    Finset.mem_filter] at ha hb ha' hb' hc hd
  obtain ⟨u, huQ, huP⟩ := exists_mem_support_of_crossing Q P
    (hbox Q hQS) (hbox P hPS) hc.2 hd.2 ha.2 hb.2
  obtain ⟨v, hvQ, hvP⟩ := exists_mem_support_of_crossing Q P'
    (hbox Q hQS) (hbox P' hP'S) hc.2 hd.2 ha'.2 hb'.2
  have c1 : ω ∈ openConnIn (surroundingRectangle n) l a :=
    openConnIn_mono (centered_subset_surrounding n) _ _ (by rwa [openConnIn_comm])
  have c2 : ω ∈ openConnIn (surroundingRectangle n) a u :=
    openConnIn_mono (square_subset_surrounding n) _ _
      (mem_openConnIn_of_mem_support P hPS hPω huP)
  have c3 : ω ∈ openConnIn (surroundingRectangle n) u v :=
    openConnIn_mono (square_subset_surrounding n) _ _ (PlanarDuality.openConnIn_trans
      (by rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support Q hQS hQω huQ)
      (mem_openConnIn_of_mem_support Q hQS hQω hvQ))
  have c4 : ω ∈ openConnIn (surroundingRectangle n) v a' :=
    openConnIn_mono (square_subset_surrounding n) _ _ (by
      rw [openConnIn_comm]; exact mem_openConnIn_of_mem_support P' hP'S hP'ω hvP)
  have c5 : ω ∈ openConnIn (surroundingRectangle n) a' r :=
    openConnIn_mono (reflected_subset_surrounding n) _ _ har
  exact ⟨l, hl, r, hr, PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans
    (PlanarDuality.openConnIn_trans (PlanarDuality.openConnIn_trans c1 c2) c3) c4) c5⟩

private theorem reflected_square (n : ℕ) :
    (rectangle n n).image (reflX n) = rectangle n n := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [mem_rectangle_iff, reflX_apply_zero, reflX_apply_one] at *
    omega
  · intro hx
    refine ⟨reflX n x, ?_, reflX_reflX _ _⟩
    simp only [mem_rectangle_iff, reflX_apply_zero, reflX_apply_one] at *
    omega

private theorem reflected_bottom (n : ℕ) :
    reflX n '' (bottomSide n n : Set Site) = bottomSide n n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [Finset.mem_coe, bottomSide, Finset.mem_filter, mem_rectangle_iff,
    reflX_apply_zero, reflX_apply_one]
  omega

private theorem reflected_top (n : ℕ) :
    reflX n '' (topSide n n : Set Site) = topSide n n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [Finset.mem_coe, topSide, Finset.mem_filter, mem_rectangle_iff,
    reflX_apply_zero, reflX_apply_one]
  omega

private theorem reflected_left (n : ℕ) : reflX n '' outerLeft n = outerRight n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [outerLeft, outerRight, Set.mem_ofPred_eq, reflX_apply_zero, reflX_apply_one]
  omega

/-- Reflection preserves the probability of a vertical joined crossing. -/
theorem vertical_joined_reflection_probability (n : ℕ) :
    μ.real (joinedCrossingIn (rectangle n n) ((centeredSquare n).image (reflX n))
      (bottomSide n n) (topSide n n) (outerRight n)) =
    μ.real (joinedCrossingIn (rectangle n n) (centeredSquare n)
      (bottomSide n n) (topSide n n) (outerLeft n)) := by
  have hswap : joinedCrossingIn (rectangle n n) (centeredSquare n)
      (topSide n n) (bottomSide n n) (outerLeft n) =
      joinedCrossingIn (rectangle n n) (centeredSquare n)
        (bottomSide n n) (topSide n n) (outerLeft n) := by
    unfold joinedCrossingIn
    rw [joinedCrossing_swap _ _ _ _ _ (square_subset_centered n)]
  simpa only [reflected_square, reflected_bottom, reflected_top, reflected_left, hswap] using
    joinedCrossingIn_probability_image_swap (reflX n) half (rectangle n n)
      (centeredSquare n) (topSide n n) (bottomSide n n) (outerLeft n)
      (square_subset_centered n)

/-- The critical inclusive `3n` by `2n` rectangle is crossed with probability at least `1/128`. -/
theorem one_div_128_le_integer_rectangle_crossing (n : ℕ) (hn : 1 ≤ n) :
    (1 / 128 : ℝ) ≤ crossingProb half (3 * n) (2 * n) := by
  classical
  let : LinearOrder Prop := Prop.linearOrder
  let L := joinedCrossingIn (rectangle n n) (centeredSquare n)
    (bottomSide n n) (topSide n n) (outerLeft n)
  let R := joinedCrossingIn (rectangle n n) ((centeredSquare n).image (reflX n))
    (bottomSide n n) (topSide n n) (outerRight n)
  let H := crossing n n
  have hL : (1 / 8 : ℝ) ≤ μ.real L := eighth_le_vertical_joined n hn
  have hH : (1 / 2 : ℝ) ≤ μ.real H := half_le_square_crossing n
  have hr : μ.real R = μ.real L := vertical_joined_reflection_probability n
  have hLR : μ.real L * μ.real R ≤ μ.real (L ∩ R) :=
    LatticeProb.infinitePi_harris _ (isUpperSet_joinedCrossingIn _ _ _ _ _)
      (isUpperSet_joinedCrossingIn _ _ _ _ _)
      (measurableSet_joinedCrossingIn _ _ _ _ _) (measurableSet_joinedCrossingIn _ _ _ _ _)
  have hLRH : μ.real (L ∩ R) * μ.real H ≤ μ.real ((L ∩ R) ∩ H) :=
    LatticeProb.infinitePi_harris _
      ((isUpperSet_joinedCrossingIn _ _ _ _ _).inter
        (isUpperSet_joinedCrossingIn _ _ _ _ _)) (isUpperSet_crossing n n)
      ((measurableSet_joinedCrossingIn _ _ _ _ _).inter
        (measurableSet_joinedCrossingIn _ _ _ _ _)) (measurableSet_crossing n n)
  have hsub : (L ∩ R) ∩ H ⊆
      crossingIn (surroundingRectangle n) (outerLeft n) (outerRight n) := by
    rintro η ⟨⟨hl, hr⟩, hh⟩
    exact crossing_of_vertical_joined_crossings n hl hr hh
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  rw [surrounding_crossing_probability] at hmono
  have hpos : (0 : ℝ) ≤ μ.real L := measureReal_nonneg
  have hposH : (0 : ℝ) ≤ μ.real H := measureReal_nonneg
  have hs : (0 : ℝ) ≤ (μ.real L) ^ 2 := sq_nonneg _
  rw [hr] at hLR
  nlinarith [mul_nonneg (sub_nonneg.mpr hLR) hposH,
    mul_nonneg (sub_nonneg.mpr hH) hs, sq_nonneg (μ.real L - 1 / 8)]

end EdgeCrossing
