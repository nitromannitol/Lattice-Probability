import LatticeProb.Probability.Percolation.JoinedCrossingSymmetry
import LatticeProb.Probability.Percolation.TranslatedSquareCrossing

/-!
# Reflection and gluing of joined crossings

A vertical square crossing joins two horizontal crossings connected to opposite sides
of a surrounding rectangle. The joined events have equal product probabilities.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

private abbrev Site := LatticeModels.Site 2

/-- The square `[-n,n]²` in the integer lattice. -/
def centeredSquare (n : ℕ) : Finset Site :=
  (rectangle (2 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)])

/-- The rectangle `[-n,2n] × [-n,n]` in the integer lattice. -/
def surroundingRectangle (n : ℕ) : Finset Site :=
  (rectangle (3 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)])

/-- The left boundary of the centered square. -/
def outerLeft (n : ℕ) : Set Site :=
  {x | x 0 = -(n : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n}

/-- The right boundary of the surrounding rectangle. -/
def outerRight (n : ℕ) : Set Site :=
  {x | x 0 = 2 * (n : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n}

private theorem mem_centeredSquare (n : ℕ) (x : Site) :
    x ∈ centeredSquare n ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := by
  exact mem_centered_square n x

private theorem mem_surroundingRectangle (n : ℕ) (x : Site) :
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

private theorem square_subset_centered (n : ℕ) :
    (rectangle n n : Set Site) ⊆ centeredSquare n := by
  intro x hx
  rw [Finset.mem_coe, mem_centeredSquare]
  simp only [Finset.mem_coe, mem_rectangle_iff] at hx
  omega

private theorem square_subset_surrounding (n : ℕ) :
    (rectangle n n : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  rw [Finset.mem_coe, mem_surroundingRectangle]
  simp only [Finset.mem_coe, mem_rectangle_iff] at hx
  omega

private theorem centered_subset_surrounding (n : ℕ) :
    (centeredSquare n : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  rw [Finset.mem_coe, mem_centeredSquare] at hx
  rw [Finset.mem_coe, mem_surroundingRectangle]
  omega

private theorem reflected_subset_surrounding (n : ℕ) :
    ((centeredSquare n).image (reflX n) : Set Site) ⊆ surroundingRectangle n := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_centeredSquare] at hy
  rw [Finset.mem_coe, mem_surroundingRectangle]
  simp only [reflX_apply_zero, reflX_apply_one]
  omega

/-- The reflected square is `[0,2n] × [-n,n]`. -/
theorem mem_reflected_centeredSquare (n : ℕ) (x : Site) :
    x ∈ (centeredSquare n).image (reflX n) ↔
      (0 : ℤ) ≤ x 0 ∧ x 0 ≤ 2 * (n : ℤ) ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := by
  rw [← Finset.mem_coe, Finset.coe_image, mem_image_reflX_iff, Finset.mem_coe,
    mem_centeredSquare]
  simp only [reflX_apply_zero, reflX_apply_one]
  omega

/-- A joined event may use any vertex of its crossing as the attachment point. -/
theorem mem_joinedCrossingIn_iff_walk (S R : Finset Site) (A B T : Set Site)
    (hSR : (S : Set Site) ⊆ R) (η : (LatticeModels.zdGraph 2).edgeSet → Prop) :
    η ∈ joinedCrossingIn S R A B T ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ P : (LatticeModels.zdGraph 2).Walk a b,
        (∀ z ∈ P.support, z ∈ S) ∧
        (∀ e ∈ P.edges, e ∈ extend (LatticeModels.zdGraph 2) η) ∧
        ∃ x ∈ P.support, ∃ t ∈ T,
          extend (LatticeModels.zdGraph 2) η ∈ openConnIn R x t := by
  constructor
  · rintro ⟨a, ha, b, hb, t, ht, hab, hat⟩
    obtain ⟨P, hP, hPω⟩ := exists_walk_of_mem_openConnIn (extend_subset _ _) hab
    exact ⟨a, ha, b, hb, P, hP, hPω, a, P.start_mem_support, t, ht, hat⟩
  · rintro ⟨a, ha, b, hb, P, hP, hPω, x, hx, t, ht, hxt⟩
    refine ⟨a, ha, b, hb, t, ht, mem_openConnIn_of_walk P hP hPω, ?_⟩
    exact PlanarDuality.openConnIn_trans
      (openConnIn_mono hSR _ _ (mem_openConnIn_of_mem_support P hP hPω hx)) hxt

private theorem reflected_left (n : ℕ) :
    reflX n '' outerLeft n = outerRight n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [outerLeft, outerRight, Set.mem_ofPred_eq, reflX_apply_zero,
    reflX_apply_one]
  omega

/-- The two reflected joined crossings have the same Bernoulli product probability. -/
theorem joined_reflection_probability (p : unitInterval) (n : ℕ) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (joinedCrossingIn ((rectangle n n).image (reflX n))
        ((centeredSquare n).image (reflX n))
        (reflX n '' (rightSide n n : Set Site))
        (reflX n '' (leftSide n n : Set Site)) (outerRight n)) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (joinedCrossingIn (rectangle n n) (centeredSquare n) (leftSide n n)
        (rightSide n n) (outerLeft n)) := by
  simpa only [reflected_left] using
    joinedCrossingIn_probability_image_swap (reflX n) p (rectangle n n)
      (centeredSquare n) (leftSide n n) (rightSide n n) (outerLeft n)
      (square_subset_centered n)

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

private theorem reflected_rightSide (n : ℕ) :
    reflX n '' (rightSide n n : Set Site) = leftSide n n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [Finset.mem_coe, rightSide, leftSide, Finset.mem_filter, mem_rectangle_iff,
    reflX_apply_zero, reflX_apply_one]
  omega

private theorem reflected_leftSide (n : ℕ) :
    reflX n '' (leftSide n n : Set Site) = rightSide n n := by
  ext x
  rw [mem_image_reflX_iff]
  simp only [Finset.mem_coe, rightSide, leftSide, Finset.mem_filter, mem_rectangle_iff,
    reflX_apply_zero, reflX_apply_one]
  omega

/-- Reflection preserves the probability of the joined crossing with opposite target. -/
theorem joined_crossing_reflection_probability (p : unitInterval) (n : ℕ) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (joinedCrossingIn (rectangle n n) ((centeredSquare n).image (reflX n))
        (leftSide n n) (rightSide n n) (outerRight n)) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
      (joinedCrossingIn (rectangle n n) (centeredSquare n) (leftSide n n)
        (rightSide n n) (outerLeft n)) := by
  simpa only [reflected_square, reflected_rightSide, reflected_leftSide] using
    joined_reflection_probability p n

/-- Two joined horizontal crossings and a vertical crossing yield a crossing of the
surrounding rectangle. -/
theorem crossing_of_joined_crossings (n : ℕ)
    {η : (LatticeModels.zdGraph 2).edgeSet → Prop}
    (hL : η ∈ joinedCrossingIn (rectangle n n) (centeredSquare n)
      (leftSide n n) (rightSide n n) (outerLeft n))
    (hR : η ∈ joinedCrossingIn (rectangle n n) ((centeredSquare n).image (reflX n))
      (leftSide n n) (rightSide n n) (outerRight n))
    (hV : η ∈ crossingIn (rectangle n n) (bottomSide n n) (topSide n n)) :
    η ∈ crossingIn (surroundingRectangle n) (outerLeft n) (outerRight n) := by
  let ω := extend (LatticeModels.zdGraph 2) η
  change ω ∈ joinedCrossing _ _ _ _ _ at hL hR
  change ω ∈ openCrossing _ _ _ at hV ⊢
  obtain ⟨a, ha, b, hb, l, hl, hab, hal⟩ := hL
  obtain ⟨a', ha', b', hb', r, hr, hab', har⟩ := hR
  obtain ⟨c, hc, d, hd, hcd⟩ := hV
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
  obtain ⟨u, huP, huQ⟩ := exists_mem_support_of_crossing P Q
    (hbox P hPS) (hbox Q hQS) ha.2 hb.2 hc.2 hd.2
  obtain ⟨v, hvP, hvQ⟩ := exists_mem_support_of_crossing P' Q
    (hbox P' hP'S) (hbox Q hQS) ha'.2 hb'.2 hc.2 hd.2
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

end EdgeCrossing
