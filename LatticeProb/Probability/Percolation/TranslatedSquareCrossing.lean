import LatticeProb.Probability.Percolation.EdgeCrossing
import LatticeProb.Vendor.FormalMathPercolation.Literature.RSWProofs
import LatticeProb.Vendor.FormalMathPercolation.Literature.LatticeSymmetry

/-!
# Crossings of translated squares

Critical horizontal and vertical crossing estimates for translated inclusive squares
under the edge-indexed Bernoulli product law.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace EdgeCrossing

/-- The edge-indexed crossing event in a finite region between two vertex sets. -/
def crossingIn (S : Finset (LatticeModels.Site 2)) (A B : Set (LatticeModels.Site 2)) :
    Set ((LatticeModels.zdGraph 2).edgeSet → Prop) :=
  extend (LatticeModels.zdGraph 2) ⁻¹' openCrossing S A B

/-- Membership is witnessed by an open nearest-neighbor walk inside the region. -/
theorem mem_crossingIn_iff (S : Finset (LatticeModels.Site 2))
    (A B : Set (LatticeModels.Site 2)) (η : (LatticeModels.zdGraph 2).edgeSet → Prop) :
    η ∈ crossingIn S A B ↔ ∃ x ∈ A, ∃ y ∈ B,
      ∃ q : (LatticeModels.zdGraph 2).Walk x y,
        (∀ z ∈ q.support, z ∈ S) ∧
        ∀ e (he : e ∈ q.edges), η ⟨e, q.edges_subset_edgeSet he⟩ := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨q, hq, ho⟩ := exists_walk_of_mem_openConnIn (extend_subset _ _) hxy
    exact ⟨x, hx, y, hy, q, hq, fun e he => (ho e he).choose_spec⟩
  · rintro ⟨x, hx, y, hy, q, hq, ho⟩
    refine ⟨x, hx, y, hy, mem_openConnIn_of_walk q hq ?_⟩
    intro e he
    exact ⟨q.edges_subset_edgeSet he, ho e he⟩

/-- Edge-indexed and ambient crossing events have the same probability. -/
theorem crossingIn_probability (p : unitInterval) (S : Finset (LatticeModels.Site 2))
    (A B : Set (LatticeModels.Site 2)) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (crossingIn S A B) =
      (bondPercolation (LatticeModels.zdGraph 2) p).real (openCrossing S A B) := by
  have hm : MeasurableSet (crossingIn S A B) :=
    (measurableSet_openCrossing S A B).preimage (measurable_extend _)
  rw [← edge_product_law (LatticeModels.zdGraph 2) p, measureReal_def,
    Measure.map_apply (measurable_restrict _) hm, measureReal_def]
  congr 1
  apply measure_congr
  filter_upwards [edge_support_ae (LatticeModels.zdGraph 2) p] with ω hω
  apply propext
  change (extend (LatticeModels.zdGraph 2) (restrict (LatticeModels.zdGraph 2) ω) ∈
    openCrossing S A B) ↔ ω ∈ openCrossing S A B
  rw [extend_restrict, hω]

/-- Translating a finite crossing region and both sides preserves its edge-product probability. -/
theorem crossingIn_probability_shift (p : unitInterval) (v : LatticeModels.Site 2)
    (S : Finset (LatticeModels.Site 2)) (A B : Set (LatticeModels.Site 2)) :
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real
        (crossingIn (S.image (· + v)) ((· + v) '' A) ((· + v) '' B)) =
    (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
      bernoulliMeasure True False p)).real (crossingIn S A B) := by
  rw [crossingIn_probability, crossingIn_probability]
  simpa only [Finset.coe_image] using real_openCrossing_shift p v (S : Set _) A B

/-- A translated inclusive square has critical horizontal crossing probability at least one half. -/
theorem half_le_translated_square_horizontal (n : ℕ) (v : LatticeModels.Site 2) :
    (1 / 2 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
          (crossingIn ((rectangle n n).image (· + v))
            ((· + v) '' (leftSide n n : Set _)) ((· + v) '' (rightSide n n : Set _))) := by
  rw [crossingIn_probability_shift, crossingIn_probability]
  exact half_le_crossingProb_self crossingProb_half_succ_self_holds n

/-- A translated inclusive square has critical vertical crossing probability at least one half. -/
theorem half_le_translated_square_vertical (n : ℕ) (v : LatticeModels.Site 2) :
    (1 / 2 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
          (crossingIn ((rectangle n n).image (· + v))
            ((· + v) '' (bottomSide n n : Set _)) ((· + v) '' (topSide n n : Set _))) := by
  rw [crossingIn_probability_shift, crossingIn_probability, ← tbCrossing, real_tbCrossing]
  exact half_le_crossingProb_self crossingProb_half_succ_self_holds n

/-- The square of side length `2 * n`, translated by `(-n, -n)`, has endpoints `-n` and `n`. -/
theorem mem_centered_square (n : ℕ) (x : LatticeModels.Site 2) :
    x ∈ (rectangle (2 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)]) ↔
      -(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n := by
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

/-- The left side of the centered square has first coordinate `-n`. -/
theorem mem_centered_square_left (n : ℕ) (x : LatticeModels.Site 2) :
    x ∈ (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (leftSide (2 * n) (2 * n) : Set (LatticeModels.Site 2)) ↔
      x ∈ (rectangle (2 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)]) ∧
        x 0 = -(n : ℤ) := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter] at hy
    refine ⟨Finset.mem_image.mpr ⟨y, hy.1, rfl⟩, ?_⟩
    simp [hy.2]
  · rintro ⟨hx, hx0⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨y, ?_, rfl⟩
    simp only [Finset.mem_coe, leftSide, Finset.mem_filter]
    refine ⟨hy, ?_⟩
    simp only [Pi.add_apply, Matrix.cons_val_zero] at hx0
    omega

/-- The right side of the centered square has first coordinate `n`. -/
theorem mem_centered_square_right (n : ℕ) (x : LatticeModels.Site 2) :
    x ∈ (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (rightSide (2 * n) (2 * n) : Set (LatticeModels.Site 2)) ↔
      x ∈ (rectangle (2 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)]) ∧
        x 0 = n := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter] at hy
    refine ⟨Finset.mem_image.mpr ⟨y, hy.1, rfl⟩, ?_⟩
    simp only [Pi.add_apply, Matrix.cons_val_zero, hy.2, Nat.cast_mul, Nat.cast_ofNat]
    omega
  · rintro ⟨hx, hx0⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    refine ⟨y, ?_, rfl⟩
    simp only [Finset.mem_coe, rightSide, Finset.mem_filter]
    refine ⟨hy, ?_⟩
    simp only [Pi.add_apply, Matrix.cons_val_zero, Nat.cast_mul, Nat.cast_ofNat] at *
    omega

/-- The horizontal crossing probability of `[-n,n]²` at criticality is at least one half. -/
theorem half_le_centered_square_horizontal (n : ℕ) :
    (1 / 2 : ℝ) ≤
      (Measure.infinitePi (fun _ : (LatticeModels.zdGraph 2).edgeSet =>
        bernoulliMeasure True False half)).real
        (crossingIn ((rectangle (2 * n) (2 * n)).image (· + ![-(n : ℤ), -(n : ℤ)]))
          {x : LatticeModels.Site 2 | (-(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n) ∧
            x 0 = -(n : ℤ)}
          {x : LatticeModels.Site 2 | (-(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n) ∧
            x 0 = n}) := by
  have hl : (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (leftSide (2 * n) (2 * n) : Set (LatticeModels.Site 2)) =
      {x : LatticeModels.Site 2 | (-(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n) ∧
        x 0 = -(n : ℤ)} := by
    ext x
    exact (mem_centered_square_left n x).trans (and_congr (mem_centered_square n x) Iff.rfl)
  have hr : (· + ![-(n : ℤ), -(n : ℤ)]) ''
      (rightSide (2 * n) (2 * n) : Set (LatticeModels.Site 2)) =
      {x : LatticeModels.Site 2 | (-(n : ℤ) ≤ x 0 ∧ x 0 ≤ n ∧ -(n : ℤ) ≤ x 1 ∧ x 1 ≤ n) ∧
        x 0 = n} := by
    ext x
    exact (mem_centered_square_right n x).trans (and_congr (mem_centered_square n x) Iff.rfl)
  simpa only [hl, hr] using
    half_le_translated_square_horizontal (2 * n) ![-(n : ℤ), -(n : ℤ)]

end EdgeCrossing
