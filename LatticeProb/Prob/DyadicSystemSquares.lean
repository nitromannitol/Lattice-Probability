import LatticeProb.Prob.DyadicSystemInvariance
import LatticeProb.Euclidean.ParentBlock

/-!
# The squares of a uniform dyadic system in scale and offset coordinates

A dyadic system of the plane (Gwynne, Miller and Sheffield, *An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, Section 2.1) is described here by a scale
`s : ℝ` and, for each of the two coordinates, an offset sequence `o : ℕ → ℝ`. In one coordinate,
the left ends of the intervals of generation `j : ℤ` form the progression
`gridPoints s o j = -2^s o_{max j 0} + 2^(s + j) ℤ`; the squares of generation `j` are the
products of two such intervals (`generationSquares`), and the system is the union over `j`
(`dyadicSquares`). For the uniform dyadic system, `s` is uniform on `[0, 1)` and the offsets have
law `offsetLaw` (see `LatticeProb.Prob.DyadicOffsetLaw`); `originSquare` is the square of
generation `k ∈ ℕ` that contains the origin.

This file proves the covariance of these squares under the maps whose measure preservation is
proved in `LatticeProb.Prob.DyadicSystemInvariance`: the image of the system under `z ↦ 2^t z`
is the system with coordinates `(fract (s + t), dilateOffsets ⌊s + t⌋ o¹, dilateOffsets ⌊s + t⌋ o²)`,
generation `j` going to generation `j + ⌊s + t⌋`, and the image under `z ↦ z + w` is the
system with coordinates `(s, shiftOffsets (2^(-s) Re w) o¹, shiftOffsets (2^(-s) Im w) o²)`.
The dilation statement needs the offsets to be compatible (`IsCompatible`: consecutive offsets
agree modulo the side of the finer generation), which holds almost surely under `offsetLaw`.

## Main statements

* `LatticeProb.DyadicOffset.image_two_rpow_mul_gridPoints_eq`: one-dimensional dilation covariance.
* `LatticeProb.DyadicOffset.mem_gridPoints_shiftOffsets`: one-dimensional translation covariance.
* `LatticeProb.DyadicOffset.ae_isCompatible_offsetLaw`.
* `LatticeProb.DyadicOffset.image_dyadicSquares_smul`, `image_dyadicSquares_add`: covariance of
  the system of squares of the plane under dilations by `2^t` and translations.
-/

open MeasureTheory Set

namespace LatticeProb.DyadicOffset

/-! ### Arithmetic progressions -/

/-- The arithmetic progression `a + p ℤ`. -/
def shiftedLattice (a p : ℝ) : Set ℝ := {x | ∃ n : ℤ, x = a + n * p}

theorem mem_shiftedLattice {a p x : ℝ} : x ∈ shiftedLattice a p ↔ ∃ n : ℤ, x = a + n * p :=
  Iff.rfl

theorem shiftedLattice_add_intMul (a p : ℝ) (n : ℤ) :
    shiftedLattice (a + n * p) p = shiftedLattice a p := by
  ext x
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨n + m, by push_cast; ring⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m - n, by push_cast; ring⟩

theorem shiftedLattice_eq_of_eq_add {a a' p : ℝ} (n : ℤ) (h : a' = a + n * p) :
    shiftedLattice a' p = shiftedLattice a p := by
  rw [h, shiftedLattice_add_intMul]

theorem image_mul_shiftedLattice (c a p : ℝ) :
    (fun x => c * x) '' shiftedLattice a p = shiftedLattice (c * a) (c * p) := by
  ext x
  constructor
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, by ring⟩
  · rintro ⟨n, rfl⟩
    exact ⟨a + n * p, ⟨n, rfl⟩, by ring⟩

theorem mem_shiftedLattice_add (a p b x : ℝ) :
    x ∈ shiftedLattice (a + b) p ↔ x - b ∈ shiftedLattice a p := by
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, by ring⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by linarith⟩

/-- `2^s 2^(max j 0) = 2^(max (-j) 0) 2^(s + j)`. -/
theorem two_rpow_mul_two_pow_toNat (s : ℝ) (j : ℤ) :
    (2 : ℝ) ^ s * 2 ^ j.toNat = 2 ^ (-j).toNat * (2 : ℝ) ^ (s + (j : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add two_pos,
    ← Real.rpow_add two_pos]
  congr 1
  have h1 : ((j.toNat : ℤ)) - ((-j).toNat : ℤ) = j := by omega
  have h2 : ((j.toNat : ℝ)) - ((-j).toNat : ℝ) = j := by exact_mod_cast h1
  linarith

/-! ### The grid of one coordinate -/

/-- The left ends of the intervals of generation `j` of the dyadic system of the line with scale
`s` and offsets `o`: the progression `-2^s o_{max j 0} + 2^(s + j) ℤ`. -/
noncomputable def gridPoints (s : ℝ) (o : ℕ → ℝ) (j : ℤ) : Set ℝ :=
  shiftedLattice (-((2 : ℝ) ^ s * o j.toNat)) ((2 : ℝ) ^ (s + (j : ℝ)))

/-- Consecutive offsets agree modulo the side of the finer generation:
`o (k + 1) ∈ o k + 2^k ℤ`. -/
def IsCompatible (o : ℕ → ℝ) : Prop := ∀ k : ℕ, ∃ n : ℤ, o (k + 1) = o k + n * 2 ^ k

theorem isCompatible_offsetsL (x : ℝ) (e : ℕ → Bool) : IsCompatible (offsetsL 1 x e) := by
  intro k
  refine ⟨if e k then 1 else 0, ?_⟩
  simp only [offsetsL, Finset.sum_range_succ, bit]
  split_ifs <;> push_cast <;> ring

theorem isCompatible_halfOffsets {o : ℕ → ℝ} (ho : IsCompatible o) :
    IsCompatible (halfOffsets o) := by
  intro k
  obtain ⟨n, hn⟩ := ho (k + 1)
  refine ⟨n, ?_⟩
  unfold halfOffsets
  rw [hn]
  ring

theorem isCompatible_doubleOffsets {o : ℕ → ℝ} (ho : IsCompatible o) :
    IsCompatible (doubleOffsets o) := by
  rintro (_ | k)
  · refine ⟨toIcoDiv (zero_lt_one' ℝ) 0 (2 * o 0), ?_⟩
    rw [show doubleOffsets o (0 + 1) = 2 * o 0 from rfl,
      show doubleOffsets o 0 = toIcoMod (zero_lt_one' ℝ) 0 (2 * o 0) from rfl,
      ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
    ring
  · obtain ⟨n, hn⟩ := ho k
    refine ⟨n, ?_⟩
    rw [show doubleOffsets o (k + 1 + 1) = 2 * o (k + 1) from rfl,
      show doubleOffsets o (k + 1) = 2 * o k from rfl, hn]
    ring

theorem isCompatible_halfOffsets_iterate {o : ℕ → ℝ} (ho : IsCompatible o) (n : ℕ) :
    IsCompatible (halfOffsets^[n] o) := by
  induction n with
  | zero => exact ho
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isCompatible_halfOffsets ih

theorem isCompatible_doubleOffsets_iterate {o : ℕ → ℝ} (ho : IsCompatible o) (n : ℕ) :
    IsCompatible (doubleOffsets^[n] o) := by
  induction n with
  | zero => exact ho
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact isCompatible_doubleOffsets ih

theorem isCompatible_dilateOffsets {o : ℕ → ℝ} (ho : IsCompatible o) (m : ℤ) :
    IsCompatible (dilateOffsets m o) := by
  cases m with
  | ofNat n => exact isCompatible_doubleOffsets_iterate ho n
  | negSucc n => exact isCompatible_halfOffsets_iterate ho (n + 1)

theorem measurableSet_isCompatible : MeasurableSet {o : ℕ → ℝ | IsCompatible o} := by
  have h : {o : ℕ → ℝ | IsCompatible o} =
      ⋂ k : ℕ, ⋃ n : ℤ, {o : ℕ → ℝ | o (k + 1) = o k + n * 2 ^ k} := by
    ext o
    simp [IsCompatible]
  rw [h]
  exact .iInter fun k => .iUnion fun n => measurableSet_eq_fun (by fun_prop) (by fun_prop)

/-- Almost every offset sequence of the uniform dyadic system is compatible. -/
theorem ae_isCompatible_offsetLaw : ∀ᵐ o ∂offsetLaw, IsCompatible o := by
  rw [offsetLaw, ae_map_iff
    (measurable_pi_iff.mpr fun k => measurable_offsetsL_eval 1 k).aemeasurable
    measurableSet_isCompatible]
  exact Filter.Eventually.of_forall fun q => isCompatible_offsetsL q.1 q.2

/-- Doubling the scale coordinate is the same as doubling the offsets and raising the
generation by one. -/
theorem gridPoints_add_one (s : ℝ) (o : ℕ → ℝ) (j : ℤ) :
    gridPoints (s + 1) o j = gridPoints s (doubleOffsets o) (j + 1) := by
  have hP : (2 : ℝ) ^ (s + 1 + (j : ℝ)) = (2 : ℝ) ^ (s + ((j + 1 : ℤ) : ℝ)) := by
    congr 1; push_cast; ring
  unfold gridPoints
  rw [hP, Real.rpow_add two_pos s 1, Real.rpow_one]
  rcases le_or_gt 0 j with hj | hj
  · have h1 : (j + 1).toNat = j.toNat + 1 := by omega
    rw [h1, show doubleOffsets o (j.toNat + 1) = 2 * o j.toNat from rfl]
    congr 1
    ring
  · have h0 : j.toNat = 0 := by omega
    have h1 : (j + 1).toNat = 0 := by omega
    obtain ⟨N, hN⟩ : ∃ N : ℤ, doubleOffsets o 0 = 2 * o 0 - N :=
      ⟨toIcoDiv (zero_lt_one' ℝ) 0 (2 * o 0), by
        rw [show doubleOffsets o 0 = toIcoMod (zero_lt_one' ℝ) 0 (2 * o 0) from rfl,
          ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul, mul_one]⟩
    rw [h0, h1, hN]
    refine (shiftedLattice_eq_of_eq_add (N * 2 ^ (-(j + 1)).toNat) ?_).symm
    have := two_rpow_mul_two_pow_toNat s (j + 1)
    rw [h1, pow_zero, mul_one] at this
    push_cast at this ⊢
    linear_combination (N : ℝ) * this

/-- Halving the scale coordinate is the same as halving the offsets and lowering the
generation by one (for compatible offsets). -/
theorem gridPoints_sub_one {o : ℕ → ℝ} (ho : IsCompatible o) (s : ℝ) (j : ℤ) :
    gridPoints (s - 1) o j = gridPoints s (halfOffsets o) (j - 1) := by
  have hP : (2 : ℝ) ^ (s - 1 + (j : ℝ)) = (2 : ℝ) ^ (s + ((j - 1 : ℤ) : ℝ)) := by
    congr 1; push_cast; ring
  have h2 : (2 : ℝ) ^ s = 2 ^ (s - 1) * 2 := by
    rw [← Real.rpow_add_one two_ne_zero, sub_add_cancel]
  unfold gridPoints halfOffsets
  rw [← hP, h2]
  rcases le_or_gt 1 j with hj | hj
  · have h1 : (j - 1).toNat + 1 = j.toNat := by omega
    rw [h1]
    congr 1
    ring
  · have h0 : j.toNat = 0 := by omega
    have h1 : (j - 1).toNat = 0 := by omega
    obtain ⟨n, hn⟩ := ho 0
    rw [h0, h1, hn]
    refine (shiftedLattice_eq_of_eq_add (-n * 2 ^ (-j).toNat) ?_).symm
    have := two_rpow_mul_two_pow_toNat (s - 1) j
    rw [h0, pow_zero, mul_one] at this
    push_cast at this ⊢
    linear_combination (-(n : ℝ)) * this

theorem gridPoints_add_natCast (n : ℕ) :
    ∀ (s : ℝ) (o : ℕ → ℝ) (j : ℤ),
      gridPoints (s + n) o j = gridPoints s (doubleOffsets^[n] o) (j + n) := by
  induction n with
  | zero => intro s o j; simp
  | succ n ih =>
    intro s o j
    have h1 : s + ((n + 1 : ℕ) : ℝ) = s + 1 + n := by push_cast; ring
    have h2 : j + ((n + 1 : ℕ) : ℤ) = j + n + 1 := by push_cast; ring
    rw [h1, h2, Function.iterate_succ_apply', ← gridPoints_add_one, ih]

theorem gridPoints_sub_natCast (n : ℕ) :
    ∀ (s : ℝ) (o : ℕ → ℝ), IsCompatible o → ∀ j : ℤ,
      gridPoints (s - n) o j = gridPoints s (halfOffsets^[n] o) (j - n) := by
  induction n with
  | zero => intro s o _ j; simp
  | succ n ih =>
    intro s o ho j
    have h1 : s - ((n + 1 : ℕ) : ℝ) = s - 1 - n := by push_cast; ring
    have h2 : j - ((n + 1 : ℕ) : ℤ) = j - n - 1 := by push_cast; ring
    rw [h1, h2, Function.iterate_succ_apply',
      ← gridPoints_sub_one (isCompatible_halfOffsets_iterate ho n), ih (s - 1) o ho]

/-- Moving the scale coordinate by an integer `m` is the same as dilating the offsets by `2^m`
and moving the generation by `m`. -/
theorem gridPoints_add_intCast {o : ℕ → ℝ} (ho : IsCompatible o) (s : ℝ) (m j : ℤ) :
    gridPoints (s + m) o j = gridPoints s (dilateOffsets m o) (j + m) := by
  cases m with
  | ofNat n =>
    rw [show dilateOffsets (Int.ofNat n) = doubleOffsets^[n] from rfl, Int.ofNat_eq_natCast,
      Int.cast_natCast]
    exact gridPoints_add_natCast n s o j
  | negSucc n =>
    have h1 : s + ((Int.negSucc n : ℤ) : ℝ) = s - ((n + 1 : ℕ) : ℝ) := by
      rw [Int.cast_negSucc]; push_cast; ring
    have h2 : j + Int.negSucc n = j - ((n + 1 : ℕ) : ℤ) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [show dilateOffsets (Int.negSucc n) = halfOffsets^[n + 1] from rfl, h1, h2]
    exact gridPoints_sub_natCast (n + 1) s o ho j

theorem image_two_rpow_mul_gridPoints (t s : ℝ) (o : ℕ → ℝ) (j : ℤ) :
    (fun x => (2 : ℝ) ^ t * x) '' gridPoints s o j = gridPoints (s + t) o j := by
  unfold gridPoints
  rw [image_mul_shiftedLattice]
  congr 1
  · rw [Real.rpow_add two_pos s t]
    ring
  · rw [← Real.rpow_add two_pos]
    congr 1
    ring

/-- **Dilation covariance, one coordinate.** The image of the generation-`j` grid under
`x ↦ 2^t x` is the generation-`(j + ⌊s + t⌋)` grid of the system with scale `fract (s + t)` and
offsets `dilateOffsets ⌊s + t⌋ o`. -/
theorem image_two_rpow_mul_gridPoints_eq {o : ℕ → ℝ} (ho : IsCompatible o) (t s : ℝ) (j : ℤ) :
    (fun x => (2 : ℝ) ^ t * x) '' gridPoints s o j =
      gridPoints (Int.fract (s + t)) (dilateOffsets ⌊s + t⌋ o) (j + ⌊s + t⌋) := by
  rw [image_two_rpow_mul_gridPoints, ← gridPoints_add_intCast ho, Int.fract_add_floor]

theorem exists_shiftOffsets_eq (c : ℝ) (o : ℕ → ℝ) (k : ℕ) :
    ∃ N : ℤ, shiftOffsets c o k = o k - c - N * 2 ^ k :=
  ⟨toIcoDiv (two_pow_pos' k) 0 (o k - c), by
    rw [shiftOffsets, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]⟩

/-- **Translation covariance, one coordinate.** The grid with offsets `shiftOffsets c o` is the
grid with offsets `o` translated by `2^s c`. -/
theorem mem_gridPoints_shiftOffsets (s c : ℝ) (o : ℕ → ℝ) (j : ℤ) (x : ℝ) :
    x ∈ gridPoints s (shiftOffsets c o) j ↔ x - 2 ^ s * c ∈ gridPoints s o j := by
  obtain ⟨N, hN⟩ := exists_shiftOffsets_eq c o j.toNat
  have key : gridPoints s (shiftOffsets c o) j =
      shiftedLattice (-((2 : ℝ) ^ s * o j.toNat) + 2 ^ s * c) ((2 : ℝ) ^ (s + (j : ℝ))) := by
    unfold gridPoints
    rw [hN]
    refine shiftedLattice_eq_of_eq_add (N * 2 ^ (-j).toNat) ?_
    have := two_rpow_mul_two_pow_toNat s j
    push_cast
    linear_combination (N : ℝ) * this
  rw [key, mem_shiftedLattice_add, gridPoints]

/-! ### Squares of the plane -/

/-- The closed square `[a, a + ℓ] × [b, b + ℓ]` with lower left corner `a + b i` and side `ℓ`. -/
def cornerSquare (a b ℓ : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ a + ℓ ∧ b ≤ z.im ∧ z.im ≤ b + ℓ}

theorem mem_cornerSquare {a b ℓ : ℝ} {z : ℂ} :
    z ∈ cornerSquare a b ℓ ↔ a ≤ z.re ∧ z.re ≤ a + ℓ ∧ b ≤ z.im ∧ z.im ≤ b + ℓ :=
  Iff.rfl

theorem cornerSquare_eq_closedSquare (a b ℓ : ℝ) :
    cornerSquare a b ℓ = ParentBlock.closedSquare ⟨a + ℓ / 2, b + ℓ / 2⟩ ℓ := by
  ext z
  show _ ↔ |z.re - (a + ℓ / 2)| ≤ ℓ / 2 ∧ |z.im - (b + ℓ / 2)| ≤ ℓ / 2
  rw [mem_cornerSquare, abs_le, abs_le]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem smul_mem_cornerSquare {r a b ℓ : ℝ} (hr : 0 ≤ r) {z : ℂ}
    (hz : z ∈ cornerSquare a b ℓ) : r • z ∈ cornerSquare (r * a) (r * b) (r * ℓ) := by
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_cornerSquare, Complex.smul_re, Complex.smul_im, smul_eq_mul, smul_eq_mul, ← mul_add,
    ← mul_add]
  exact ⟨mul_le_mul_of_nonneg_left h1 hr, mul_le_mul_of_nonneg_left h2 hr,
    mul_le_mul_of_nonneg_left h3 hr, mul_le_mul_of_nonneg_left h4 hr⟩

theorem image_smul_cornerSquare {r : ℝ} (hr : 0 < r) (a b ℓ : ℝ) :
    (fun z : ℂ => r • z) '' cornerSquare a b ℓ = cornerSquare (r * a) (r * b) (r * ℓ) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact smul_mem_cornerSquare hr.le hz
  · intro hw
    refine ⟨r⁻¹ • w, ?_, smul_inv_smul₀ hr.ne' w⟩
    have := smul_mem_cornerSquare (inv_nonneg.2 hr.le) hw
    rwa [inv_mul_cancel_left₀ hr.ne', inv_mul_cancel_left₀ hr.ne',
      inv_mul_cancel_left₀ hr.ne'] at this

theorem image_add_cornerSquare (w : ℂ) (a b ℓ : ℝ) :
    (fun z : ℂ => z + w) '' cornerSquare a b ℓ = cornerSquare (a + w.re) (b + w.im) ℓ := by
  ext u
  constructor
  · rintro ⟨z, ⟨h1, h2, h3, h4⟩, rfl⟩
    simp only [mem_cornerSquare, Complex.add_re, Complex.add_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨u - w, ?_, sub_add_cancel u w⟩
    simp only [mem_cornerSquare, Complex.sub_re, Complex.sub_im]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The squares of generation `j` of the dyadic system of the plane with scale `s` and offset
sequences `o₁`, `o₂`: side `2^(s + j)`, lower left corners in `gridPoints s o₁ j × gridPoints s o₂ j`. -/
noncomputable def generationSquares (s : ℝ) (o₁ o₂ : ℕ → ℝ) (j : ℤ) : Set (Set ℂ) :=
  {S | ∃ a ∈ gridPoints s o₁ j, ∃ b ∈ gridPoints s o₂ j,
    S = cornerSquare a b ((2 : ℝ) ^ (s + (j : ℝ)))}

/-- The dyadic system of the plane with scale `s` and offset sequences `o₁`, `o₂`: the squares
of all generations. -/
noncomputable def dyadicSquares (s : ℝ) (o₁ o₂ : ℕ → ℝ) : Set (Set ℂ) :=
  ⋃ j : ℤ, generationSquares s o₁ o₂ j

/-- The square of generation `k ∈ ℕ` with lower left corner `-2^s (o₁ k + o₂ k i)`; it contains
the origin when `o₁ k, o₂ k ∈ [0, 2^k]`. -/
noncomputable def originSquare (s : ℝ) (o₁ o₂ : ℕ → ℝ) (k : ℕ) : Set ℂ :=
  cornerSquare (-((2 : ℝ) ^ s * o₁ k)) (-((2 : ℝ) ^ s * o₂ k)) ((2 : ℝ) ^ (s + (k : ℝ)))

theorem originSquare_mem_generationSquares (s : ℝ) (o₁ o₂ : ℕ → ℝ) (k : ℕ) :
    originSquare s o₁ o₂ k ∈ generationSquares s o₁ o₂ k := by
  refine ⟨-((2 : ℝ) ^ s * o₁ k), ⟨0, by simp⟩, -((2 : ℝ) ^ s * o₂ k), ⟨0, by simp⟩, ?_⟩
  simp [originSquare]

theorem zero_mem_originSquare {s : ℝ} {o₁ o₂ : ℕ → ℝ} {k : ℕ} (h₁ : o₁ k ∈ Icc 0 (2 ^ k))
    (h₂ : o₂ k ∈ Icc 0 (2 ^ k)) : (0 : ℂ) ∈ originSquare s o₁ o₂ k := by
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have hk : (2 : ℝ) ^ (s + (k : ℝ)) = 2 ^ s * 2 ^ k := by
    rw [Real.rpow_add two_pos, Real.rpow_natCast]
  rw [originSquare, mem_cornerSquare, hk, Complex.zero_re, Complex.zero_im]
  obtain ⟨a1, a2⟩ := h₁
  obtain ⟨b1, b2⟩ := h₂
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **Dilation covariance.** The image of the squares of generation `j` under `z ↦ 2^t z` are
the squares of generation `j + ⌊s + t⌋` of the system with scale `fract (s + t)` and offsets
`dilateOffsets ⌊s + t⌋ o_i`. -/
theorem image_generationSquares_smul {o₁ o₂ : ℕ → ℝ} (h₁ : IsCompatible o₁)
    (h₂ : IsCompatible o₂) (t s : ℝ) (j : ℤ) :
    (fun S : Set ℂ => (fun z : ℂ => (2 : ℝ) ^ t • z) '' S) '' generationSquares s o₁ o₂ j =
      generationSquares (Int.fract (s + t)) (dilateOffsets ⌊s + t⌋ o₁)
        (dilateOffsets ⌊s + t⌋ o₂) (j + ⌊s + t⌋) := by
  have hr : (0 : ℝ) < 2 ^ t := by positivity
  have hside : (2 : ℝ) ^ t * (2 : ℝ) ^ (s + (j : ℝ)) =
      (2 : ℝ) ^ (Int.fract (s + t) + ((j + ⌊s + t⌋ : ℤ) : ℝ)) := by
    rw [← Real.rpow_add two_pos]
    congr 1
    push_cast
    linarith [Int.fract_add_floor (s + t)]
  have g₁ := image_two_rpow_mul_gridPoints_eq h₁ t s j
  have g₂ := image_two_rpow_mul_gridPoints_eq h₂ t s j
  ext S
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨2 ^ t * a, ?_, 2 ^ t * b, ?_, ?_⟩
    · rw [← g₁]
      exact ⟨a, ha, rfl⟩
    · rw [← g₂]
      exact ⟨b, hb, rfl⟩
    · beta_reduce
      rw [image_smul_cornerSquare hr, hside]
  · rintro ⟨a', ha', b', hb', rfl⟩
    rw [← g₁] at ha'
    rw [← g₂] at hb'
    obtain ⟨a, ha, rfl⟩ := ha'
    obtain ⟨b, hb, rfl⟩ := hb'
    refine ⟨cornerSquare a b ((2 : ℝ) ^ (s + (j : ℝ))), ⟨a, ha, b, hb, rfl⟩, ?_⟩
    beta_reduce
    rw [image_smul_cornerSquare hr, hside]

/-- **Translation covariance.** The image of the squares of generation `j` under `z ↦ z + w` are
the squares of generation `j` of the system with the same scale and offsets
`shiftOffsets (2^(-s) Re w) o₁`, `shiftOffsets (2^(-s) Im w) o₂`. -/
theorem image_generationSquares_add (w : ℂ) (s : ℝ) (o₁ o₂ : ℕ → ℝ) (j : ℤ) :
    (fun S : Set ℂ => (fun z : ℂ => z + w) '' S) '' generationSquares s o₁ o₂ j =
      generationSquares s (shiftOffsets ((2 : ℝ) ^ (-s) * w.re) o₁)
        (shiftOffsets ((2 : ℝ) ^ (-s) * w.im) o₂) j := by
  have hc : ∀ x : ℝ, (2 : ℝ) ^ s * ((2 : ℝ) ^ (-s) * x) = x := fun x => by
    rw [Real.rpow_neg zero_le_two, mul_inv_cancel_left₀ (by positivity)]
  ext S
  constructor
  · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨a + w.re, ?_, b + w.im, ?_, ?_⟩
    · rw [mem_gridPoints_shiftOffsets, hc, add_sub_cancel_right]
      exact ha
    · rw [mem_gridPoints_shiftOffsets, hc, add_sub_cancel_right]
      exact hb
    · beta_reduce
      rw [image_add_cornerSquare]
  · rintro ⟨a', ha', b', hb', rfl⟩
    rw [mem_gridPoints_shiftOffsets, hc] at ha' hb'
    refine ⟨cornerSquare (a' - w.re) (b' - w.im) ((2 : ℝ) ^ (s + (j : ℝ))),
      ⟨_, ha', _, hb', rfl⟩, ?_⟩
    beta_reduce
    rw [image_add_cornerSquare, sub_add_cancel, sub_add_cancel]

/-- **Dilation covariance of the dyadic system of the plane** (for compatible offsets). -/
theorem image_dyadicSquares_smul {o₁ o₂ : ℕ → ℝ} (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    (t s : ℝ) :
    (fun S : Set ℂ => (fun z : ℂ => (2 : ℝ) ^ t • z) '' S) '' dyadicSquares s o₁ o₂ =
      dyadicSquares (Int.fract (s + t)) (dilateOffsets ⌊s + t⌋ o₁) (dilateOffsets ⌊s + t⌋ o₂) := by
  rw [dyadicSquares, image_iUnion]
  simp_rw [image_generationSquares_smul h₁ h₂]
  exact (Equiv.addRight ⌊s + t⌋).surjective.iUnion_comp
    (generationSquares (Int.fract (s + t)) (dilateOffsets ⌊s + t⌋ o₁) (dilateOffsets ⌊s + t⌋ o₂))

/-- **Translation covariance of the dyadic system of the plane.** -/
theorem image_dyadicSquares_add (w : ℂ) (s : ℝ) (o₁ o₂ : ℕ → ℝ) :
    (fun S : Set ℂ => (fun z : ℂ => z + w) '' S) '' dyadicSquares s o₁ o₂ =
      dyadicSquares s (shiftOffsets ((2 : ℝ) ^ (-s) * w.re) o₁)
        (shiftOffsets ((2 : ℝ) ^ (-s) * w.im) o₂) := by
  rw [dyadicSquares, image_iUnion]
  simp_rw [image_generationSquares_add]
  rfl

end LatticeProb.DyadicOffset
