import LatticeProb.Prob.CellConfigSelectedSquare

/-!
# The uniform-average kernel of the capped squares integrates to one in its centre

Let `S_m^w` be the capped square of cell mass `m` around `w` for the uniform dyadic system of the
plane (Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515, (2.1)), selected as the square of the generation `j` with
`ν(S_j(w)) ≤ m < ν(S_{j+1}(w))`, where `S_j(w)` is the square of generation `j` whose lower left
corner is formed by the left ends of the grid intervals containing the coordinates of `w`.

For a point `z` that lies on no grid line and compatible offsets, `z ∈ S_j(w)` forces
`S_j(w) = S_j(z)` and `S_{j+1}(w) = S_{j+1}(z)`, so the selected generation at `w` is the one at
`z`, and the set of `w` with `z ∈ S_j(w)` is the half-open square of the same side. Hence

`∫ |S_m^w|⁻¹ 1(z ∈ S_m^w) dw = 1`,

almost surely in the dyadic system, which evaluates the right side of the mass-transport
identity behind (B.6) of arXiv 1807.07515.

## Main statements

* `LatticeProb.CellConfigCappedSquare.squareAt_mono_of_isCompatible`: for compatible offsets, the
  squares `S_j(w)` increase with `j` for every point `w`.
* `LatticeProb.CellConfigCappedSquare.setOf_mem_squareAt_eq`: for an off-grid `z`, the set of `w`
  with `z ∈ S_j(w)` is the half-open square of generation `j` containing `z`.
* `LatticeProb.CellConfigCappedSquare.lintegral_averageKernel_reverse`: the deterministic identity.
* `LatticeProb.CellConfigCappedSquare.ae_lintegral_averageKernel_reverse`: almost surely in the
  dyadic system, for every mass `m ∈ (0, ∞)`, the kernel integrates to one in its centre.
-/

open MeasureTheory Set Complex
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

section Squares

variable {s : ℝ} {o₁ o₂ : ℕ → ℝ}

/-- If an off-grid point `z` lies in the square of generation `j` at `w`, the grid intervals of
generation `j` containing the coordinates of `w` and of `z` have the same left ends. -/
theorem gridFloor_eq_of_mem_squareAt {z w : ℂ} (hz : IsOffGrid s o₁ o₂ z) {j : ℤ}
    (h : z ∈ squareAt s o₁ o₂ j w) :
    gridFloor s o₁ j w.re = gridFloor s o₁ j z.re ∧
      gridFloor s o₂ j w.im = gridFloor s o₂ j z.im := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  obtain ⟨h1, h2, h3, h4⟩ := h
  have h2' : z.re < gridFloor s o₁ j w.re + (2 : ℝ) ^ (s + (j : ℝ)) :=
    lt_of_le_of_ne h2 fun h => (hz j).1 (h ▸ add_mem_shiftedLattice (gridFloor_mem s o₁ j w.re))
  have h4' : z.im < gridFloor s o₂ j w.im + (2 : ℝ) ^ (s + (j : ℝ)) :=
    lt_of_le_of_ne h4 fun h => (hz j).2 (h ▸ add_mem_shiftedLattice (gridFloor_mem s o₂ j w.im))
  exact ⟨eq_latticeFloor hp (gridFloor_mem s o₁ j w.re) h1 h2',
    eq_latticeFloor hp (gridFloor_mem s o₂ j w.im) h3 h4'⟩

/-- If an off-grid point `z` lies in the square of generation `j` at `w`, that square is the
square of generation `j` at `z`. -/
theorem squareAt_eq_of_mem {z w : ℂ} (hz : IsOffGrid s o₁ o₂ z) {j : ℤ}
    (h : z ∈ squareAt s o₁ o₂ j w) : squareAt s o₁ o₂ j w = squareAt s o₁ o₂ j z := by
  obtain ⟨h1, h2⟩ := gridFloor_eq_of_mem_squareAt hz h
  unfold squareAt
  rw [h1, h2]

/-- Two half-open intervals containing the same point share an interior point. -/
theorem exists_mem_Ioo_inter {a a' p p' t : ℝ} (h1 : a ≤ t) (h2 : t < a + p) (h3 : a' ≤ t)
    (h4 : t < a' + p') : ∃ x, x ∈ Ioo a (a + p) ∧ x ∈ Ioo a' (a' + p') := by
  have hm := lt_min h2 h4
  have hl := min_le_left (a + p) (a' + p')
  have hr := min_le_right (a + p) (a' + p')
  exact ⟨(t + min (a + p) (a' + p')) / 2, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The squares of two generations at the same point have a common interior point. -/
theorem exists_mem_interior_squareAt_inter (j j' : ℤ) (w : ℂ) :
    ∃ ζ, ζ ∈ interior (squareAt s o₁ o₂ j w) ∧ ζ ∈ interior (squareAt s o₁ o₂ j' w) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  have hp' : (0 : ℝ) < (2 : ℝ) ^ (s + (j' : ℝ)) := by positivity
  obtain ⟨x, hx, hx'⟩ := exists_mem_Ioo_inter
    (latticeFloor_le hp (-((2 : ℝ) ^ s * o₁ j.toNat)) w.re)
    (lt_latticeFloor_add hp (-((2 : ℝ) ^ s * o₁ j.toNat)) w.re)
    (latticeFloor_le hp' (-((2 : ℝ) ^ s * o₁ j'.toNat)) w.re)
    (lt_latticeFloor_add hp' (-((2 : ℝ) ^ s * o₁ j'.toNat)) w.re)
  obtain ⟨y, hy, hy'⟩ := exists_mem_Ioo_inter
    (latticeFloor_le hp (-((2 : ℝ) ^ s * o₂ j.toNat)) w.im)
    (lt_latticeFloor_add hp (-((2 : ℝ) ^ s * o₂ j.toNat)) w.im)
    (latticeFloor_le hp' (-((2 : ℝ) ^ s * o₂ j'.toNat)) w.im)
    (lt_latticeFloor_add hp' (-((2 : ℝ) ^ s * o₂ j'.toNat)) w.im)
  refine ⟨⟨x, y⟩, ?_, ?_⟩
  · rw [squareAt, interior_cornerSquare]
    exact mem_reProdIm.2 ⟨hx, hy⟩
  · rw [squareAt, interior_cornerSquare]
    exact mem_reProdIm.2 ⟨hx', hy'⟩

/-- For compatible offsets, the squares of the system at any point `w` increase with the
generation. -/
theorem squareAt_mono_of_isCompatible (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) (w : ℂ) :
    Monotone fun j => squareAt s o₁ o₂ j w := by
  intro j j' hjj
  rcases generationSquares_nest h₁ h₂ hjj (squareAt_mem_generationSquares j w)
      (squareAt_mem_generationSquares j' w) with h | h
  · exact h
  · obtain ⟨ζ, hζ, hζ'⟩ := exists_mem_interior_squareAt_inter (s := s) (o₁ := o₁) (o₂ := o₂) j j' w
    exact absurd hζ' (disjoint_left.1 h hζ)

/-- For an off-grid point `z`, the points `w` whose square of generation `j` contains `z` form the
half-open square of generation `j` containing `z`. -/
theorem setOf_mem_squareAt_eq {z : ℂ} (hz : IsOffGrid s o₁ o₂ z) (j : ℤ) :
    {w | z ∈ squareAt s o₁ o₂ j w} =
      Ico (gridFloor s o₁ j z.re) (gridFloor s o₁ j z.re + (2 : ℝ) ^ (s + (j : ℝ))) ×ℂ
        Ico (gridFloor s o₂ j z.im) (gridFloor s o₂ j z.im + (2 : ℝ) ^ (s + (j : ℝ))) := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  ext w
  simp only [mem_ofPred_eq, mem_reProdIm, mem_Ico]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := gridFloor_eq_of_mem_squareAt hz h
    rw [← h1, ← h2]
    exact ⟨⟨latticeFloor_le hp _ _, lt_latticeFloor_add hp _ _⟩,
      ⟨latticeFloor_le hp _ _, lt_latticeFloor_add hp _ _⟩⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    have hA : gridFloor s o₁ j z.re = gridFloor s o₁ j w.re :=
      eq_latticeFloor hp (gridFloor_mem s o₁ j z.re) h1 h2
    have hB : gridFloor s o₂ j z.im = gridFloor s o₂ j w.im :=
      eq_latticeFloor hp (gridFloor_mem s o₂ j z.im) h3 h4
    have hzz := mem_squareAt (s := s) (o₁ := o₁) (o₂ := o₂) j z
    unfold squareAt at hzz ⊢
    rwa [← hA, ← hB]

end Squares

/-- The area of the half-open square `[a, a + ℓ) × [b, b + ℓ)`. -/
theorem volume_reProdIm_Ico (a b ℓ : ℝ) :
    volume (Ico a (a + ℓ) ×ℂ Ico b (b + ℓ)) = ENNReal.ofReal ℓ * ENNReal.ofReal ℓ := by
  have hset : Ico a (a + ℓ) ×ℂ Ico b (b + ℓ) =
      measurableEquivRealProd ⁻¹' (Ico a (a + ℓ) ×ˢ Ico b (b + ℓ)) := by
    ext z
    simp only [mem_reProdIm, mem_preimage, measurableEquivRealProd_apply, mem_prod]
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Ico a (a + ℓ) ×ˢ Ico b (b + ℓ)) (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico, Real.volume_Ico,
    add_sub_cancel_left, add_sub_cancel_left] at h
  rw [hset]
  exact h

theorem measurableSet_reProdIm_Ico (a b ℓ : ℝ) :
    MeasurableSet (Ico a (a + ℓ) ×ℂ Ico b (b + ℓ)) :=
  (continuous_re.measurable measurableSet_Ico).inter (continuous_im.measurable measurableSet_Ico)

/-- The uniform-average kernel centred at the points `w`, evaluated at an off-grid point `z`, is
the sum over the generations selected at `z` of the normalized indicators of the sets
`{w | z ∈ S_j(w)}`. -/
theorem averageKernel_reverse_eq {m : ℝ≥0∞} (H : GMSSpace) {q : DyadicCoord}
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {z : ℂ}
    (hz : IsOffGrid q.1 q.2.1 q.2.2 z) (w : ℂ) :
    averageKernel m (H, (q, w), z) =
      ∑' j : ℤ, (selectionSet (complexCells H.1) m q z).indicator
        (fun j => (volume (squareAt q.1 q.2.1 q.2.2 j z))⁻¹ *
          {w' | z ∈ squareAt q.1 q.2.1 q.2.2 j w'}.indicator (fun _ => (1 : ℝ≥0∞)) w) j := by
  unfold averageKernel selectedSum
  refine tsum_congr fun j => ?_
  by_cases hj : z ∈ squareAt q.1 q.2.1 q.2.2 j w
  · have e1 := squareAt_eq_of_mem hz hj
    have e2 := squareAt_eq_of_mem hz
      (squareAt_mono_of_isCompatible h₁ h₂ w (by omega : j ≤ j + 1) hj)
    have hmem : j ∈ selectionSet (complexCells H.1) m q w ↔
        j ∈ selectionSet (complexCells H.1) m q z := by
      simp only [selectionSet, mem_ofPred_eq, e1, e2]
    have hR : {w' | z ∈ squareAt q.1 q.2.1 q.2.2 j w'}.indicator (fun _ => (1 : ℝ≥0∞)) w = 1 :=
      indicator_of_mem (show w ∈ {w' | z ∈ squareAt q.1 q.2.1 q.2.2 j w'} from hj) _
    have hL : (squareAt q.1 q.2.1 q.2.2 j z).indicator (fun _ => (1 : ℝ≥0∞)) z = 1 :=
      indicator_of_mem (mem_squareAt j z) _
    by_cases hjz : j ∈ selectionSet (complexCells H.1) m q z
    · simp only [indicator_of_mem (hmem.2 hjz), indicator_of_mem hjz, hR, e1, hL]
    · rw [indicator_of_notMem (fun h => hjz (hmem.1 h)), indicator_of_notMem hjz]
  · classical
    simp [Set.indicator_apply, hj]

/-- **The kernel integrates to one in its centre** (deterministic form): for compatible offsets,
an off-grid point `z` and a mass `m` for which exactly one generation is selected at `z`,
`∫ |S_m^w|⁻¹ 1(z ∈ S_m^w) dw = 1`. -/
theorem lintegral_averageKernel_reverse {m : ℝ≥0∞} (H : GMSSpace) {q : DyadicCoord}
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) {z : ℂ}
    (hz : IsOffGrid q.1 q.2.1 q.2.2 z)
    (hsel : selectedSum (complexCells H.1) m q z (fun _ => 1) = 1) :
    ∫⁻ w, averageKernel m (H, (q, w), z) ∂volume = 1 := by
  have hS : ∀ j : ℤ, MeasurableSet {w' | z ∈ squareAt q.1 q.2.1 q.2.2 j w'} := fun j => by
    rw [setOf_mem_squareAt_eq hz j]
    exact measurableSet_reProdIm_Ico _ _ _
  have hmeas : ∀ j : ℤ, AEMeasurable (fun w => (selectionSet (complexCells H.1) m q z).indicator
      (fun j => (volume (squareAt q.1 q.2.1 q.2.2 j z))⁻¹ *
        {w' | z ∈ squareAt q.1 q.2.1 q.2.2 j w'}.indicator (fun _ => (1 : ℝ≥0∞)) w) j) volume :=
    fun j => by
      by_cases hjz : j ∈ selectionSet (complexCells H.1) m q z
      · simp only [indicator_of_mem hjz]
        exact ((measurable_const.indicator (hS j)).const_mul _).aemeasurable
      · simp only [indicator_of_notMem hjz]
        exact aemeasurable_const
  rw [lintegral_congr (averageKernel_reverse_eq H h₁ h₂ hz), lintegral_tsum hmeas]
  refine Eq.trans ?_ hsel
  unfold selectedSum
  refine tsum_congr fun j => ?_
  by_cases hjz : j ∈ selectionSet (complexCells H.1) m q z
  · have hp : (0 : ℝ) < (2 : ℝ) ^ (q.1 + (j : ℝ)) := by positivity
    simp only [indicator_of_mem hjz]
    rw [lintegral_const_mul _ (measurable_const.indicator (hS j)),
      lintegral_indicator_const (hS j), one_mul, setOf_mem_squareAt_eq hz j, volume_reProdIm_Ico,
      squareAt, volume_cornerSquare]
    exact ENNReal.inv_mul_cancel
      (mul_ne_zero (ENNReal.ofReal_pos.2 hp).ne' (ENNReal.ofReal_pos.2 hp).ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  · simp only [indicator_of_notMem hjz, lintegral_zero]

/-- **The kernel integrates to one in its centre**: almost surely in the uniform dyadic system,
for every mass `m ∈ (0, ∞)`, `∫ |S_m^w|⁻¹ 1(z ∈ S_m^w) dw = 1`. -/
theorem ae_lintegral_averageKernel_reverse (H : GMSSpace) (z : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∫⁻ w, averageKernel m (H, (q, w), z) ∂volume = 1 := by
  filter_upwards [ae_isCompatible_isOffGrid_system z,
    ae_selectedSum_eq_cappedSquare_complexCells H.2 z] with q hq hs
  intro m hm0 hmtop
  exact lintegral_averageKernel_reverse H hq.1 hq.2.1 hq.2.2 (hs m hm0 hmtop fun _ => 1)

end LatticeProb.CellConfigCappedSquare
