import LatticeProb.Prob.DyadicCappedSquare
import LatticeProb.Euclidean.CellMass

/-!
# The cell mass along the dyadic squares containing a point

Let `c : ι → Set ℂ` be a countable, locally finite family of cells covering the plane, and let
`cellMass volume c S = ∑' i, Area (c i ∩ S) / Area (c i)` be the number of cells in `S`, with the
fractional parts of the cells meeting the boundary of `S` counted (Gwynne-Miller-Sheffield,
*An invariance principle for ergodic scale-free random environments*, (2.1)).

For a dyadic system with compatible offsets and a point `w` on no grid line, the squares
`squareAt s o₁ o₂ j w`, `j ∈ ℤ`, form the increasing chain of the dyadic squares containing `w`.
We show:

* the squares are compact, of area `side ^ 2`, and the increments of the chain have positive area;
* the cell mass is strictly increasing along the chain (the observation in the proof of Lemma 2.2
  of the paper), so the square of generation `j` is `Ŝ_m^w` exactly for `m` in the half-open
  interval between the masses of generations `j` and `j + 1`;
* for cells of positive area the mass tends to `0` as `j → -∞`, and for compact cells it tends to
  `∞` as `j → +∞` when the chain exhausts the plane;
* hence `Ŝ_m^w` exists for every `m ∈ (0, ∞)`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal

namespace LatticeProb.CellMass

variable {E ι : Type*} [MeasurableSpace E] (μ : Measure E) (c : ι → Set E)

/-- The cell mass of `S ⊆ T` is at most the measure of `S` times the sum of the reciprocal cell
measures over a finite set of indices containing every cell that meets `T`. -/
theorem cellMass_le_measure_mul {S T : Set E} (hST : S ⊆ T) {F : Finset ι}
    (hF : ∀ i, (c i ∩ T).Nonempty → i ∈ F) :
    cellMass μ c S ≤ μ S * ∑ i ∈ F, (μ (c i))⁻¹ := by
  have hzero : ∀ i ∉ F, μ (c i ∩ S) / μ (c i) = 0 := by
    intro i hi
    have h : c i ∩ S = ∅ := by
      rw [← not_nonempty_iff_eq_empty]
      exact fun hne => hi (hF i (hne.mono (inter_subset_inter_right _ hST)))
    rw [h, measure_empty, ENNReal.zero_div]
  calc cellMass μ c S = ∑ i ∈ F, μ (c i ∩ S) / μ (c i) := tsum_eq_sum hzero
    _ ≤ ∑ i ∈ F, μ S * (μ (c i))⁻¹ := Finset.sum_le_sum fun i _ => by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (measure_mono inter_subset_right) zero_le
    _ = μ S * ∑ i ∈ F, (μ (c i))⁻¹ := (Finset.mul_sum _ _ _).symm

/-- Along an increasing chain exhausting the space, the cell mass of infinitely many cells of
finite positive measure tends to infinity. -/
theorem tendsto_cellMass_atTop [Infinite ι] {C : ℤ → Set E} (hmono : Monotone C)
    (hexh : ⋃ j, C j = univ) (hpos : ∀ i, μ (c i) ≠ 0) (hfin : ∀ i, μ (c i) ≠ ∞) :
    Tendsto (fun j => cellMass μ c (C j)) atTop (𝓝 ∞) := by
  refine ENNReal.tendsto_nhds_top fun n => ?_
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq ι (n + 1)
  have hterm : ∀ i, Tendsto (fun j => μ (c i ∩ C j) / μ (c i)) atTop (𝓝 1) := by
    intro i
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun j => c i ∩ C j)
      (fun a b hab => inter_subset_inter_right (c i) (hmono hab))
    simp only [← inter_iUnion, hexh, inter_univ] at h
    have h2 := ENNReal.Tendsto.div_const h (Or.inr (hpos i))
    rwa [ENNReal.div_self (hpos i) (hfin i)] at h2
  have hsum : Tendsto (fun j => ∑ i ∈ F, μ (c i ∩ C j) / μ (c i)) atTop
      (𝓝 (F.card : ℝ≥0∞)) := by
    have := tendsto_finsetSum F fun i _ => hterm i
    rwa [Finset.sum_const, nsmul_eq_mul, mul_one] at this
  have hlt : (n : ℝ≥0∞) < F.card := by
    rw [hF]
    exact_mod_cast Nat.lt_succ_self n
  filter_upwards [hsum.eventually (lt_mem_nhds hlt)] with j hj
  exact hj.trans_le (ENNReal.sum_le_tsum F)

/-- A family of compact sets covering a noncompact space is infinite. -/
theorem infinite_of_iUnion_eq_univ {X : Type*} [TopologicalSpace X] [NoncompactSpace X]
    {c : ι → Set X} (hcover : ⋃ i, c i = univ) (hc : ∀ i, IsCompact (c i)) : Infinite ι := by
  rcases finite_or_infinite ι with h | h
  · have hK := isCompact_iUnion hc
    rw [hcover] at hK
    exact absurd hK (noncompact_univ X)
  · exact h

end LatticeProb.CellMass

namespace LatticeProb.DyadicOffset

open CellMass CappedSquare

/-! ### Corner squares -/

theorem isClosed_cornerSquare (a b ℓ : ℝ) : IsClosed (cornerSquare a b ℓ) := by
  rw [cornerSquare_eq_reProdIm]
  exact isClosed_Icc.reProdIm isClosed_Icc

theorem measurableSet_cornerSquare (a b ℓ : ℝ) : MeasurableSet (cornerSquare a b ℓ) :=
  (isClosed_cornerSquare a b ℓ).measurableSet

theorem isCompact_cornerSquare (a b ℓ : ℝ) : IsCompact (cornerSquare a b ℓ) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_cornerSquare a b ℓ) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := |a| + |ℓ| + (|b| + |ℓ|))).subset ?_
  intro z hz
  rw [mem_cornerSquare] at hz
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : |z.re| ≤ |a| + |ℓ| := abs_le.2
    ⟨by linarith [neg_abs_le a, abs_nonneg ℓ, hz.1], by linarith [le_abs_self a, le_abs_self ℓ, hz.2.1]⟩
  have h2 : |z.im| ≤ |b| + |ℓ| := abs_le.2
    ⟨by linarith [neg_abs_le b, abs_nonneg ℓ, hz.2.2.1],
      by linarith [le_abs_self b, le_abs_self ℓ, hz.2.2.2]⟩
  exact (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add h1 h2)

/-- The area of the square `[a, a + ℓ] × [b, b + ℓ]`. -/
theorem volume_cornerSquare (a b ℓ : ℝ) :
    volume (cornerSquare a b ℓ) = ENNReal.ofReal ℓ * ENNReal.ofReal ℓ := by
  have hset : cornerSquare a b ℓ =
      measurableEquivRealProd ⁻¹' (Icc a (a + ℓ) ×ˢ Icc b (b + ℓ)) := by
    ext z
    simp only [mem_cornerSquare, mem_preimage, measurableEquivRealProd_apply, mem_prod, mem_Icc,
      and_assoc]
  have h := Complex.volume_preserving_equiv_real_prod.measure_preimage
    (s := Icc a (a + ℓ) ×ˢ Icc b (b + ℓ)) (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet
  rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
    add_sub_cancel_left, add_sub_cancel_left] at h
  rw [hset]
  exact h

/-! ### The chain of squares containing a point -/

variable {s : ℝ} {o₁ o₂ : ℕ → ℝ}

theorem measurableSet_squareAt (j : ℤ) (w : ℂ) : MeasurableSet (squareAt s o₁ o₂ j w) :=
  measurableSet_cornerSquare _ _ _

theorem isCompact_squareAt (j : ℤ) (w : ℂ) : IsCompact (squareAt s o₁ o₂ j w) :=
  isCompact_cornerSquare _ _ _

theorem volume_squareAt (j : ℤ) (w : ℂ) :
    volume (squareAt s o₁ o₂ j w) =
      ENNReal.ofReal ((2 : ℝ) ^ (s + (j : ℝ))) * ENNReal.ofReal ((2 : ℝ) ^ (s + (j : ℝ))) :=
  volume_cornerSquare _ _ _

/-- For compatible offsets and an off-grid point, each square of the chain has positive area
outside the previous one (its side is twice as long). -/
theorem volume_squareAt_succ_diff_ne_zero (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    {w : ℂ} (hw : IsOffGrid s o₁ o₂ w) (j : ℤ) :
    volume (squareAt s o₁ o₂ (j + 1) w \ squareAt s o₁ o₂ j w) ≠ 0 := by
  have hsub : squareAt s o₁ o₂ j w ⊆ squareAt s o₁ o₂ (j + 1) w :=
    squareAt_mono h₁ h₂ hw (by omega)
  have hp : (0 : ℝ) < (2 : ℝ) ^ (s + (j : ℝ)) := by positivity
  have h2 : (2 : ℝ) ^ (s + ((j + 1 : ℤ) : ℝ)) = 2 * (2 : ℝ) ^ (s + (j : ℝ)) := by
    rw [Int.cast_add, Int.cast_one, ← add_assoc, Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0),
      mul_comm]
  rw [measure_sdiff hsub (measurableSet_squareAt j w).nullMeasurableSet
    (isCompact_squareAt j w).measure_lt_top.ne, volume_squareAt, volume_squareAt, h2,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ (s + (j : ℝ))),
    ← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_sub _ (mul_nonneg hp.le hp.le)]
  exact (ENNReal.ofReal_pos.2 (by nlinarith [mul_pos hp hp])).ne'

/-- The area of the square of generation `j` tends to `0` as `j → -∞`. -/
theorem tendsto_volume_squareAt_atBot (w : ℂ) :
    Tendsto (fun j : ℤ => volume (squareAt s o₁ o₂ j w)) atBot (𝓝 0) := by
  have hr : Tendsto (fun j : ℤ => (2 : ℝ) ^ (s + (j : ℝ))) atBot (𝓝 0) := by
    have h := ((tendsto_rpow_atBot_of_base_gt_one 2 one_lt_two).comp
      ((tendsto_intCast_atBot_iff (R := ℝ)).2 tendsto_id)).const_mul ((2 : ℝ) ^ s)
    rw [mul_zero] at h
    refine h.congr fun j => ?_
    simp only [Function.comp_apply, id_eq, Real.rpow_add two_pos]
  have h := ENNReal.tendsto_ofReal (hr.mul hr)
  rw [mul_zero, ENNReal.ofReal_zero] at h
  refine h.congr fun j => ?_
  rw [volume_squareAt, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (s + (j : ℝ)))]

/-! ### The cell mass along the chain -/

variable {ι : Type*} [Countable ι] {c : ι → Set ℂ}

/-- Gwynne-Miller-Sheffield, observation in the proof of Lemma 2.2: for a countable, locally
finite family of cells of finite area covering the plane, the cell mass is strictly increasing
along the squares of a dyadic system containing an off-grid point. -/
theorem strictMono_cellMass_squareAt (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {w : ℂ}
    (hw : IsOffGrid s o₁ o₂ w) (hc : LocallyFinite c) (hcover : ⋃ i, c i = univ)
    (hfin : ∀ i, volume (c i) ≠ ∞) :
    StrictMono fun j => cellMass volume c (squareAt s o₁ o₂ j w) :=
  strictMono_cellMass volume c (fun j => squareAt_mono h₁ h₂ hw (by omega))
    (fun j => measurableSet_squareAt j w) hcover hfin
    (volume_squareAt_succ_diff_ne_zero h₁ h₂ hw)
    (fun j => cellMass_ne_top volume c hc (isCompact_squareAt j w))

/-- Gwynne-Miller-Sheffield, Lemma 2.2, first part, for the cell mass: the square of generation
`j` containing the off-grid point `w` is `Ŝ_m^w` exactly for `m` between the cell masses of the
squares of generations `j` (included) and `j + 1` (excluded). -/
theorem isCappedSquare_squareAt_iff_cellMass (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    {w : ℂ} (hw : IsOffGrid s o₁ o₂ w) (hc : LocallyFinite c) (hcover : ⋃ i, c i = univ)
    (hfin : ∀ i, volume (c i) ≠ ∞) {m : ℝ≥0∞} (j : ℤ) :
    IsCappedSquare (dyadicSquares s o₁ o₂) (cellMass volume c) m w (squareAt s o₁ o₂ j w) ↔
      m ∈ Ico (cellMass volume c (squareAt s o₁ o₂ j w))
        (cellMass volume c (squareAt s o₁ o₂ (j + 1) w)) :=
  isCappedSquare_squareAt_iff h₁ h₂ hw (strictMono_cellMass_squareAt h₁ h₂ hw hc hcover hfin) j

omit [Countable ι] in
/-- For a locally finite family of cells of positive area, the cell mass of the square of
generation `j` containing an off-grid point tends to `0` as `j → -∞`. -/
theorem tendsto_cellMass_squareAt_atBot (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂) {w : ℂ}
    (hw : IsOffGrid s o₁ o₂ w) (hc : LocallyFinite c) (hpos : ∀ i, volume (c i) ≠ 0) :
    Tendsto (fun j => cellMass volume c (squareAt s o₁ o₂ j w)) atBot (𝓝 0) := by
  have hF := hc.finite_nonempty_inter_compact (isCompact_squareAt (s := s) (o₁ := o₁)
    (o₂ := o₂) 0 w)
  have hK : ∑ i ∈ hF.toFinset, (volume (c i))⁻¹ ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun i _ => ENNReal.inv_ne_top.2 (hpos i)
  have hlim := ENNReal.Tendsto.mul_const (tendsto_volume_squareAt_atBot (s := s) (o₁ := o₁)
    (o₂ := o₂) w) (Or.inr hK)
  rw [zero_mul] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_le_atBot 0] with j hj
  exact cellMass_le_measure_mul volume c (squareAt_mono h₁ h₂ hw hj)
    fun i hi => hF.mem_toFinset.2 hi

/-- Existence of `Ŝ_m^w` for the cell mass (Gwynne-Miller-Sheffield, (2.1)): for a countable,
locally finite family of compact cells of positive area covering the plane, an off-grid point
`w` whose chain of dyadic squares exhausts the plane, and `0 < m < ∞`, the square of the largest
generation of mass at most `m` is `Ŝ_m^w`. -/
theorem exists_isCappedSquare_squareAt_cellMass (h₁ : IsCompatible o₁) (h₂ : IsCompatible o₂)
    {w : ℂ} (hw : IsOffGrid s o₁ o₂ w) (hexh : ⋃ j, squareAt s o₁ o₂ j w = univ)
    (hc : LocallyFinite c) (hcover : ⋃ i, c i = univ) (hcpt : ∀ i, IsCompact (c i))
    (hpos : ∀ i, volume (c i) ≠ 0) {m : ℝ≥0∞} (hm0 : m ≠ 0) (hmtop : m ≠ ∞) :
    ∃ j, cellMass volume c (squareAt s o₁ o₂ j w) ≤ m ∧
      m < cellMass volume c (squareAt s o₁ o₂ (j + 1) w) ∧
      IsCappedSquare (dyadicSquares s o₁ o₂) (cellMass volume c) m w (squareAt s o₁ o₂ j w) := by
  have hfin : ∀ i, volume (c i) ≠ ∞ := fun i => (hcpt i).measure_lt_top.ne
  have hinf : Infinite ι := infinite_of_iUnion_eq_univ hcover hcpt
  refine exists_isCappedSquare_squareAt h₁ h₂ hw
    (strictMono_cellMass_squareAt h₁ h₂ hw hc hcover hfin).monotone ?_ ?_
  · obtain ⟨j, hj⟩ := ((tendsto_cellMass_squareAt_atBot h₁ h₂ hw hc hpos).eventually
      (gt_mem_nhds (pos_iff_ne_zero.2 hm0))).exists
    exact ⟨j, hj.le⟩
  · exact ((tendsto_cellMass_atTop volume c (squareAt_mono h₁ h₂ hw) hexh hpos hfin).eventually
      (lt_mem_nhds hmtop.lt_top)).exists

end LatticeProb.DyadicOffset
