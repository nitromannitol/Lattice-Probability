import LatticeProb.Prob.DyadicCappedSquare

/-!
# Almost every point lies on no grid line of a dyadic system

For a dyadic system of the plane with scale `s` and offset sequences `o₁, o₂`, the grid lines of
generation `j` are the vertical lines through the points of `gridPoints s o₁ j` and the horizontal
lines through the points of `gridPoints s o₂ j`. There are countably many of them. Hence:

* for fixed `s, o₁, o₂`, Lebesgue-almost every `w ∈ ℂ` lies on no grid line
  (`ae_isOffGrid_volume`);
* for fixed `w ∈ ℂ`, almost every dyadic system of the uniform dyadic system of the plane (scale
  uniform on `[0, 1)`, two independent offset sequences of law `offsetLaw`) has no grid line
  through `w` (`ae_isOffGrid_system`). Indeed the offset of generation `k` is uniform on
  `[0, 2^k)` (`map_eval_offsetLaw`), so it has no atoms, and for a fixed scale the event that `w`
  lies on a line of generation `j` asks this offset to lie in a countable set; Fubini over the
  scale concludes.

Together with the compatibility of almost every offset sequence, the capped squares of the dyadic
system around a fixed point are then almost surely described by the chain of squares containing
it (`ae_isCompatible_isOffGrid_system`), as in Gwynne, Miller and Sheffield, *An invariance
principle for ergodic scale-free random environments* (arXiv 1807.07515), Section 2.
-/

open MeasureTheory Set Complex
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-! ### Countability of the grid points -/

theorem countable_shiftedLattice (a p : ℝ) : (shiftedLattice a p).Countable :=
  (countable_range fun n : ℤ => a + n * p).mono (by rintro x ⟨n, rfl⟩; exact ⟨n, rfl⟩)

theorem countable_gridPoints (s : ℝ) (o : ℕ → ℝ) (j : ℤ) : (gridPoints s o j).Countable :=
  countable_shiftedLattice _ _

/-- For fixed `s`, `x` and `j`, the offsets `y` for which `x` lies in the progression
`-2^s y + 2^(s + j) ℤ` form a countable set. -/
theorem countable_offsetSet (s x : ℝ) (j : ℤ) :
    {y : ℝ | x ∈ shiftedLattice (-((2 : ℝ) ^ s * y)) ((2 : ℝ) ^ (s + (j : ℝ)))}.Countable := by
  refine (countable_range fun n : ℤ => ((n : ℝ) * (2 : ℝ) ^ (s + (j : ℝ)) - x) / (2 : ℝ) ^ s).mono ?_
  rintro y ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have h2 : (0 : ℝ) < (2 : ℝ) ^ s := Real.rpow_pos_of_pos two_pos s
  show ((n : ℝ) * (2 : ℝ) ^ (s + (j : ℝ)) - x) / (2 : ℝ) ^ s = y
  rw [div_eq_iff h2.ne']
  linear_combination (-1 : ℝ) * hn

/-! ### Lebesgue-almost every point is off the grid -/

/-- The preimage of a countable set of reals under the real part is Lebesgue-null. -/
theorem volume_re_preimage_of_countable {A : Set ℝ} (hA : A.Countable) :
    volume (re ⁻¹' A) = 0 := by
  have h : re ⁻¹' A = measurableEquivRealProd ⁻¹' (A ×ˢ univ) := by
    ext w; simp [measurableEquivRealProd_apply]
  rw [h, volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, hA.measure_zero, zero_mul]

/-- The preimage of a countable set of reals under the imaginary part is Lebesgue-null. -/
theorem volume_im_preimage_of_countable {A : Set ℝ} (hA : A.Countable) :
    volume (im ⁻¹' A) = 0 := by
  have h : im ⁻¹' A = measurableEquivRealProd ⁻¹' (univ ×ˢ A) := by
    ext w; simp [measurableEquivRealProd_apply]
  rw [h, volume_preserving_equiv_real_prod.measure_preimage_equiv, Measure.volume_eq_prod,
    Measure.prod_prod, hA.measure_zero, mul_zero]

theorem ae_re_not_mem_of_countable {A : Set ℝ} (hA : A.Countable) : ∀ᵐ w : ℂ, w.re ∉ A :=
  ae_iff.mpr (measure_mono_null (t := re ⁻¹' A) (fun _ hw => not_not.mp hw)
    (volume_re_preimage_of_countable hA))

theorem ae_im_not_mem_of_countable {A : Set ℝ} (hA : A.Countable) : ∀ᵐ w : ℂ, w.im ∉ A :=
  ae_iff.mpr (measure_mono_null (t := im ⁻¹' A) (fun _ hw => not_not.mp hw)
    (volume_im_preimage_of_countable hA))

/-- For every dyadic system, Lebesgue-almost every point of the plane lies on no grid line. -/
theorem ae_isOffGrid_volume (s : ℝ) (o₁ o₂ : ℕ → ℝ) : ∀ᵐ w : ℂ, IsOffGrid s o₁ o₂ w := by
  refine ae_all_iff.mpr fun j => ?_
  filter_upwards [ae_re_not_mem_of_countable (countable_gridPoints s o₁ j),
    ae_im_not_mem_of_countable (countable_gridPoints s o₂ j)] with w h₁ h₂
  exact ⟨h₁, h₂⟩

/-! ### A fixed point is almost surely off the grid of the uniform dyadic system -/

/-- The uniform law on `[0, p)` charges no countable set. -/
theorem unifIco_of_countable (p : ℝ) {C : Set ℝ} (hC : C.Countable) : unifIco p C = 0 := by
  have h0 : volume.restrict (Ico 0 p) C = 0 :=
    nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans (hC.measure_zero volume).le)
  rw [unifIco, Measure.smul_apply, h0, smul_zero]

/-- Under the offset law, the offset of generation `k` is uniform on `[0, 2^k)`. -/
theorem map_eval_offsetLaw (k : ℕ) : offsetLaw.map (fun o => o k) = unifIco (2 ^ k) := by
  rw [offsetLaw, Measure.map_map (measurable_pi_apply k) (measurable_offsetsL 1)]
  exact map_offsetsL_one_eval k

/-- The offset of a fixed generation lies in a given countable set with probability zero. -/
theorem offsetLaw_eval_mem_of_countable (k : ℕ) {C : Set ℝ} (hC : C.Countable) :
    offsetLaw {o | o k ∈ C} = 0 := by
  have h := congrArg (fun μ : Measure ℝ => μ C) (map_eval_offsetLaw k)
  rw [Measure.map_apply (measurable_pi_apply k) hC.measurableSet, unifIco_of_countable _ hC] at h
  exact h

/-- For a fixed scale, a fixed real is a grid point of a fixed generation with probability
zero under the offset law. -/
theorem offsetLaw_mem_gridPoints (s x : ℝ) (j : ℤ) : offsetLaw {o | x ∈ gridPoints s o j} = 0 :=
  offsetLaw_eval_mem_of_countable j.toNat (countable_offsetSet s x j)

theorem measurableSet_mem_gridPoints {β : Type*} [MeasurableSpace β] {f : β → ℝ}
    {g : β → ℕ → ℝ} (hf : Measurable f) (hg : Measurable g) (x : ℝ) (j : ℤ) :
    MeasurableSet {b | x ∈ gridPoints (f b) (g b) j} := by
  have h : {b | x ∈ gridPoints (f b) (g b) j} =
      ⋃ n : ℤ, {b | x = -((2 : ℝ) ^ f b * g b j.toNat) + (n : ℝ) * (2 : ℝ) ^ (f b + (j : ℝ))} := by
    ext b; rw [mem_iUnion]; exact Iff.rfl
  rw [h]
  refine MeasurableSet.iUnion fun n => measurableSet_eq_fun measurable_const ?_
  exact (((measurable_const.pow hf).mul ((measurable_pi_apply j.toNat).comp hg)).neg).add
    (measurable_const.mul (measurable_const.pow (hf.add_const _)))

/-- Fubini step: if, for every scale, a fixed real is almost surely not a grid point of
generation `j` of the offsets `g o`, then the same holds for almost every system. -/
theorem ae_not_mem_gridPoints_system (x : ℝ) (j : ℤ) {g : (ℕ → ℝ) × (ℕ → ℝ) → ℕ → ℝ}
    (hg : Measurable g) (h0 : ∀ s, (offsetLaw.prod offsetLaw) {o | x ∈ gridPoints s (g o) j} = 0) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), x ∉ gridPoints q.1 (g q.2) j := by
  have hE : MeasurableSet {q : ℝ × ((ℕ → ℝ) × (ℕ → ℝ)) | x ∈ gridPoints q.1 (g q.2) j} :=
    measurableSet_mem_gridPoints measurable_fst (hg.comp measurable_snd) x j
  refine ae_iff.mpr (measure_mono_null (t := {q | x ∈ gridPoints q.1 (g q.2) j})
    (fun _ hq => not_not.mp hq) ?_)
  rw [Measure.measure_prod_null hE]
  exact Filter.Eventually.of_forall fun s => h0 s

/-- For a fixed point `w` of the plane, almost every dyadic system of the uniform dyadic system
of the plane has no grid line through `w`. -/
theorem ae_isOffGrid_system (w : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsOffGrid q.1 q.2.1 q.2.2 w := by
  refine ae_all_iff.mpr fun j => ?_
  have h₁ : ∀ s, (offsetLaw.prod offsetLaw) {o | w.re ∈ gridPoints s o.1 j} = 0 := fun s =>
    measure_mono_null (t := {o | w.re ∈ gridPoints s o j} ×ˢ univ) (fun _ ho => ⟨ho, trivial⟩)
      (by rw [Measure.prod_prod, offsetLaw_mem_gridPoints, zero_mul])
  have h₂ : ∀ s, (offsetLaw.prod offsetLaw) {o | w.im ∈ gridPoints s o.2 j} = 0 := fun s =>
    measure_mono_null (t := univ ×ˢ {o | w.im ∈ gridPoints s o j}) (fun _ ho => ⟨trivial, ho⟩)
      (by rw [Measure.prod_prod, offsetLaw_mem_gridPoints, mul_zero])
  filter_upwards [ae_not_mem_gridPoints_system w.re j measurable_fst h₁,
    ae_not_mem_gridPoints_system w.im j measurable_snd h₂] with q hq₁ hq₂
  exact ⟨hq₁, hq₂⟩

/-- Almost every system of the uniform dyadic system of the plane has compatible offset
sequences in both coordinates. -/
theorem ae_isCompatible_system :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsCompatible q.2.1 ∧ IsCompatible q.2.2 := by
  have h := ae_iff.mp ae_isCompatible_offsetLaw
  have h₁ : ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsCompatible q.2.1 :=
    ae_iff.mpr (measure_mono_null (t := univ ×ˢ ({o | ¬IsCompatible o} ×ˢ univ))
      (fun _ hq => ⟨trivial, hq, trivial⟩)
      (by rw [Measure.prod_prod, Measure.prod_prod, h, zero_mul, mul_zero]))
  have h₂ : ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), IsCompatible q.2.2 :=
    ae_iff.mpr (measure_mono_null (t := univ ×ˢ (univ ×ˢ {o | ¬IsCompatible o}))
      (fun _ hq => ⟨trivial, trivial, hq⟩)
      (by rw [Measure.prod_prod, Measure.prod_prod, h, mul_zero, mul_zero]))
  filter_upwards [h₁, h₂] with q hq₁ hq₂
  exact ⟨hq₁, hq₂⟩

/-- For a fixed point `w`, almost every system of the uniform dyadic system of the plane is
compatible in both coordinates and has no grid line through `w`; the capped squares around `w`
are then described by the chain `squareAt j w` (see `isCappedSquare_squareAt_iff`). -/
theorem ae_isCompatible_isOffGrid_system (w : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw),
      IsCompatible q.2.1 ∧ IsCompatible q.2.2 ∧ IsOffGrid q.1 q.2.1 q.2.2 w := by
  filter_upwards [ae_isCompatible_system, ae_isOffGrid_system w] with q hq hw
  exact ⟨hq.1, hq.2, hw⟩

end LatticeProb.DyadicOffset
