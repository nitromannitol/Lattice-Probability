import LatticeProb.Prob.DyadicOffsetDilation

/-!
# Invariance of the uniform dyadic system under dilations and translations

A uniform dyadic system of the plane (Gwynne, Miller and Sheffield, *An invariance principle for
ergodic scale-free random environments*, arXiv 1807.07515, Section 2.1) is described by a scale
`s ∈ [0, 1)` and, for each of the two coordinates, an offset sequence `o` with law `offsetLaw`
(see `LatticeProb.Prob.DyadicOffsetLaw`): the origin-containing square of generation `k ∈ ℕ` has
side length `2^(s + k)` and, in each coordinate, left end `-2^s o k`. The scale is uniform on
`[0, 1)` and independent of the two offset sequences, which are independent of each other.

The image of the system under `x ↦ 2^t x` has scale `fract (s + t)`, and its offsets are those
of the image of the system under `x ↦ 2^m x` with `m = ⌊s + t⌋`, that is `dilateOffsets m o`.
The image of the system under `x ↦ x - z` has the same scale, and in each coordinate the
offsets `shiftOffsets (-2^(-s) z_i) o`.

## Main statements

* `LatticeProb.DyadicOffset.measurePreserving_dilateOffsets`: `dilateOffsets m` preserves
  `offsetLaw` for every `m : ℤ`.
* `LatticeProb.DyadicOffset.measurePreserving_scaleSkew`: for a family `F m` of maps preserving a
  law `ν`, the map `(s, ω) ↦ (fract (s + t), F ⌊s + t⌋ ω)` preserves `unifIco 1 ⊗ ν`.
* `LatticeProb.DyadicOffset.measurePreserving_dilateScale₂`: the coordinate law
  `unifIco 1 ⊗ offsetLaw ⊗ offsetLaw` of the uniform dyadic system of the plane is invariant under
  dilation by `2^t` for every real `t`.
* `LatticeProb.DyadicOffset.measurePreserving_shiftSkew₂`: it is invariant under the fibrewise
  translations `(s, o¹, o²) ↦ (s, shiftOffsets (c₁ s) o¹, shiftOffsets (c₂ s) o²)` for measurable
  `c₁, c₂`, in particular under every translation of the plane.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-- The offsets of the image of the dyadic system under `x ↦ 2^m x`. -/
noncomputable def dilateOffsets : ℤ → (ℕ → ℝ) → ℕ → ℝ
  | Int.ofNat n => doubleOffsets^[n]
  | Int.negSucc n => halfOffsets^[n + 1]

/-- **Invariance of the offset law under dilation by `2^m`.** -/
theorem measurePreserving_dilateOffsets :
    ∀ m : ℤ, MeasurePreserving (dilateOffsets m) offsetLaw offsetLaw
  | Int.ofNat n => measurePreserving_doubleOffsets.iterate n
  | Int.negSucc n => measurePreserving_halfOffsets.iterate (n + 1)

theorem measurable_dilateOffsets (m : ℤ) : Measurable (dilateOffsets m) :=
  (measurePreserving_dilateOffsets m).measurable

/-- Iterated doubling: generation `k + n` of the image under `x ↦ 2^n x` is `2^n` times
generation `k`. -/
theorem doubleOffsets_iterate_apply (n : ℕ) :
    ∀ (o : ℕ → ℝ) (k : ℕ), doubleOffsets^[n] o (k + n) = 2 ^ n * o k := by
  induction n with
  | zero => intro o k; simp
  | succ n ih =>
    intro o k
    rw [Function.iterate_succ_apply, show k + (n + 1) = (k + 1) + n by omega, ih, pow_succ]
    show 2 ^ n * (2 * o k) = 2 ^ n * 2 * o k
    ring

/-- Iterated halving: generation `k` of the image under `x ↦ 2^(-n) x` is `2^(-n)` times
generation `k + n`. -/
theorem halfOffsets_iterate_apply (n : ℕ) :
    ∀ (o : ℕ → ℝ) (k : ℕ), halfOffsets^[n] o k = o (k + n) / 2 ^ n := by
  induction n with
  | zero => intro o k; simp
  | succ n ih =>
    intro o k
    rw [Function.iterate_succ_apply, ih]
    show o (k + n + 1) / 2 / 2 ^ n = o (k + n + 1) / 2 ^ (n + 1)
    rw [pow_succ]
    ring

/-- **Dilation of the scale coordinate.** If every `F m` preserves `ν`, then
`(s, ω) ↦ (fract (s + t), F ⌊s + t⌋ ω)` preserves `unifIco 1 ⊗ ν`. -/
theorem measurePreserving_scaleSkew {γ : Type*} [MeasurableSpace γ] {ν : Measure γ} [SFinite ν]
    (F : ℤ → γ → γ) (hF : ∀ m, MeasurePreserving (F m) ν ν) (t : ℝ) :
    MeasurePreserving (fun p : ℝ × γ => (Int.fract (p.1 + t), F ⌊p.1 + t⌋ p.2))
      ((unifIco 1).prod ν) ((unifIco 1).prod ν) := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hbase : MeasurePreserving (fun s : ℝ => Int.fract (s + t)) (unifIco 1) (unifIco 1) := by
    refine ⟨(measurable_add_const t).fract, ?_⟩
    have h := map_toIcoMod_sub_unifIco (zero_lt_one' ℝ) (-t)
    simp only [sub_neg_eq_add, toIcoMod_zero_one] at h
    exact h
  have hm : Measurable fun q : γ × ℤ => F q.2 q.1 :=
    measurable_from_prod_countable_left fun m => (hF m).measurable
  refine hbase.skew_product (g := fun s ω => F ⌊s + t⌋ ω) ?_
    (ae_of_all _ fun s => (hF _).map_eq)
  exact hm.comp (measurable_snd.prodMk (measurable_fst.add_const t).floor)

/-- **Dilation invariance, one coordinate.** -/
theorem measurePreserving_dilateScale (t : ℝ) :
    MeasurePreserving (fun p : ℝ × (ℕ → ℝ) => (Int.fract (p.1 + t), dilateOffsets ⌊p.1 + t⌋ p.2))
      ((unifIco 1).prod offsetLaw) ((unifIco 1).prod offsetLaw) :=
  measurePreserving_scaleSkew dilateOffsets measurePreserving_dilateOffsets t

/-- **Dilation invariance of the uniform dyadic system of the plane**: the coordinate law
`unifIco 1 ⊗ offsetLaw ⊗ offsetLaw` is invariant under dilation by `2^t`, for every real `t`. -/
theorem measurePreserving_dilateScale₂ (t : ℝ) :
    MeasurePreserving (fun p : ℝ × ((ℕ → ℝ) × (ℕ → ℝ)) =>
        (Int.fract (p.1 + t), Prod.map (dilateOffsets ⌊p.1 + t⌋) (dilateOffsets ⌊p.1 + t⌋) p.2))
      ((unifIco 1).prod (offsetLaw.prod offsetLaw))
      ((unifIco 1).prod (offsetLaw.prod offsetLaw)) :=
  measurePreserving_scaleSkew (fun m => Prod.map (dilateOffsets m) (dilateOffsets m))
    (fun m => (measurePreserving_dilateOffsets m).prod (measurePreserving_dilateOffsets m)) t

theorem measurePreserving_shiftOffsets (c : ℝ) :
    MeasurePreserving (shiftOffsets c) offsetLaw offsetLaw :=
  ⟨measurable_shiftOffsets c, map_shiftOffsets_offsetLaw c⟩

/-- Joint measurability of the translated offsets in the translation and the offsets. -/
theorem measurable_shiftOffsets_uncurry {α : Type*} [MeasurableSpace α] {c : α → ℝ}
    (hc : Measurable c) : Measurable fun p : α × (ℕ → ℝ) => shiftOffsets (c p.1) p.2 :=
  measurable_pi_iff.mpr fun k => (measurable_toIcoMod (two_pow_pos' k)).comp
    (((measurable_pi_apply k).comp measurable_snd).sub (hc.comp measurable_fst))

/-- **Fibrewise translation, one coordinate.** For every s-finite `μ` and measurable `c`,
`(s, o) ↦ (s, shiftOffsets (c s) o)` preserves `μ ⊗ offsetLaw`. -/
theorem measurePreserving_shiftSkew {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {c : α → ℝ} (hc : Measurable c) :
    MeasurePreserving (fun p : α × (ℕ → ℝ) => (p.1, shiftOffsets (c p.1) p.2))
      (μ.prod offsetLaw) (μ.prod offsetLaw) :=
  (MeasurePreserving.id μ).skew_product (g := fun s o => shiftOffsets (c s) o)
    (measurable_shiftOffsets_uncurry hc) (ae_of_all _ fun s => map_shiftOffsets_offsetLaw (c s))

/-- **Translation invariance of the uniform dyadic system of the plane**, in the fibrewise form:
for measurable `c₁, c₂` (for the translation by `z`, `c_i s = -2^(-s) z_i`) the map
`(s, o¹, o²) ↦ (s, shiftOffsets (c₁ s) o¹, shiftOffsets (c₂ s) o²)` preserves
`μ ⊗ offsetLaw ⊗ offsetLaw` for every s-finite `μ`. -/
theorem measurePreserving_shiftSkew₂ {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {c₁ c₂ : α → ℝ} (hc₁ : Measurable c₁) (hc₂ : Measurable c₂) :
    MeasurePreserving (fun p : α × ((ℕ → ℝ) × (ℕ → ℝ)) =>
        (p.1, Prod.map (shiftOffsets (c₁ p.1)) (shiftOffsets (c₂ p.1)) p.2))
      (μ.prod (offsetLaw.prod offsetLaw)) (μ.prod (offsetLaw.prod offsetLaw)) := by
  refine (MeasurePreserving.id μ).skew_product
    (g := fun s q => Prod.map (shiftOffsets (c₁ s)) (shiftOffsets (c₂ s)) q) ?_
    (ae_of_all _ fun s =>
      ((measurePreserving_shiftOffsets (c₁ s)).prod (measurePreserving_shiftOffsets (c₂ s))).map_eq)
  exact ((measurable_shiftOffsets_uncurry hc₁).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk
    ((measurable_shiftOffsets_uncurry hc₂).comp (measurable_fst.prodMk measurable_snd.snd))

end LatticeProb.DyadicOffset
