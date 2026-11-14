import LatticeProb.Prob.DyadicOffsetLaw

/-!
# Dilation invariance of the uniform dyadic offset law

For the uniform dyadic system of the line with offset sequence `o` (generation `k` is the grid
`-o k + 2^k ℤ`, see `LatticeProb.Prob.DyadicOffsetLaw`), the image of the system under `x ↦ x / 2`
has the offsets `halfOffsets o`, with `halfOffsets o k = o (k + 1) / 2`, and the image under
`x ↦ 2 x` has the offsets `doubleOffsets o`, with `doubleOffsets o (k + 1) = 2 o k` and with
generation `0` the refinement `toIcoMod 1 0 (2 o 0)` of generation `1`.

## Main statements

* `LatticeProb.DyadicOffset.map_halfOffsets_offsetLaw`: the law of the offset sequence is invariant
  under `halfOffsets`. The first bit is absorbed into the base point: `(x + e 0) / 2` is again
  uniform on `[0, 1)` and independent of the remaining bits.
* `LatticeProb.DyadicOffset.map_doubleOffsets_offsetLaw`: the law is invariant under
  `doubleOffsets`, which inverts `halfOffsets` almost surely.

Together with `map_shiftOffsets_offsetLaw` these give the invariance of the uniform dyadic system
of the line under translations and under dilations by powers of two (Gwynne, Miller and Sheffield,
*An invariance principle for ergodic scale-free random environments*, arXiv 1807.07515, Lemma 2.1).
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-- Scaling the base length and the base point scales every offset. -/
theorem offsetsL_mul (c L x : ℝ) (e : ℕ → Bool) (k : ℕ) :
    offsetsL (c * L) (c * x) e k = c * offsetsL L x e k := by
  unfold offsetsL
  rw [mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The uniform law on `[0, c p)` rescaled by `c⁻¹` is the uniform law on `[0, p)`. -/
theorem map_inv_mul_unifIco {c p : ℝ} (hc : 0 < c) :
    (unifIco (c * p)).map (fun y => c⁻¹ * y) = unifIco p := by
  have hm : Measurable fun y : ℝ => c⁻¹ * y := by fun_prop
  have hpre : (fun y : ℝ => c⁻¹ * y) ⁻¹' Ico 0 p = Ico 0 (c * p) := by
    ext y
    simp only [mem_preimage, mem_Ico]
    have hcy : c * (c⁻¹ * y) = y := by
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [← hcy]; exact mul_nonneg hc.le h1
      · rw [← hcy]; exact mul_lt_mul_of_pos_left h2 hc
    · rintro ⟨h1, h2⟩
      refine ⟨mul_nonneg (inv_nonneg.2 hc.le) h1, ?_⟩
      have := mul_lt_mul_of_pos_left h2 (inv_pos.2 hc)
      rwa [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] at this
  rw [unifIco, unifIco, Measure.map_smul, ← hpre, ← Measure.restrict_map hm measurableSet_Ico,
    Real.map_volume_mul_left (inv_ne_zero hc.ne'), inv_inv, abs_of_pos hc,
    Measure.restrict_smul, smul_smul]
  congr 1
  rw [ENNReal.ofReal_mul hc.le, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl ENNReal.ofReal_ne_top), mul_right_comm,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top, one_mul]
  exact hm.aemeasurable

/-- Absorbing the first bit into the base point: `(x + L e 0, (e 1, e 2, …))` is a uniform point
of `[0, 2 L)` together with an independent sequence of fair bits. -/
theorem map_addBit_tail (L : ℝ) (hL : 0 < L) :
    ((unifIco L).prod bitLaw).map
        (fun q : ℝ × (ℕ → Bool) => (q.1 + L * bit (q.2 0), fun n => q.2 (n + 1))) =
      (unifIco (2 * L)).prod bitLaw := by
  have := isProbabilityMeasure_unifIco hL
  have hcons : (unifIco L).prod bitLaw =
      ((unifIco L).prod (bitProb.prod bitLaw)).map (Prod.map id consBit) := by
    conv_lhs => rw [← map_consBit, ← Measure.map_id (μ := unifIco L)]
    rw [Measure.map_prod_map _ _ measurable_id measurable_consBit]
  have hm : Measurable fun q : ℝ × Bool => q.1 + L * bit q.2 := by fun_prop
  rw [hcons, Measure.map_map (by fun_prop) (measurable_id.prodMap measurable_consBit),
    ← Measure.prodAssoc_prod, Measure.map_map (by fun_prop)
      MeasurableEquiv.prodAssoc.measurable]
  have : ((fun q : ℝ × (ℕ → Bool) => (q.1 + L * bit (q.2 0), fun n => q.2 (n + 1))) ∘
      Prod.map id consBit) ∘ MeasurableEquiv.prodAssoc =
      Prod.map (fun q : ℝ × Bool => q.1 + L * bit q.2) id := by
    funext q; rfl
  rw [this, ← Measure.map_prod_map _ _ hm measurable_id, map_addBit L hL, Measure.map_id]

/-- The offsets of the image of the dyadic system under `x ↦ x / 2`. -/
noncomputable def halfOffsets (o : ℕ → ℝ) (k : ℕ) : ℝ := o (k + 1) / 2

theorem measurable_halfOffsets : Measurable halfOffsets :=
  measurable_pi_iff.mpr fun k => (measurable_pi_apply (k + 1)).div_const 2

/-- Halving the system built from `(x, e)` gives the system built from `((x + e 0) / 2, e (· + 1))`. -/
theorem halfOffsets_offsetsL (x : ℝ) (e : ℕ → Bool) :
    halfOffsets (offsetsL 1 x e) =
      offsetsL 1 (2⁻¹ * (x + 1 * bit (e 0))) (fun n => e (n + 1)) := by
  funext k
  have h := offsetsL_mul 2⁻¹ (2 * 1) (x + 1 * bit (e 0)) (fun n => e (n + 1)) k
  rw [show (2 : ℝ)⁻¹ * (2 * 1) = 1 by norm_num] at h
  rw [h, halfOffsets, offsetsL_succ]
  ring

/-- **Invariance of the uniform dyadic offset law under `x ↦ x / 2`.** -/
theorem map_halfOffsets_offsetLaw : offsetLaw.map halfOffsets = offsetLaw := by
  have h1 := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have h2 := isProbabilityMeasure_unifIco (by norm_num : (0 : ℝ) < 2 * 1)
  have hΦ : Measurable fun q : ℝ × (ℕ → Bool) =>
      (q.1 + 1 * bit (q.2 0), fun n => q.2 (n + 1)) := by fun_prop
  have hP : Measurable (Prod.map (fun y : ℝ => 2⁻¹ * y) (id : (ℕ → Bool) → ℕ → Bool)) := by
    fun_prop
  have hfun : halfOffsets ∘ (fun q : ℝ × (ℕ → Bool) => offsetsL 1 q.1 q.2) =
      (fun q : ℝ × (ℕ → Bool) => offsetsL 1 q.1 q.2) ∘
        (Prod.map (fun y : ℝ => 2⁻¹ * y) (id : (ℕ → Bool) → ℕ → Bool) ∘
          fun q : ℝ × (ℕ → Bool) => (q.1 + 1 * bit (q.2 0), fun n => q.2 (n + 1))) := by
    funext q
    exact halfOffsets_offsetsL q.1 q.2
  rw [offsetLaw, Measure.map_map measurable_halfOffsets (measurable_offsetsL 1), hfun,
    ← Measure.map_map (measurable_offsetsL 1) (hP.comp hΦ), ← Measure.map_map hP hΦ,
    map_addBit_tail 1 one_pos, ← Measure.map_prod_map _ _ (by fun_prop) measurable_id,
    map_inv_mul_unifIco two_pos, Measure.map_id]

theorem measurePreserving_halfOffsets : MeasurePreserving halfOffsets offsetLaw offsetLaw :=
  ⟨measurable_halfOffsets, map_halfOffsets_offsetLaw⟩

/-- The offsets of the image of the dyadic system under `x ↦ 2 x`: generation `k + 1` is twice
generation `k`, and generation `0` is the refinement of generation `1`. -/
noncomputable def doubleOffsets (o : ℕ → ℝ) : ℕ → ℝ
  | 0 => toIcoMod (zero_lt_one' ℝ) 0 (2 * o 0)
  | k + 1 => 2 * o k

theorem measurable_doubleOffsets : Measurable doubleOffsets := by
  refine measurable_pi_iff.mpr fun n => ?_
  cases n with
  | zero =>
    exact (measurable_toIcoMod (zero_lt_one' ℝ)).comp ((measurable_pi_apply 0).const_mul 2)
  | succ k => exact (measurable_pi_apply k).const_mul 2

/-- `halfOffsets` is a left inverse of `doubleOffsets`. -/
theorem halfOffsets_doubleOffsets (o : ℕ → ℝ) : halfOffsets (doubleOffsets o) = o := by
  funext k
  show 2 * o k / 2 = o k
  ring

/-- On the support of the offset law, `doubleOffsets` is a left inverse of `halfOffsets`. -/
theorem doubleOffsets_halfOffsets_offsetsL {x : ℝ} (hx : x ∈ Ico 0 1) (e : ℕ → Bool) :
    doubleOffsets (halfOffsets (offsetsL 1 x e)) = offsetsL 1 x e := by
  funext k
  cases k with
  | zero =>
    obtain ⟨n, hn⟩ := exists_offsetsL_sub 1 x e (j := 0) (k := 1) (Nat.zero_le 1)
    simp only [pow_zero, mul_one] at hn
    show toIcoMod (zero_lt_one' ℝ) 0 (2 * (offsetsL 1 x e 1 / 2)) = offsetsL 1 x e 0
    rw [show 2 * (offsetsL 1 x e 1 / 2) = offsetsL 1 x e 1 by ring, eq_add_of_sub_eq hn,
      toIcoMod_zsmul_add, toIcoMod_eq_self]
    simpa using offsetsL_mem_Ico one_pos hx e 0
  | succ k =>
    show 2 * (offsetsL 1 x e (k + 1) / 2) = offsetsL 1 x e (k + 1)
    ring

/-- **Invariance of the uniform dyadic offset law under `x ↦ 2 x`.** -/
theorem map_doubleOffsets_offsetLaw : offsetLaw.map doubleOffsets = offsetLaw := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  have hae : ∀ᵐ q ∂((unifIco 1).prod bitLaw), q.1 ∈ Ico (0 : ℝ) 1 := by
    rw [ae_iff]
    have : {q : ℝ × (ℕ → Bool) | ¬q.1 ∈ Ico (0 : ℝ) 1} = (Ico (0 : ℝ) 1)ᶜ ×ˢ univ := by
      ext q; simp
    rw [this, Measure.prod_prod, unifIco, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Ico.compl, compl_inter_self]
    simp
  calc offsetLaw.map doubleOffsets
      = (offsetLaw.map halfOffsets).map doubleOffsets := by rw [map_halfOffsets_offsetLaw]
    _ = ((unifIco 1).prod bitLaw).map
          ((doubleOffsets ∘ halfOffsets) ∘ fun q : ℝ × (ℕ → Bool) => offsetsL 1 q.1 q.2) := by
        rw [Measure.map_map measurable_doubleOffsets measurable_halfOffsets, offsetLaw,
          Measure.map_map (measurable_doubleOffsets.comp measurable_halfOffsets)
            (measurable_offsetsL 1)]
    _ = offsetLaw := by
        rw [offsetLaw]
        refine Measure.map_congr ?_
        filter_upwards [hae] with q hq
        exact doubleOffsets_halfOffsets_offsetsL hq q.2

theorem measurePreserving_doubleOffsets : MeasurePreserving doubleOffsets offsetLaw offsetLaw :=
  ⟨measurable_doubleOffsets, map_doubleOffsets_offsetLaw⟩

end LatticeProb.DyadicOffset
