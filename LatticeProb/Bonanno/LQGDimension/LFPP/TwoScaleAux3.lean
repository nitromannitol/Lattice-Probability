/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.TwoScaleAux3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.TwoScaleAux2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Lemma 3.1, auxiliary file 3: the unregularized bound

* `dbl_coupling_bound`: for finite measures `α₁, α₂` with growth `L min(1, s/R)` coupled within
  `u`, and `β₁, β₂` coupled within `v`, the four-term Gaussian pairing
  `dbl β₁ α₁ - dbl β₁ α₂ - dbl β₂ α₁ + dbl β₂ α₂` is at most
  `4 min(1, uv/t²) · 32 L t / R · β₁(ℂ)`.  (Four-point kernel bound integrated against both
  couplings; the coarse side is integrated inside, where the growth bound applies.)
* `gaussPair_bound`: the same for segment combinations.
* `logCov_symm`: symmetry of `logCov` when the first argument is nondegenerate.
* `logCov_twoScale_bound`: `|logCov(μR - νR, μr - νr)| ≤ 256 L √(uv) / R`, by the heat-kernel
  representation and `∫_0^∞ min(1, uv/t²) dt = 2√(uv)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.TwoScale

open Blueprint.Draft

/-! ## Couplings -/

lemma isFiniteMeasure_of_map_fst {pm : Measure (ℂ × ℂ)} {μ : Measure ℂ} [IsFiniteMeasure μ]
    (h : pm.map Prod.fst = μ) : IsFiniteMeasure pm := by
  constructor
  have := measure_lt_top μ univ
  rw [← h, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at this
  exact this

lemma real_univ_of_map_fst {pm : Measure (ℂ × ℂ)} {μ : Measure ℂ} (h : pm.map Prod.fst = μ) :
    pm.real univ = μ.real univ := by
  rw [← h, measureReal_def, measureReal_def, Measure.map_apply measurable_fst MeasurableSet.univ,
    preimage_univ]

lemma integral_comp_fst {pm : Measure (ℂ × ℂ)} {μ : Measure ℂ} (h : pm.map Prod.fst = μ)
    (g : ℂ → ℝ) (hg : Continuous g) : ∫ q, g q.1 ∂pm = ∫ z, g z ∂μ := by
  rw [← h, integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable]

lemma integral_comp_snd {pm : Measure (ℂ × ℂ)} {μ : Measure ℂ} (h : pm.map Prod.snd = μ)
    (g : ℂ → ℝ) (hg : Continuous g) : ∫ q, g q.2 ∂pm = ∫ z, g z ∂μ := by
  rw [← h, integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable]

lemma integrable_kt_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (pm : Measure X) [IsFiniteMeasure pm] (t : ℝ) (g : X → ℂ)
    (hg : Continuous g) : Integrable (fun q => kt t (g q)) pm :=
  Integrable.of_bound ((continuous_kt t).comp hg).aestronglyMeasurable 1
    (ae_of_all _ fun q => by rw [Real.norm_eq_abs, abs_of_pos (kt_pos t _)]; exact kt_le_one t _)

lemma et_le_one (t : ℝ) (x : ℂ) : et t x ≤ 1 := by
  unfold et; rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

lemma integrable_et_comp {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (pm : Measure X) [IsFiniteMeasure pm] (t : ℝ) (g : X → ℂ)
    (hg : Continuous g) : Integrable (fun q => et t (g q)) pm :=
  Integrable.of_bound ((continuous_et t).comp hg).aestronglyMeasurable 1
    (ae_of_all _ fun q => by rw [Real.norm_eq_abs, abs_of_pos (et_pos t _)]; exact et_le_one t _)

/-- `H α w = ∫ kt(w - z) dα(z)` is continuous and bounded by `α(ℂ)`. -/
lemma integrable_H_comp (pm : Measure (ℂ × ℂ)) [IsFiniteMeasure pm] (t : ℝ) (α : Measure ℂ)
    [IsFiniteMeasure α] (g : ℂ × ℂ → ℂ) (hg : Continuous g) :
    Integrable (fun q => ∫ z, kt t (g q - z) ∂α) pm := by
  refine Integrable.of_bound ((continuous_integral_kt t α).comp hg).aestronglyMeasurable
    (1 * α.real univ) (ae_of_all _ fun q => ?_)
  refine norm_integral_le_of_norm_le_const (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (kt_pos t _)]; exact kt_le_one t _

/-- Growth integral for the comparison Gaussian: `∫ et(y - z) dα(z) ≤ 8 L t / R`. -/
lemma integral_et_le {α : Measure ℂ} [IsFiniteMeasure α] {L R t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hG : GrowthBound α L R) (y : ℂ) : ∫ z, et t (y - z) ∂α ≤ 8 * L * t / R := by
  have h := integral_gauss_le_of_growth α hR hG (a := 16 * t ^ 2) (by positivity) y
  have hs : Real.sqrt (16 * t ^ 2) = 4 * t := by
    rw [show 16 * t ^ 2 = (4 * t) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs] at h
  unfold et
  calc _ ≤ 2 * L * (4 * t) / R := h
    _ = 8 * L * t / R := by ring

/-- **Four-term Gaussian pairing through the couplings.** -/
theorem dbl_coupling_bound {α₁ α₂ β₁ β₂ : Measure ℂ} [IsFiniteMeasure α₁] [IsFiniteMeasure α₂]
    [IsFiniteMeasure β₁] [IsFiniteMeasure β₂] {L R u v t : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hG₁ : GrowthBound α₁ L R) (hG₂ : GrowthBound α₂ L R)
    (hcR : CoupledWithin α₁ α₂ u) (hcr : CoupledWithin β₁ β₂ v) :
    |dbl t β₁ α₁ - dbl t β₁ α₂ - dbl t β₂ α₁ + dbl t β₂ α₂| ≤
      4 * min 1 (u * v / t ^ 2) * (32 * L * t / R) * β₁.real univ := by
  obtain ⟨cR, hR1, hR2, hRae⟩ := hcR
  obtain ⟨cr, hr1, hr2, hrae⟩ := hcr
  have := isFiniteMeasure_of_map_fst hR1
  have := isFiniteMeasure_of_map_fst hr1
  have hL := growth_L_nonneg hR hG₁
  -- the inner integral over the coarse coupling
  have hinner : ∀ q' : ℂ × ℂ, ∫ q, (kt t (q'.1 - q.1) - kt t (q'.1 - q.2) - kt t (q'.2 - q.1) +
      kt t (q'.2 - q.2)) ∂cR =
      (∫ z, kt t (q'.1 - z) ∂α₁) - (∫ z, kt t (q'.1 - z) ∂α₂) - (∫ z, kt t (q'.2 - z) ∂α₁) +
        (∫ z, kt t (q'.2 - z) ∂α₂) := by
    intro q'
    have i1 := integrable_kt_comp cR t (fun q => q'.1 - q.1) (by fun_prop)
    have i2 := integrable_kt_comp cR t (fun q => q'.1 - q.2) (by fun_prop)
    have i3 := integrable_kt_comp cR t (fun q => q'.2 - q.1) (by fun_prop)
    have i4 := integrable_kt_comp cR t (fun q => q'.2 - q.2) (by fun_prop)
    have i12 : Integrable (fun q : ℂ × ℂ => kt t (q'.1 - q.1) - kt t (q'.1 - q.2)) cR :=
      i1.sub i2
    have i123 : Integrable (fun q : ℂ × ℂ => kt t (q'.1 - q.1) - kt t (q'.1 - q.2) -
      kt t (q'.2 - q.1)) cR := i12.sub i3
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
    have c1 : Continuous fun z => kt t (q'.1 - z) :=
      (continuous_kt t).comp (continuous_const.sub continuous_id)
    have c2 : Continuous fun z => kt t (q'.2 - z) :=
      (continuous_kt t).comp (continuous_const.sub continuous_id)
    rw [integral_comp_fst hR1 _ c1, integral_comp_snd hR2 _ c1, integral_comp_fst hR1 _ c2,
      integral_comp_snd hR2 _ c2]
  -- the outer integral over the fine coupling
  have houter : ∫ q' : ℂ × ℂ, ((∫ z, kt t (q'.1 - z) ∂α₁) - (∫ z, kt t (q'.1 - z) ∂α₂) -
      (∫ z, kt t (q'.2 - z) ∂α₁) + (∫ z, kt t (q'.2 - z) ∂α₂)) ∂cr =
      dbl t β₁ α₁ - dbl t β₁ α₂ - dbl t β₂ α₁ + dbl t β₂ α₂ := by
    have j1 := integrable_H_comp cr t α₁ Prod.fst continuous_fst
    have j2 := integrable_H_comp cr t α₂ Prod.fst continuous_fst
    have j3 := integrable_H_comp cr t α₁ Prod.snd continuous_snd
    have j4 := integrable_H_comp cr t α₂ Prod.snd continuous_snd
    have j12 : Integrable (fun q : ℂ × ℂ => (∫ z, kt t (q.1 - z) ∂α₁) -
      ∫ z, kt t (q.1 - z) ∂α₂) cr := j1.sub j2
    have j123 : Integrable (fun q : ℂ × ℂ => (∫ z, kt t (q.1 - z) ∂α₁) -
      (∫ z, kt t (q.1 - z) ∂α₂) - ∫ z, kt t (q.2 - z) ∂α₁) cr := j12.sub j3
    rw [integral_add j123 j4, integral_sub j12 j3, integral_sub j1 j2]
    unfold dbl
    rw [integral_comp_fst hr1 _ (continuous_integral_kt t α₁),
      integral_comp_fst hr1 _ (continuous_integral_kt t α₂),
      integral_comp_snd hr2 _ (continuous_integral_kt t α₁),
      integral_comp_snd hr2 _ (continuous_integral_kt t α₂)]
  set m := min 1 (u * v / t ^ 2) with hm
  have hm0 : 0 ≤ m := le_min zero_le_one (by positivity)
  -- pointwise bound on the inner integral
  have hpt : ∀ᵐ q' ∂cr, ‖∫ q, (kt t (q'.1 - q.1) - kt t (q'.1 - q.2) - kt t (q'.2 - q.1) +
      kt t (q'.2 - q.2)) ∂cR‖ ≤ 4 * m * (32 * L * t / R) := by
    filter_upwards [hrae] with q' hq'
    have hDb : ∀ᵐ q ∂cR, ‖kt t (q'.1 - q.1) - kt t (q'.1 - q.2) - kt t (q'.2 - q.1) +
        kt t (q'.2 - q.2)‖ ≤ 4 * m * (et t (q'.1 - q.1) + et t (q'.1 - q.2) +
          et t (q'.2 - q.1) + et t (q'.2 - q.2)) := by
      filter_upwards [hRae] with q hq
      have h := kt_four_point ht hu hv (q'.1 - q.1) (q.1 - q.2) (q'.2 - q'.1) hq
        (by rw [norm_sub_rev]; exact hq')
      have e1 : q'.1 - q.1 + (q.1 - q.2) = q'.1 - q.2 := by ring
      have e2 : q'.1 - q.1 + (q'.2 - q'.1) = q'.2 - q.1 := by ring
      have e3 : q'.1 - q.2 + (q'.2 - q'.1) = q'.2 - q.2 := by ring
      rw [e1, e2, e3] at h
      rw [Real.norm_eq_abs]
      exact h
    have k1 := integrable_et_comp cR t (fun q => q'.1 - q.1) (by fun_prop)
    have k2 := integrable_et_comp cR t (fun q => q'.1 - q.2) (by fun_prop)
    have k3 := integrable_et_comp cR t (fun q => q'.2 - q.1) (by fun_prop)
    have k4 := integrable_et_comp cR t (fun q => q'.2 - q.2) (by fun_prop)
    have hsum := ((k1.add k2).add k3).add k4
    have d1 : Continuous fun z => et t (q'.1 - z) :=
      (continuous_et t).comp (continuous_const.sub continuous_id)
    have d2 : Continuous fun z => et t (q'.2 - z) :=
      (continuous_et t).comp (continuous_const.sub continuous_id)
    calc _ ≤ ∫ q, 4 * m * (et t (q'.1 - q.1) + et t (q'.1 - q.2) +
          et t (q'.2 - q.1) + et t (q'.2 - q.2)) ∂cR :=
          norm_integral_le_of_norm_le (hsum.const_mul _) hDb
      _ = 4 * m * ((∫ z, et t (q'.1 - z) ∂α₁) + (∫ z, et t (q'.1 - z) ∂α₂) +
          (∫ z, et t (q'.2 - z) ∂α₁) + (∫ z, et t (q'.2 - z) ∂α₂)) := by
          have k12 : Integrable (fun q : ℂ × ℂ => et t (q'.1 - q.1) + et t (q'.1 - q.2)) cR :=
            k1.add k2
          have k123 : Integrable (fun q : ℂ × ℂ => et t (q'.1 - q.1) + et t (q'.1 - q.2) +
            et t (q'.2 - q.1)) cR := k12.add k3
          rw [integral_const_mul, integral_add k123 k4, integral_add k12 k3, integral_add k1 k2,
            integral_comp_fst hR1 _ d1, integral_comp_snd hR2 _ d1,
            integral_comp_fst hR1 _ d2, integral_comp_snd hR2 _ d2]
      _ ≤ 4 * m * (8 * L * t / R + 8 * L * t / R + 8 * L * t / R + 8 * L * t / R) := by
          have e1 := integral_et_le hR ht hG₁ q'.1
          have e2 := integral_et_le hR ht hG₂ q'.1
          have e3 := integral_et_le hR ht hG₁ q'.2
          have e4 := integral_et_le hR ht hG₂ q'.2
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = 4 * m * (32 * L * t / R) := by ring
  rw [← houter, ← real_univ_of_map_fst hr1]
  have := norm_integral_le_of_norm_le_const hpt
  simp_rw [hinner] at this
  rw [← Real.norm_eq_abs]
  exact this

/-- **Two-scale bound for one heat level**, for segment combinations. -/
theorem gaussPair_bound {μR νR μr νr : SegComb} {L R u v t : ℝ}
    (hμR : μR.IsProb) (hνR : νR.IsProb) (hμr : μr.IsProb) (hνr : νr.IsProb)
    (hR : 0 < R) (ht : 0 < t) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hGμ : GrowthBound μR.toMeasure L R) (hGν : GrowthBound νR.toMeasure L R)
    (hcR : CoupledWithin μR.toMeasure νR.toMeasure u)
    (hcr : CoupledWithin μr.toMeasure νr.toMeasure v) :
    |gaussPair t (μr.sub νr) (μR.sub νR)| ≤ 128 * L / R * t * min 1 (u * v / t ^ 2) := by
  rw [gaussPair_sub_sub, gaussPair_eq_dbl t _ _ hμr.1 hμR.1, gaussPair_eq_dbl t _ _ hμr.1 hνR.1,
    gaussPair_eq_dbl t _ _ hνr.1 hμR.1, gaussPair_eq_dbl t _ _ hνr.1 hνR.1]
  have h := dbl_coupling_bound (β₁ := μr.toMeasure) (β₂ := νr.toMeasure) hR ht hu hv hGμ hGν
    hcR hcr
  rw [toMeasure_real_univ μr hμr.1, hμr.2] at h
  calc _ ≤ 4 * min 1 (u * v / t ^ 2) * (32 * L * t / R) * 1 := h
    _ = 128 * L / R * t * min 1 (u * v / t ^ 2) := by ring

/-! ## Symmetry of `logCov` -/

lemma list_sum_comm {α β : Type*} (l₁ : List α) (l₂ : List β) (f : α → β → ℝ) :
    (l₁.map fun a => (l₂.map fun b => f a b).sum).sum =
      (l₂.map fun b => (l₁.map fun a => f a b).sum).sum := by
  induction l₁ with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [list_sum_map_add']

lemma segLogPair_symm (a b a' b' : ℂ) (hab : a ≠ b) :
    segLogPair a b a' b' = segLogPair a' b' a b := by
  rw [HeatKernel.segLogPair_eq a' b' a b hab, ← integral_neg]
  have hf : Integrable (fun q : ℝ × ℝ => -Real.log (HeatKernel.segDist a' b' a b q))
      HeatKernel.unitSq := (HeatKernel.integrable_log_segDist a' b' a b hab).neg
  have hswap : Integrable (fun q : ℝ × ℝ => -Real.log (HeatKernel.segDist a' b' a b q.swap))
      HeatKernel.unitSq := by
    unfold HeatKernel.unitSq at hf ⊢
    exact hf.swap
  have e := integral_prod_swap (μ := volume.restrict (Ioc (0 : ℝ) 1))
    (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (fun q : ℝ × ℝ => -Real.log (HeatKernel.segDist a' b' a b q))
  unfold HeatKernel.unitSq at hswap ⊢
  rw [← e, integral_prod _ hswap]
  unfold segLogPair
  simp only [intervalIntegral.integral_of_le zero_le_one, HeatKernel.segDist, Prod.swap_prod_mk]
  congr 1; funext s; congr 1; funext s'
  rw [norm_sub_rev]

lemma logCov_symm (c c' : SegComb) (hc : c.Nondeg) : c.logCov c' = c'.logCov c := by
  unfold SegComb.logCov
  rw [list_sum_comm c]
  congr 1; apply List.map_congr_left; intro p' _
  congr 1; apply List.map_congr_left; intro p hp
  by_cases h0 : p.1 = 0
  · simp [h0]
  · rw [segLogPair_symm _ _ _ _ (hc p hp h0)]; ring

/-! ## The unregularized bound -/

/-- `∫_0^∞ min(1, uv/t²) dt ≤ 2√(uv)`, in the form used below. -/
lemma integral_min_le {A u v : ℝ} (hA : 0 ≤ A) (huv : 0 < u * v) (F : ℝ → ℝ)
    (hF : ∀ t > 0, |F t| ≤ A * min 1 (u * v / t ^ 2)) :
    ∫ t in Ioi (0 : ℝ), |F t| ≤ 2 * A * Real.sqrt (u * v) := by
  set s := Real.sqrt (u * v) with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 huv
  have hss : s ^ 2 = u * v := Real.sq_sqrt huv.le
  set g : ℝ → ℝ := fun t => Set.indicator (Ioc 0 s) (fun _ => A) t +
    Set.indicator (Ioi s) (fun t => A * (u * v) * t ^ (-2 : ℝ)) t with hg
  have hg1 : Integrable (Set.indicator (Ioc 0 s) (fun _ => A)) (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioc, inter_eq_left.2 Ioc_subset_Ioi_self]
    exact (continuous_const.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hg2 : Integrable (Set.indicator (Ioi s) (fun t => A * (u * v) * t ^ (-2 : ℝ)))
      (volume.restrict (Ioi 0)) := by
    rw [integrable_indicator_iff measurableSet_Ioi, IntegrableOn,
      Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi hs0.le)]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hs0).const_mul _
  have hgi : Integrable g (volume.restrict (Ioi 0)) := hg1.add hg2
  have hbound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), |F t| ≤ g t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    refine (hF t ht0).trans ?_
    simp only [hg]
    rcases le_or_gt t s with hts | hts
    · rw [Set.indicator_of_mem (show t ∈ Ioc 0 s from ⟨ht0, hts⟩),
        Set.indicator_of_notMem (show t ∉ Ioi s from fun h => by
          simp only [mem_Ioi] at h; linarith)]
      have := min_le_left 1 (u * v / t ^ 2)
      nlinarith
    · rw [Set.indicator_of_notMem (show t ∉ Ioc 0 s from fun h => by linarith [h.2]),
        Set.indicator_of_mem (show t ∈ Ioi s from hts),
        Real.rpow_neg ht0.le, Real.rpow_two, zero_add]
      have := min_le_right 1 (u * v / t ^ 2)
      calc A * min 1 (u * v / t ^ 2) ≤ A * (u * v / t ^ 2) := mul_le_mul_of_nonneg_left this hA
        _ = A * (u * v) * (t ^ 2)⁻¹ := by ring
  calc ∫ t in Ioi 0, |F t| ≤ ∫ t in Ioi 0, g t :=
        integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) hgi hbound
    _ = A * s + A * (u * v) * s⁻¹ := by
        rw [hg, integral_add hg1 hg2, setIntegral_indicator measurableSet_Ioc,
          setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 Ioc_subset_Ioi_self,
          inter_eq_right.2 (Ioi_subset_Ioi hs0.le), setIntegral_const, integral_const_mul,
          integral_Ioi_rpow_of_lt (a := -2) (by norm_num) hs0, show (-2 : ℝ) + 1 = -1 by norm_num,
          Real.rpow_neg_one, measureReal_def, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hs0.le, smul_eq_mul]
        ring
    _ = 2 * A * s := by
        have h : A * (u * v) * s⁻¹ = A * s := by
          rw [← hss, sq, ← mul_assoc, mul_inv_cancel_right₀ hs0.ne']
        rw [h]; ring

/-- **Lemma 3.1 for the log kernel** (with explicit constant `256`). -/
theorem logCov_twoScale_bound {μR νR μr νr : SegComb} {L R u v : ℝ}
    (hμR : μR.IsProb) (hνR : νR.IsProb) (hμr : μr.IsProb) (hνr : νr.IsProb)
    (hR : 0 < R) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hGμ : GrowthBound μR.toMeasure L R) (hGν : GrowthBound νR.toMeasure L R)
    (hcR : CoupledWithin μR.toMeasure νR.toMeasure u)
    (hcr : CoupledWithin μr.toMeasure νr.toMeasure v) :
    |(μR.sub νR).logCov (μr.sub νr)| ≤ 256 * L * Real.sqrt (u * v) / R := by
  have hL := growth_L_nonneg hR hGμ
  have hNd : (μR.sub νR).Nondeg := nondeg_sub μR νR hμR.1 hνR.1
    (nondeg_of_growth μR hR hGμ) (nondeg_of_growth νR hR hGν)
  have hmass : (μr.sub νr).mass = 0 := by rw [mass_sub, hμr.2, hνr.2]; ring
  rw [logCov_symm _ _ hNd, (HeatKernel.gaussPair_heatRep (μr.sub νr) (μR.sub νR) hmass hNd).2]
  set A := 128 * L / R with hA
  have hA0 : 0 ≤ A := div_nonneg (mul_nonneg (by norm_num) hL) hR.le
  have hpt : ∀ t > 0, |gaussPair t (μr.sub νr) (μR.sub νR) / t| ≤ A * min 1 (u * v / t ^ 2) := by
    intro t ht
    have h := gaussPair_bound hμR hνR hμr hνr hR ht hu hv hGμ hGν hcR hcr
    rw [abs_div, abs_of_pos ht, div_le_iff₀ ht]
    calc _ ≤ 128 * L / R * t * min 1 (u * v / t ^ 2) := h
      _ = A * min 1 (u * v / t ^ 2) * t := by rw [hA]; ring
  refine abs_integral_le_integral_abs.trans ?_
  rcases eq_or_lt_of_le (mul_nonneg hu hv) with huv | huv
  · rw [← huv, Real.sqrt_zero, mul_zero, zero_div]
    refine le_of_eq (setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_)
    have h := hpt t ht
    rw [← huv, zero_div, min_eq_right zero_le_one, mul_zero] at h
    exact le_antisymm h (abs_nonneg _)
  · calc _ ≤ 2 * A * Real.sqrt (u * v) := integral_min_le hA0 huv _ hpt
      _ = 256 * L * Real.sqrt (u * v) / R := by rw [hA]; ring

end LQGDimension.TwoScale
