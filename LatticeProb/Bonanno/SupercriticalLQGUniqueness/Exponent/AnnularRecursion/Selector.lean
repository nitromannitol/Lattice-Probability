/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Selector at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.DetRecursion
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Exponent.AnnularRecursion.Law




 















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal Convex

namespace SupercriticalLQGUniqueness.Exponent.AnnularRecursion

open LQGMetric LQGMetric.LFPP

 

 
def blockWeight (m : ℕ) (ξ : ℝ) (ij : ℤ × ℤ) (f : C(ℂ, ℝ)) : ℝ≥0∞ :=
  ⨆ q : ℚ × ℚ, (block (((2 : ℝ) ^ m)⁻¹) ij).indicator
    (fun z => ENNReal.ofReal (Real.exp (ξ * f z))) (ratC q)

theorem measurable_blockWeight (m : ℕ) (ξ : ℝ) (ij : ℤ × ℤ) :
    Measurable (blockWeight m ξ ij) := by
  refine Measurable.iSup fun q => ?_
  by_cases h : ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij
  · simp only [indicator_of_mem h]
    exact ((ContinuousMap.measurable_eval (ratC q)).const_mul ξ).exp.ennreal_ofReal
  · simp only [indicator_of_notMem h]
    exact measurable_const

private theorem exists_rat_near_Icc {l u x ρ : ℝ} (hlu : l < u) (hx : x ∈ Icc l u) (hρ : 0 < ρ) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc l u ∧ |(q : ℝ) - x| < ρ := by
  have h : max l (x - ρ) < min u (x + ρ) := by
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨hlu, by linarith [hx.2]⟩, ⟨by linarith [hx.1], by linarith⟩⟩
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn h
  simp only [max_lt_iff] at hqlo
  simp only [lt_min_iff] at hqhi
  exact ⟨q, ⟨hqlo.1.le, hqhi.1.le⟩, abs_lt.mpr ⟨by linarith [hqlo.2], by linarith [hqhi.2]⟩⟩

 
theorem exists_ratC_near (m : ℕ) (ij : ℤ × ℤ) {z : ℂ} (hz : z ∈ block (((2 : ℝ) ^ m)⁻¹) ij)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ q : ℚ × ℚ, ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij ∧ ‖ratC q - z‖ < ρ := by
  have ha : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
  obtain ⟨q₁, hq₁, hq₁'⟩ := exists_rat_near_Icc
    (show ((ij.1 : ℝ) - 1) * ((2 : ℝ) ^ m)⁻¹ < ((ij.1 : ℝ) + 2) * ((2 : ℝ) ^ m)⁻¹ by nlinarith)
    ⟨h1, h2⟩ (half_pos hρ)
  obtain ⟨q₂, hq₂, hq₂'⟩ := exists_rat_near_Icc
    (show ((ij.2 : ℝ) - 1) * ((2 : ℝ) ^ m)⁻¹ < ((ij.2 : ℝ) + 2) * ((2 : ℝ) ^ m)⁻¹ by nlinarith)
    ⟨h3, h4⟩ (half_pos hρ)
  refine ⟨(q₁, q₂), ⟨?_, ?_⟩, ?_⟩
  · simpa [ratC] using hq₁
  · simpa [ratC] using hq₂
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [Complex.sub_re, Complex.sub_im, ratC_re, ratC_im]
    linarith

theorem le_blockWeight (m : ℕ) (ξ : ℝ) (ij : ℤ × ℤ) (f : C(ℂ, ℝ)) {z : ℂ}
    (hz : z ∈ block (((2 : ℝ) ^ m)⁻¹) ij) :
    ENNReal.ofReal (Real.exp (ξ * f z)) ≤ blockWeight m ξ ij f := by
  set S : Set ℂ := {w | ENNReal.ofReal (Real.exp (ξ * f w)) ≤ blockWeight m ξ ij f}
  have hcont : Continuous fun w => ENNReal.ofReal (Real.exp (ξ * f w)) :=
    ENNReal.continuous_ofReal.comp ((f.continuous.const_mul ξ).rexp)
  have hS : IsClosed S := isClosed_le hcont continuous_const
  have hR : (ratC '' {q | ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij}) ⊆ S := by
    rintro _ ⟨q, hq, rfl⟩
    have hq' : ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij := hq
    have := le_iSup (fun q : ℚ × ℚ => (block (((2 : ℝ) ^ m)⁻¹) ij).indicator
      (fun z => ENNReal.ofReal (Real.exp (ξ * f z))) (ratC q)) q
    rw [indicator_of_mem hq'] at this
    exact this
  have hzc : z ∈ closure (ratC '' {q | ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij}) := by
    rw [Metric.mem_closure_iff]
    intro ρ hρ
    obtain ⟨q, hq, hqz⟩ := exists_ratC_near m ij hz hρ
    exact ⟨ratC q, ⟨q, hq, rfl⟩, by rw [dist_comm, dist_eq_norm]; exact hqz⟩
  exact (closure_minimal hR hS) hzc

theorem blockWeight_le (m : ℕ) {ξ : ℝ} (hξ : 0 ≤ ξ) (ij : ℤ × ℤ) (f : C(ℂ, ℝ)) {M : ℝ}
    (hM : ∀ z ∈ block (((2 : ℝ) ^ m)⁻¹) ij, f z ≤ M) :
    blockWeight m ξ ij f ≤ ENNReal.ofReal (Real.exp (ξ * M)) := by
  refine iSup_le fun q => ?_
  by_cases h : ratC q ∈ block (((2 : ℝ) ^ m)⁻¹) ij
  · rw [indicator_of_mem h]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hM _ h) hξ))
  · rw [indicator_of_notMem h]
    exact bot_le

 

variable (ξ : ℝ) (δ : ℝ≥0∞) (e : ℕ → Exponent.PolygonalCost.RatPolygonFamily)

 
def SelProp (j : ℕ) (f : C(ℂ, ℝ)) : Prop :=
  (e j).Admitted ∧ (e j).cost ξ f < polyCostC ξ f + δ

open Classical in
 
def selIdx (f : C(ℂ, ℝ)) : ℕ :=
  if h : ∃ j, SelProp ξ δ e j f then Nat.find h else 0

theorem measurableSet_selProp (j : ℕ) : MeasurableSet {f : C(ℂ, ℝ) | SelProp ξ δ e j f} := by
  by_cases hadm : (e j).Admitted
  · have hc : Measurable fun f : C(ℂ, ℝ) => (e j).cost ξ f :=
      Exponent.PolygonalCost.measurable_ratPolygonFamily_cost (Y := fun x (f : C(ℂ, ℝ)) => f x)
        (fun f => f.continuous) (fun x => ContinuousMap.measurable_eval x) (e j) ξ
    have hU : Measurable fun f : C(ℂ, ℝ) => polyCostC ξ f + δ :=
      (measurable_polyCostC ξ).add_const δ
    have e1 : {f : C(ℂ, ℝ) | SelProp ξ δ e j f} =
        {f : C(ℂ, ℝ) | (e j).cost ξ f < polyCostC ξ f + δ} := by
      ext f; simp only [SelProp, mem_ofPred_eq, hadm, true_and]
    rw [e1]
    exact measurableSet_lt hc hU
  · have e1 : {f : C(ℂ, ℝ) | SelProp ξ δ e j f} = ∅ := by
      ext f; simp only [SelProp, mem_ofPred_eq, hadm, false_and, mem_empty_iff_false]
    rw [e1]
    exact MeasurableSet.empty

theorem measurable_selIdx : Measurable (selIdx ξ δ e) := by
  classical
  refine measurable_to_countable' fun j => ?_
  have e1 : selIdx ξ δ e ⁻¹' {j} =
      ({f | SelProp ξ δ e j f} ∩ ⋂ i ∈ Finset.range j, {f | SelProp ξ δ e i f}ᶜ) ∪
        ({f | ∀ i, ¬ SelProp ξ δ e i f} ∩ {_f | j = 0}) := by
    ext f
    simp only [mem_preimage, mem_singleton_iff, selIdx, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_compl_iff]
    by_cases h : ∃ j, SelProp ξ δ e j f
    · rw [dite_eq_left h, Nat.find_eq_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h1, fun i hi => h2 i hi⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨h1, fun i hi => h2 i hi⟩
        · exact absurd h (not_exists.2 h1)
    · rw [dite_eq_right h]
      push Not at h
      constructor
      · intro hj; exact Or.inr ⟨h, hj.symm⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 (h j)
        · exact h2.symm
  rw [e1]
  refine MeasurableSet.union ?_ ?_
  · refine (measurableSet_selProp ξ δ e j).inter ?_
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ => (measurableSet_selProp ξ δ e i).compl
  · refine MeasurableSet.inter ?_ (MeasurableSet.const _)
    have : {f : C(ℂ, ℝ) | ∀ i, ¬ SelProp ξ δ e i f} = ⋂ i, {f | SelProp ξ δ e i f}ᶜ := by
      ext f; simp
    rw [this]
    exact MeasurableSet.iInter fun i => (measurableSet_selProp ξ δ e i).compl

theorem selIdx_spec {f : C(ℂ, ℝ)} (h : ∃ j, SelProp ξ δ e j f) :
    SelProp ξ δ e (selIdx ξ δ e f) f := by
  classical
  simp only [selIdx, dite_eq_left h]
  exact Nat.find_spec h

open Classical in
 
def chargedWeight (m : ℕ) (ij : ℤ × ℤ) (f : C(ℂ, ℝ)) : ℝ≥0∞ :=
  if ij ∈ longTiles m (imageFamily (aQ m) (e (selIdx ξ δ e f))) then blockWeight m ξ ij f else 0

theorem measurable_chargedWeight (m : ℕ) (ij : ℤ × ℤ) :
    Measurable (chargedWeight ξ δ e m ij) := by
  classical
  let h : ℕ × C(ℂ, ℝ) → ℝ≥0∞ := fun p =>
    if ij ∈ longTiles m (imageFamily (aQ m) (e p.1)) then blockWeight m ξ ij p.2 else 0
  have hh : Measurable h := by
    refine measurable_from_prod_countable_right fun j => ?_
    by_cases hj : ij ∈ longTiles m (imageFamily (aQ m) (e j))
    · simp only [h, ite_eq_left hj]; exact measurable_blockWeight m ξ ij
    · simp only [h, ite_eq_right hj]; exact measurable_const
  have e1 : chargedWeight ξ δ e m ij = h ∘ fun f => (selIdx ξ δ e f, f) := by
    funext f; rfl
  rw [e1]
  exact hh.comp ((measurable_selIdx ξ δ e).prodMk measurable_id)

 
theorem abs_sub_corner_le_of_long (m : ℕ) (hm : 8 ≤ m) {F : Exponent.PolygonalCost.RatPolygonFamily}
    (hF : F.Admitted) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) {G : ℝ} (hG0 : 0 ≤ G)
    (hG : ∀ z ∈ Exponent.InwardMap.gradientBox, ‖fderiv ℝ φ z‖ ≤ G) {ij : ℤ × ℤ}
    (hij : ij ∈ longTiles m (imageFamily (aQ m) F)) {z : ℂ}
    (hz : z ∈ block (((2 : ℝ) ^ m)⁻¹) ij) :
    |φ z - φ (corner (((2 : ℝ) ^ m)⁻¹) ij)| ≤ 4 * ((2 : ℝ) ^ m)⁻¹ * G := by
  have ha : (0 : ℝ) < ((2 : ℝ) ^ m)⁻¹ := by positivity
  obtain ⟨hadm, hcl⟩ := imageFamily_admitted (aQ m) (aQ_pos m) (aQ_le m hm) F hF
  rw [aQ_cast] at hcl
  have hLA := longTiles_block_subset m _ hm hcl hij
  have hcB : corner (((2 : ℝ) ^ m)⁻¹) ij ∈ block (((2 : ℝ) ^ m)⁻¹) ij :=
    tile_subset_block ha.le ij (corner_mem_tile ha.le ij)
  have hdiff : ∀ z ∈ Exponent.InwardMap.gradientBox, DifferentiableAt ℝ φ z :=
    fun z _ => (hφ.differentiable (by norm_num)).differentiableAt
  have hmv := Exponent.InwardMap.convex_gradientBox.norm_image_sub_le_of_norm_fderiv_le hdiff hG
    (hLA.2 hcB) (hLA.2 hz)
  have hd := norm_sub_corner_le ha.le ij hz
  rw [← Real.norm_eq_abs]
  calc ‖φ z - φ (corner (((2 : ℝ) ^ m)⁻¹) ij)‖ ≤ G * ‖z - corner (((2 : ℝ) ^ m)⁻¹) ij‖ := hmv
    _ ≤ G * (4 * ((2 : ℝ) ^ m)⁻¹) := mul_le_mul_of_nonneg_left hd hG0
    _ = 4 * ((2 : ℝ) ^ m)⁻¹ * G := by ring

open Classical in
 
theorem charged_bounds (m : ℕ) (hm : 8 ≤ m) (hξ : 0 ≤ ξ) (f : C(ℂ, ℝ))
    (hf : ContDiff ℝ 1 f) (hsel : ∃ j, SelProp ξ δ e j f) (ψ : ℂ → ℝ) :
    Exponent.PolygonalCost.polyAnnularCost ξ (fun z => f z + ψ z) ≤
        ∑ ij ∈ tileUniv m, chargedWeight ξ δ e m ij f *
          ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
            Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z)) ∧
      ∑ ij ∈ tileUniv m, ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * chargedWeight ξ δ e m ij f ≤
        20 * ENNReal.ofReal (Real.exp (54 * ξ * (((2 : ℝ) ^ m)⁻¹ *
          Exponent.InwardMap.gradientSup f))) * (polyCostC ξ f + δ) := by
  set F := e (selIdx ξ δ e f)
  have hspec := selIdx_spec ξ δ e hsel
  set L := longTiles m (imageFamily (aQ m) F)
  have hfc : ContinuousOn (fun z => fderiv ℝ f z) Exponent.InwardMap.gradientBox :=
    (hf.continuous_fderiv (by norm_num)).continuousOn
  set G := Exponent.InwardMap.gradientSup f
  have hG0 : 0 ≤ G := Exponent.InwardMap.gradientSup_nonneg _ hfc
  have hG := Exponent.InwardMap.gradientSup_bound f hfc
  have hdet := det_recursion m hm hξ F hspec.1 ψ hf hG0 hG (fun ij => blockWeight m ξ ij f)
    (fun ij z hz => le_blockWeight m ξ ij f hz)
    (fun ij hij => blockWeight_le m hξ ij f fun z hz => by
      have := abs_sub_corner_le_of_long m hm hspec.1 hf hG0 hG hij hz
      linarith [le_abs_self (f z - f (corner (((2 : ℝ) ^ m)⁻¹) ij))])
  have hsum : ∀ X : ℤ × ℤ → ℝ≥0∞, ∑ ij ∈ tileUniv m, chargedWeight ξ δ e m ij f * X ij =
      ∑ ij ∈ L, blockWeight m ξ ij f * X ij := by
    intro X
    have hsub : L ⊆ tileUniv m := longTiles_subset m _
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun ij hij => ?_
      simp only [chargedWeight, F, L] at hij ⊢
      rw [ite_eq_left hij]
    · intro ij _ hij
      simp only [chargedWeight]
      rw [ite_eq_right hij, zero_mul]
  constructor
  · calc Exponent.PolygonalCost.polyAnnularCost ξ (fun z => f z + ψ z) ≤
        ∑ ij ∈ L, blockWeight m ξ ij f * ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
          Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z)) := hdet.1
      _ = _ := by
        have := hsum fun ij => ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) *
          Exponent.PolygonalCost.polyAnnularCost ξ (fun z => ψ (tileMap m ij z))
        simp only [← mul_assoc] at this
        exact this.symm
  · calc ∑ ij ∈ tileUniv m, ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * chargedWeight ξ δ e m ij f =
        ∑ ij ∈ L, ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹) * blockWeight m ξ ij f := by
          have := hsum fun _ => ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹)
          simp only [mul_comm (ENNReal.ofReal _)] at this ⊢
          exact this
      _ ≤ 20 * ENNReal.ofReal (Real.exp (54 * ξ * (((2 : ℝ) ^ m)⁻¹ * G))) * F.cost ξ f := hdet.2
      _ ≤ 20 * ENNReal.ofReal (Real.exp (54 * ξ * (((2 : ℝ) ^ m)⁻¹ * G))) *
          (polyCostC ξ f + δ) := by gcongr; exact hspec.2.le



end SupercriticalLQGUniqueness.Exponent.AnnularRecursion
