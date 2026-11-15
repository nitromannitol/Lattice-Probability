/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Section5.TVLocal at commit fdb5cad; trimmed to bounded duality,
   the kernel bind bound, product contraction, and their prerequisites. -/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Kernel.Basic

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace QuantumZipper

namespace TV

/-! ## The total variation distance -/

/-- The total variation distance of two measures on a measurable space, as the supremum of
`|μ s - ν s|` over measurable sets, valued in `ℝ≥0∞`. -/
def tvDist {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ (s : Set α) (_ : MeasurableSet s), (μ s - ν s) ⊔ (ν s - μ s)

section Basic

variable {α : Type*} [MeasurableSpace α] {μ ν ρ : Measure α}

/-- The two halves of the defining supremum. -/
theorem le_tvDist {s : Set α} (hs : MeasurableSet s) : μ s - ν s ≤ tvDist μ ν :=
  le_iSup₂_of_le s hs le_sup_left

theorem le_tvDist' {s : Set α} (hs : MeasurableSet s) : ν s - μ s ≤ tvDist μ ν :=
  le_iSup₂_of_le s hs le_sup_right

theorem tvDist_comm : tvDist μ ν = tvDist ν μ :=
  iSup_congr fun _ => iSup_congr fun _ => sup_comm _ _

theorem tvDist_self : tvDist μ μ = 0 := by
  simp [tvDist]

theorem tvDist_triangle [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ] :
    tvDist μ ρ ≤ tvDist μ ν + tvDist ν ρ := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · exact (tsub_le_tsub_add_tsub (a := μ s) (b := ν s) (c := ρ s)).trans
      (add_le_add (le_tvDist hs) (le_tvDist hs))
  · refine (tsub_le_tsub_add_tsub (a := ρ s) (b := ν s) (c := μ s)).trans ?_
    rw [add_comm (tvDist μ ν) (tvDist ν ρ)]
    exact add_le_add (le_tvDist' (μ := ν) (ν := ρ) hs) (le_tvDist' (μ := μ) (ν := ν) hs)

theorem tvDist_le_one [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : tvDist μ ν ≤ 1 := by
  refine iSup_le fun s => iSup_le fun _ => sup_le ?_ ?_
  · have hμ : μ s ≤ 1 := by
      rw [← IsProbabilityMeasure.measure_univ (μ := μ)]
      exact measure_mono (Set.subset_univ s)
    exact (tsub_le_self).trans hμ
  · have hν : ν s ≤ 1 := by
      rw [← IsProbabilityMeasure.measure_univ (μ := ν)]
      exact measure_mono (Set.subset_univ s)
    exact (tsub_le_self).trans hν

theorem tvDist_map_le {β : Type*} [MeasurableSpace β] {f : α → β} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
    exact le_tvDist (hf hs)
  · rw [Measure.map_apply hf hs, Measure.map_apply hf hs]
    exact le_tvDist' (hf hs)

/-- For finite measures the total variation distance is finite (`toReal` is applied to it in
`abs_integral_sub_le`). -/
theorem tvDist_lt_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] : tvDist μ ν < ⊤ := by
  have h : tvDist μ ν ≤ μ Set.univ + ν Set.univ :=
    iSup_le fun s => iSup_le fun _ => sup_le
      (((tsub_le_self).trans (measure_mono (μ := μ) (Set.subset_univ s))).trans le_self_add)
      (((tsub_le_self).trans (measure_mono (μ := ν) (Set.subset_univ s))).trans le_add_self)
  exact lt_of_le_of_lt h (ENNReal.add_lt_top.mpr
    ⟨IsFiniteMeasure.measure_univ_lt_top, IsFiniteMeasure.measure_univ_lt_top⟩)

theorem tvDist_ne_top [IsFiniteMeasure μ] [IsFiniteMeasure ν] : tvDist μ ν ≠ ⊤ :=
  (tvDist_lt_top (μ := μ) (ν := ν)).ne

end Basic

/-! ## Bounded duality

The key estimate: for a measurable `g : α → ℝ≥0∞` with `g ≤ 1` the difference of the integrals
against `μ` and `ν` is bounded by `tvDist μ ν`.  Proof: layer cake (`lintegral_eq_lintegral_meas_lt`)
turns `∫⁻ g` into the integral over `t ∈ (0,1]` of `μ {g > t}` (valid because `g ≤ 1` bounds the
level sets above `1` to be empty), and each level set is compared by the defining property of
`tvDist`.  No finiteness of `μ`, `ν` is needed. -/

section Duality

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- Bounded duality in `ℝ≥0∞` form, for `ℝ`-valued `f`. -/
theorem ofReal_lintegral_le_add_tvDist {f : α → ℝ} (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x)
    (h1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂ν + tvDist μ ν := by
  have hfnn : 0 ≤ᵐ[μ] f := Eventually.of_forall h0
  have hfnnν : 0 ≤ᵐ[ν] f := Eventually.of_forall h0
  have hlayerμ : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < f a} :=
    lintegral_eq_lintegral_meas_lt μ hfnn hf.aemeasurable
  have hlayerν : ∫⁻ x, ENNReal.ofReal (f x) ∂ν = ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < f a} :=
    lintegral_eq_lintegral_meas_lt ν hfnnν hf.aemeasurable
  have hIoi : ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < f a} =
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, μ {a | t < f a} := by
    have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases h' : t ≤ 1
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (not_le.mp h')
      · rintro (⟨h, -⟩ | h)
        · exact h
        · exact lt_trans one_pos h
    rw [hU, lintegral_union measurableSet_Ioi (by
      rw [Set.disjoint_left]
      exact fun t ht ht' => absurd ht' (not_lt.mpr ht.2))]
    have hz : ∫⁻ t in Set.Ioi (1 : ℝ), μ {a | t < f a} = 0 := by
      have h0 : ∀ t ∈ Set.Ioi (1 : ℝ), μ {a | t < f a} = 0 := fun t ht =>
        measure_mono_null
          (fun a ha => absurd ha (not_lt.mpr ((lt_of_le_of_lt (h1 a) ht).le))) measure_empty
      rw [setLIntegral_congr_fun measurableSet_Ioi h0]
      simp
    rw [hz, add_zero]
  have hIoiν : ∫⁻ t in Set.Ioi (0 : ℝ), ν {a | t < f a} =
      ∫⁻ t in Set.Ioc (0 : ℝ) 1, ν {a | t < f a} := by
    have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
      ext t
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro h
        by_cases h' : t ≤ 1
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr (not_le.mp h')
      · rintro (⟨h, -⟩ | h)
        · exact h
        · exact lt_trans one_pos h
    rw [hU, lintegral_union measurableSet_Ioi (by
      rw [Set.disjoint_left]
      exact fun t ht ht' => absurd ht' (not_lt.mpr ht.2))]
    have hz : ∫⁻ t in Set.Ioi (1 : ℝ), ν {a | t < f a} = 0 := by
      have h0 : ∀ t ∈ Set.Ioi (1 : ℝ), ν {a | t < f a} = 0 := fun t ht =>
        measure_mono_null
          (fun a ha => absurd ha (not_lt.mpr ((lt_of_le_of_lt (h1 a) ht).le))) measure_empty
      rw [setLIntegral_congr_fun measurableSet_Ioi h0]
      simp
    rw [hz, add_zero]
  have hbdd : ∀ t : ℝ, μ {a | t < f a} ≤ ν {a | t < f a} + tvDist μ ν := fun t =>
    tsub_le_iff_left.mp (le_tvDist (measurableSet_lt measurable_const hf))
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, μ {a | t < f a} := by
        rw [hlayerμ, hIoi]
    _ ≤ ∫⁻ t in Set.Ioc (0 : ℝ) 1, (ν {a | t < f a} + tvDist μ ν) := lintegral_mono hbdd
    _ = ∫⁻ t in Set.Ioc (0 : ℝ) 1, (tvDist μ ν + ν {a | t < f a}) :=
        lintegral_congr fun t => add_comm _ _
    _ = tvDist μ ν + ∫⁻ t in Set.Ioc (0 : ℝ) 1, ν {a | t < f a} := by
        rw [lintegral_add_left (f := fun _ : ℝ => tvDist μ ν) measurable_const]
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc]
        norm_num
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂ν + tvDist μ ν := by
        rw [add_comm, hlayerν, ← hIoiν]

/-- Bounded duality: `∫⁻ g dμ ≤ ∫⁻ g dν + tvDist μ ν` for measurable `g ≤ 1`. -/
theorem lintegral_le_lintegral_add_tvDist {g : α → ℝ≥0∞} (hg : Measurable g)
    (h1 : ∀ x, g x ≤ 1) :
    ∫⁻ x, g x ∂μ ≤ ∫⁻ x, g x ∂ν + tvDist μ ν := by
  have hgne : ∀ x, g x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (h1 x)
  have key := ofReal_lintegral_le_add_tvDist (μ := μ) (ν := ν) (f := fun x => (g x).toReal)
    (ENNReal.measurable_toReal.comp hg) (fun x => ENNReal.toReal_nonneg) (fun x =>
      ENNReal.toReal_mono ENNReal.one_ne_top (h1 x))
  have hμ : ∫⁻ x, ENNReal.ofReal ((g x).toReal) ∂μ = ∫⁻ x, g x ∂μ :=
    lintegral_congr fun x => ENNReal.ofReal_toReal (hgne x)
  have hν : ∫⁻ x, ENNReal.ofReal ((g x).toReal) ∂ν = ∫⁻ x, g x ∂ν :=
    lintegral_congr fun x => ENNReal.ofReal_toReal (hgne x)
  rw [hμ, hν] at key
  exact key

end Duality

/-! ## Kernels and products -/

section Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

/-- Composing one measure with two Markov kernels is `1`-Lipschitz for `tvDist` against the
average of the pointwise distances (Levin–Peres–Wilmer, *Markov Chains and Mixing Times* §4.1,
the "TV is non-increasing under applications of a transition matrix" bound in the general
kernel form). -/
theorem tvDist_bind_le (κ₁ κ₂ : Kernel α β) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] :
    tvDist (μ.bind κ₁) (μ.bind κ₂) ≤ ∫⁻ x, tvDist (κ₁ x) (κ₂ x) ∂μ := by
  refine iSup_le fun s => iSup_le fun hs => sup_le ?_ ?_
  · have hb : (μ.bind κ₁) s ≤ (μ.bind κ₂) s + ∫⁻ x, tvDist (κ₁ x) (κ₂ x) ∂μ := by
      rw [Measure.bind_apply hs κ₁.measurable.aemeasurable,
        Measure.bind_apply hs κ₂.measurable.aemeasurable]
      calc ∫⁻ x, κ₁ x s ∂μ ≤ ∫⁻ x, (κ₂ x s + tvDist (κ₁ x) (κ₂ x)) ∂μ :=
            lintegral_mono fun x =>
              (le_add_tsub (a := κ₁ x s) (b := κ₂ x s)).trans
                (add_le_add le_rfl (le_tvDist (μ := κ₁ x) (ν := κ₂ x) hs))
        _ = ∫⁻ x, κ₂ x s ∂μ + ∫⁻ x, tvDist (κ₁ x) (κ₂ x) ∂μ :=
            lintegral_add_left (κ₂.measurable_coe hs) _
    exact tsub_le_iff_left.mpr hb
  · have hb : (μ.bind κ₂) s ≤ (μ.bind κ₁) s + ∫⁻ x, tvDist (κ₁ x) (κ₂ x) ∂μ := by
      rw [Measure.bind_apply hs κ₂.measurable.aemeasurable,
        Measure.bind_apply hs κ₁.measurable.aemeasurable]
      calc ∫⁻ x, κ₂ x s ∂μ ≤ ∫⁻ x, (κ₁ x s + tvDist (κ₁ x) (κ₂ x)) ∂μ :=
            lintegral_mono fun x =>
              (le_add_tsub (a := κ₂ x s) (b := κ₁ x s)).trans
                (add_le_add le_rfl (le_tvDist' (μ := κ₁ x) (ν := κ₂ x) hs))
        _ = ∫⁻ x, κ₁ x s ∂μ + ∫⁻ x, tvDist (κ₁ x) (κ₂ x) ∂μ :=
            lintegral_add_left (κ₁.measurable_coe hs) _
    exact tsub_le_iff_left.mpr hb

end Kernel

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ ν : Measure α}
  {ρ : Measure β}

/-- Multiplying on the right by a fixed probability measure is `1`-Lipschitz for `tvDist`. -/
theorem tvDist_prod_right_le [SFinite μ] [SFinite ν] [IsProbabilityMeasure ρ] :
    tvDist (μ.prod ρ) (ν.prod ρ) ≤ tvDist μ ν := by
  refine iSup_le fun t => iSup_le fun ht => sup_le ?_ ?_
  · have hg : Measurable fun x => ρ (Prod.mk x ⁻¹' t) := measurable_measure_prodMk_left ht
    have hg1 : ∀ x, ρ (Prod.mk x ⁻¹' t) ≤ 1 := fun x => by
      have h := measure_mono (μ := ρ) (Set.subset_univ (Prod.mk x ⁻¹' t))
      simpa using h
    rw [Measure.prod_apply ht, Measure.prod_apply ht]
    exact tsub_le_iff_left.mpr (lintegral_le_lintegral_add_tvDist (μ := μ) (ν := ν) hg hg1)
  · have hg : Measurable fun x => ρ (Prod.mk x ⁻¹' t) := measurable_measure_prodMk_left ht
    have hg1 : ∀ x, ρ (Prod.mk x ⁻¹' t) ≤ 1 := fun x => by
      have h := measure_mono (μ := ρ) (Set.subset_univ (Prod.mk x ⁻¹' t))
      simpa using h
    rw [Measure.prod_apply ht, Measure.prod_apply ht]
    exact (tsub_le_iff_left.mpr
      (lintegral_le_lintegral_add_tvDist (μ := ν) (ν := μ) hg hg1)).trans_eq
      (tvDist_comm (μ := ν) (ν := μ))

end Prod

end TV
end QuantumZipper
