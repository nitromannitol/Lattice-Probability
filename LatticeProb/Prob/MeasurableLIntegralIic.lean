import Mathlib

/-!
# Integrals against a family of measures given by its masses on `Iic t`

Let `κ : α → Measure ℝ≥0` be a family of measures such that each `κ a` is finite on every
interval `Iic t`, and `a ↦ κ a (Iic t)` is measurable for every `t`. Then `a ↦ κ a S` is
measurable for every Borel set `S`, and `a ↦ ∫⁻ u, F (a, u) ∂(κ a)` is measurable for every
jointly measurable `F : α × ℝ≥0 → ℝ≥0∞`.

This is the measurability of kernel integrals: a family of measures on `ℝ≥0` which is measurable
on the generating π-system of intervals `Iic t` is a measurable kernel, and its integrals of
jointly measurable functions are measurable. The Mathlib analogue is
`Measurable.lintegral_kernel_prod_right` (`Mathlib/Probability/Kernel/MeasurableLIntegral.lean`),
which assumes s-finiteness of the kernel. Here the family is only finite at each point: the
restrictions `(κ a).restrict (Iic n)` are finite for every `a`, which is all that Dynkin's
π–λ argument needs (`ProbabilityTheory.Kernel.measurable_kernel_prodMk_left_of_finite`).
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- For a family `κ` of measures on `ℝ≥0` whose masses on the intervals `Iic t` are finite and
measurable in the parameter, the masses `a ↦ κ a (S ∩ Iic n)` are measurable for every Borel set
`S`. Proof: Dynkin's π–λ theorem (`MeasurableSpace.induction_on_inter`) on the π-system of the
intervals `Iic t`, which generates the Borel σ-algebra of `ℝ≥0` (`borel_eq_generateFrom_Iic`). -/
theorem measurable_measure_inter_Iic {α : Type*} [MeasurableSpace α] (κ : α → Measure ℝ≥0)
    (hfin : ∀ a (t : ℝ≥0), κ a (Set.Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun a => κ a (Set.Iic t)) (n : ℝ≥0) :
    ∀ S : Set ℝ≥0, MeasurableSet S → Measurable fun a => κ a (S ∩ Set.Iic n) := by
  have hgen : (inferInstance : MeasurableSpace ℝ≥0) =
      MeasurableSpace.generateFrom (range (Set.Iic : ℝ≥0 → Set ℝ≥0)) :=
    BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic ℝ≥0)
  have hpi : IsPiSystem (range (Set.Iic : ℝ≥0 → Set ℝ≥0)) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _
    exact ⟨a ⊓ b, Set.Iic_inter_Iic.symm⟩
  intro S hS
  induction S, hS using MeasurableSpace.induction_on_inter hgen hpi with
  | empty =>
    simp only [Set.empty_inter, measure_empty]
    exact measurable_const
  | basic t ht =>
    obtain ⟨m, rfl⟩ := ht
    simp only [Set.Iic_inter_Iic]
    exact hIic (m ⊓ n)
  | compl t htm iht =>
    have hset : ∀ a, κ a (tᶜ ∩ Set.Iic n) = κ a (Set.Iic n) - κ a (t ∩ Set.Iic n) := by
      intro a
      have hsub : tᶜ ∩ Set.Iic n = Set.Iic n \ (t ∩ Set.Iic n) := by
        ext u
        simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]
        tauto
      rw [hsub, measure_sdiff Set.inter_subset_right
        (htm.inter measurableSet_Iic).nullMeasurableSet
        (ne_top_of_le_ne_top (hfin a n) (measure_mono Set.inter_subset_right))]
    simp_rw [hset]
    exact (hIic n).sub iht
  | iUnion f hd hfm hC =>
    have hfun : ∀ a, κ a ((⋃ i, f i) ∩ Set.Iic n) = ∑' i, κ a (f i ∩ Set.Iic n) := by
      intro a
      rw [Set.iUnion_inter, measure_iUnion]
      · exact fun i j hij => (hd hij).mono Set.inter_subset_left Set.inter_subset_left
      · exact fun i => (hfm i).inter measurableSet_Iic
    simp_rw [hfun]
    exact Measurable.tsum hC

/-- Measurability of `a ↦ ∫⁻ u, G (a, u) ∂(ν a)` for a family `ν` of measures on `ℝ≥0` that are
finite at each point and whose masses `a ↦ ν a S` are measurable. Only pointwise finiteness is
used. The proof is that of `Measurable.lintegral_kernel_prod_right`
(`Mathlib/Probability/Kernel/MeasurableLIntegral.lean`), with
`Kernel.measurable_kernel_prodMk_left_of_finite` in place of
`Kernel.measurable_kernel_prodMk_left`. -/
theorem measurable_lintegral_of_finite_family {α : Type*} [MeasurableSpace α]
    (ν : α → Measure ℝ≥0) (hν : ∀ S : Set ℝ≥0, MeasurableSet S → Measurable fun a => ν a S)
    (hfin : ∀ a, IsFiniteMeasure (ν a)) {G : α × ℝ≥0 → ℝ≥0∞} (hG : Measurable G) :
    Measurable fun a => ∫⁻ u, G (a, u) ∂(ν a) := by
  let K : Kernel α ℝ≥0 := ⟨ν, Measure.measurable_of_measurable_coe ν hν⟩
  have hK : ∀ t : Set (α × ℝ≥0), MeasurableSet t → Measurable fun a => ν a (Prod.mk a ⁻¹' t) :=
    fun t ht => Kernel.measurable_kernel_prodMk_left_of_finite (κ := K) ht hfin
  have hind : ∀ (t : Set (α × ℝ≥0)), MeasurableSet t → ∀ c : ℝ≥0∞,
      Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × ℝ≥0) c) (a, b) ∂(ν a) := by
    intro t ht c
    unfold Function.const
    simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
    exact Measurable.const_mul (hK t ht) c
  have hsup : (fun a => ∫⁻ u, G (a, u) ∂(ν a)) =
      fun a => ⨆ n : ℕ, ∫⁻ u, SimpleFunc.eapprox G n (a, u) ∂(ν a) := by
    funext a
    have hG' : (fun u => G (a, u)) = fun u => ⨆ n : ℕ, SimpleFunc.eapprox G n (a, u) := by
      funext u
      exact (SimpleFunc.iSup_eapprox_apply hG (a, u)).symm
    rw [hG', lintegral_iSup]
    · intro n
      exact (SimpleFunc.eapprox G n).measurable.comp measurable_prodMk_left
    · exact fun i j hij u => SimpleFunc.monotone_eapprox G hij (a, u)
  rw [hsup]
  refine Measurable.iSup fun n => ?_
  refine SimpleFunc.induction (motive := fun f : SimpleFunc (α × ℝ≥0) ℝ≥0∞ =>
    Measurable fun a => ∫⁻ u, f (a, u) ∂(ν a)) ?_ ?_ (SimpleFunc.eapprox G n)
  · intro c s hs
    simp only [SimpleFunc.coe_piecewise, SimpleFunc.coe_const]
    exact hind s hs c
  · intro f g _ hf hg
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add : (fun a => ∫⁻ u, f (a, u) + g (a, u) ∂(ν a)) =
        (fun a => ∫⁻ u, f (a, u) ∂(ν a)) + fun a => ∫⁻ u, g (a, u) ∂(ν a) := by
      funext a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact hf.add hg

/-- **Measurability of kernel integrals from the masses on `Iic`.** Let `κ : α → Measure ℝ≥0`
with each `κ a (Iic t)` finite and measurable in `a`. Then `a ↦ ∫⁻ u, F (a, u) ∂(κ a)` is
measurable for every measurable `F : α × ℝ≥0 → ℝ≥0∞`. Proof: write the integral as the increasing
limit over `n` of the integrals against the finite measures `(κ a).restrict (Iic n)`
(monotone convergence along the indicators of `Iic n`), and apply
`measurable_lintegral_of_finite_family` to each.

Locator: Kallenberg, *Foundations of Modern Probability*, 2nd ed. (Springer 2002), Lemma 1.40
(iii)⇒(i), p. 20, and Lemma 1.41 (i), p. 21, stated for probability kernels. The locally finite
case: restrict to `Iic n`, normalise, and take the monotone limit (Mathlib:
`Measurable.measure_of_isPiSystem`, `Kernel.measurable_kernel_prodMk_left_of_finite`). -/
theorem measurable_lintegral_of_measurable_Iic {α : Type*} [MeasurableSpace α]
    (κ : α → Measure ℝ≥0) (hfin : ∀ a t, κ a (Set.Iic t) ≠ ∞)
    (hIic : ∀ t : ℝ≥0, Measurable fun a => κ a (Set.Iic t))
    {F : α × ℝ≥0 → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun a => ∫⁻ u, F (a, u) ∂(κ a) := by
  have hL : ∀ n : ℕ,
      Measurable fun a => ∫⁻ u, F (a, u) ∂((κ a).restrict (Set.Iic (n : ℝ≥0))) := by
    intro n
    refine measurable_lintegral_of_finite_family (fun a => (κ a).restrict (Set.Iic (n : ℝ≥0)))
      ?_ ?_ hF
    · intro S hS
      simp only [Measure.restrict_apply hS]
      exact measurable_measure_inter_Iic κ hfin hIic (n : ℝ≥0) S hS
    · intro a
      show IsFiniteMeasure ((κ a).restrict (Set.Iic (n : ℝ≥0)))
      constructor
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 (hfin a n)
  have hsplit : ∀ a, ∫⁻ u, F (a, u) ∂(κ a) =
      ⨆ n : ℕ, ∫⁻ u, F (a, u) ∂((κ a).restrict (Set.Iic (n : ℝ≥0))) := by
    intro a
    have hpt : ∀ u : ℝ≥0,
        F (a, u) = ⨆ n : ℕ, (Set.Iic (n : ℝ≥0)).indicator (fun u => F (a, u)) u := by
      intro u
      refine le_antisymm (le_iSup_of_le ⌈u⌉₊ (le_of_eq ?_))
        (iSup_le fun n => Set.indicator_le_self _ _ u)
      exact (Set.indicator_of_mem (show u ∈ Set.Iic ((⌈u⌉₊ : ℕ) : ℝ≥0) from Nat.le_ceil u) (fun v => F (a, v))).symm
    calc ∫⁻ u, F (a, u) ∂(κ a)
        = ∫⁻ u, ⨆ n : ℕ, (Set.Iic (n : ℝ≥0)).indicator (fun u => F (a, u)) u ∂(κ a) :=
          lintegral_congr fun u => hpt u
      _ = ⨆ n : ℕ, ∫⁻ u, (Set.Iic (n : ℝ≥0)).indicator (fun u => F (a, u)) u ∂(κ a) := by
          refine lintegral_iSup (fun n => ?_) (fun i j hij u => ?_)
          · exact (hF.comp measurable_prodMk_left).indicator measurableSet_Iic
          · exact Set.indicator_le_indicator_of_subset
              (Set.Iic_subset_Iic.2 (Nat.cast_le.2 hij)) (fun _ => zero_le) u
      _ = ⨆ n : ℕ, ∫⁻ u, F (a, u) ∂((κ a).restrict (Set.Iic (n : ℝ≥0))) :=
          iSup_congr fun n => lintegral_indicator measurableSet_Iic _
  have hfun : (fun a => ∫⁻ u, F (a, u) ∂(κ a)) =
      fun a => ⨆ n : ℕ, ∫⁻ u, F (a, u) ∂((κ a).restrict (Set.Iic (n : ℝ≥0))) :=
    funext hsplit
  rw [hfun]
  exact Measurable.iSup hL

end LatticeProb
