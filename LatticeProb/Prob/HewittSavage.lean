/-
The Hewitt-Savage zero-one law for a product measure on `ι → X`.

An exchangeable event, one unchanged by permuting finitely many coordinates,
has probability `0` or `1`.  The proof is the approximation argument of
`LatticeProb.measure_eq_zero_or_one_of_preimage_eq`, with one change.  There a
single transformation was fixed in advance and its iterates supplied the
independence; here no single permutation moves every finite set of coordinates
off itself, so the transformation is chosen after the approximating cylinder.
Given a cylinder over the coordinates `s`, the index type is infinite, so a
disjoint copy `t` of `s` exists, and the permutation that swaps `s` with `t`
carries the cylinder to an independent one while fixing the event.

`measure_eq_zero_or_one_of_family` is that variant of the abstract criterion.
Its proof is the proof of `measure_eq_zero_or_one_of_preimage_eq` with the
iterate replaced by the transformation the hypothesis supplies, and it is
therefore adapted from the same Apache-2.0 licensed source; see NOTICE.
-/
import LatticeProb.Prob.ZeroOne

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory
open scoped symmDiff ENNReal

/-! ### The abstract criterion, with the transformation chosen per approximation -/

section Abstract

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- **Abstract zero-one law, with a transformation for each approximating set.**
If the ring `C` generates the sigma algebra and covers the space up to a null
set, and every `B` in `C` admits a measure-preserving map that fixes `A` and
makes `B` independent of its own preimage, then `A` has measure `0` or `1`. -/
theorem measure_eq_zero_or_one_of_family [IsProbabilityMeasure μ] {C : Set (Set Ω)}
    (hC : IsSetRing C) (hcov : ∃ D : Set (Set Ω), D.Countable ∧ D ⊆ C ∧ μ (⋃₀ D)ᶜ = 0)
    (hgen : mΩ = MeasurableSpace.generateFrom C)
    {A : Set Ω} (hA : MeasurableSet A)
    (hmix : ∀ B ∈ C, ∃ S : Ω → Ω, MeasurePreserving S μ μ ∧ S ⁻¹' A = A ∧
      μ (B ∩ S ⁻¹' B) = μ B * μ B) :
    μ A = 0 ∨ μ A = 1 := by
  -- Step 1: `|μ(A) - μ(A)²| < 4ε` for every `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → |μ.real A - μ.real A * μ.real A| < 4 * ε := by
    intro ε hε
    obtain ⟨B, hBC, hBA⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing hC hcov hgen hA
      (ENNReal.ofReal_pos.2 hε)
    have hBm : MeasurableSet B := by
      have : MeasurableSet[MeasurableSpace.generateFrom C] B :=
        MeasurableSpace.measurableSet_generateFrom hBC
      rwa [← hgen] at this
    obtain ⟨S, hSmp, hSA, hn⟩ := hmix B hBC
    have hS : MeasurePreserving S μ μ := hSmp
    -- the approximation error `d = μ(B ∆ A) < ε`
    have hd : μ.real (B ∆ A) < ε := ENNReal.toReal_lt_of_lt_ofReal hBA
    have h1 : |μ.real A - μ.real B| ≤ μ.real (B ∆ A) := by
      rw [symmDiff_comm]
      exact abs_measureReal_sub_le_measureReal_symmDiff hA.nullMeasurableSet hBm.nullMeasurableSet
    -- `|μ(A) - μ(B ∩ T⁻ⁿB)| ≤ 2d`
    have h2 : |μ.real A - μ.real (B ∩ S ⁻¹' B)| ≤ 2 * μ.real (B ∆ A) := by
      have hpre : μ.real (S ⁻¹' (A ∆ B)) = μ.real (A ∆ B) := by
        simp only [measureReal_def]
        rw [hS.measure_preimage (hA.symmDiff hBm).nullMeasurableSet]
      calc |μ.real A - μ.real (B ∩ S ⁻¹' B)|
          = |μ.real (A ∩ S ⁻¹' A) - μ.real (B ∩ S ⁻¹' B)| := by
            rw [hSA, Set.inter_self]
        _ ≤ μ.real ((A ∩ S ⁻¹' A) ∆ (B ∩ S ⁻¹' B)) :=
            abs_measureReal_sub_le_measureReal_symmDiff
              (hA.inter (hS.measurable hA)).nullMeasurableSet
              (hBm.inter (hS.measurable hBm)).nullMeasurableSet
        _ ≤ μ.real ((A ∆ B) ∪ S ⁻¹' (A ∆ B)) := by
            refine measureReal_mono ?_
            intro x hx
            simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union] at hx ⊢
            tauto
        _ ≤ μ.real (A ∆ B) + μ.real (S ⁻¹' (A ∆ B)) := measureReal_union_le _ _
        _ = 2 * μ.real (B ∆ A) := by rw [hpre, symmDiff_comm]; ring
    -- independence: `μ(B ∩ T⁻ⁿB) = μ(B)²`
    have h3 : μ.real (B ∩ S ⁻¹' B) = μ.real B * μ.real B := by
      simp only [measureReal_def]; rw [hn, ENNReal.toReal_mul]
    rw [h3] at h2
    have hA0 : 0 ≤ μ.real A := measureReal_nonneg
    have hA1 : μ.real A ≤ 1 := measureReal_le_one
    have hB0 : 0 ≤ μ.real B := measureReal_nonneg
    have hB1 : μ.real B ≤ 1 := measureReal_le_one
    have h4 : |μ.real B * μ.real B - μ.real A * μ.real A| ≤ 2 * μ.real (B ∆ A) := by
      have : μ.real B * μ.real B - μ.real A * μ.real A =
          (μ.real B - μ.real A) * (μ.real B + μ.real A) := by ring
      rw [this, abs_mul, abs_sub_comm]
      calc |μ.real A - μ.real B| * |μ.real B + μ.real A| ≤ μ.real (B ∆ A) * 2 := by
            refine mul_le_mul h1 ?_ (abs_nonneg _) measureReal_nonneg
            rw [abs_le]; constructor <;> linarith
        _ = 2 * μ.real (B ∆ A) := by ring
    calc |μ.real A - μ.real A * μ.real A|
        ≤ |μ.real A - μ.real B * μ.real B| + |μ.real B * μ.real B - μ.real A * μ.real A| :=
          abs_sub_le _ _ _
      _ ≤ 4 * μ.real (B ∆ A) := by linarith
      _ < 4 * ε := by linarith
  -- Step 2: hence `μ(A) = μ(A)²`, i.e. `μ(A) ∈ {0, 1}`.
  have ha : μ.real A - μ.real A * μ.real A = 0 := by
    by_contra hne
    have hpos : 0 < |μ.real A - μ.real A * μ.real A| := abs_pos.2 hne
    have := key (|μ.real A - μ.real A * μ.real A| / 4) (by positivity)
    linarith
  have hreal : μ.real A = 0 ∨ μ.real A = 1 := by
    have : μ.real A * (1 - μ.real A) = 0 := by rw [← ha]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hreal with h | h
  · exact Or.inl ((measureReal_eq_zero_iff (measure_ne_top μ A)).1 h)
  · right
    rw [measureReal_def] at h
    exact (ENNReal.toReal_eq_one_iff _).1 h


end Abstract

/-! ### Swapping two disjoint finite sets of coordinates -/

section Swap

variable {ι : Type*} [DecidableEq ι] {s t : Finset ι}

/-- The involution of `ι` that carries `s` to `t` along `e` and fixes everything
outside `s ∪ t`. -/
def swapAlong (e : {x // x ∈ s} ≃ {x // x ∈ t}) : ι → ι := fun i =>
  if h : i ∈ s then (e ⟨i, h⟩ : ι) else if h : i ∈ t then (e.symm ⟨i, h⟩ : ι) else i

theorem swapAlong_mem_of_mem (e : {x // x ∈ s} ≃ {x // x ∈ t}) {i : ι} (h : i ∈ s) :
    swapAlong e i ∈ t := by
  rw [swapAlong, dif_pos h]
  exact (e ⟨i, h⟩).2

theorem swapAlong_notMem_of_mem (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t})
    {i : ι} (h : i ∈ s) : swapAlong e i ∉ s := fun hc =>
  (Finset.disjoint_left.mp hst) hc (swapAlong_mem_of_mem e h)

theorem swapAlong_eq_self (e : {x // x ∈ s} ≃ {x // x ∈ t}) {i : ι} (h1 : i ∉ s) (h2 : i ∉ t) :
    swapAlong e i = i := by rw [swapAlong, dif_neg h1, dif_neg h2]

theorem swapAlong_involutive (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t}) :
    Function.Involutive (swapAlong e) := by
  intro i
  by_cases h1 : i ∈ s
  · have hin : swapAlong e i = (e ⟨i, h1⟩ : ι) := by rw [swapAlong, dif_pos h1]
    have hj : (e ⟨i, h1⟩ : ι) ∈ t := (e ⟨i, h1⟩).2
    have hjs : (e ⟨i, h1⟩ : ι) ∉ s := fun hc => (Finset.disjoint_left.mp hst) hc hj
    rw [hin, swapAlong, dif_neg hjs, dif_pos hj]
    have : (⟨(e ⟨i, h1⟩ : ι), hj⟩ : {x // x ∈ t}) = e ⟨i, h1⟩ := rfl
    rw [this, Equiv.symm_apply_apply]
  · by_cases h2 : i ∈ t
    · have hin : swapAlong e i = (e.symm ⟨i, h2⟩ : ι) := by
        rw [swapAlong, dif_neg h1, dif_pos h2]
      have hk : (e.symm ⟨i, h2⟩ : ι) ∈ s := (e.symm ⟨i, h2⟩).2
      rw [hin, swapAlong, dif_pos hk]
      have : (⟨(e.symm ⟨i, h2⟩ : ι), hk⟩ : {x // x ∈ s}) = e.symm ⟨i, h2⟩ := rfl
      rw [this, Equiv.apply_symm_apply]
    · rw [swapAlong_eq_self e h1 h2, swapAlong_eq_self e h1 h2]

/-- The permutation of `ι` swapping the disjoint finite sets `s` and `t`. -/
def swapPerm (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t}) : Equiv.Perm ι :=
  (swapAlong_involutive hst e).toPerm _

theorem swapPerm_apply (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t}) (i : ι) :
    swapPerm hst e i = swapAlong e i := rfl

theorem swapPerm_notMem (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t})
    {i : ι} (h : i ∈ s) : swapPerm hst e i ∉ s :=
  swapAlong_notMem_of_mem hst e h

theorem swapPerm_support_finite (hst : Disjoint s t) (e : {x // x ∈ s} ≃ {x // x ∈ t}) :
    {i : ι | swapPerm hst e i ≠ i}.Finite := by
  refine Set.Finite.subset (s ∪ t : Finset ι).finite_toSet fun i hi => ?_
  by_contra hc
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hc
  push Not at hc
  exact hi (swapPerm_apply hst e i ▸ swapAlong_eq_self e hc.1 hc.2)

omit [DecidableEq ι] in
/-- In an infinite index type every finite set of coordinates has a disjoint copy
of the same size. -/
theorem exists_disjoint_finset_card_eq [Infinite ι] (s : Finset ι) :
    ∃ t : Finset ι, Disjoint s t ∧ s.card = t.card := by
  obtain ⟨t, hts, hcard⟩ :=
    ((s : Set ι).toFinite.infinite_compl).exists_subset_card_eq s.card
  refine ⟨t, ?_, hcard.symm⟩
  rw [Finset.disjoint_left]
  intro i hi hit
  exact (hts hit) hi

end Swap

/-! ### The Hewitt-Savage zero-one law -/

/-- **The Hewitt-Savage zero-one law.**  Give `ι → X` the product of copies of a
probability measure `μ`, with `ι` infinite.  An event unchanged by every
permutation of finitely many coordinates has probability `0` or `1`. -/
theorem measure_zero_or_one_of_exchangeable {ι X : Type*} [DecidableEq ι] [Infinite ι]
    [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    {A : Set (ι → X)} (hA : MeasurableSet A)
    (hinv : ∀ σ : Equiv.Perm ι, {i : ι | σ i ≠ i}.Finite →
      coordShift (X := X) (fun i => σ i) ⁻¹' A = A) :
    Measure.infinitePi (fun _ : ι => μ) A = 0
      ∨ Measure.infinitePi (fun _ : ι => μ) A = 1 := by
  classical
  set P : ι → Measure X := fun _ => μ with hP
  refine measure_eq_zero_or_one_of_family (C := measurableCylinders fun _ : ι => X)
    isSetRing_measurableCylinders ?_ generateFrom_measurableCylinders.symm hA ?_
  · refine ⟨{Set.univ}, Set.countable_singleton _, ?_, by simp⟩
    rw [Set.singleton_subset_iff]
    exact isSetAlgebra_measurableCylinders.univ_mem
  · intro B hB
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders B).1 hB
    obtain ⟨t, hst, hcard⟩ := exists_disjoint_finset_card_eq (ι := ι) s
    set e : {x // x ∈ s} ≃ {x // x ∈ t} := Finset.equivOfCardEq hcard with he
    set σ : Equiv.Perm ι := swapPerm hst e with hσ
    refine ⟨coordShift (X := X) fun i => σ i, ?_, hinv σ (swapPerm_support_finite hst e), ?_⟩
    · exact measurePreserving_coordShift P σ.injective fun _ => rfl
    · rw [infinitePi_inter_preimage_coordShift_cylinder P s
        (fun i hi => swapPerm_notMem hst e hi) hS,
        (measurePreserving_coordShift P σ.injective fun _ => rfl).measure_preimage
        (MeasurableSet.cylinder s hS).nullMeasurableSet]

end LatticeProb

end
