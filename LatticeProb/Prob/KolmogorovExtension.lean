import Mathlib

/-!
# Kolmogorov extension theorem: real coordinates, arbitrary index set

Statement: `LatticeProb.exists_isProjectiveLimit_real`, the Kolmogorov extension theorem for real coordinates and an arbitrary index set. Source: William J. Anderson, *Advanced Probability II Notes*,
Theorem 6.0.6, p. 60. Mathlib states the theorem as absent (`Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean`,
module docstring); the content-level construction is Mathlib's `projectiveFamilyContent`.

Route (after `Mathlib/Probability/ProductMeasure.lean`, `infinitePi`):

* `projectiveFamilyContent hP` is an additive content on the measurable cylinders of `ι → ℝ`.
* Its σ-additivity follows from continuity at `∅` along decreasing cylinders
  (`addContent_iUnion_eq_sum_of_tendsto_zero`); that continuity is `kolmogorov_tendsto_content`, proved by
  inner regularity of the finite-dimensional marginals (`MeasurableSet.exists_isCompact_lt_add`) and the
  Tychonoff argument `kolmogorov_exists_forall_mem`.
* Carathéodory (`AddContent.measure`) gives the measure; its cylinder values are the marginals.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb

universe u

variable {ι : Type u}

/-- A compact set of functions on a finite index set is bounded, uniformly in the finitely many coordinates. -/
lemma kolmogorov_exists_bound {S : Finset ι} {K : Set (S → ℝ)} (hK : IsCompact K) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ K, ∀ j : S, |y j| ≤ R := by
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun y hy j => ?_⟩
  have h1 : ‖y j‖ ≤ ‖y‖ := norm_le_pi_norm y j
  rw [Real.norm_eq_abs] at h1
  exact h1.trans ((hC y hy).trans (le_max_left _ _))

/-- Nested sets `{x | ∀ k ≤ n, x|I k ∈ K k}` with `K k` compact and nonempty at every stage have a common
point. Tychonoff on a box: coordinate `j` is bounded on the first stage `c j` containing it. -/
lemma kolmogorov_exists_forall_mem (I : ℕ → Finset ι) (K : ∀ k, Set (I k → ℝ)) (hK : ∀ k, IsCompact (K k))
    (hne : ∀ n, ∃ x : ι → ℝ, ∀ k ≤ n, (fun j : I k => x j) ∈ K k) :
    ∃ x : ι → ℝ, ∀ k, (fun j : I k => x j) ∈ K k := by
  classical
  choose R hR0 hRb using fun k => kolmogorov_exists_bound (hK k)
  obtain ⟨c, hc⟩ : ∃ c : ι → ℕ, ∀ j, c j = sInf {k | j ∈ I k} := ⟨_, fun _ => rfl⟩
  have hcmem : ∀ j, (∃ k, j ∈ I k) → j ∈ I (c j) := by
    intro j hj
    rw [hc j]
    exact Nat.sInf_mem hj
  have hcle : ∀ j k, j ∈ I k → c j ≤ k := by
    intro j k hk
    rw [hc j]
    exact Nat.sInf_le hk
  obtain ⟨B, hBdef⟩ : ∃ B : Set (ι → ℝ), B = Set.pi univ fun j => Icc (-R (c j)) (R (c j)) := ⟨_, rfl⟩
  have hB : IsCompact B := by
    rw [hBdef]
    exact isCompact_univ_pi fun j => isCompact_Icc
  obtain ⟨H, hHdef⟩ : ∃ H : ℕ → Set (ι → ℝ), ∀ n, H n = {x | ∀ k ≤ n, (fun j : I k => x j) ∈ K k} :=
    ⟨fun n => {x | ∀ k ≤ n, (fun j : I k => x j) ∈ K k}, fun _ => rfl⟩
  have hmemH : ∀ n (x : ι → ℝ), (∀ k ≤ n, (fun j : I k => x j) ∈ K k) → x ∈ H n := by
    intro n x hx
    rw [hHdef]
    exact hx
  have hHk : ∀ n (x : ι → ℝ), x ∈ H n → ∀ k ≤ n, (fun j : I k => x j) ∈ K k := by
    intro n x hx
    rw [hHdef] at hx
    exact hx
  have hHcl : ∀ n, IsClosed (H n) := by
    intro n
    have heq : H n = ⋂ k, ⋂ (_ : k ≤ n), (fun x : ι → ℝ => fun j : I k => x j) ⁻¹' K k := by
      ext x
      simp only [hHdef, Set.mem_ofPred_eq, mem_iInter, mem_preimage]
    rw [heq]
    refine isClosed_iInter fun k => isClosed_iInter fun _ => ?_
    exact IsClosed.preimage (f := fun x : ι → ℝ => fun j : I k => x j)
      (continuous_pi fun j => continuous_apply (j : ι)) (hK k).isClosed
  have hstage : ∀ n, (H n ∩ B).Nonempty := by
    intro n
    obtain ⟨x, hx⟩ := hne n
    obtain ⟨x', hx'def⟩ : ∃ x' : ι → ℝ, x' = fun j => if (∃ k ≤ n, j ∈ I k) then x j else 0 := ⟨_, rfl⟩
    have hagree : ∀ k ≤ n, (fun j : I k => x' j) = fun j : I k => x j := by
      intro k hk
      funext j
      have h : ∃ k' ≤ n, (j : ι) ∈ I k' := ⟨k, hk, j.2⟩
      simp [hx'def, h]
    refine ⟨x', hmemH n x' fun k hk => ?_, ?_⟩
    · rw [hagree k hk]
      exact hx k hk
    · rw [hBdef]
      refine Set.mem_univ_pi.2 fun j => ?_
      by_cases hj : ∃ k ≤ n, j ∈ I k
      · obtain ⟨k, hkn, hjk⟩ := hj
        have hcn : c j ≤ n := (hcle j k hjk).trans hkn
        have hy : (fun i : I (c j) => x i) ∈ K (c j) := hx (c j) hcn
        have hb : |x j| ≤ R (c j) := hRb (c j) _ hy ⟨j, hcmem j ⟨k, hjk⟩⟩
        have hxj : x' j = x j := by
          have h : ∃ k' ≤ n, j ∈ I k' := ⟨k, hkn, hjk⟩
          simp [hx'def, h]
        rw [hxj]
        exact abs_le.1 hb
      · have hxj : x' j = 0 := by
          simp [hx'def, hj]
        rw [hxj]
        exact ⟨by linarith [hR0 (c j)], hR0 (c j)⟩
  have hanti : ∀ n, H (n + 1) ∩ B ⊆ H n ∩ B := by
    rintro n x ⟨h1, h2⟩
    exact ⟨hmemH n x fun k hk => hHk (n + 1) x h1 k (hk.trans (Nat.le_succ n)), h2⟩
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => H n ∩ B) hanti hstage (hB.inter_left (hHcl 0)) fun n => (hHcl n).inter hB.isClosed
  refine ⟨x, fun k => ?_⟩
  have hxk : x ∈ H k ∩ B := mem_iInter.1 hx k
  exact hHk k x hxk.1 k le_rfl

/-- Continuity at `∅` of the projective content along decreasing cylinders with empty intersection
(analogue of `Kernel.trajContent_tendsto_zero`). -/
lemma kolmogorov_tendsto_content {P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ)}
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) [∀ J : Finset ι, IsProbabilityMeasure (P J)]
    {A : ℕ → Set (ι → ℝ)} (hA : ∀ n, A n ∈ measurableCylinders (fun _ : ι => ℝ))
    (hanti : Antitone A) (hinter : ⋂ n, A n = ∅) :
    Tendsto (fun n => projectiveFamilyContent hP (A n)) atTop (𝓝 0) := by
  classical
  choose I S hS hAeq using fun n => (mem_measurableCylinders (A n)).1 (hA n)
  refine ENNReal.tendsto_atTop_zero.2 fun ε hε => ?_
  suffices h : ∃ N, projectiveFamilyContent hP (A N) ≤ ε by
    obtain ⟨N, hN⟩ := h
    exact ⟨N, fun n hn => (projectiveFamilyContent_mono hP (hA n) (hA N) (hanti hn)).trans hN⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδpos, hδsum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
  -- compact approximations of the finite-dimensional marginals
  have hKex : ∀ k, ∃ K : Set (I k → ℝ), K ⊆ S k ∧ IsCompact K ∧ P (I k) (S k \ K) ≤ (δ k : ℝ≥0∞) := by
    intro k
    obtain ⟨K, hKS, hKc, hlt⟩ := (hS k).exists_isCompact_lt_add (measure_ne_top (P (I k)) (S k))
      (ENNReal.coe_ne_zero.2 (hδpos k).ne')
    refine ⟨K, hKS, hKc, ?_⟩
    rw [measure_sdiff hKS hKc.isClosed.measurableSet.nullMeasurableSet (measure_ne_top _ _)]
    exact tsub_le_iff_right.2 (by rw [add_comm]; exact hlt.le)
  choose K hKS hKc hKδ using hKex
  obtain ⟨D, hD⟩ : ∃ D : ℕ → Set (ι → ℝ), ∀ k, D k = A k \ cylinder (I k) (K k) := ⟨_, fun _ => rfl⟩
  have hDcyl : ∀ k, D k = cylinder (I k) (S k \ K k) := by
    intro k
    rw [hD k, hAeq k]
    exact (Set.preimage_sdiff _ _ _).symm
  have hDmem : ∀ k, D k ∈ measurableCylinders (fun _ : ι => ℝ) := fun k => by
    rw [hDcyl k]
    exact cylinder_mem_measurableCylinders _ _ ((hS k).diff (hKc k).isClosed.measurableSet)
  have hDδ : ∀ k, projectiveFamilyContent hP (D k) ≤ (δ k : ℝ≥0∞) := fun k => by
    rw [hDcyl k, projectiveFamilyContent_cylinder hP ((hS k).diff (hKc k).isClosed.measurableSet)]
    exact hKδ k
  -- every finite stage of the compact approximation is nonempty
  have hstage : ∀ n, ∃ x : ι → ℝ, ∀ k ≤ n, (fun j : I k => x j) ∈ K k := by
    intro n
    by_contra hnone
    push Not at hnone
    have hsub : A n ⊆ ⋃ k ∈ Finset.range (n + 1), D k := by
      intro x hx
      obtain ⟨k, hkn, hk⟩ := hnone x
      rw [mem_iUnion₂]
      refine ⟨k, Finset.mem_range.2 (Nat.lt_succ_of_le hkn), ?_⟩
      rw [hD k]
      exact ⟨hanti hkn hx, hk⟩
    have h1 : projectiveFamilyContent hP (A n) ≤ projectiveFamilyContent hP (⋃ k ∈ Finset.range (n + 1), D k) :=
      projectiveFamilyContent_mono hP (hA n) (isSetRing_measurableCylinders.biUnion_mem _ fun k _ => hDmem k) hsub
    have h2 : projectiveFamilyContent hP (⋃ k ∈ Finset.range (n + 1), D k)
        ≤ ∑ k ∈ Finset.range (n + 1), projectiveFamilyContent hP (D k) :=
      addContent_biUnion_le isSetRing_measurableCylinders fun k _ => hDmem k
    have h3 : ∑ k ∈ Finset.range (n + 1), projectiveFamilyContent hP (D k)
        ≤ ∑ k ∈ Finset.range (n + 1), (δ k : ℝ≥0∞) :=
      Finset.sum_le_sum fun k _ => hDδ k
    have h4 : ∑ k ∈ Finset.range (n + 1), (δ k : ℝ≥0∞) ≤ ∑' k, (δ k : ℝ≥0∞) := ENNReal.sum_le_tsum _
    exact (not_lt.2 (h1.trans (h2.trans (h3.trans (h4.trans hδsum.le))))) (hcon n)
  obtain ⟨x, hx⟩ := kolmogorov_exists_forall_mem I K hKc hstage
  have hxA : ∀ k, x ∈ A k := by
    intro k
    rw [hAeq k]
    exact hKS k (hx k)
  have hx0 : x ∈ ⋂ n, A n := mem_iInter.2 hxA
  rw [hinter] at hx0
  simp at hx0

/-- The content of a projective family of probability measures on real coordinates is σ-subadditive. -/
lemma kolmogorov_isSigmaSubadditive {P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ)}
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) [∀ J : Finset ι, IsProbabilityMeasure (P J)] :
    (projectiveFamilyContent hP).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum isSetRing_measurableCylinders ?_
  intro f hf hUf hdisj
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders _
    (fun s _ => projectiveFamilyContent_ne_top hP)
    (fun s hs anti hinter => kolmogorov_tendsto_content hP hs anti hinter) hf hUf hdisj

/-- **Kolmogorov extension theorem** (real coordinates, arbitrary index set, product σ-algebra).
A projective family of probability measures on the finite-dimensional coordinate spaces has a projective
limit, which is a probability measure on `ι → ℝ`. Source: Anderson, *Advanced Probability II Notes*, Thm 6.0.6. -/
theorem exists_isProjectiveLimit_real (ι : Type) (P : ∀ J : Finset ι, Measure (∀ _ : J, ℝ))
    (hP : IsProjectiveMeasureFamily (α := fun _ : ι => ℝ) P) (h1 : ∀ J : Finset ι, IsProbabilityMeasure (P J)) :
    ∃ μ : Measure (ι → ℝ), IsProbabilityMeasure μ ∧ IsProjectiveLimit (α := fun _ : ι => ℝ) μ P := by
  have : ∀ J : Finset ι, IsProbabilityMeasure (P J) := h1
  set μ : Measure (ι → ℝ) := (projectiveFamilyContent hP).measure isSetSemiring_measurableCylinders
    generateFrom_measurableCylinders.ge (kolmogorov_isSigmaSubadditive hP) with hμdef
  have hproj : IsProjectiveLimit (α := fun _ : ι => ℝ) μ P := by
    intro I
    ext s hs
    have hm : Measurable (I.restrict : (ι → ℝ) → (∀ j : I, ℝ)) := Finset.measurable_restrict I
    rw [Measure.map_apply hm hs]
    change μ (cylinder I s) = P I s
    rw [hμdef, AddContent.measure_eq (projectiveFamilyContent hP) isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.symm (kolmogorov_isSigmaSubadditive hP) (cylinder_mem_measurableCylinders _ _ hs),
      projectiveFamilyContent_cylinder hP hs]
  exact ⟨μ, hproj.isProbabilityMeasure, hproj⟩

end LatticeProb
