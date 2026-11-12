/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.DisjointUnion at commit 31e7483; only the module paths of local imports are changed.
   Changed: docstring wording of the module docstring entry for dualCov_union_of_disjoint and dualCov_iUnion_of_pairwise_disjoint. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.DualNorm
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# GFF-K3, node C3: the dual Dirichlet norm on disjoint unions

For a disjoint union of open sets, the Dirichlet space is the orthogonal direct sum of the
Dirichlet spaces of the pieces, so the squared dual norm splits additively over the pieces. **Own
argument** for this form: Sheffield, arXiv:1012.4797, p. 12, only says that the zero-boundary GFF
on a domain with several components is "the sum of an independent zero boundary GFF on each
component"; it states no disjoint-union identity for the Dirichlet space (the earlier citation
"Sheffield (2007) §2" had none — AUDIT8 K8-3).

Main results:
* `dualNormSq_union_of_disjoint` — two open disjoint pieces;
* `dualNormSq_iUnion_of_pairwise_disjoint` — countably many open pairwise disjoint pieces;
* `dualCov_union_of_disjoint`, `dualCov_iUnion_of_pairwise_disjoint` — the polarized versions,
  for measures **admissible on the union** (`IsAdmissibleDual` on `D₁ ∪ D₂`, which the countable
  identity needs; finite dual norm on each piece does not suffice).

A test function `f ∈ zeroSpace (D₁ ∪ D₂)` is split with a smooth cut-off `χ`, equal to `1` on
`tsupport f ∩ closure D₁` and supported in `D₁`; the cut-off is built by hand from finitely many
`ContDiffBump`s covering the compact set `tsupport f ∩ closure D₁` (own elementary
construction). Then `f = f·χ + f·(1-χ)` with the two parts supported in `D₁` resp. `D₂`, and
each part vanishes identically on the *other* (open) piece, so the gradients never interact and
the energies split exactly. The degenerate case of vanishing energy is handled by
`eq_zero_of_dirichletEnergyOn_eq_zero`; the reverse inequality uses the "optimal scaling" of the
blueprint: the combination `(a₁/e₁)f₁ + (a₂/e₂)f₂` has energy exactly `a₁²/e₁ + a₂²/e₂`.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal Function

namespace QuantumZipper.K3

variable {D₁ D₂ : Set ℂ} {μ ν : Measure ℂ}

/-! ### Analytic preliminaries -/

/-- A function vanishing on a neighbourhood of a point has zero Fréchet derivative there. -/
private lemma fderiv_eq_zero_of_eventuallyEq_zero {g : ℂ → ℝ} {z : ℂ}
    (hg : DifferentiableAt ℝ g z) (h : ∀ᶠ y in 𝓝 z, g y = 0) : fderiv ℝ g z = 0 := by
  have h1 : (0 : ℂ → ℝ) =ᶠ[𝓝 z] g := h.mono fun y hy => hy.symm
  exact ((hasFDerivAt_const (0 : ℝ) z).unique (hg.hasFDerivAt.congr_of_eventuallyEq h1)).symm

/-- `0 ≤ ∏ (1 - u i)` when all `u i ≤ 1`; own elementary proof by induction. -/
private lemma prod_one_sub_nonneg {ι : Type*} (t : Finset ι) {u : ι → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ u i) (h1 : ∀ i ∈ t, u i ≤ 1) : 0 ≤ ∏ i ∈ t, (1 - u i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_nonneg (by linarith [h1 a (Finset.mem_insert_self a s)])
        (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi)))

/-- `∏ (1 - u i) ≤ 1` when all `u i ∈ [0,1]`; own elementary proof by induction. -/
private lemma prod_one_sub_le_one {ι : Type*} (t : Finset ι) {u : ι → ℝ}
    (h0 : ∀ i ∈ t, 0 ≤ u i) (h1 : ∀ i ∈ t, u i ≤ 1) : ∏ i ∈ t, (1 - u i) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hsa : 1 - u a ≤ 1 := by linarith [h0 a (Finset.mem_insert_self a s)]
      have hsn : 0 ≤ ∏ i ∈ s, (1 - u i) :=
        prod_one_sub_nonneg s (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
      calc (1 - u a) * ∏ i ∈ s, (1 - u i) ≤ 1 * (∏ i ∈ s, (1 - u i)) :=
            mul_le_mul_of_nonneg_right hsa hsn
        _ = ∏ i ∈ s, (1 - u i) := one_mul _
        _ ≤ 1 := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
            (fun i hi => h1 i (Finset.mem_insert_of_mem hi))

/-- Smoothness of `y ↦ ∏ i ∈ t, (1 - b i y)`; standalone so that the induction over `t` is not
polluted by hypotheses mentioning `t`. -/
private lemma contDiff_prod_one_sub {ι : Type*} (t : Finset ι) {b : ι → ℂ → ℝ}
    (hb : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y => ∏ i ∈ t, (1 - b i y) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simpa using (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun _ : ℂ => (1 : ℝ))
  | insert a s ha ih =>
      have hsplit : (fun y => ∏ i ∈ insert a s, (1 - b i y)) =
          fun y => (1 - b a y) * ∏ i ∈ s, (1 - b i y) := by
        funext y
        rw [Finset.prod_insert ha]
      rw [hsplit]
      exact (contDiff_const.sub (hb a)).mul ih

/-! ### The cut-off -/

/-- A function supported in the union of two disjoint open sets is supported in `D₁` near
`closure D₁`. -/
private lemma tsupport_inter_closure_subset (h₂ : IsOpen D₂) (hd : Disjoint D₁ D₂)
    {f : ℂ → ℝ} (hf : tsupport f ⊆ D₁ ∪ D₂) : tsupport f ∩ closure D₁ ⊆ D₁ := by
  intro z hz
  by_contra hzD₁
  have hzD₂ : z ∈ D₂ := (hf hz.1).resolve_left hzD₁
  have hsub : D₁ ⊆ D₂ᶜ := fun y hy => disjoint_left.mp hd hy
  have : closure D₁ ⊆ D₂ᶜ := (closure_mono hsub).trans h₂.isClosed_compl.closure_subset
  exact this hz.2 hzD₂

/-- **Cut-off lemma.** For `f` compactly supported in `D₁ ∪ D₂` with `D₁, D₂` open and disjoint
there is a smooth compactly supported `χ` with `tsupport χ ⊆ D₁`, `χ = 1` on
`tsupport f ∩ closure D₁` and `0 ≤ χ ≤ 1`. Own elementary construction: finitely many
`ContDiffBump`s `b_z` with `closedBall z (2 r z) ⊆ D₁` cover `tsupport f ∩ closure D₁`, and
`χ = 1 - ∏_z (1 - b_z)` equals `1` on the union of the larger balls and vanishes where all the
`b_z` vanish. -/
private lemma exists_smooth_cutoff {f : ℂ → ℝ} (hf : HasCompactSupport f)
    (h₁ : IsOpen D₁) (h₂ : IsOpen D₂) (hd : Disjoint D₁ D₂) (hfsupp : tsupport f ⊆ D₁ ∪ D₂) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ D₁ ∧ (∀ z ∈ tsupport f ∩ closure D₁, χ z = 1) ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) := by
  classical
  have hKc : IsCompact (tsupport f ∩ closure D₁) :=
    (show IsCompact (tsupport f) from hf).inter_right isClosed_closure
  have hball : ∀ i : ↥(tsupport f ∩ closure D₁),
      ∃ r : ℝ, 0 < r ∧ closedBall i.1 (2 * r) ⊆ D₁ := by
    intro i
    have hiD : i.1 ∈ D₁ := tsupport_inter_closure_subset h₂ hd hfsupp i.2
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp h₁ i.1 hiD
    exact ⟨ε / 4, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hεsub⟩
  choose r hrpos hrsub using hball
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover (fun i : ↥(tsupport f ∩ closure D₁) => ball i.1 (r i))
    (fun _ => isOpen_ball) fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, mem_ball_self (hrpos ⟨y, hy⟩)⟩
  let b : (i : ↥(tsupport f ∩ closure D₁)) → ContDiffBump i.1 :=
    fun i => ⟨r i, 2 * r i, hrpos i, by have h := hrpos i; linarith⟩
  let χ : ℂ → ℝ := fun y => 1 - ∏ i ∈ t, (1 - b i y)
  have hχsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ :=
    contDiff_const.sub (contDiff_prod_one_sub t fun i => (b i).contDiff)
  have hzero_prod : ∀ y : ℂ, (∀ i ∈ t, y ∉ ball i.1 (2 * r i)) →
      (∏ i ∈ t, (1 - b i y)) = 1 := by
    intro y hy
    have hb : ∀ i ∈ t, b i y = 0 := fun i hi => by
      have hne : y ∉ Function.support (b i) := by
        rw [(b i).support_eq]
        exact hy i hi
      simpa [Function.mem_support] using hne
    calc (∏ i ∈ t, (1 - b i y)) = ∏ i ∈ t, (1 - (0 : ℝ)) :=
          Finset.prod_congr rfl fun i hi => by rw [hb i hi]
      _ = 1 := by simp
  have hsupp : Function.support χ ⊆ ⋃ i ∈ t, closedBall i.1 (2 * r i) := by
    intro y hy
    by_contra hy'
    have h1 : (∏ i ∈ t, (1 - b i y)) = 1 :=
      hzero_prod y fun i hi hc =>
        hy' (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, ball_subset_closedBall hc⟩⟩)
    exact hy (by simp only [χ, h1]; norm_num)
  have hunion_compact : IsCompact (⋃ i ∈ t, closedBall i.1 (2 * r i)) :=
    t.isCompact_biUnion fun i _ => isCompact_closedBall i.1 (2 * r i)
  have hunion_sub : (⋃ i ∈ t, closedBall i.1 (2 * r i)) ⊆ D₁ := by
    intro y hy
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
    obtain ⟨-, hyi'⟩ := Set.mem_iUnion.mp hyi
    exact hrsub i hyi'
  have htsupp_union : tsupport χ ⊆ ⋃ i ∈ t, closedBall i.1 (2 * r i) :=
    closure_minimal hsupp hunion_compact.isClosed
  refine ⟨χ, hχsmooth, IsCompact.of_isClosed_subset hunion_compact (isClosed_tsupport χ) htsupp_union,
    htsupp_union.trans hunion_sub, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp (ht hz)
    obtain ⟨him, hzi'⟩ := Set.mem_iUnion.mp hzi
    have hbi : b i z = 1 := (b i).one_of_mem_closedBall (ball_subset_closedBall hzi')
    have h0 : (1 : ℝ) - b i z = 0 := by rw [hbi]; norm_num
    have hprod : (∏ j ∈ t, (1 - b j z)) = 0 := by
      rw [← Finset.prod_erase_mul t (fun j => 1 - b j z) him, h0, mul_zero]
    simp only [χ, hprod]
    norm_num
  · intro z
    have h0 : 0 ≤ ∏ i ∈ t, (1 - b i z) :=
      prod_one_sub_nonneg t (fun i _ => (b i).nonneg) fun i _ => (b i).le_one
    have h1 : (∏ i ∈ t, (1 - b i z)) ≤ 1 :=
      prod_one_sub_le_one t (fun i _ => (b i).nonneg) fun i _ => (b i).le_one
    constructor <;> simp only [χ] <;> linarith

/-! ### Zero energy forces zero -/

/-- **Zero energy forces zero.** A smooth compactly supported function `g` with
`tsupport g ⊆ D`, `D` open, and `dirichletEnergyOn D g = 0` is identically zero: the gradient
vanishes a.e. on `D`, hence everywhere by continuity, so `g` is locally constant; the set
`D ∩ {g ≠ 0}` is then both closed and open, so if nonempty it contains all of `ℂ` and `g` would
have to be a nonzero constant, contradicting compact support. -/
private lemma eq_zero_of_dirichletEnergyOn_eq_zero {D : Set ℂ} (hD : IsOpen D) {g : ℂ → ℝ}
    (hg : g ∈ zeroSpace D) (hE : dirichletEnergyOn D g = 0) : ∀ z, g z = 0 := by
  have hgrad : ∀ z ∈ D, fderiv ℝ g z = 0 := by
    have hint : IntegrableOn (fun z => ‖fderiv ℝ g z‖ ^ 2) D :=
      (isDNSpace_zeroSpace D).energy g hg
    have hcont : Continuous fun z => ‖fderiv ℝ g z‖ ^ 2 :=
      ((hg.1.continuous_fderiv smooth_ne_zero).norm).pow 2
    have h0 : ∫ z in D, ‖fderiv ℝ g z‖ ^ 2 = 0 := by
      have hE' : (2 * Real.pi)⁻¹ * ∫ z in D, ‖fderiv ℝ g z‖ ^ 2 = 0 := hE
      exact (mul_eq_zero.mp hE').resolve_left (inv_ne_zero (by positivity))
    have hae : (fun z => ‖fderiv ℝ g z‖ ^ 2) =ᵐ[volume.restrict D] 0 :=
      (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z => sq_nonneg _) hint).mp h0
    have hEq := MeasureTheory.Measure.eqOn_open_of_ae_eq hae hD hcont.continuousOn
      continuous_zero.continuousOn
    intro z hz
    have hz' := hEq hz
    simpa [pow_eq_zero_iff two_ne_zero, norm_eq_zero] using hz'
  have hAopen : IsOpen (D ∩ g ⁻¹' {y : ℝ | y ≠ 0}) :=
    hD.isOpen_inter_preimage_of_fderiv_eq_zero
      (hg.1.differentiable smooth_ne_zero).differentiableOn
      (fun z hz => hgrad z hz) {y : ℝ | y ≠ 0}
  have hsub : closure (D ∩ Function.support g) ⊆ D :=
    (closure_mono Set.inter_subset_right).trans hg.2.2
  have hAclosed : IsClosed (D ∩ g ⁻¹' {y : ℝ | y ≠ 0}) := by
    rw [← closure_subset_iff_isClosed]
    intro z hzcl
    have hzD : z ∈ D := hsub hzcl
    obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.mp hD z hzD
    have hconst : ∀ y ∈ ball z ρ, g y = g z := by
      intro y hy
      exact (convex_ball z ρ).is_const_of_fderivWithin_eq_zero
        (hg.1.differentiable smooth_ne_zero).differentiableOn
        (fun w hw => by rw [fderivWithin_of_isOpen isOpen_ball hw]; exact hgrad w (hρsub hw))
        hy (mem_ball_self hρ)
    obtain ⟨y, hyA, hyρ⟩ := Metric.mem_closure_iff.mp hzcl (ρ / 2) (by positivity)
    have hyg : g y ≠ 0 := hyA.2
    have hyball : y ∈ ball z ρ := by
      rw [mem_ball, dist_comm]
      exact lt_of_lt_of_le hyρ (by linarith)
    exact ⟨hzD, by
      show g z ≠ 0
      rw [← hconst y hyball]
      exact hyg⟩
  intro z
  by_contra hz
  have hzsupp : z ∈ Function.support g := by simpa [Function.mem_support] using hz
  have hzD : z ∈ D := hg.2.2 (subset_tsupport g hzsupp)
  have hne : ((univ : Set ℂ) ∩ (D ∩ Function.support g)).Nonempty :=
    ⟨z, mem_univ z, hzD, hzsupp⟩
  have hsub' : (univ : Set ℂ) ⊆ D ∩ Function.support g :=
    convex_univ.isPreconnected.subset_isClopen ⟨hAclosed, hAopen⟩ hne
  have hsuppuniv : Function.support g = univ :=
    top_le_iff.mp (hsub'.trans Set.inter_subset_right)
  have hcomp : IsCompact (univ : Set ℂ) := by
    have h2 : tsupport g = (univ : Set ℂ) := by
      have h3 : tsupport g = closure (Function.support g) := rfl
      rw [h3, hsuppuniv, closure_univ]
    exact h2 ▸ (show IsCompact (tsupport g) from hg.2.1)
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hcomp.isBounded
  have hC0 : (0 : ℝ) ≤ C := by simpa using hC (mem_univ (0 : ℂ))
  have hC1 : ‖((C + 1 : ℝ) • (1 : ℂ) : ℂ)‖ ≤ C := by
    have h := hC (mem_univ ((C + 1 : ℝ) • (1 : ℂ)))
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ C + 1 by linarith), norm_one,
    mul_one] at hC1
  linarith

/-! ### Energy of a disjoint decomposition -/

/-- The two-term Engel (Titu/Sedrakyan) inequality, deduced from the `Finset` version
`Finset.sq_sum_div_le_sum_sq_div`. -/
private lemma sq_add_sq_div_le (a₁ a₂ e₁ e₂ : ℝ) (h₁ : 0 < e₁) (h₂ : 0 < e₂) :
    (a₁ + a₂) ^ 2 / (e₁ + e₂) ≤ a₁ ^ 2 / e₁ + a₂ ^ 2 / e₂ := by
  classical
  have hf : (∑ x ∈ ({0, 1} : Finset ℝ), (if x = 0 then a₁ else a₂)) = a₁ + a₂ := by
    rw [Finset.sum_pair (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  have hg : (∑ x ∈ ({0, 1} : Finset ℝ), (if x = 0 then e₁ else e₂)) = e₁ + e₂ := by
    rw [Finset.sum_pair (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  have hfg : (∑ x ∈ ({0, 1} : Finset ℝ),
      (if x = 0 then a₁ else a₂) ^ 2 / (if x = 0 then e₁ else e₂)) =
      a₁ ^ 2 / e₁ + a₂ ^ 2 / e₂ := by
    rw [Finset.sum_pair (by norm_num : (0 : ℝ) ≠ 1)]
    simp
  rw [← hf, ← hg, ← hfg]
  exact Finset.sq_sum_div_le_sum_sq_div _ _ fun i hi => by
    rcases Finset.mem_insert.mp hi with h | h
    · rw [h]; simpa using h₁
    · rw [Finset.mem_singleton.mp h]; simpa using h₂

/-- Splitting `f ∈ zeroSpace (D₁ ∪ D₂)` as `f·χ + f·(1-χ)`, with the two parts in
`zeroSpace D₁`, `zeroSpace D₂` and each vanishing on the other piece. -/
private lemma exists_decomposition_of_mem_zeroSpace_union (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    (hd : Disjoint D₁ D₂) {f : ℂ → ℝ} (hf : f ∈ zeroSpace (D₁ ∪ D₂)) (hint : Integrable f μ) :
    ∃ g ∈ zeroSpace D₁, ∃ h ∈ zeroSpace D₂, Integrable g μ ∧ Integrable h μ ∧
      (∀ z, f z = g z + h z) ∧ (∀ z ∈ D₁, h z = 0) ∧ (∀ z ∈ D₂, g z = 0) := by
  obtain ⟨χ, hχsmooth, hχcs, hχsupp, hχone, hχbdd⟩ :=
    exists_smooth_cutoff hf.2.1 h₁ h₂ hd hf.2.2
  have hχmeas : AEStronglyMeasurable χ μ := hχsmooth.continuous.measurable.aestronglyMeasurable
  have hχbound : ∀ᵐ z ∂μ, ‖χ z‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hχbdd z).1]
      exact (hχbdd z).2
  have hgm : Integrable (fun z => f z * χ z) μ :=
    (hint.bdd_mul hχmeas hχbound).congr (Eventually.of_forall fun z => mul_comm (χ z) (f z))
  have hhm : Integrable (fun z => f z * (1 - χ z)) μ :=
    (hint.sub hgm).congr (Eventually.of_forall fun z => by simp only [Pi.sub_apply]; ring)
  have hh0 : ∀ z ∈ D₁, f z * (1 - χ z) = 0 := by
    intro z hz
    by_cases hz0 : f z = 0
    · rw [hz0, zero_mul]
    · have hzK : z ∈ tsupport f ∩ closure D₁ :=
        ⟨subset_tsupport f (by simpa [Function.mem_support] using hz0), subset_closure hz⟩
      rw [hχone z hzK, sub_self, mul_zero]
  have hg0 : ∀ z ∈ D₂, f z * χ z = 0 := by
    intro z hz
    have hzχ : χ z = 0 := by
      by_contra hc
      exact disjoint_left.mp hd
        (hχsupp (subset_tsupport χ (by simpa [Function.mem_support] using hc))) hz
    rw [hzχ, mul_zero]
  have hhtsupp : tsupport (fun z => f z * (1 - χ z)) ⊆ D₂ := by
    intro z hz
    have hzU : z ∈ D₁ ∪ D₂ :=
      hf.2.2 ((tsupport_mul_subset_left (f := f) (g := fun z => 1 - χ z)) hz)
    rcases hzU with hzD₁ | hzD₂
    · exfalso
      have hsub'' : Function.support (fun y => f y * (1 - χ y)) ⊆ D₁ᶜ :=
        fun y hy hyD₁ => hy (hh0 y hyD₁)
      have hcl : closure (Function.support fun y => f y * (1 - χ y)) ⊆ D₁ᶜ :=
        (closure_mono hsub'').trans (le_of_eq h₁.isClosed_compl.closure_eq)
      exact hcl hz hzD₁
    · exact hzD₂
  exact ⟨fun z => f z * χ z,
    ⟨hf.1.mul hχsmooth, hf.2.1.mul_right (f' := χ),
      (tsupport_mul_subset_right (f := f) (g := χ)).trans hχsupp⟩,
    fun z => f z * (1 - χ z),
    ⟨hf.1.mul (contDiff_const.sub hχsmooth),
      hf.2.1.mul_right (f' := fun z => 1 - χ z), hhtsupp⟩,
    hgm, hhm, fun z => by ring, hh0, hg0⟩

-- `‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2` when one of the two summands vanishes. Stated for an
-- abstract seminormed group so that the proof only unfolds `pow` on `ℝ`.
private lemma norm_add_sq_of_eq_zero_left {E : Type*} [SeminormedAddCommGroup E] {a b : E}
    (ha : a = 0) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [ha, zero_add, norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num), zero_add]

private lemma norm_add_sq_of_eq_zero_right {E : Type*} [SeminormedAddCommGroup E] {a b : E}
    (hb : b = 0) : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [hb, add_zero, norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num), add_zero]

-- The pointwise identity `‖∇(g + h)‖² = ‖∇g‖² + ‖∇h‖²`: the two gradients never coexist, since
-- near a point of `D₁` the function `h` vanishes and outside `D₁` the support of `g` keeps away
-- from the point.
private lemma normSq_fderiv_add_of_disjoint (h₁ : IsOpen D₁) (_h₂ : IsOpen D₂)
    {g h : ℂ → ℝ} (hg : g ∈ zeroSpace D₁) (hh : h ∈ zeroSpace D₂)
    (hh0 : ∀ z ∈ D₁, h z = 0) (_hg0 : ∀ z ∈ D₂, g z = 0) :
    ∀ z, ‖fderiv ℝ (g + h) z‖ ^ 2 = ‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ h z‖ ^ 2 := by
  have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := hg.1
  have hhs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h := hh.1
  have hgd : Differentiable ℝ g := hgs.differentiable smooth_ne_zero
  have hhd : Differentiable ℝ h := hhs.differentiable smooth_ne_zero
  intro z
  rw [fderiv_add (hgd z) (hhd z)]
  by_cases hz1 : z ∈ D₁
  · exact norm_add_sq_of_eq_zero_right (fderiv_eq_zero_of_eventuallyEq_zero (hhd z)
      (Filter.Eventually.mono (h₁.mem_nhds hz1) fun y hy => hh0 y hy))
  · exact norm_add_sq_of_eq_zero_left (fderiv_eq_zero_of_eventuallyEq_zero (hgd z)
      (Filter.Eventually.mono
        (((isClosed_tsupport g).isOpen_compl).mem_nhds fun hc => hz1 (hg.2.2 hc))
        fun y hy => image_eq_zero_of_notMem_tsupport hy))

set_option maxHeartbeats 800000 in
-- Additivity of the Dirichlet energy for `g + h` with `g` supported in `D₁`, `h` supported in
-- `D₂` and each vanishing on the other piece: the gradients never interact on `D₁ ∪ D₂`. The
-- integrability of the two squared gradients on the union comes from `IsDNSpace.energy`, and the
-- set integrals over the pieces collapse to whole-space integrals because each squared gradient
-- vanishes away from its own piece.
private lemma dirichletEnergyOn_add_of_disjoint (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    {g h : ℂ → ℝ} (hg : g ∈ zeroSpace D₁) (hh : h ∈ zeroSpace D₂)
    (hh0 : ∀ z ∈ D₁, h z = 0) (hg0 : ∀ z ∈ D₂, g z = 0) :
    dirichletEnergyOn (D₁ ∪ D₂) (g + h) =
      dirichletEnergyOn D₁ g + dirichletEnergyOn D₂ h := by
  have hpoint := normSq_fderiv_add_of_disjoint h₁ h₂ hg hh hh0 hg0
  have hgU : g ∈ zeroSpace (D₁ ∪ D₂) := ⟨hg.1, hg.2.1, hg.2.2.trans subset_union_left⟩
  have hhU : h ∈ zeroSpace (D₁ ∪ D₂) := ⟨hh.1, hh.2.1, hh.2.2.trans subset_union_right⟩
  -- the gradients vanish away from their own piece
  have hgv : ∀ z ∉ D₁, fderiv ℝ g z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hg.2.2 (support_fderiv_subset (𝕜 := ℝ) (f := g) hne))
  have hhv : ∀ z ∉ D₂, fderiv ℝ h z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hh.2.2 (support_fderiv_subset (𝕜 := ℝ) (f := h) hne))
  -- the set integrals over the union collapse to the ones over the pieces
  have hIg : ∫ z in D₁ ∪ D₂, ‖fderiv ℝ g z‖ ^ 2 = ∫ z in D₁, ‖fderiv ℝ g z‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
        (f := fun z => ‖fderiv ℝ g z‖ ^ 2) (s := D₁ ∪ D₂) fun z hz => by
      rw [hgv z fun hz1 => hz (Or.inl hz1), norm_zero,
        zero_pow (show (2 : ℕ) ≠ 0 by norm_num)],
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
        (f := fun z => ‖fderiv ℝ g z‖ ^ 2) (s := D₁) fun z hz => by
      rw [hgv z hz, norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num)]]
  have hIh : ∫ z in D₁ ∪ D₂, ‖fderiv ℝ h z‖ ^ 2 = ∫ z in D₂, ‖fderiv ℝ h z‖ ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
        (f := fun z => ‖fderiv ℝ h z‖ ^ 2) (s := D₁ ∪ D₂) fun z hz => by
      rw [hhv z fun hz1 => hz (Or.inr hz1), norm_zero,
        zero_pow (show (2 : ℕ) ≠ 0 by norm_num)],
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume)
        (f := fun z => ‖fderiv ℝ h z‖ ^ 2) (s := D₂) fun z hz => by
      rw [hhv z hz, norm_zero, zero_pow (show (2 : ℕ) ≠ 0 by norm_num)]]
  -- the integral of the sum over the union splits
  have hIU : ∫ z in D₁ ∪ D₂, ‖fderiv ℝ (g + h) z‖ ^ 2 =
      (∫ z in D₁ ∪ D₂, ‖fderiv ℝ g z‖ ^ 2) +
        (∫ z in D₁ ∪ D₂, ‖fderiv ℝ h z‖ ^ 2) := by
    rw [show (fun z => ‖fderiv ℝ (g + h) z‖ ^ 2) =
      (fun z => ‖fderiv ℝ g z‖ ^ 2 + ‖fderiv ℝ h z‖ ^ 2) from funext hpoint]
    exact integral_add ((isDNSpace_zeroSpace (D₁ ∪ D₂)).energy g hgU)
      ((isDNSpace_zeroSpace (D₁ ∪ D₂)).energy h hhU)
  unfold dirichletEnergyOn
  rw [hIU, hIg, hIh, mul_add]

/-- Additivity of the Dirichlet energy over two disjoint open pieces: for `f = g + h` with `g`
supported in `D₁`, `h` supported in `D₂` and each vanishing on the other piece, the gradients
never interact on `D₁ ∪ D₂`. -/
private lemma dirichletEnergyOn_union_of_disjoint (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    {f g h : ℂ → ℝ} (_hf : f ∈ zeroSpace (D₁ ∪ D₂)) (hg : g ∈ zeroSpace D₁)
    (hh : h ∈ zeroSpace D₂) (hadd : ∀ z, f z = g z + h z)
    (hh0 : ∀ z ∈ D₁, h z = 0) (hg0 : ∀ z ∈ D₂, g z = 0) :
    dirichletEnergyOn (D₁ ∪ D₂) f = dirichletEnergyOn D₁ g + dirichletEnergyOn D₂ h := by
  rw [funext hadd]
  exact dirichletEnergyOn_add_of_disjoint h₁ h₂ hg hh hh0 hg0

/-- Energy of a constant multiple. -/
private lemma dirichletEnergyOn_const_mul (D : Set ℂ) (c : ℝ) {f : ℂ → ℝ}
    (hf : Differentiable ℝ f) :
    dirichletEnergyOn D (fun z => c * f z) = c ^ 2 * dirichletEnergyOn D f := by
  have hpoint : ∀ z, ‖fderiv ℝ (fun y => c * f y) z‖ ^ 2 = c ^ 2 * ‖fderiv ℝ f z‖ ^ 2 := by
    intro z
    rw [show fderiv ℝ (fun y => c * f y) z = c • fderiv ℝ f z from
      fderiv_const_smul (hf z) c]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [dirichletEnergyOn, dirichletEnergyOn,
    integral_congr_ae (f := fun z => ‖fderiv ℝ (fun y => c * f y) z‖ ^ 2)
      (g := fun z => c ^ 2 * ‖fderiv ℝ f z‖ ^ 2) (Eventually.of_forall hpoint),
    integral_const_mul]
  ring

/-! ### The two inequalities for the binary union -/

/-- Reverse inequality, "optimal scaling" step: for test functions on the two pieces the sum of
the two sup-values is bounded by the dual norm of the union. If both pairings are nonzero one
uses `w = (a₁/e₁) f₁ + (a₂/e₂) f₂`, whose energy on the union is
`(a₁/e₁)² e₁ + (a₂/e₂)² e₂ = a₁²/e₁ + a₂²/e₂`, because the pieces have disjoint support. -/
private lemma ofReal_add_div_le_dualNormSq_union (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    (hd : Disjoint D₁ D₂) {f₁ f₂ : ℂ → ℝ} (hf₁ : f₁ ∈ zeroSpace D₁) (hf₂ : f₂ ∈ zeroSpace D₂)
    (he₁ : 0 < dirichletEnergyOn D₁ f₁) (he₂ : 0 < dirichletEnergyOn D₂ f₂) (μ : Measure ℂ) :
    ENNReal.ofReal ((∫ x, f₁ x ∂μ) ^ 2 / dirichletEnergyOn D₁ f₁) +
      ENNReal.ofReal ((∫ x, f₂ x ∂μ) ^ 2 / dirichletEnergyOn D₂ f₂) ≤
      dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ := by
  have hf₁U : f₁ ∈ zeroSpace (D₁ ∪ D₂) := ⟨hf₁.1, hf₁.2.1, hf₁.2.2.trans subset_union_left⟩
  have hf₂U : f₂ ∈ zeroSpace (D₁ ∪ D₂) := ⟨hf₂.1, hf₂.2.1, hf₂.2.2.trans subset_union_right⟩
  have henergy₁ : dirichletEnergyOn (D₁ ∪ D₂) f₁ = dirichletEnergyOn D₁ f₁ :=
    (energy_eq_of_tsupport_subset hf₁U.2.2).trans (energy_eq_of_tsupport_subset hf₁.2.2).symm
  have henergy₂ : dirichletEnergyOn (D₁ ∪ D₂) f₂ = dirichletEnergyOn D₂ f₂ :=
    (energy_eq_of_tsupport_subset hf₂U.2.2).trans (energy_eq_of_tsupport_subset hf₂.2.2).symm
  have hb₁ := le_dualNormSq (D := D₁ ∪ D₂) (V := zeroSpace (D₁ ∪ D₂)) (μ := μ) hf₁U
    (by rw [henergy₁]; exact he₁)
  rw [henergy₁] at hb₁
  have hb₂ := le_dualNormSq (D := D₁ ∪ D₂) (V := zeroSpace (D₁ ∪ D₂)) (μ := μ) hf₂U
    (by rw [henergy₂]; exact he₂)
  rw [henergy₂] at hb₂
  by_cases hi₁ : Integrable f₁ μ
  · by_cases hi₂ : Integrable f₂ μ
    · rcases eq_or_ne (∫ x, f₁ x ∂μ) 0 with ha₁ | ha₁
      · refine le_trans ?_ hb₂
        rw [ha₁]
        norm_num
      · rcases eq_or_ne (∫ x, f₂ x ∂μ) 0 with ha₂ | ha₂
        · refine le_trans ?_ hb₁
          rw [ha₂]
          norm_num
        · have hf₁diff : Differentiable ℝ f₁ := hf₁.1.differentiable smooth_ne_zero
          have hf₂diff : Differentiable ℝ f₂ := hf₂.1.differentiable smooth_ne_zero
          set a₁ : ℝ := ∫ x, f₁ x ∂μ with ha₁def
          set a₂ : ℝ := ∫ x, f₂ x ∂μ with ha₂def
          set e₁ : ℝ := dirichletEnergyOn D₁ f₁ with he₁def
          set e₂ : ℝ := dirichletEnergyOn D₂ f₂ with he₂def
          have he₁pos : 0 < e₁ := by rw [he₁def]; exact he₁
          have he₂pos : 0 < e₂ := by rw [he₂def]; exact he₂
          have huV : (fun z => (a₁ / e₁) * f₁ z) ∈ zeroSpace D₁ :=
            ⟨contDiff_const.mul hf₁.1, hf₁.2.1.mul_left (f := fun _ => a₁ / e₁),
              (tsupport_mul_subset_right (f := fun _ => a₁ / e₁) (g := f₁)).trans hf₁.2.2⟩
          have hvV : (fun z => (a₂ / e₂) * f₂ z) ∈ zeroSpace D₂ :=
            ⟨contDiff_const.mul hf₂.1, hf₂.2.1.mul_left (f := fun _ => a₂ / e₂),
              (tsupport_mul_subset_right (f := fun _ => a₂ / e₂) (g := f₂)).trans hf₂.2.2⟩
          set w : ℂ → ℝ := fun z => (a₁ / e₁) * f₁ z + (a₂ / e₂) * f₂ z with hwdef
          have hwfun : w = fun z => (a₁ / e₁) * f₁ z + (a₂ / e₂) * f₂ z := by rw [hwdef]
          have hwU : w ∈ zeroSpace (D₁ ∪ D₂) :=
            ⟨huV.1.add hvV.1, huV.2.1.add hvV.2.1,
              (tsupport_add (f := fun z => (a₁ / e₁) * f₁ z)
                (g := fun z => (a₂ / e₂) * f₂ z)).trans
                (union_subset (huV.2.2.trans subset_union_left)
                  (hvV.2.2.trans subset_union_right))⟩
          have hv0 : ∀ z ∈ D₁, (fun z => (a₂ / e₂) * f₂ z) z = 0 := by
            intro z hz
            have hz0 : f₂ z = 0 :=
              image_eq_zero_of_notMem_tsupport fun hc => disjoint_left.mp hd hz (hf₂.2.2 hc)
            show (a₂ / e₂) * f₂ z = 0
            rw [hz0, mul_zero]
          have hu0 : ∀ z ∈ D₂, (fun z => (a₁ / e₁) * f₁ z) z = 0 := by
            intro z hz
            have hz0 : f₁ z = 0 :=
              image_eq_zero_of_notMem_tsupport fun hc => disjoint_left.mp hd (hf₁.2.2 hc) hz
            show (a₁ / e₁) * f₁ z = 0
            rw [hz0, mul_zero]
          have hwE : dirichletEnergyOn (D₁ ∪ D₂) w =
              (a₁ / e₁) ^ 2 * e₁ + (a₂ / e₂) ^ 2 * e₂ := by
            have h := dirichletEnergyOn_add_of_disjoint h₁ h₂ huV hvV hv0 hu0
            show dirichletEnergyOn (D₁ ∪ D₂) ((fun z => (a₁ / e₁) * f₁ z) +
                (fun z => (a₂ / e₂) * f₂ z)) =
              (a₁ / e₁) ^ 2 * e₁ + (a₂ / e₂) ^ 2 * e₂
            rw [h, dirichletEnergyOn_const_mul D₁ (a₁ / e₁) hf₁diff,
              dirichletEnergyOn_const_mul D₂ (a₂ / e₂) hf₂diff, ← he₁def, ← he₂def]
          have hwEpos : 0 < dirichletEnergyOn (D₁ ∪ D₂) w := by
            rw [hwE]
            have h₁' : 0 < (a₁ / e₁) ^ 2 * e₁ :=
              mul_pos (sq_pos_of_ne_zero (div_ne_zero ha₁ he₁pos.ne')) he₁pos
            have h₂' : 0 < (a₂ / e₂) ^ 2 * e₂ :=
              mul_pos (sq_pos_of_ne_zero (div_ne_zero ha₂ he₂pos.ne')) he₂pos
            linarith
          have hwint : ∫ z, w z ∂μ = a₁ / e₁ * a₁ + a₂ / e₂ * a₂ := by
            have hu : Integrable (fun z => (a₁ / e₁) * f₁ z) μ := hi₁.const_mul (a₁ / e₁)
            have hv : Integrable (fun z => (a₂ / e₂) * f₂ z) μ := hi₂.const_mul (a₂ / e₂)
            rw [hwfun, integral_add hu hv, integral_const_mul, integral_const_mul,
              ha₁def.symm, ha₂def.symm]
          have hval : (∫ z, w z ∂μ) ^ 2 / dirichletEnergyOn (D₁ ∪ D₂) w =
              a₁ ^ 2 / e₁ + a₂ ^ 2 / e₂ := by
            rw [hwint, hwE]
            have h1 : e₁ ≠ 0 := he₁pos.ne'
            have h2 : e₂ ≠ 0 := he₂pos.ne'
            field_simp
            try ring
          have hmain := le_dualNormSq (D := D₁ ∪ D₂) (V := zeroSpace (D₁ ∪ D₂)) (μ := μ) hwU
            hwEpos
          rw [hval] at hmain
          rw [← ENNReal.ofReal_add (div_nonneg (sq_nonneg _) he₁pos.le)
            (div_nonneg (sq_nonneg _) he₂pos.le)]
          exact hmain
    · refine le_trans ?_ hb₁
      rw [integral_undef hi₂]
      norm_num
  · refine le_trans ?_ hb₂
    rw [integral_undef hi₁]
    norm_num

/-- The sum of the two dual norms is at most the dual norm of the union: the sup over pairs of
test functions is bounded pointwise by `ofReal_add_div_le_dualNormSq_union`, the empty cases
being handled by the monotonicity of the dual norm. -/
private lemma add_dualNormSq_le_dualNormSq_union (h₁ : IsOpen D₁) (h₂ : IsOpen D₂)
    (hd : Disjoint D₁ D₂) (μ : Measure ℂ) :
    dualNormSq D₁ (zeroSpace D₁) μ + dualNormSq D₂ (zeroSpace D₂) μ ≤
      dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ := by
  have hzero : ∀ {D : Set ℂ}, ¬ ({f : ℂ → ℝ | f ∈ zeroSpace D ∧
      0 < dirichletEnergyOn D f}).Nonempty → dualNormSq D (zeroSpace D) μ = 0 := by
    intro D hD
    have hDe : ({f : ℂ → ℝ | f ∈ zeroSpace D ∧ 0 < dirichletEnergyOn D f}) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hD
    rw [dualNormSq]
    refine le_antisymm ?_ zero_le
    refine iSup_le fun f => iSup_le fun hf => ?_
    rw [hDe] at hf
    exact absurd hf (by simp)
  by_cases hs : ({f : ℂ → ℝ | f ∈ zeroSpace D₁ ∧ 0 < dirichletEnergyOn D₁ f}).Nonempty
  · by_cases ht : ({f : ℂ → ℝ | f ∈ zeroSpace D₂ ∧ 0 < dirichletEnergyOn D₂ f}).Nonempty
    · refine ENNReal.biSup_add_biSup_le hs ht ?_
      intro f₁ hf₁ f₂ hf₂
      exact ofReal_add_div_le_dualNormSq_union h₁ h₂ hd hf₁.1 hf₂.1 hf₁.2 hf₂.2 μ
    · rw [hzero ht, add_zero]
      exact dualNormSq_zeroSpace_mono h₁ subset_union_left
  · rw [hzero hs, zero_add]
    exact dualNormSq_zeroSpace_mono h₂ subset_union_right

/-- **The squared dual norm splits over a disjoint union of two open sets** (Sheffield §2). -/
theorem dualNormSq_union_of_disjoint (h₁ : IsOpen D₁) (h₂ : IsOpen D₂) (hd : Disjoint D₁ D₂)
    (μ) :
    dualNormSq (D₁ ∪ D₂) (zeroSpace (D₁ ∪ D₂)) μ =
      dualNormSq D₁ (zeroSpace D₁) μ + dualNormSq D₂ (zeroSpace D₂) μ := by
  refine le_antisymm ?_ (add_dualNormSq_le_dualNormSq_union h₁ h₂ hd μ)
  unfold dualNormSq
  refine iSup_le fun f => iSup_le fun hf => ?_
  obtain ⟨hfV, hfE⟩ := hf
  by_cases hint : Integrable f μ
  · obtain ⟨g, hgV, h, hhV, hintg, hinth, hadd, hh0, hg0⟩ :=
      exists_decomposition_of_mem_zeroSpace_union h₁ h₂ hd hfV hint
    have hE := dirichletEnergyOn_union_of_disjoint h₁ h₂ hfV hgV hhV hadd hh0 hg0
    have hfint : ∫ x, f x ∂μ = ∫ x, g x ∂μ + ∫ x, h x ∂μ := by
      rw [integral_congr_ae (Eventually.of_forall hadd), integral_add hintg hinth]
    rcases eq_or_lt_of_le (energy_nonneg D₁ g) with hE₁ | hE₁
    · have hgz : ∫ x, g x ∂μ = 0 := by
        have hzero : (fun x => g x) = fun _ => (0 : ℝ) :=
          funext (eq_zero_of_dirichletEnergyOn_eq_zero h₁ hgV hE₁.symm)
        rw [hzero]
        simp
      rcases eq_or_lt_of_le (energy_nonneg D₂ h) with hE₂ | hE₂
      · exfalso
        have hfE0 : dirichletEnergyOn (D₁ ∪ D₂) f = 0 := by
          rw [hE, hE₁.symm, hE₂.symm]
          simp
        rw [hfE0] at hfE
        exact lt_irrefl 0 hfE
      · calc ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn (D₁ ∪ D₂) f)
            = ENNReal.ofReal ((∫ x, h x ∂μ) ^ 2 / dirichletEnergyOn D₂ h) := by
              rw [hfint, hgz, hE, hE₁.symm, zero_add, zero_add]
          _ ≤ dualNormSq D₂ (zeroSpace D₂) μ := le_dualNormSq hhV hE₂
          _ ≤ dualNormSq D₁ (zeroSpace D₁) μ + dualNormSq D₂ (zeroSpace D₂) μ :=
              (calc dualNormSq D₂ (zeroSpace D₂) μ = 0 + dualNormSq D₂ (zeroSpace D₂) μ :=
                    (zero_add _).symm
                _ ≤ _ := add_le_add zero_le le_rfl)
    · rcases eq_or_lt_of_le (energy_nonneg D₂ h) with hE₂ | hE₂
      · have hhz : ∫ x, h x ∂μ = 0 := by
          have hzero : (fun x => h x) = fun _ => (0 : ℝ) :=
            funext (eq_zero_of_dirichletEnergyOn_eq_zero h₂ hhV hE₂.symm)
          rw [hzero]
          simp
        calc ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn (D₁ ∪ D₂) f)
            = ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn D₁ g) := by
              rw [hfint, hhz, add_zero, hE, hE₂.symm, add_zero]
          _ ≤ dualNormSq D₁ (zeroSpace D₁) μ := le_dualNormSq hgV hE₁
          _ ≤ dualNormSq D₁ (zeroSpace D₁) μ + dualNormSq D₂ (zeroSpace D₂) μ :=
              (calc dualNormSq D₁ (zeroSpace D₁) μ = dualNormSq D₁ (zeroSpace D₁) μ + 0 :=
                    (add_zero _).symm
                _ ≤ _ := add_le_add le_rfl zero_le)
      · calc ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn (D₁ ∪ D₂) f)
            ≤ ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn D₁ g +
                (∫ x, h x ∂μ) ^ 2 / dirichletEnergyOn D₂ h) := by
              rw [hfint, hE]
              exact ENNReal.ofReal_le_ofReal (sq_add_sq_div_le _ _ _ _ hE₁ hE₂)
          _ = ENNReal.ofReal ((∫ x, g x ∂μ) ^ 2 / dirichletEnergyOn D₁ g) +
                ENNReal.ofReal ((∫ x, h x ∂μ) ^ 2 / dirichletEnergyOn D₂ h) :=
              ENNReal.ofReal_add (div_nonneg (sq_nonneg _) (energy_nonneg D₁ g))
                (div_nonneg (sq_nonneg _) (energy_nonneg D₂ h))
          _ ≤ dualNormSq D₁ (zeroSpace D₁) μ + dualNormSq D₂ (zeroSpace D₂) μ :=
              add_le_add (le_dualNormSq hgV hE₁) (le_dualNormSq hhV hE₂)
  · rw [integral_undef hint]
    simp

/-! ### Countable disjoint unions -/

/-- The Dirichlet energy of the empty domain vanishes. -/
private lemma dirichletEnergyOn_empty (f : ℂ → ℝ) : dirichletEnergyOn ∅ f = 0 := by
  unfold dirichletEnergyOn
  rw [Measure.restrict_empty, integral_zero_measure, mul_zero]

/-- The dual norm of the empty domain vanishes. -/
private lemma dualNormSq_empty (μ : Measure ℂ) : dualNormSq ∅ (zeroSpace ∅) μ = 0 := by
  refine le_antisymm ?_ zero_le
  refine iSup₂_le fun f _ => by simp [dirichletEnergyOn_empty f]

/-- The squared dual norm splits over a finite disjoint union of open sets: induction on the
binary case. -/
private lemma dualNormSq_finset_biUnion_of_pairwise_disjoint (D : ℕ → Set ℂ)
    (hD : ∀ n, IsOpen (D n)) (hd : Pairwise (Disjoint on D)) (s : Finset ℕ) (μ : Measure ℂ) :
    dualNormSq (⋃ n ∈ s, D n) (zeroSpace (⋃ n ∈ s, D n)) μ =
      ∑ n ∈ s, dualNormSq (D n) (zeroSpace (D n)) μ := by
  induction s using Finset.induction_on with
  | empty =>
    rw [show (⋃ n ∈ (∅ : Finset ℕ), D n) = ∅ from by simp, Finset.sum_empty,
      dualNormSq_empty μ]
  | insert a s ha ih =>
    have hU : IsOpen (⋃ n ∈ s, D n) := isOpen_biUnion fun n _ => hD n
    have hdisj : Disjoint (D a) (⋃ n ∈ s, D n) := by
      rw [Set.disjoint_left]
      intro z hza hzs
      obtain ⟨n, hn, hzn⟩ := Set.mem_iUnion₂.mp hzs
      have hane : a ≠ n := by rintro rfl; exact ha hn
      exact (Set.disjoint_left.mp (hd hane) hza) hzn
    rw [show (⋃ n ∈ (insert a s : Finset ℕ), D n) = D a ∪ ⋃ n ∈ s, D n from by
        ext z
        simp only [Set.mem_iUnion₂, Finset.mem_insert, Set.mem_union]
        constructor
        · rintro ⟨n, (rfl | hn), hz⟩
          · exact Or.inl hz
          · exact Or.inr ⟨n, hn, hz⟩
        · rintro (hz | ⟨n, hn, hz⟩)
          · exact ⟨a, Or.inl rfl, hz⟩
          · exact ⟨n, Or.inr hn, hz⟩,
      Finset.sum_insert ha]
    rw [dualNormSq_union_of_disjoint (hD a) hU hdisj μ, ih]

/-- **The squared dual norm splits over a countable disjoint union of open sets** (Sheffield §2):
the sup defining the left-hand side sees only test functions with compact support, each of which
meets finitely many pieces, so it is the sup of the dual norms of the finite sub-unions. -/
theorem dualNormSq_iUnion_of_pairwise_disjoint (D : ℕ → Set ℂ) (hD : ∀ n, IsOpen (D n))
    (hd : Pairwise (Disjoint on D)) (μ) :
    dualNormSq (⋃ n, D n) (zeroSpace (⋃ n, D n)) μ =
      ∑' n, dualNormSq (D n) (zeroSpace (D n)) μ := by
  have hstep : dualNormSq (⋃ n, D n) (zeroSpace (⋃ n, D n)) μ =
      ⨆ s : Finset ℕ, dualNormSq (⋃ n ∈ s, D n) (zeroSpace (⋃ n ∈ s, D n)) μ := by
    refine le_antisymm ?_ (iSup_le fun s =>
      dualNormSq_zeroSpace_mono (isOpen_biUnion fun n _ => hD n)
        (iUnion₂_subset fun n _ => le_iSup D n))
    refine iSup₂_le fun f hf => ?_
    obtain ⟨hfV, hfE⟩ := hf
    obtain ⟨s, hs⟩ := (show IsCompact (tsupport f) from hfV.2.1).elim_finite_subcover D hD hfV.2.2
    have hen : dirichletEnergyOn (⋃ n ∈ s, D n) f = dirichletEnergyOn (⋃ n, D n) f :=
      (energy_eq_of_tsupport_subset hs).trans (energy_eq_of_tsupport_subset hfV.2.2).symm
    have hpos : 0 < dirichletEnergyOn (⋃ n ∈ s, D n) f := by rw [hen]; exact hfE
    calc ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn (⋃ n, D n) f)
        = ENNReal.ofReal ((∫ x, f x ∂μ) ^ 2 / dirichletEnergyOn (⋃ n ∈ s, D n) f) := by
          rw [hen]
      _ ≤ dualNormSq (⋃ n ∈ s, D n) (zeroSpace (⋃ n ∈ s, D n)) μ :=
          le_dualNormSq ⟨hfV.1, hfV.2.1, hs⟩ hpos
      _ ≤ ⨆ s : Finset ℕ, dualNormSq (⋃ n ∈ s, D n) (zeroSpace (⋃ n ∈ s, D n)) μ :=
          le_iSup (f := fun s : Finset ℕ =>
            dualNormSq (⋃ n ∈ s, D n) (zeroSpace (⋃ n ∈ s, D n)) μ) s
  rw [hstep, ENNReal.tsum_eq_iSup_sum]
  exact iSup_congr fun s => dualNormSq_finset_biUnion_of_pairwise_disjoint D hD hd s μ

/-! ### The polarized versions -/

end QuantumZipper.K3
