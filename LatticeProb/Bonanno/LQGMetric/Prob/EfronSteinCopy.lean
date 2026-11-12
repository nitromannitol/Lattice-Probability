/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.EfronSteinCopy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.EfronSteinResample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Efron–Stein inequality with independent copies

`X_i : Ω → E i` (`i : ι`, `ι` finite) and copies `X'_i`, all `2|ι|` variables independent, with
`X'_i` distributed as `X_i`. For measurable `f` with `F = f(X) ∈ L²` and
`F^{(i)} = f(X_1, …, X'_i, …, X_n)`:

* `efronStein_copy_half`: `Var F ≤ ½ ∑_i E[(F^{(i)} - F)²]` (LM (5.3), arXiv:1905.00379
  `local-metrics-final.tex` lines 1017–1020);
* `efronStein_copy_posPart`: `Var F ≤ ∑_i E[(F^{(i)} - F)_+²]` (DDDF (5.58), arXiv:1904.08021
  `tightness.tex` lines 1081–1090; LM (5.4));
* `efronStein_copy_term`: the per-coordinate identities
  `E[(F - E[F | X_j, j ≠ i])²] = ½ E[(F^{(i)} - F)²] = E[(F^{(i)} - F)_+²]`.

Sources: Boucheron–Lugosi–Massart, *Concentration Inequalities*, Thm 3.1; R. van Handel,
*Probability in High Dimension* (2016), §2.1 (theorem numbers not checked). The proof combines
`efronStein_sigma` with `es_resample_identity`; the law facts come from the swap
`(X, X'_i) ↦ (X with X'_i in slot i, X_i)`, which preserves the joint law (both sides have law
`(⊗_j law X_j) ⊗ law X_i`, by independence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ENNReal

namespace LQGMetric

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
  {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*} [mE : ∀ i, MeasurableSpace (E i)]

/-- The `2|ι|` σ-algebras `σ(X_i)` (left copy of `ι`) and `σ(X'_i)` (right copy). -/
abbrev esCopySigma (X X' : ∀ i, Ω → E i) : ι ⊕ ι → MeasurableSpace Ω :=
  Sum.elim (fun i => (mE i).comap (X i)) (fun i => (mE i).comap (X' i))

/-- The reindexing `j ↦ inl j` for `j ≠ i`, `i ↦ inr i` (the family with `X'_i` in slot `i`). -/
def esSwapIdx (i : ι) (j : ι) : ι ⊕ ι := if j = i then Sum.inr i else Sum.inl j

omit [Fintype ι] in
lemma esSwapIdx_injective (i : ι) : Function.Injective (esSwapIdx i) := by
  intro j k h
  unfold esSwapIdx at h
  by_cases hj : j = i <;> by_cases hk : k = i <;> simp_all

variable (X X' : ∀ i, Ω → E i)

omit [Fintype ι] in
lemma es_comap_update (i j : ι) :
    (mE j).comap (Function.update X i (X' i) j) = esCopySigma X X' (esSwapIdx i j) := by
  by_cases h : j = i
  · subst h; simp [esSwapIdx, esCopySigma]
  · simp [esSwapIdx, esCopySigma, h]

omit [Fintype ι] mE in
lemma es_update_vec (i : ι) :
    (fun ω j => Function.update X i (X' i) j ω) =
      fun ω => Function.update (fun j => X j ω) i (X' i ω) := by
  funext ω j
  by_cases h : j = i
  · subst h; simp
  · simp [Function.update_of_ne h]

variable {X X'}

omit [DecidableEq ι] in
/-- Law of `(vector, extra coordinate)` for an independent family plus one more variable. -/
lemma es_map_pair_eq [IsProbabilityMeasure μ] {Y : ∀ j, Ω → E j} {k : ι} {V : Ω → E k}
    (hY : ∀ j, Measurable (Y j)) (hV : Measurable V)
    (hYi : iIndep (fun j => (mE j).comap (Y j)) μ)
    (hYV : Indep (⨆ j, (mE j).comap (Y j)) ((mE k).comap V) μ) :
    μ.map (fun ω => ((fun j => Y j ω), V ω)) =
      (Measure.pi fun j => μ.map (Y j)).prod (μ.map V) := by
  have hvec : Measurable fun ω j => Y j ω := measurable_pi_iff.2 hY
  have h1 : IndepFun (fun ω j => Y j ω) V μ := by
    rw [IndepFun_iff_Indep, comap_process_pi]; exact hYV
  rw [(indepFun_iff_map_prod_eq_prod_map_map hvec.aemeasurable hV.aemeasurable).1 h1,
    (iIndepFun_iff_map_fun_eq_pi_map fun j => (hY j).aemeasurable).1
      ((iIndepFun_iff_iIndep _ _ _).2 hYi)]

variable (hX : ∀ i, Measurable (X i)) (hX' : ∀ i, Measurable (X' i))
  (hind : iIndep (esCopySigma X X') μ) (hlaw : ∀ i, μ.map (X' i) = μ.map (X i))
include hX hX' hind hlaw

omit [Fintype ι] [DecidableEq ι] hind hlaw in
lemma es_le_sigma (k : ι ⊕ ι) : esCopySigma X X' k ≤ m₀ := by
  rcases k with k | k
  · exact (hX k).comap_le
  · exact (hX' k).comap_le

/-- **Swap invariance**: `(X, X'_i)` and `(X with X'_i in slot i, X_i)` have the same law. -/
lemma es_map_swap_eq [IsProbabilityMeasure μ] (i : ι) :
    μ.map (fun ω => ((fun j => X j ω), X' i ω)) =
      μ.map (fun ω => (Function.update (fun j => X j ω) i (X' i ω), X i ω)) := by
  have hle := es_le_sigma hX hX'
  -- left side
  have hL := es_map_pair_eq (μ := μ) (Y := X) (V := X' i) hX (hX' i)
    (hind.precomp Sum.inl_injective) (by
      have h := indep_iSup_of_disjoint hle hind (S := Set.range Sum.inl) (T := {Sum.inr i})
        (by simp [Set.disjoint_left])
      simp only [iSup_range, Set.mem_singleton_iff, iSup_iSup_eq_left] at h
      exact h)
  -- right side
  have hY : ∀ j, Measurable (Function.update X i (X' i) j) := by
    intro j; by_cases h : j = i
    · subst h; simpa using hX' j
    · simpa [Function.update_of_ne h] using hX j
  have hfam : (fun j => (mE j).comap (Function.update X i (X' i) j)) =
      esCopySigma X X' ∘ esSwapIdx i := funext (es_comap_update X X' i)
  have hsup : (⨆ j, (mE j).comap (Function.update X i (X' i) j)) =
      ⨆ j, esCopySigma X X' (esSwapIdx i j) := by simp only [es_comap_update]
  have hR := es_map_pair_eq (μ := μ) (Y := Function.update X i (X' i)) (V := X i) hY (hX i)
    (by rw [hfam]; exact hind.precomp (esSwapIdx_injective i)) (by
      have h := indep_iSup_of_disjoint hle hind (S := Set.range (esSwapIdx i))
        (T := {Sum.inl i}) (by
          rw [Set.disjoint_singleton_right]
          rintro ⟨j, hj⟩
          unfold esSwapIdx at hj
          by_cases h : j = i <;> simp_all)
      simp only [iSup_range, Set.mem_singleton_iff, iSup_iSup_eq_left] at h
      rw [hsup]; exact h)
  have hv : ∀ ω, (fun j => Function.update X i (X' i) j ω) =
      Function.update (fun j => X j ω) i (X' i ω) := fun ω => congrFun (es_update_vec X X' i) ω
  simp only [hv] at hR
  rw [hL, hR, hlaw i]
  congr 2
  funext j
  by_cases h : j = i
  · subst h; simp [hlaw]
  · simp [Function.update_of_ne h]

lemma es_integral_swap [IsProbabilityMeasure μ] (i : ι) {φ : (∀ j, E j) × E i → ℝ}
    (hφ : Measurable φ) :
    ∫ ω, φ (Function.update (fun j => X j ω) i (X' i ω), X i ω) ∂μ =
      ∫ ω, φ ((fun j => X j ω), X' i ω) ∂μ := by
  have hW : Measurable (fun ω => ((fun j => X j ω), X' i ω)) :=
    (measurable_pi_iff.2 hX).prodMk (hX' i)
  have hW' : Measurable (fun ω => (Function.update (fun j => X j ω) i (X' i ω), X i ω)) :=
    (measurable_update'.comp hW).prodMk (hX i)
  calc ∫ ω, φ (Function.update (fun j => X j ω) i (X' i ω), X i ω) ∂μ
      = ∫ p, φ p ∂(μ.map fun ω => (Function.update (fun j => X j ω) i (X' i ω), X i ω)) :=
        (integral_map hW'.aemeasurable hφ.aestronglyMeasurable).symm
    _ = ∫ p, φ p ∂(μ.map fun ω => ((fun j => X j ω), X' i ω)) := by
        rw [es_map_swap_eq hX hX' hind hlaw i]
    _ = ∫ ω, φ ((fun j => X j ω), X' i ω) ∂μ :=
        integral_map hW.aemeasurable hφ.aestronglyMeasurable

omit [Fintype ι] [DecidableEq ι] hX hX' hind hlaw in
lemma es_measurable_vec {m : MeasurableSpace Ω} {Y : ∀ j, Ω → E j}
    (h : ∀ j, (mE j).comap (Y j) ≤ m) : Measurable[m] (fun ω j => Y j ω) :=
  measurable_iff_comap_le.2 (by rw [comap_process_pi]; exact iSup_le h)

/-- **Per-coordinate Efron–Stein identities**: with `F = f(X)`, `F^{(i)}` the value with `X'_i`
in slot `i`, `E[(F - E[F | σ(X_j, j ≠ i)])²] = ½ E[(F^{(i)} - F)²]`, and
`½ E[(F^{(i)} - F)²] = E[(F^{(i)} - F)_+²]`. -/
theorem efronStein_copy_term [IsProbabilityMeasure μ] {f : (∀ j, E j) → ℝ} (hf : Measurable f)
    (hF : MemLp (fun ω => f (fun j => X j ω)) 2 μ) (i : ι) :
    ∫ ω, (f (fun j => X j ω) - μ[fun ω => f (fun j => X j ω) |
        ⨆ j ∈ Finset.univ.erase i, (mE j).comap (X j)] ω) ^ 2 ∂μ =
      (1 / 2) * ∫ ω, (f (Function.update (fun j => X j ω) i (X' i ω)) - f (fun j => X j ω)) ^ 2 ∂μ
    ∧ (1 / 2) * ∫ ω, (f (Function.update (fun j => X j ω) i (X' i ω)) - f (fun j => X j ω)) ^ 2 ∂μ
      = ∫ ω, max (f (Function.update (fun j => X j ω) i (X' i ω)) - f (fun j => X j ω)) 0 ^ 2 ∂μ
    := by
  have hle := es_le_sigma hX hX'
  -- law facts (stated before any local σ-algebra enters the context)
  have hW : Measurable (fun ω => ((fun j => X j ω), X' i ω)) :=
    (measurable_pi_iff.2 hX).prodMk (hX' i)
  have hW' : Measurable (fun ω => (Function.update (fun j => X j ω) i (X' i ω), X i ω)) :=
    (measurable_update'.comp hW).prodMk (hX i)
  have hg : Measurable fun p : (∀ j, E j) × E i => f p.1 := hf.comp measurable_fst
  have hF' : MemLp (fun ω => f (Function.update (fun j => X j ω) i (X' i ω))) 2 μ := by
    have hm := (memLp_map_measure_iff hg.aestronglyMeasurable hW.aemeasurable).2
      (show MemLp ((fun p : (∀ j, E j) × E i => f p.1) ∘
        fun ω => ((fun j => X j ω), X' i ω)) 2 μ from hF)
    rw [es_map_swap_eq hX hX' hind hlaw i] at hm
    exact (memLp_map_measure_iff hg.aestronglyMeasurable hW'.aemeasurable).1 hm
  have hsq := es_integral_swap hX hX' hind hlaw (μ := μ) i (φ := fun p => f p.1 ^ 2)
    (hg.pow_const 2)
  have hR : Measurable fun p : (∀ j, E j) × E i => fun j : {j // j ≠ i} => p.1 j :=
    measurable_pi_iff.2 fun j => (measurable_pi_apply j.1).comp measurable_fst
  have hupd : ∀ ω, Function.update (Function.update (fun j => X j ω) i (X' i ω)) i (X i ω) =
      fun j => X j ω := fun ω => by
    rw [Function.update_idem]; exact Function.update_eq_self i _
  have hsymm := es_integral_swap hX hX' hind hlaw (μ := μ) i
    (φ := fun p => max (f (Function.update p.1 i p.2) - f p.1) 0 ^ 2)
    (((hf.comp measurable_update').sub hg).max measurable_const |>.pow_const 2)
  simp only [hupd] at hsymm
  have hloc : ∀ t : Set (∀ j : {j // j ≠ i}, E j), MeasurableSet t →
      ∫ ω, (((fun p : (∀ j, E j) × E i => fun j : {j // j ≠ i} => p.1 j) ⁻¹' t).indicator
        fun p => f p.1) (Function.update (fun j => X j ω) i (X' i ω), X i ω) ∂μ =
      ∫ ω, (((fun p : (∀ j, E j) × E i => fun j : {j // j ≠ i} => p.1 j) ⁻¹' t).indicator
        fun p => f p.1) ((fun j => X j ω), X' i ω) ∂μ := fun t ht =>
    es_integral_swap hX hX' hind hlaw (μ := μ) i (hg.indicator (hR ht))
  -- the σ-algebras
  set A : MeasurableSpace Ω := ⨆ j ∈ Finset.univ.erase i, (mE j).comap (X j) with hAdef
  have hA : A ≤ m₀ := iSup₂_le fun j _ => (hX j).comap_le
  have hAj : ∀ j, j ≠ i → (mE j).comap (X j) ≤ A := fun j h =>
    le_iSup₂ (f := fun j _ => (mE j).comap (X j)) j (Finset.mem_erase.2 ⟨h, Finset.mem_univ j⟩)
  have hind' : Indep ((mE i).comap (X' i)) (A ⊔ (mE i).comap (X i)) μ := by
    have h := indep_iSup_of_disjoint hle hind (S := {Sum.inr i}) (T := Set.range Sum.inl)
      (by simp)
    simp only [iSup_range, Set.mem_singleton_iff, iSup_iSup_eq_left] at h
    refine indep_of_indep_of_le_right h (sup_le (iSup₂_le fun j _ => ?_) ?_)
    · exact le_iSup (fun j => esCopySigma X X' (Sum.inl j)) j
    · exact le_iSup (fun j => esCopySigma X X' (Sum.inl j)) i
  have hFm : StronglyMeasurable[A ⊔ (mE i).comap (X i)] (fun ω => f (fun j => X j ω)) := by
    refine (hf.comp (es_measurable_vec fun j => ?_)).stronglyMeasurable
    by_cases h : j = i
    · subst h; exact le_sup_right
    · exact (hAj j h).trans le_sup_left
  have hF'm : StronglyMeasurable[A ⊔ (mE i).comap (X' i)]
      (fun ω => f (Function.update (fun j => X j ω) i (X' i ω))) := by
    have hv : Measurable[A ⊔ (mE i).comap (X' i)]
        (fun ω j => Function.update X i (X' i) j ω) := by
      refine es_measurable_vec fun j => ?_
      rw [es_comap_update]
      unfold esSwapIdx
      split_ifs with h
      · subst h; exact le_sup_right
      · exact (hAj j h).trans le_sup_left
    rw [es_update_vec] at hv
    exact (hf.comp hv).stronglyMeasurable
  -- `∫_s F' = ∫_s F` for `s ∈ A`
  have hAZ : A ≤ (MeasurableSpace.pi).comap (fun ω (j : {j // j ≠ i}) => X j.1 ω) := by
    rw [comap_process_pi]
    exact iSup₂_le fun j hj =>
      le_iSup (fun j : {j // j ≠ i} => (mE j.1).comap (X j.1)) ⟨j, (Finset.mem_erase.1 hj).1⟩
  have hset : ∀ s, MeasurableSet[A] s →
      ∫ ω in s, f (Function.update (fun j => X j ω) i (X' i ω)) ∂μ =
        ∫ ω in s, f (fun j => X j ω) ∂μ := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := measurableSet_comap.1 (hAZ s hs)
    have hs0 := hA _ hs
    rw [← integral_indicator hs0, ← integral_indicator hs0]
    have key : ∀ (y : ∀ j, E j) (z : E i) (ω : Ω), (fun j : {j // j ≠ i} => y j.1) =
        (fun j : {j // j ≠ i} => X j.1 ω) →
        ((fun p : (∀ j, E j) × E i => fun j : {j // j ≠ i} => p.1 j) ⁻¹' t).indicator
          (fun p => f p.1) (y, z) =
        ((fun ω (j : {j // j ≠ i}) => X j.1 ω) ⁻¹' t).indicator (fun _ => f y) ω := by
      intro y z ω e
      by_cases hω : (fun j : {j // j ≠ i} => X j.1 ω) ∈ t
      · rw [Set.indicator_of_mem (show ω ∈ (fun ω (j : {j // j ≠ i}) => X j.1 ω) ⁻¹' t from hω),
          Set.indicator_of_mem (show (y, z) ∈ (fun p : (∀ j, E j) × E i =>
            fun j : {j // j ≠ i} => p.1 j) ⁻¹' t from by
              show (fun j : {j // j ≠ i} => y j.1) ∈ t; rw [e]; exact hω)]
      · rw [Set.indicator_of_notMem (show ω ∉ (fun ω (j : {j // j ≠ i}) => X j.1 ω) ⁻¹' t
            from hω),
          Set.indicator_of_notMem (show (y, z) ∉ (fun p : (∀ j, E j) × E i =>
            fun j : {j // j ≠ i} => p.1 j) ⁻¹' t from by
              show (fun j : {j // j ≠ i} => y j.1) ∉ t; rw [e]; exact hω)]
    have h1 := hloc t ht
    simp only [fun ω => key _ (X i ω) ω (funext fun (j : {j // j ≠ i}) =>
        Function.update_of_ne j.2 (X' i ω) (fun j => X j ω)),
      fun ω => key (fun j => X j ω) (X' i ω) ω rfl] at h1
    convert h1 using 2 <;> funext ω <;>
      by_cases hω : ω ∈ (fun ω (j : {j // j ≠ i}) => X j.1 ω) ⁻¹' t <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  exact ⟨es_resample_identity hA (hX i).comap_le (hX' i).comap_le hind' hFm hF'm hF hF'
    hsq hset, es_half_sq_eq_posPart_sq hF hF' hsymm.symm⟩

omit [DecidableEq ι] hX hX' hind hlaw in
lemma es_stronglyMeasurable_iSup {f : (∀ j, E j) → ℝ} (hf : Measurable f) :
    StronglyMeasurable[⨆ j ∈ (Finset.univ : Finset ι), (mE j).comap (X j)]
      (fun ω => f (fun j => X j ω)) :=
  (hf.comp (es_measurable_vec fun j =>
    le_iSup₂ (f := fun j _ => (mE j).comap (X j)) j (Finset.mem_univ j))).stronglyMeasurable

/-- **Efron–Stein inequality, positive-part form** (DDDF (5.58), LM (5.4)):
`Var F ≤ ∑_i E[(F^{(i)} - F)_+²]`. -/
theorem efronStein_copy_posPart [IsProbabilityMeasure μ] {f : (∀ j, E j) → ℝ}
    (hf : Measurable f) (hF : MemLp (fun ω => f (fun j => X j ω)) 2 μ) :
    variance (fun ω => f (fun j => X j ω)) μ ≤ ∑ i,
      ∫ ω, max (f (Function.update (fun j => X j ω) i (X' i ω)) - f (fun j => X j ω)) 0 ^ 2 ∂μ := by
  have h := efronStein_sigma (fun j => (mE j).comap (X j)) (fun j => (hX j).comap_le)
    (hind.precomp Sum.inl_injective) Finset.univ (es_stronglyMeasurable_iSup (X := X) hf) hF
  exact h.trans_eq (Finset.sum_congr rfl fun i _ =>
    (efronStein_copy_term hX hX' hind hlaw hf hF i).1.trans
      (efronStein_copy_term hX hX' hind hlaw hf hF i).2)

end LQGMetric
