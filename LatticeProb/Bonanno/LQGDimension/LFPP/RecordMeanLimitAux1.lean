/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordMeanLimitAux1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Section2.Subadditive
import LatticeProb.Bonanno.LQGDimension.Section2.ZCovPSD
import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Node `M46` (`Draft.RecordMeanLimit`), auxiliary part 1: finite Gaussian families

* `gEM_comp_image`: reindexing a Gaussian expected maximum along an arbitrary (not necessarily
  injective) map, when the kernel is positive semidefinite on the image;
* `gEM_const`: a constant drift comes out of the expected maximum;
* `gEM_empty`: the expected maximum of the empty family is `0`;
* positive semidefiniteness: congruence, scaling, the zero kernel, and the increment kernel
  `zDiffCov` of the limit process.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.RML

open Blueprint.Draft

/-! ## Positive semidefiniteness -/

lemma psdOn_congr {ι : Type*} (F : Finset ι) {C C' : ι → ι → ℝ} (hC : PSDOn F C)
    (h : ∀ i ∈ F, ∀ j ∈ F, C i j = C' i j) : PSDOn F C' := by
  unfold PSDOn at hC ⊢
  have e : (Matrix.of fun i j : F => C' i j) = Matrix.of fun i j : F => C i j := by
    ext i j
    simp [h i i.2 j j.2]
  rw [e]
  exact hC

lemma psdOn_smul {ι : Type*} (F : Finset ι) {C : ι → ι → ℝ} (hC : PSDOn F C) {r : ℝ}
    (hr : 0 ≤ r) : PSDOn F (fun i j => r * C i j) := by
  unfold PSDOn at hC ⊢
  have e : (Matrix.of fun i j : F => r * C i j) = r • Matrix.of fun i j : F => C i j := by
    ext i j
    simp
  rw [e]
  exact hC.smul hr

lemma psdOn_zero {ι : Type*} (F : Finset ι) : PSDOn F (fun _ _ => (0 : ℝ)) := by
  unfold PSDOn
  have e : (Matrix.of fun _ _ : F => (0 : ℝ)) = 0 := by
    ext i j
    simp
  rw [e]
  exact Matrix.PosSemidef.zero

/-- The increment kernel `zDiffCov` is positive semidefinite on every finite family of pairs of
continuous functions. -/
theorem psdOn_zDiffCov {ι : Type*} (F : Finset ι) (a g : ι → ℝ → ℝ)
    (ha : ∀ i ∈ F, Continuous (a i)) (hg : ∀ i ∈ F, Continuous (g i)) :
    PSDOn F (fun i j => zDiffCov (a i) (g i) (a j) (g j)) := by
  classical
  set S : Finset (ℝ → ℝ) := F.image g ∪ F.image (fun i => a i + g i) with hS
  have hScont : ∀ f ∈ S, Continuous f := by
    intro f hf
    rcases Finset.mem_union.1 hf with hf | hf
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hf
      exact hg i hi
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hf
      exact (ha i hi).add (hg i hi)
  obtain ⟨U, hU⟩ := exists_gram_of_psdOn S zCov
    (zCovPSD S fun f hf => (hScont f hf).intervalIntegrable 0 1)
  have m1 : ∀ i ∈ F, g i ∈ S := fun i hi =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hi)
  have m2 : ∀ i ∈ F, a i + g i ∈ S := fun i hi =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => a i + g i) hi)
  have hG : PSDOn F (fun i j => ⟪U (a i + g i) - U (g i), U (a j + g j) - U (g j)⟫) :=
    posSemidef_gramOn F (fun i => U (a i + g i) - U (g i))
  refine psdOn_congr F hG fun i hi j hj => ?_
  simp only [inner_sub_left, inner_sub_right]
  rw [hU _ (m2 i hi) _ (m2 j hj), hU _ (m2 i hi) _ (m1 j hj), hU _ (m1 i hi) _ (m2 j hj),
    hU _ (m1 i hi) _ (m1 j hj)]
  simp only [zDiffCov]
  ring

/-! ## Gaussian expected maxima -/

/-- Reindexing along an arbitrary map `φ`: the expected maximum of the pulled-back family equals
that of the image family (duplicated indices do not change the maximum). -/
theorem gEM_comp_image {ι κ : Type*} [DecidableEq κ] (F : Finset ι) (φ : ι → κ)
    (C : κ → κ → ℝ) (b : κ → ℝ) (hC : PSDOn (F.image φ) C) :
    gaussianExpectedMax F (fun i j => C (φ i) (φ j)) (fun i => b (φ i)) =
      gaussianExpectedMax (F.image φ) C b := by
  obtain ⟨v, hv⟩ := exists_gram_of_psdOn (F.image φ) C hC
  calc gaussianExpectedMax F (fun i j => C (φ i) (φ j)) (fun i => b (φ i))
      = gaussianExpectedMax F (fun i j => ⟪v (φ i), v (φ j)⟫) (fun i => b (φ i)) :=
        gaussianExpectedMax_congr F _ fun i hi j hj =>
          (hv _ (Finset.mem_image_of_mem φ hi) _ (Finset.mem_image_of_mem φ hj)).symm
    _ = vecExpectedMax F (fun i => v (φ i)) (fun i => b (φ i)) :=
        gaussianExpectedMax_gram_eq_vecExpectedMax F _ _
    _ = vecExpectedMax (F.image φ) v b := Subadd.vecEM_comp_image F φ v b
    _ = gaussianExpectedMax (F.image φ) (fun i j => ⟪v i, v j⟫) b :=
        (gaussianExpectedMax_gram_eq_vecExpectedMax _ _ _).symm
    _ = gaussianExpectedMax (F.image φ) C b :=
        gaussianExpectedMax_congr _ _ fun i hi j hj => hv i hi j hj

/-- A constant drift comes out of the expected maximum. -/
theorem gEM_const {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (C : ι → ι → ℝ)
    (hC : PSDOn F C) (c : ℝ) :
    gaussianExpectedMax F C (fun _ => c) = gaussianExpectedMax F C (fun _ => 0) + c := by
  obtain ⟨v, -, hgem⟩ := exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  rw [hgem, hgem]
  have : Nonempty F := hF.to_subtype
  have hint := integrable_iSup_inner_add F v (fun _ => (0 : ℝ))
  unfold vecExpectedMax
  simp only [add_zero] at hint ⊢
  have hpt : ∀ x : EuclideanSpace ℝ F, (⨆ i : F, ⟪v i, x⟫ + c) = (⨆ i : F, ⟪v i, x⟫) + c :=
    fun x => (ciSup_add (Finite.bddAbove_range _) c).symm
  simp_rw [hpt]
  rw [integral_add hint (integrable_const c), integral_const, probReal_univ, one_smul]

/-- The expected maximum of the empty family is `0`. -/
theorem gEM_empty {ι : Type*} (C : ι → ι → ℝ) (b : ι → ℝ) :
    gaussianExpectedMax (∅ : Finset ι) C b = 0 := by
  unfold gaussianExpectedMax
  have : ∀ x : EuclideanSpace ℝ (∅ : Finset ι), (⨆ i : (∅ : Finset ι), x i + b i) = 0 := by
    intro x
    exact Real.iSup_of_isEmpty _
  simp only [this, integral_zero]

end LQGDimension.RML
