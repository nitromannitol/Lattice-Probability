/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Var.Ag at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.HigherDimLFPP.Var.PSD
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic
import LatticeProb.Bonanno.LQGDimension.Section2.Subadditive
import LatticeProb.Bonanno.LQGDimension.Assembly.AStar

/-!
# Finite Gaussian families and basic properties of `Ag E n`

* `gEM_empty`, `vecEM_congr_drift`, `gEM_image` (reindexing along any map, HA1 (T5));
* `le_Ag`, `Ag_le_of_forall`, `Ag_nonneg`, `Ag_ne_bot`, `gEM_le_toReal`;
* refinement monotonicity `Ag E n ≤ Ag E n'` for `n ≤ n'` (HA1 D3.3), from `Vg E n ⊆ Vg E n'`;
* `Ag E 0 = 0`.

The finite Gaussian layer (`gaussianExpectedMax`, `vecExpectedMax`, Gram bridge, reindexing
lemmas `LQGDimension.Subadd.*`) is reused from `LQGDimension` (`Gaussian/Basic.lean`,
`Section2/Subadditive.lean`); the `Ag` lemmas port `LQGDimension/Assembly/AStar.lean`
(`aE_nonneg`, `aE_zero_le_zero`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Finite Gaussian families -/

lemma gEM_empty {ι : Type*} (C : ι → ι → ℝ) (b : ι → ℝ) :
    gaussianExpectedMax (∅ : Finset ι) C b = 0 := by
  unfold gaussianExpectedMax
  have : (fun x : EuclideanSpace ℝ (∅ : Finset ι) => ⨆ i : (∅ : Finset ι), x i + b i) =
      fun _ => (0 : ℝ) := by
    funext x
    exact (iSup_of_empty' _).trans Real.sSup_empty
  rw [this]
  exact integral_zero _ _

/-- `vecExpectedMax F v b` only depends on the drift `b` on `F`. -/
lemma vecEM_congr_drift {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] [MeasurableSpace H] (F : Finset ι) (v : ι → H) {b b' : ι → ℝ}
    (h : ∀ i ∈ F, b i = b' i) : vecExpectedMax F v b = vecExpectedMax F v b' := by
  unfold vecExpectedMax
  congr 1
  funext x
  congr 1
  funext i
  rw [h i i.2]

/-- **Reindexing** (HA1 (T5)): for a kernel that is PSD on the image,
`𝕄_{φ(F)}(C, b) = 𝕄_F(C ∘ (φ × φ), b ∘ φ)`. -/
theorem gEM_image {ι κ : Type*} [DecidableEq κ] (F : Finset ι) (φ : ι → κ) (C : κ → κ → ℝ)
    (b : κ → ℝ) (hC : PSDOn (F.image φ) C) :
    gaussianExpectedMax (F.image φ) C b =
      gaussianExpectedMax F (fun i j => C (φ i) (φ j)) (fun i => b (φ i)) := by
  obtain ⟨T, hT⟩ := LQGDimension.exists_gram_of_psdOn (F.image φ) C hC
  rw [LQGDimension.gaussianExpectedMax_congr (F.image φ) b (fun i hi j hj => (hT i hi j hj).symm),
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax,
    ← LQGDimension.Subadd.vecEM_comp_image F φ T b,
    ← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  exact LQGDimension.gaussianExpectedMax_congr F _ (fun i hi j hj =>
    hT (φ i) (Finset.mem_image_of_mem φ hi) (φ j) (Finset.mem_image_of_mem φ hj))

/-! ## `Ag`: suprema over finite subfamilies -/

section AgBasic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma le_Ag {n : ℕ} (G : Finset (Vg E n)) :
    ((gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g)
      (fun f => -energy (f : ℝ → E)) : ℝ) : EReal) ≤ Ag E n :=
  le_iSup (fun F : Finset (Vg E n) => ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g)
    (fun f => -energy (f : ℝ → E)) : ℝ) : EReal)) G

lemma Ag_le_of_forall {n : ℕ} {B : EReal}
    (h : ∀ G : Finset (Vg E n), ((gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g)
      (fun f => -energy (f : ℝ → E)) : ℝ) : EReal) ≤ B) : Ag E n ≤ B :=
  iSup_le h

lemma Ag_nonneg (n : ℕ) : 0 ≤ Ag E n := by
  have h := le_Ag (E := E) (n := n) ∅
  rwa [gEM_empty, EReal.coe_zero] at h

lemma Ag_ne_bot (n : ℕ) : Ag E n ≠ ⊥ :=
  ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (Ag_nonneg n)

lemma Ag_eq_coe_toReal {n : ℕ} (h : Ag E n ≠ ⊤) : ((Ag E n).toReal : EReal) = Ag E n :=
  EReal.coe_toReal h (Ag_ne_bot n)

/-- Each finite family is bounded by the (finite) value `Ag E n`. -/
lemma gEM_le_toReal {n : ℕ} (h : Ag E n ≠ ⊤) (G : Finset (Vg E n)) :
    gaussianExpectedMax G (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E)) ≤
      (Ag E n).toReal := by
  have h1 := le_Ag G
  rw [← Ag_eq_coe_toReal h] at h1
  exact EReal.coe_le_coe_iff.1 h1

end AgBasic

section AgInner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Monotonicity of `Ag` along an inclusion of index spaces. -/
lemma Ag_le_of_subset {n n' : ℕ} (h : Vg E n ⊆ Vg E n') : Ag E n ≤ Ag E n' := by
  classical
  refine Ag_le_of_forall fun F => ?_
  let φ : Vg E n → Vg E n' := fun f => ⟨f.1, h f.2⟩
  have heq := gEM_image F φ (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E))
    (gCov_psdOn_Vg n' _)
  have h2 := le_Ag (F.image φ)
  rw [heq] at h2
  exact h2

/-- **(T5) Refinement monotonicity** (HA1 D3.3): `Ag E n ≤ Ag E n'` for `n ≤ n'`; in particular
`Ag E n ≤ Ag E (n + 1)`. -/
theorem Ag_mono {n n' : ℕ} (h : n ≤ n') : Ag E n ≤ Ag E n' :=
  Ag_le_of_subset (Vg_mono h)

end AgInner

/-! ## `Ag E 0 = 0` -/

section AgZero

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end AgZero

end HigherDimLFPP.Var
