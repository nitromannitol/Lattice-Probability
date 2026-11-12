/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.FerniqueFinite at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailBorell
import LatticeProb.Bonanno.LQGDimension.Gaussian.ChainingBox

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Fernique–Dudley chaining bound for finite Gaussian families

If the points of a finite family carry parameters `p i ∈ ℝ^d` (sup norm) of diameter `≤ a` and
the increments satisfy `E (X_i - X_j)² ≤ L² ‖p i - p j‖`, then for a centered Gaussian vector
`E max_i X_i ≤ 20 √5 · L √((d + 1) a)` (`integral_iSup_finVec_le`); the same for finite
families `X (t i)` of a centered Gaussian process (`integral_iSup_family_le`).

This is the finite-index content of the Fernique criterion (X. Fernique, *Régularité des
trajectoires des fonctions aléatoires gaussiennes*, LNM 480, 1975; R. J. Adler, *An
Introduction to Continuity, Extrema, and Related Topics for General Gaussian Processes*, IMS
Lecture Notes 12, 1990, Thm 4.1; Adler–Taylor, *Random Fields and Geometry*, Thm 1.3.3), in the
form used by Ding–Zeitouni–Zhang, arXiv:1807.00422, Lemma 2.3 (LaTeX lines 364–373): with
`a = b`, `L² = c/b` the bound is a universal constant. The chaining itself is
`LQGDimension.ChainBox.chainingBox_bound` (Dudley chaining on dyadic cells, reused verbatim);
here it is transferred from the Gram representation `(⟪v i, Z⟫)_i` (standard Gaussian `Z`)
to an arbitrary centered Gaussian vector by `GaussConc.exists_gramVec_of_centered`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped RealInnerProductSpace NNReal

namespace LQGMetric

namespace SupTail

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- `E ⟪u, x⟫ = 0` under the standard Gaussian. -/
lemma integral_inner_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (u : E) :
    ∫ x, ⟪u, x⟫ ∂stdGaussian E = 0 := by
  have h0 := integral_strongDual_stdGaussian (E := E) (innerSL ℝ u)
  rwa [LQGDimension.GaussianMax.coe_innerSL_eq] at h0


lemma integrable_inner_stdGaussian {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (u : E) :
    Integrable (fun x => ⟪u, x⟫) (stdGaussian E) := by
  have h := (IsGaussian.memLp_dual (stdGaussian E) (innerSL ℝ u) 1 (by simp)).integrable le_rfl
  rwa [LQGDimension.GaussianMax.coe_innerSL_eq] at h

lemma continuous_iSup_fin {n : ℕ} (hn : 0 < n) :
    Continuous fun x : Fin n → ℝ => ⨆ i, x i := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  have h : (fun x : Fin n → ℝ => ⨆ i, x i) = fun x => Finset.univ.sup' hne x := by
    funext x; exact (Finset.sup'_univ_eq_ciSup x).symm
  rw [h]
  exact (GaussConc.lipschitzWith_sup' hne).continuous

/-- **Chaining bound for a centered Gaussian vector** (finite form of the Fernique/Dudley
criterion): if the parameters `p i ∈ ℝ^d` (sup norm) have diameter `≤ a` and
`E (X_i - X_j)² ≤ L² ‖p i - p j‖`, then `E max_i X_i ≤ 20 √5 L √((d+1) a)`.
From `LQGDimension.ChainBox.chainingBox_bound` via the Gram representation. -/
theorem integral_iSup_finVec_le {n d : ℕ} (hn : 0 < n) {X : Ω → Fin n → ℝ}
    (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) (p : Fin n → Fin d → ℝ)
    {L a : ℝ} (hL : 0 ≤ L) (hp : ∀ i j, ‖p i - p j‖ ≤ a)
    (hv : ∀ i j, ∫ ω, (X ω i - X ω j) ^ 2 ∂P ≤ L ^ 2 * ‖p i - p j‖) :
    ∫ ω, ⨆ i, X ω i ∂P ≤ 20 * √5 * L * √((d + 1) * a) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have := hX.isProbabilityMeasure
  obtain ⟨v, -, hmap⟩ := GaussConc.exists_gramVec_of_centered hX h0
  set μ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hg : Measurable (GaussConc.gramVec v) :=
    (continuous_pi fun i => continuous_const.inner continuous_id).measurable
  have transfer : ∀ f : (Fin n → ℝ) → ℝ, Continuous f →
      ∫ ω, f (X ω) ∂P = ∫ z, f (GaussConc.gramVec v z) ∂μ := by
    intro f hf
    rw [← integral_map hX.aemeasurable hf.aestronglyMeasurable, hmap,
      integral_map hg.aemeasurable hf.aestronglyMeasurable]
  have hinc : ∀ i j, ‖v i - v j‖ ^ 2 ≤ L ^ 2 * ‖p i - p j‖ := by
    intro i j
    have h := transfer (fun x => (x i - x j) ^ 2) (by fun_prop)
    rw [← LQGDimension.GaussianMax.integral_inner_sq (v i - v j)]
    simp only [GaussConc.gramVec, inner_sub_left] at h ⊢
    rw [← h]
    exact hv i j
  rw [transfer _ (continuous_iSup_fin hn)]
  set i0 : Fin n := ⟨0, hn⟩
  have key := LQGDimension.ChainBox.chainingBox_bound (Finset.univ) p v hL
    (fun i _ j _ => hp i j) (fun i _ j _ => hinc i j) (Finset.mem_univ i0)
  unfold LQGDimension.vecExpectedMax at key
  simp only [Pi.zero_apply, add_zero] at key
  have hint := LQGDimension.ChainBox.integrable_iSup_inner (Finset.univ : Finset (Fin n))
    (fun i => v i - v i0)
  have hpt : ∀ z, (⨆ i, GaussConc.gramVec v z i) =
      (⨆ i : ↥(Finset.univ : Finset (Fin n)), ⟪v i - v i0, z⟫) + ⟪v i0, z⟫ := by
    intro z
    have : Nonempty ↥(Finset.univ : Finset (Fin n)) := ⟨⟨i0, Finset.mem_univ _⟩⟩
    rw [show ∀ (c : ℝ), (⨆ i : ↥(Finset.univ : Finset (Fin n)), ⟪v i - v i0, z⟫) + c =
        ⨆ i : ↥(Finset.univ : Finset (Fin n)), (⟪v i - v i0, z⟫ + c) from fun c =>
      (OrderIso.addRight c).map_ciSup (Finite.bddAbove_range _)]
    simp only [inner_sub_left, sub_add_cancel]
    exact ((Equiv.subtypeUnivEquiv Finset.mem_univ).iSup_comp
      (g := fun i => GaussConc.gramVec v z i)).symm
  simp_rw [hpt]
  rw [integral_add hint (integrable_inner_stdGaussian _), integral_inner_stdGaussian, add_zero]
  exact key


/-- **Chaining bound for finite families of a centered Gaussian process.** -/
theorem integral_iSup_family_le {X : T → Ω → ℝ} (hX : IsGaussianProcess X P)
    (h0 : ∀ s, ∫ ω, X s ω ∂P = 0) {n d : ℕ} (hn : 0 < n) (t : Fin n → T)
    (p : T → Fin d → ℝ) {L a : ℝ} (hL : 0 ≤ L) (hp : ∀ i j, ‖p (t i) - p (t j)‖ ≤ a)
    (hv : ∀ i j, ∫ ω, (X (t i) ω - X (t j) ω) ^ 2 ∂P ≤ L ^ 2 * ‖p (t i) - p (t j)‖) :
    ∫ ω, ⨆ i, X (t i) ω ∂P ≤ 20 * √5 * L * √((d + 1) * a) :=
  integral_iSup_finVec_le hn (hasGaussianLaw_finVec hX t) (fun i => h0 _) (fun i => p (t i))
    hL hp hv

end SupTail

end LQGMetric
