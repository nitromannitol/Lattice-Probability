/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.MarkedSimilarityActionLaws at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.ActualMarkedBlockTransport
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridDilationInvariance

/-!
# Composition laws of the translation and dilation actions on the marked space

The actual marked configuration space is `Env × Grid`.  Translation acts by
`ActualMarkedBlockTransport.translateEnv` on environments and
`DyadicGridTranslation.translate` on grids; dilation acts by
`EnvironmentLaws.similarityTargetEnv s 0` on environments and
`UniformGridDilationInvariance.dilate` on grids.  This module proves the
compatibility law `dilate s (shift w ω) = shift (s • w) (dilate s ω)` on both
factors, together with the identification `markedSimilarity s u = dilate s ∘ shift u`
of the general canonical similarity with a translation followed by a dilation.

* Grids: `dilate_translate`, via `grid_ext_of_origin` (a grid is determined by its
  phase and origins, since `Grid.compatible` recovers the digits).
* Environments: `similarityTargetEnv_similarityTargetEnv`, the general composition
  law of the canonical similarity action obtained from the existing
  `positiveSimilarity_comp` and the uniqueness
  `EnvironmentLaws.eq_similarityTargetEnv_of_isSimilarity`; its specialisations
  `similarityTargetEnv_zero_translateEnv`, `translateEnv_similarityTargetEnv_zero`
  and `similarityTargetEnv_zero_translateEnv_eq_translateEnv`.

Nothing here concerns laws: every statement is a pathwise identity.
-/

set_option autoImplicit false

namespace ReflectedGMS.MarkedSimilarityActionLaws

open DyadicApproximation DyadicGridTranslation UniformGridDilationInvariance
open Code EnvironmentLaws ActualMarkedBlockTransport

/-! ## Grids -/

/-- A grid is determined by its phase and origins: the digits are recovered from
`Grid.compatible` because the side lengths are positive. -/
theorem grid_ext_of_origin {D E : Grid} (hp : D.phase = E.phase) (ho : D.origin = E.origin) :
    D = E := by
  refine grid_ext hp ho (funext fun k => funext fun i => ?_)
  have hD := D.compatible k i
  have hE := E.compatible k i
  rw [ho, hp] at hD
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (E.phase + (k : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h2 : (2 : ℝ) ^ (E.phase + (k : ℝ)) * ((D.digit k i).val : ℝ)
      = (2 : ℝ) ^ (E.phase + (k : ℝ)) * ((E.digit k i).val : ℝ) := by linarith
  exact Fin.ext (Nat.cast_injective (mul_left_cancel₀ hpos.ne' h2))

/-- **Dilation–translation compatibility on grids.**  Dilating the grid seen from
`w` is the grid seen from `s • w` after dilating. -/
theorem dilate_translate (s : ℝ) (hs : 0 < s) (w : Plane) (D : Grid) :
    dilate s hs (translate w D) = translate (s • w) (dilate s hs D) := by
  refine grid_ext_of_origin rfl (funext fun k => funext fun i => ?_)
  have hsw : (s • w) i = s * w i := rfl
  show s * translatedOrigin D w (k - levelShift s D) i
      = translatedOrigin (dilate s hs D) (s • w) k i
  simp only [translatedOrigin, shiftedRelativeOrigin, side_dilate hs D k,
    relativeOrigin_dilate hs D k i, hsw,
    mul_div_mul_left (w i) (side D (k - levelShift s D)) hs.ne']
  ring

/-! ## Environments -/

/-- Composition of cell transforms, from `positiveSimilarity_comp`. -/
theorem transformCell_transformCell (s t : ℝ) (u v : Plane) (hs : 0 < s) (ht : 0 < t)
    (K : CompactCell) :
    transformCell s u hs (transformCell t v ht K)
      = transformCell (s * t) (v + t⁻¹ • u) (mul_pos hs ht) K := by
  apply SetLike.coe_injective
  rw [coe_transformCell, coe_transformCell, coe_transformCell, Set.image_image]
  congr 1
  funext z
  exact positiveSimilarity_comp s t u v z ht

/-- The physical similarity relation composes, with the composite of the two
relabelings as witness. -/
theorem isSimilarity_trans {s t : ℝ} {u v : Plane} {hs : 0 < s} {ht : 0 < t} {e e₁ e₂ : Env}
    (h₁ : IsSimilarity t v ht e e₁) (h₂ : IsSimilarity s u hs e₁ e₂) :
    IsSimilarity (s * t) (v + t⁻¹ • u) (mul_pos hs ht) e e₂ := by
  obtain ⟨q₁, hc₁, hg₁⟩ := h₁
  obtain ⟨q₂, hc₂, hg₂⟩ := h₂
  refine ⟨q₁.trans q₂, fun x => ?_, fun x y => ?_⟩
  · show (decode e₂).cell (q₂ (q₁ x))
        = transformCell (s * t) (v + t⁻¹ • u) (mul_pos hs ht) ((decode e).cell x)
    rw [hc₂ (q₁ x), hc₁ x, transformCell_transformCell]
  · show (decode e₂).graph.c (q₂ (q₁ x)) (q₂ (q₁ y)) = (decode e).graph.c x y
    rw [hg₂, hg₁]

/-- **Composition law of the canonical similarity action.** -/
theorem similarityTargetEnv_similarityTargetEnv (s t : ℝ) (u v : Plane) (hs : 0 < s)
    (ht : 0 < t) (e : Env) :
    similarityTargetEnv s u hs (similarityTargetEnv t v ht e)
      = similarityTargetEnv (s * t) (v + t⁻¹ • u) (mul_pos hs ht) e :=
  eq_similarityTargetEnv_of_isSimilarity
    (isSimilarity_trans (isSimilarity_similarityTargetEnv t v ht e)
      (isSimilarity_similarityTargetEnv s u hs _))

/-- Transport of the canonical similarity action along equal parameters. -/
theorem similarityTargetEnv_congr {s s' : ℝ} {u u' : Plane} (hs : 0 < s) (hs' : 0 < s')
    (h₁ : s = s') (h₂ : u = u') (e : Env) :
    similarityTargetEnv s u hs e = similarityTargetEnv s' u' hs' e := by
  subst h₁
  subst h₂
  rfl

/-- `markedSimilarity s u = dilate s ∘ shift u` on environments. -/
theorem similarityTargetEnv_zero_translateEnv (s : ℝ) (hs : 0 < s) (u : Plane) (e : Env) :
    similarityTargetEnv s 0 hs (translateEnv u e) = similarityTargetEnv s u hs e := by
  rw [translateEnv, similarityTargetEnv_similarityTargetEnv]
  exact similarityTargetEnv_congr _ hs (mul_one s) (by simp) e

/-- `markedSimilarity s w = shift (s • w) ∘ dilate s` on environments. -/
theorem translateEnv_similarityTargetEnv_zero (s : ℝ) (hs : 0 < s) (w : Plane) (e : Env) :
    translateEnv (s • w) (similarityTargetEnv s 0 hs e) = similarityTargetEnv s w hs e := by
  rw [translateEnv, similarityTargetEnv_similarityTargetEnv]
  exact similarityTargetEnv_congr _ hs (one_mul s)
    (by rw [zero_add, inv_smul_smul₀ hs.ne']) e

/-- **Dilation–translation compatibility on environments.** -/
theorem similarityTargetEnv_zero_translateEnv_eq_translateEnv (s : ℝ) (hs : 0 < s)
    (w : Plane) (e : Env) :
    similarityTargetEnv s 0 hs (translateEnv w e)
      = translateEnv (s • w) (similarityTargetEnv s 0 hs e) := by
  rw [similarityTargetEnv_zero_translateEnv, translateEnv_similarityTargetEnv_zero]

end ReflectedGMS.MarkedSimilarityActionLaws
