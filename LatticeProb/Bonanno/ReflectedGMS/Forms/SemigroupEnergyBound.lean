/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupEnergyBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.RealSemigroup
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreDensity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

/-!
# Full-form semigroup energy bound

The spectral multiplier inequality on the range of the resolvent gives the
quadratic semigroup bound there.  Density of resolvent lifts in the full graph
domain then extends the estimate to every finite-energy vector.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped InnerProductSpace NNReal

namespace ReflectedGMS.SemigroupMultiplier

/-- The scalar inequality behind the full-form quadratic energy estimate. -/
theorem sq_mul_one_sub_k_le {t : ℝ≥0} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x ^ 2 * (1 - k t x) ≤ (t : ℝ) * x * (1 - x) := by
  by_cases ht : t = 0
  · simp [ht]
  have htpos : 0 < t := pos_iff_ne_zero.2 ht
  rcases hx0.eq_or_lt with rfl | hx
  · simp
  rw [k_eq_exp htpos hx]
  let a : ℝ := (t : ℝ) * (1 / x - 1)
  have ha0 : 0 ≤ a := by
    dsimp [a]
    have hinv : 1 ≤ 1 / x := (le_div_iff₀ hx).2 (by simpa using hx1)
    exact mul_nonneg (by positivity) (sub_nonneg.2 hinv)
  have hexp : 1 - Real.exp (-a) ≤ a := by
    linarith [Real.add_one_le_exp (-a)]
  have hmul : x ^ 2 * (1 - Real.exp (-a)) ≤ x ^ 2 * a :=
    mul_le_mul_of_nonneg_left hexp (sq_nonneg x)
  have hxa : x ^ 2 * a = (t : ℝ) * x * (1 - x) := by
    dsimp [a]
    field_simp [hx.ne']
  have hexponent : (t : ℝ) * (1 - 1 / x) = -a := by
    dsimp [a]
    ring
  rw [hexponent]
  exact hmul.trans_eq hxa

end ReflectedGMS.SemigroupMultiplier

namespace ReflectedGMS.FullNetworkForm

open ComplexSequenceSpace SemigroupMultiplier

variable {V : Type*}

private theorem resolventLift_semigroup_energy_bound
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (f : ValueSpace V) (t : ℝ≥0) :
    ‖valueInclusion G m (oneResolventLift G m f)‖ ^ 2 -
        ⟪valueInclusion G m (oneResolventLift G m f),
          fullFormSemigroup G m t (valueInclusion G m (oneResolventLift G m f))⟫_ℝ ≤
      (t : ℝ) * G.Energy
        (unweight m (valueInclusion G m (oneResolventLift G m f))) := by
  letI cfcComplex := IsStarNormal.instContinuousFunctionalCalculus
    (A := ComplexL2 V →L[ℂ] ComplexL2 V)
  letI cfcReal := IsSelfAdjoint.instContinuousFunctionalCalculus
    (A := ComplexL2 V →L[ℂ] ComplexL2 V)
  let R := complexOneResolvent G m
  let S := fullFormSemigroupComplex G m t
  let z := ofReal V f
  let q : ℝ → ℝ := fun x =>
    (t : ℝ) * x * (1 - x) - x ^ 2 * (1 - k t x)
  have hq : ∀ x ∈ spectrum ℝ R, 0 ≤ q x := by
    intro x hx
    have hs := complexOneResolvent_spectrum_subset G m hx
    dsimp only [q]
    linarith [sq_mul_one_sub_k_le (t := t) hs.1 hs.2]
  have hnonneg : (0 : ComplexL2 V →L[ℂ] ComplexL2 V) ≤
      cfc (instCFC := cfcReal) q R := cfc_nonneg (instCFC := cfcReal) hq
  have hpos : (cfc (instCFC := cfcReal) q R).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp hnonneg
  have hip := hpos.re_inner_nonneg_right z
  have hRself : IsSelfAdjoint R := complexOneResolvent_isSelfAdjoint G m
  have hid : cfc (instCFC := cfcReal) (fun x : ℝ => x) R = R :=
    cfc_id' ℝ R (instCFC := cfcReal) hRself
  have cfc_sub_real (a b : ℝ → ℝ)
      (ha : ContinuousOn a (spectrum ℝ R))
      (hb : ContinuousOn b (spectrum ℝ R)) :
      cfc (instCFC := cfcReal) (fun x => a x - b x) R =
        cfc (instCFC := cfcReal) a R - cfc (instCFC := cfcReal) b R :=
    @cfc_sub ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) _ _ _ _ _ _ _ _ _ _
      cfcReal a b R ha hb
  have hxx : cfc (instCFC := cfcReal) (fun x : ℝ => x * x) R = R * R := by
    rw [cfc_mul (instCFC := cfcReal) (fun x : ℝ => x) (fun x : ℝ => x) R
      continuous_id.continuousOn continuous_id.continuousOn, hid]
  have hxkx : cfc (instCFC := cfcReal) (fun x : ℝ => x * k t x * x) R =
      R * cfc (instCFC := cfcReal) (k t) R * R := by
    rw [cfc_mul (instCFC := cfcReal) (fun x : ℝ => x * k t x)
        (fun x : ℝ => x) R
      (continuous_id.mul (continuous_k t)).continuousOn continuous_id.continuousOn,
      cfc_mul (instCFC := cfcReal) (fun x : ℝ => x) (k t) R
        continuous_id.continuousOn (continuous_k t).continuousOn, hid]
  have hleft : cfc (instCFC := cfcReal) (fun x : ℝ => x - x * x) R =
      R - R * R := by
    rw [cfc_sub_real (fun x : ℝ => x) (fun x : ℝ => x * x)
      continuous_id.continuousOn (continuous_id.mul continuous_id).continuousOn,
      hid, hxx]
  have hright : cfc (instCFC := cfcReal)
      (fun x : ℝ => x * x - x * k t x * x) R =
      R * R - R * cfc (instCFC := cfcReal) (k t) R * R := by
    rw [cfc_sub_real (fun x : ℝ => x * x)
        (fun x : ℝ => x * k t x * x)
      (continuous_id.mul continuous_id).continuousOn
      ((continuous_id.mul (continuous_k t)).mul continuous_id).continuousOn,
      hxx, hxkx]
  have hscale : cfc (instCFC := cfcReal)
      (fun x : ℝ => (t : ℝ) * (x - x * x)) R =
      algebraMap ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) (t : ℝ) * (R - R * R) := by
    rw [cfc_mul (instCFC := cfcReal) (fun _ : ℝ => (t : ℝ))
        (fun x : ℝ => x - x * x) R continuous_const.continuousOn
      (continuous_id.sub (continuous_id.mul continuous_id)).continuousOn,
      cfc_const (instCFC := cfcReal) (t : ℝ) R hRself, hleft]
    rfl
  have hqop : cfc (instCFC := cfcReal) q R =
      algebraMap ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) (t : ℝ) * (R - R * R) -
        (R * R - R * S * R) := by
    dsimp only [q, S, fullFormSemigroupComplex, spectralSemigroup]
    rw [show (fun x : ℝ => (t : ℝ) * x * (1 - x) - x ^ 2 * (1 - k t x)) =
        (fun x : ℝ => (t : ℝ) * (x - x * x) - (x * x - x * k t x * x)) by
      funext x; ring]
    rw [cfc_sub_real
      (fun x : ℝ => (t : ℝ) * (x - x * x))
      (fun x : ℝ => x * x - x * k t x * x)
      (continuous_const.mul (continuous_id.sub
        (continuous_id.mul continuous_id))).continuousOn
      ((continuous_id.mul continuous_id).sub
        ((continuous_id.mul (continuous_k t)).mul continuous_id)).continuousOn,
      hscale, hright]
  rw [hqop] at hip
  dsimp only [R, S, z] at hip
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, one_apply_eq_self,
    ContinuousLinearMap.mul_apply, complexOneResolvent_ofReal,
    fullFormSemigroupComplex_ofReal, ofReal_inner, Complex.ofReal_re,
    inner_sub_right, inner_smul_real_right, inner_smul_left, map_sub, map_smul,
    real_inner_self_eq_norm_sq] at hip
  have hsmul (u : ValueSpace V) :
      (RCLike.re ⟪ofReal V f, (t : ℝ) • ofReal V u⟫_ℂ) =
        (t : ℝ) * ⟪f, u⟫_ℝ := by
    rw [← map_smul, ofReal_inner]
    simp only [inner_smul_right, starRingEnd_apply, star_trivial, smul_eq_mul]
    exact Complex.ofReal_re _
  rw [hsmul, hsmul] at hip
  change 0 ≤
      (t : ℝ) * ⟪f, oneResolvent G m f⟫_ℝ -
        (t : ℝ) * ⟪f, oneResolvent G m (oneResolvent G m f)⟫_ℝ -
      (⟪f, oneResolvent G m (oneResolvent G m f)⟫_ℝ -
        ⟪f, oneResolvent G m
          (fullFormSemigroup G m t (oneResolvent G m f))⟫_ℝ) at hip
  have hR2 : ⟪f, oneResolvent G m (oneResolvent G m f)⟫_ℝ =
      ‖oneResolvent G m f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    exact ((oneResolvent_isPositive G m).inner_left_eq_inner_right
      f (oneResolvent G m f)).symm
  have hRP : ⟪f, oneResolvent G m
        (fullFormSemigroup G m t (oneResolvent G m f))⟫_ℝ =
      ⟪oneResolvent G m f,
        fullFormSemigroup G m t (oneResolvent G m f)⟫_ℝ :=
    ((oneResolvent_isPositive G m).inner_left_eq_inner_right f
      (fullFormSemigroup G m t (oneResolvent G m f))).symm
  have hweak := oneResolventLift_weak G m f (oneResolventLift G m f)
  have hgrad :
      ⟪gradientInclusion G m (oneResolventLift G m f),
        gradientInclusion G m (oneResolventLift G m f)⟫_ℝ =
      G.Energy (unweight m
        (valueInclusion G m (oneResolventLift G m f))) := by
    rw [real_inner_self_eq_norm_sq, gradientInclusion_eq, weightedGradient_norm_sq]
  rw [real_inner_self_eq_norm_sq, hgrad] at hweak
  change ‖oneResolvent G m f‖ ^ 2 +
      G.Energy (unweight m (oneResolvent G m f)) =
        ⟪f, oneResolvent G m f⟫_ℝ at hweak
  rw [hR2, hRP] at hip
  change ‖oneResolvent G m f‖ ^ 2 -
      ⟪oneResolvent G m f,
        fullFormSemigroup G m t (oneResolvent G m f)⟫_ℝ ≤
    (t : ℝ) * G.Energy (unweight m (oneResolvent G m f))
  have henergy :
      (t : ℝ) * ⟪f, oneResolvent G m f⟫_ℝ -
          (t : ℝ) * ‖oneResolvent G m f‖ ^ 2 =
        (t : ℝ) * G.Energy (unweight m (oneResolvent G m f)) := by
    rw [← hweak]
    ring
  linarith

/-- Every vector in the full form domain satisfies the quadratic semigroup
energy estimate, with the exact normalized network energy. -/
theorem fullFormSemigroup_quadratic_deficit_le_energy
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (_hm : ∀ v, 0 < m v) (U : hilbertDomain G m) (t : ℝ≥0) :
    ‖valueInclusion G m U‖ ^ 2 -
        ⟪valueInclusion G m U,
          fullFormSemigroup G m t (valueInclusion G m U)⟫_ℝ ≤
      (t : ℝ) * G.Energy (unweight m (valueInclusion G m U)) := by
  let lhs : hilbertDomain G m → ℝ := fun W =>
    ‖valueInclusion G m W‖ ^ 2 -
      ⟪valueInclusion G m W,
        fullFormSemigroup G m t (valueInclusion G m W)⟫_ℝ
  let rhs : hilbertDomain G m → ℝ := fun W =>
    (t : ℝ) * ‖gradientInclusion G m W‖ ^ 2
  have hlhs : Continuous lhs := by
    exact ((valueInclusion G m).continuous.norm.pow 2).sub
      ((valueInclusion G m).continuous.inner
        ((fullFormSemigroup G m t).continuous.comp (valueInclusion G m).continuous))
  have hrhs : Continuous rhs := by
    exact continuous_const.mul ((gradientInclusion G m).continuous.norm.pow 2)
  have hrange : ∀ W ∈ Set.range (oneResolventLift G m), lhs W ≤ rhs W := by
    rintro W ⟨f, rfl⟩
    dsimp only [lhs, rhs]
    rw [gradientInclusion_eq, weightedGradient_norm_sq]
    exact resolventLift_semigroup_energy_bound G m f t
  have hclosure : U ∈ closure (Set.range (oneResolventLift G m)) :=
    denseRange_oneResolventLift G m U
  have hle := le_on_closure hrange hlhs.continuousOn hrhs.continuousOn hclosure
  dsimp only [lhs, rhs] at hle
  rw [gradientInclusion_eq, weightedGradient_norm_sq] at hle
  exact hle

end ReflectedGMS.FullNetworkForm
