/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.WeakSquareDynkin at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventSquareGenerator
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialDynkin
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolventMarkov
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupMarkov

/-!
# Weak Dynkin identity for a squared vertex potential

This file tests the square-generator, which is only known to be speed `L¹`,
against a vertex resolvent.  The identity is scalar and does not assert that
the square-generator is an `L²` generator vector.
-/

set_option autoImplicit false

open scoped BigOperators InnerProductSpace NNReal

open MeasureTheory

namespace ReflectedGMS

open FullNetworkForm ComplexSequenceSpace SemigroupMultiplier

variable {V : Type*}

-- Match the real restriction used by the checked complex functional calculus.
noncomputable local instance : Algebra ℝ (ComplexL2 V →L[ℂ] ComplexL2 V) :=
  Algebra.complexToReal

private theorem fullFormSemigroup_parameterizedResolvent_commute
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {h : ℝ} (hh : 0 < h) (t : ℝ≥0) :
    fullFormSemigroup G m t * parameterizedResolvent G m h =
      parameterizedResolvent G m h * fullFormSemigroup G m t := by
  apply complexifyAlgHom_isometry.injective
  change complexify (fullFormSemigroup G m t * parameterizedResolvent G m h) =
    complexify (parameterizedResolvent G m h * fullFormSemigroup G m t)
  rw [complexify_mul, complexify_mul, complexify_fullFormSemigroup,
    complexify_parameterizedResolvent_eq_cfc_eulerStep G m hh]
  change cfc (p := IsSelfAdjoint) (k t) (complexOneResolvent G m) *
      cfc (p := IsSelfAdjoint) (eulerStep h) (complexOneResolvent G m) =
    cfc (p := IsSelfAdjoint) (eulerStep h) (complexOneResolvent G m) *
      cfc (p := IsSelfAdjoint) (k t) (complexOneResolvent G m)
  exact (cfc_commute_cfc (p := IsSelfAdjoint) (k t) (eulerStep h)
    (complexOneResolvent G m)).eq

/-- A full-domain weak generator identity implies scalar Dynkin evolution when
tested against every positive-rate vertex occupation resolvent.  The generator
only appears through speed-weighted scalar pairings, so no speed-`L²`
hypothesis on it is needed. -/
theorem fullEnergyFunction_weak_dynkin
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ z, 0 < m z) (hmsum : Summable m)
    (wFun g : V → ℝ) (hwL2 : HasSpeedL2 m wFun)
    (hwE : G.HasFiniteEnergy wFun)
    (hweak : ∀ (v : V → ℝ) {B : ℝ}, (∀ z, |v z| ≤ B) →
      G.HasFiniteEnergy v →
      G.dirichletForm wFun v = -∑' z : V, m z * g z * v z)
    {beta : ℝ} (hb : 0 < beta) (t : ℝ≥0) (x : V) :
    let vValue := vertexOccupationPotentialValue G m beta x
    ⟪vValue, fullFormSemigroup G m t (weightedValue m wFun hwL2) -
        weightedValue m wFun hwL2⟫_ℝ =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        ∑' z : V, m z * g z *
          unweight m (fullFormSemigroup G m (Real.toNNReal s) vValue) z := by
  classical
  dsimp only
  let w : ValueSpace V := weightedValue m wFun hwL2
  let F : ValueSpace V :=
    weightedValue m (G.indic x) (VertexTest.indic_hasSpeedL2 G m x)
  let vValue : ValueSpace V := vertexOccupationPotentialValue G m beta x
  let gen : ValueSpace V := beta • vValue - F
  have hDynkin := fullFormSemigroup_vertexOccupationPotentialValue_dynkin
    G m hm hb t x
  have hgenCont : Continuous (fun s : ℝ ↦
      fullFormSemigroup G m (Real.toNNReal s) gen) :=
    (fullFormSemigroup_continuous G m hm gen).comp continuous_real_toNNReal
  have hgenInt : IntervalIntegrable (fun s : ℝ ↦
      fullFormSemigroup G m (Real.toNNReal s) gen) volume 0 (t : ℝ) :=
    hgenCont.intervalIntegrable 0 (t : ℝ)
  have hpoint (s : ℝ) :
      ⟪fullFormSemigroup G m (Real.toNNReal s) gen, w⟫_ℝ =
        ∑' z : V, m z * g z *
          unweight m (fullFormSemigroup G m (Real.toNNReal s) vValue) z := by
    let st : ℝ≥0 := Real.toNNReal s
    let Fs : ValueSpace V := fullFormSemigroup G m st F
    let q : V → ℝ := parameterizedResolventFunction G m (1 / beta) Fs
    have hcomm := fullFormSemigroup_parameterizedResolvent_commute
      G m (one_div_pos.mpr hb) st
    have hvEq : fullFormSemigroup G m st vValue =
        (1 / beta) • parameterizedResolvent G m (1 / beta) Fs := by
      have hcommF := congrArg (fun T : ValueSpace V →L[ℝ] ValueSpace V ↦ T F) hcomm
      change fullFormSemigroup G m st (parameterizedResolvent G m (1 / beta) F) =
        parameterizedResolvent G m (1 / beta) Fs at hcommF
      dsimp only [vValue, vertexOccupationPotentialValue]
      rw [map_smul, hcommF]
    have hqL2 : HasSpeedL2 m q :=
      parameterizedResolventFunction_hasSpeedL2 G m hm (1 / beta) Fs
    have hresWeak := parameterizedResolventFunction_weak G m hm
      (one_div_pos.mpr hb) Fs wFun hwL2 hwE
    have hqEq : unweight m (fullFormSemigroup G m st vValue) =
        (1 / beta) • q := by
      rw [hvEq]
      funext z
      simp only [unweight, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, q,
        parameterizedResolventFunction]
      ring
    have hqBound (z : V) : |q z| ≤ 1 := by
      have hFmem (z : V) : unweight m F z ∈ Set.Icc (0 : ℝ) 1 := by
        dsimp only [F]
        rw [unweight_weightedValue m hm]
        unfold ReflectedWalk.ConductanceGraph.indic
        split <;> simp
      have hFsmem (z : V) : unweight m Fs z ∈ Set.Icc (0 : ℝ) 1 :=
        fullFormSemigroup_mem_Icc G m hm st F hFmem z
      have hqmem := parameterizedResolventFunction_mem_Icc G m hm
        (one_div_pos.mpr hb) Fs hFsmem z
      rw [abs_of_nonneg hqmem.1]
      exact hqmem.2
    have hvsBound (z : V) :
        |unweight m (fullFormSemigroup G m st vValue) z| ≤ 1 / beta := by
      rw [congrFun hqEq z, Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg (one_div_nonneg.mpr hb.le)]
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hqBound z) (one_div_nonneg.mpr hb.le)
    have hvsE : G.HasFiniteEnergy
        (unweight m (fullFormSemigroup G m st vValue)) := by
      rw [hqEq]
      exact (parameterizedResolventFunction_hasFiniteEnergy G m (1 / beta) Fs).smul _
    have hgenerator := hweak
      (unweight m (fullFormSemigroup G m st vValue)) hvsBound hvsE
    have hgenEq : fullFormSemigroup G m st gen =
        parameterizedResolvent G m (1 / beta) Fs - Fs := by
      dsimp only [gen]
      rw [map_sub, map_smul, hvEq]
      apply congrArg (fun a : ValueSpace V => a - Fs)
      simp only [smul_smul]
      rw [show beta * (1 / beta) = 1 by field_simp [hb.ne']]
      simp
    have hresWeak' :
        ⟪parameterizedResolvent G m (1 / beta) Fs - Fs, w⟫_ℝ =
          -(1 / beta) * G.dirichletForm q wFun := by
      rw [inner_sub_left]
      dsimp only [w] at hresWeak ⊢
      linarith
    rw [hgenEq, hresWeak']
    have hformScale :
        (1 / beta) * G.dirichletForm q wFun =
          G.dirichletForm (unweight m
            (fullFormSemigroup G m st vValue)) wFun := by
      rw [hqEq, G.dirichletForm_smul_left]
    rw [show -(1 / beta) * G.dirichletForm q wFun =
      -((1 / beta) * G.dirichletForm q wFun) by ring,
      hformScale, G.dirichletForm_comm, hgenerator]
    ring
  have hinnerDynkin :
      ⟪fullFormSemigroup G m t vValue - vValue, w⟫_ℝ =
        ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          ⟪fullFormSemigroup G m (Real.toNNReal s) gen, w⟫_ℝ := by
    change fullFormSemigroup G m t vValue - vValue =
      ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
        fullFormSemigroup G m (Real.toNNReal s) gen at hDynkin
    rw [hDynkin]
    calc
      ⟪∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          fullFormSemigroup G m (Real.toNNReal s) gen, w⟫_ℝ =
          ⟪w, ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
            fullFormSemigroup G m (Real.toNNReal s) gen⟫_ℝ := real_inner_comm _ _
      _ = ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          ⟪w, fullFormSemigroup G m (Real.toNNReal s) gen⟫_ℝ :=
        (innerSL ℝ w).intervalIntegral_comp_comm hgenInt |>.symm
      _ = ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
          ⟪fullFormSemigroup G m (Real.toNNReal s) gen, w⟫_ℝ := by
        apply intervalIntegral.integral_congr
        intro s _
        exact real_inner_comm
          (fullFormSemigroup G m (Real.toNNReal s) gen) w
  have hself :
      ⟪vValue, fullFormSemigroup G m t w - w⟫_ℝ =
        ⟪fullFormSemigroup G m t vValue - vValue, w⟫_ℝ := by
    rw [inner_sub_right, inner_sub_left]
    congr 1
    calc
      ⟪vValue, fullFormSemigroup G m t w⟫_ℝ =
          ⟪vValue, star (fullFormSemigroup G m t) w⟫_ℝ := by
            rw [fullFormSemigroup_isSelfAdjoint]
      _ = ⟪fullFormSemigroup G m t vValue, w⟫_ℝ :=
        by rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]
  rw [hself, hinnerDynkin]
  apply intervalIntegral.integral_congr
  intro s _
  exact hpoint s

end ReflectedGMS
