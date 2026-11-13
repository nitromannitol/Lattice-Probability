/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ParameterizedResolvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventProperties

/-!
# Parameterized resolvent on the existing full form domain

The resolvent at form coefficient `h > 0` is constructed algebraically from the
checked real `1`-resolvent.  No rescaled Hilbert domain is introduced.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The affine denominator relating the `h`-resolvent to the `1`-resolvent. -/
noncomputable def resolventDenominator (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (h : ℝ) : ValueSpace V →L[ℝ] ValueSpace V :=
  h • 1 + (1 - h) • oneResolvent G m

/-- The affine denominator is invertible at every positive form coefficient. -/
theorem resolventDenominator_isUnit (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) {h : ℝ} (hh : 0 < h) : IsUnit (resolventDenominator G m h) := by
  rw [← spectrum.zero_notMem_iff ℝ]
  intro hz
  by_cases hh1 : h = 1
  · subst h
    have hden : resolventDenominator G m 1 =
        (1 : ValueSpace V →L[ℝ] ValueSpace V) := by
      apply ContinuousLinearMap.ext
      intro z
      simp [resolventDenominator]
    rw [hden] at hz
    exact (spectrum.zero_notMem ℝ (isUnit_one : IsUnit
      (1 : ValueSpace V →L[ℝ] ValueSpace V))) hz
  · have hc : 1 - h ≠ 0 := sub_ne_zero.mpr (Ne.symm hh1)
    let c : ℝˣ := Units.mk0 (1 - h) hc
    let x : ℝ := -h / (1 - h)
    have hscaled : -h ∈ spectrum ℝ ((1 - h) • oneResolvent G m) := by
      apply (spectrum.add_mem_add_iff (a := (1 - h) • oneResolvent G m)
        (r := -h) (s := h)).mp
      simpa [resolventDenominator, Algebra.algebraMap_eq_smul_one] using hz
    have hcx : (c : ℝ) • x = -h := by
      dsimp [c, x]
      field_simp [hc]
    have hxspec : x ∈ spectrum ℝ (oneResolvent G m) := by
      apply (spectrum.smul_mem_smul_iff (a := oneResolvent G m) (r := c)
        (s := x)).mp
      change (c : ℝ) • x ∈ spectrum ℝ ((c : ℝ) • oneResolvent G m)
      rw [hcx]
      exact hscaled
    have hx := oneResolvent_spectrum_subset G m hxspec
    dsimp [x] at hx
    rcases lt_or_gt_of_ne hh1 with hlt | hgt
    · have hcpos : 0 < 1 - h := sub_pos.2 hlt
      have : -h / (1 - h) < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hh) hcpos
      exact (not_lt_of_ge hx.1) this
    · have hcneg : 1 - h < 0 := sub_neg.2 hgt
      have hrel : (-h / (1 - h)) * (1 - h) = -h := by field_simp [hc]
      nlinarith [hx.2]

/-- The real `h`-resolvent, expressed using the existing ring inverse. -/
noncomputable def parameterizedResolvent (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (h : ℝ) : ValueSpace V →L[ℝ] ValueSpace V :=
  oneResolvent G m * Ring.inverse (resolventDenominator G m h)

/-- Decode the parameterized resolvent to a vertex function. -/
noncomputable def parameterizedResolventFunction (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (h : ℝ) (f : ValueSpace V) : V → ℝ :=
  unweight m (parameterizedResolvent G m h f)

/-- The parameterized resolvent is the checked `1`-resolvent applied after the
inverse affine denominator. -/
theorem parameterizedResolvent_apply (G : ReflectedWalk.ConductanceGraph V)
    (m : V → ℝ) (h : ℝ) (f : ValueSpace V) :
    parameterizedResolvent G m h f =
      oneResolvent G m (Ring.inverse (resolventDenominator G m h) f) := rfl

theorem parameterizedResolventFunction_hasFiniteEnergy
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) :
    G.HasFiniteEnergy (parameterizedResolventFunction G m h f) := by
  rw [parameterizedResolventFunction, parameterizedResolvent_apply]
  exact oneResolventFunction_hasFiniteEnergy G m _

/-- The algebraically constructed operator satisfies the full-domain weak
`h`-resolvent identity, without changing the Hilbert form domain. -/
theorem parameterizedResolventFunction_weak
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V) (g : V → ℝ)
    (hL2 : HasSpeedL2 m g) (hE : G.HasFiniteEnergy g) :
    ⟪parameterizedResolvent G m h f, weightedValue m g hL2⟫_ℝ +
        h * G.dirichletForm (parameterizedResolventFunction G m h f) g =
      ⟪f, weightedValue m g hL2⟫_ℝ := by
  let B := resolventDenominator G m h
  let v := Ring.inverse B f
  have hB : IsUnit B := resolventDenominator_isUnit G m hh
  have hcancel : B * Ring.inverse B = 1 := Ring.mul_inverse_cancel B hB
  have happ := congrArg (fun T : ValueSpace V →L[ℝ] ValueSpace V => T f) hcancel
  have hf : f = h • v + (1 - h) • oneResolvent G m v := by
    symm
    simpa [B, v, resolventDenominator, Module.End.mul_apply] using happ
  have hweak := oneResolventFunction_weak G m hm v g hL2 hE
  change ⟪oneResolvent G m v, weightedValue m g hL2⟫_ℝ +
      h * G.dirichletForm (oneResolventFunction G m v) g =
    ⟪f, weightedValue m g hL2⟫_ℝ
  rw [hf, inner_add_left, inner_smul_left, inner_smul_left]
  simp only [starRingEnd_apply, star_trivial]
  linear_combination h * hweak

end ReflectedGMS.FullNetworkForm
