/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.RouteM.JWinding at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

/-!
# Route M, winding lemmas: logarithmic increments along planar curves

The winding argument. For a curve `γ : C(I, ℂ)` avoiding a point `z`,
`logIncr γ z = L 1 - L 0` for any continuous logarithm `L` of `γ - z` (host `exists_lift_exp`, unique up to an
additive constant by `lift_sub_eq_sub_zero`); it is `2πi` times TF3's `Δ`. This module proves:

* `logIncr_eq_of_lift`: any continuous logarithm computes it;
* `logIncr_trans` (W1, additivity under `Path.trans`), `logIncr_symm` (W2, reversal), `logIncr_const`,
  `logIncr_comp` (reparametrization invariance), `logIncr_affine` (similarity invariance);
* `logIncr_eq_log_sub_log` (TF3's sector rule): on a curve with `c (γ - z)` in the slit plane, the principal
  logarithm of `c (γ - z)` is a continuous logarithm;
* `loopDeg_mul_eq_logIncr`: for a loop, `loopDeg (γ - z) · 2πi = logIncr γ z`; `loopDeg_eq_of_logIncr_eq`: loops
  with equal increments have equal degrees; `loopDeg_normalize`: the degree about `z` equals the degree of the
  normalized loop `(γ - z) / c` (the form produced by the sealed polar-template degree lemma).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped unitInterval Real
open QuantumZipper.CA.Topo

namespace MatedCRTHarmonic.RouteM

/-- The logarithmic increment of `γ` about `z`: `L 1 - L 0` for a continuous logarithm `L` of `γ - z`
(`2πi` times TF3 §7's `Δ`); `0` when `γ` meets `z`. -/
@[irreducible] noncomputable def logIncr (γ : C(I, ℂ)) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable (∀ t, (γ - ContinuousMap.const I z) t ≠ 0)
  if h : ∀ t, (γ - ContinuousMap.const I z) t ≠ 0 then
    (exists_lift_exp _ h).choose 1 - (exists_lift_exp _ h).choose 0
  else 0

theorem JAux.sub_const_apply_ne_zero {γ : C(I, ℂ)} {z : ℂ} (h : ∀ t, γ t ≠ z) (t : I) :
    (γ - ContinuousMap.const I z) t ≠ 0 := by
  simpa only [ContinuousMap.sub_apply, ContinuousMap.const_apply] using sub_ne_zero.mpr (h t)

/-- Any continuous logarithm of `γ - z` computes the increment. -/
theorem logIncr_eq_of_lift (γ : C(I, ℂ)) (z : ℂ) {L : I → ℂ} (hL : Continuous L)
    (hexp : ∀ t, Complex.exp (L t) = γ t - z) : logIncr γ z = L 1 - L 0 := by
  have hexp' : ∀ t, Complex.exp (L t) = (γ - ContinuousMap.const I z) t := fun t => by
    simpa only [ContinuousMap.sub_apply, ContinuousMap.const_apply] using hexp t
  have h : ∀ t, (γ - ContinuousMap.const I z) t ≠ 0 := fun t => by
    rw [← hexp' t]
    exact Complex.exp_ne_zero _
  unfold logIncr
  rw [dite_eq_left h]
  have hL₀ := (exists_lift_exp _ h).choose_spec
  have key := lift_sub_eq_sub_zero (γ - ContinuousMap.const I z) h
    (exists_lift_exp _ h).choose.continuous hL hL₀ hexp' 1
  linear_combination -key

/-- The increment of a curve through `z` is `0` (junk value). -/
theorem logIncr_eq_zero_of_mem {γ : C(I, ℂ)} {z : ℂ} {t : I} (ht : γ t = z) : logIncr γ z = 0 := by
  have hn : ¬ ∀ t, (γ - ContinuousMap.const I z) t ≠ 0 := fun h => h t (by simp [ht])
  unfold logIncr
  exact dite_eq_right hn

/-- The increment only depends on the values of the curve. -/
theorem logIncr_congr {γ γ' : C(I, ℂ)} (h : ∀ t, γ t = γ' t) (z : ℂ) : logIncr γ z = logIncr γ' z := by
  rw [ContinuousMap.ext h]

/-- A curve avoiding `z` has a continuous logarithm of `γ - z`. -/
theorem JAux.exists_lift_sub (γ : C(I, ℂ)) {z : ℂ} (hγ : ∀ t, γ t ≠ z) :
    ∃ L : C(I, ℂ), ∀ t, Complex.exp (L t) = γ t - z := by
  obtain ⟨L, hL⟩ := exists_lift_exp (γ - ContinuousMap.const I z) (JAux.sub_const_apply_ne_zero hγ)
  exact ⟨L, fun t => by simpa only [ContinuousMap.sub_apply, ContinuousMap.const_apply] using hL t⟩

/-- **W1 (additivity).** The increment is additive under concatenation of paths. -/
theorem logIncr_trans {x y w : ℂ} (γ : Path x y) (γ' : Path y w) {z : ℂ} (hγ : ∀ t, γ t ≠ z)
    (hγ' : ∀ t, γ' t ≠ z) :
    logIncr (γ.trans γ').toContinuousMap z =
      logIncr γ.toContinuousMap z + logIncr γ'.toContinuousMap z := by
  obtain ⟨L, hL⟩ := JAux.exists_lift_sub γ.toContinuousMap hγ
  obtain ⟨L', hL'⟩ := JAux.exists_lift_sub γ'.toContinuousMap hγ'
  have hyz : y - z ≠ 0 := by
    have := hγ 1
    rw [γ.target] at this
    exact sub_ne_zero.mpr this
  set c := L 1 - L' 0 with hc
  have hexpc : Complex.exp c = 1 := by
    rw [hc, Complex.exp_sub, hL, hL']
    simp only [Path.coe_toContinuousMap, γ.target, γ'.source]
    exact div_self hyz
  let P₁ : Path (L 0) (L 1) := { toContinuousMap := L, source' := rfl, target' := rfl }
  let P₂ : Path (L 1) (L' 1 + c) :=
    { toFun := fun t => L' t + c
      continuous_toFun := by fun_prop
      source' := by simp only [hc]; ring
      target' := rfl }
  have hexp : ∀ t, Complex.exp ((P₁.trans P₂) t) = (γ.trans γ').toContinuousMap t - z := by
    intro t
    rw [Path.coe_toContinuousMap, Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact hL _
    · change Complex.exp (L' _ + c) = _
      rw [Complex.exp_add, hexpc, mul_one, hL']
      rfl
  rw [logIncr_eq_of_lift _ z (P₁.trans P₂).continuous hexp, logIncr_eq_of_lift _ z L.continuous hL,
    logIncr_eq_of_lift _ z L'.continuous hL', Path.target, Path.source]
  ring

/-- **W2 (reversal).** Reversing a path negates its increment. -/
theorem logIncr_symm {x y : ℂ} (γ : Path x y) {z : ℂ} (hγ : ∀ t, γ t ≠ z) :
    logIncr γ.symm.toContinuousMap z = -logIncr γ.toContinuousMap z := by
  obtain ⟨L, hL⟩ := JAux.exists_lift_sub γ.toContinuousMap hγ
  have hexp : ∀ t, Complex.exp (L (σ t)) = γ.symm.toContinuousMap t - z := fun t => hL (σ t)
  rw [logIncr_eq_of_lift _ z (L.continuous.comp unitInterval.continuous_symm) hexp,
    logIncr_eq_of_lift _ z L.continuous hL]
  simp only [Function.comp_apply, unitInterval.symm_one, unitInterval.symm_zero]
  ring

/-- A constant curve has increment `0`. -/
theorem logIncr_const (x z : ℂ) : logIncr (ContinuousMap.const I x) z = 0 := by
  by_cases hx : x = z
  · exact logIncr_eq_zero_of_mem (t := 0) (by simp [hx])
  · have hexp : ∀ t : I, Complex.exp ((fun _ => Complex.log (x - z)) t) = ContinuousMap.const I x t - z :=
      fun t => by simp [Complex.exp_log (sub_ne_zero.mpr hx)]
    rw [logIncr_eq_of_lift _ z continuous_const hexp]
    ring

/-- **Sector rule** (TF3 §7, Details (d3)). If `c (γ - z)` stays in the slit plane, the principal logarithm of
`c (γ - z)` is a continuous logarithm up to the constant `log c`, so the increment is
`log (c (γ 1 - z)) - log (c (γ 0 - z))`. -/
theorem logIncr_eq_log_sub_log (γ : C(I, ℂ)) (z : ℂ) {c : ℂ} (hc : c ≠ 0)
    (hslit : ∀ t, c * (γ t - z) ∈ Complex.slitPlane) :
    logIncr γ z = Complex.log (c * (γ 1 - z)) - Complex.log (c * (γ 0 - z)) := by
  have hcont : Continuous fun t => Complex.log (c * (γ t - z)) - Complex.log c := by
    refine Continuous.sub ?_ continuous_const
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (continuousAt_clog (hslit t)).comp (f := fun t => c * (γ t - z)) (by fun_prop)
  have hexp : ∀ t, Complex.exp (Complex.log (c * (γ t - z)) - Complex.log c) = γ t - z := fun t => by
    rw [Complex.exp_sub, Complex.exp_log (Complex.slitPlane_ne_zero (hslit t)), Complex.exp_log hc]
    field_simp
  rw [logIncr_eq_of_lift γ z hcont hexp]
  ring

/-- For a loop avoiding `z`, the degree about `z` times `2πi` is the increment. -/
theorem loopDeg_mul_eq_logIncr (γ : C(I, ℂ)) (z : ℂ) (hclosed : γ 0 = γ 1)
    (h : ∀ t, (γ - ContinuousMap.const I z) t ≠ 0) :
    (loopDeg (γ - ContinuousMap.const I z) h : ℂ) * (2 * π * Complex.I) = logIncr γ z := by
  obtain ⟨L, hL⟩ := exists_lift_exp _ h
  have hexp : ∀ t, Complex.exp (L t) = γ t - z := fun t => by
    simpa only [ContinuousMap.sub_apply, ContinuousMap.const_apply] using hL t
  rw [logIncr_eq_of_lift γ z L.continuous hexp]
  exact (loopDeg_eq_of_lift _ h (by simp [hclosed]) L.continuous hL).symm

/-- Degrees of loops are determined by their values. -/
theorem JAux.loopDeg_congr {γ γ' : C(I, ℂ)} (h : γ = γ') (hγ : ∀ t, γ t ≠ 0) (hγ' : ∀ t, γ' t ≠ 0) :
    loopDeg γ hγ = loopDeg γ' hγ' := by
  subst h
  rfl

end MatedCRTHarmonic.RouteM
