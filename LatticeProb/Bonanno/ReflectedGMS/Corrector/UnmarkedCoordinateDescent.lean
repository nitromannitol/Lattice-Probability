/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.UnmarkedCoordinateDescent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicMainStatement
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Arctan

/-!
# Measure-theoretic descent to an environment-only harmonic coordinate

This file is the **measurability half** of manuscript Proposition `s:prop:gridindependence`
("The auxiliary grid disappears", `sections/05.tex` lines 52-71):

> Given `ℍ`, take independent grids `𝒟₁, 𝒟₂` ... Conditional on `ℍ`, two independent copies
> thus agree almost surely. To make the measurability conclusion without assuming moments of
> the vertex values, encode the real coordinates by their arctangents, with zero at unused
> cell labels. For any one coordinate `Z`, conditional independence gives
> `E[(Z¹ − Z²)² ∣ ℍ] = 2 Var(Z¹ ∣ ℍ) = 0`.
> Thus each bounded coordinate is `ℍ`-measurable. Inverting arctangent and using the countable
> cell coding proves that the entire gradient and normalized potential are `ℍ`-measurable.
> There is also an exactly covariant version. ...

`Corrector/HarmonicGridIndependence.lean` already proves the *comparison* half (the two coupled
grids produce a.s. equal potentials, from the four specific orthogonality relations). That
equality is kept here as the explicit hypothesis `hcopies`; **nothing in this file claims that
grid independence has been produced**, only that it descends.

## What is proved

The conditioning on `ℍ` is realised concretely: the joint law of the environment and the two
independent grids is `ν.prod (σ.prod σ)` on `Env × (Grid × Grid)`, so conditioning on `ℍ` is
evaluation at a fixed `e : Env` and the conditional variance is `Var[·; σ]`.

* `integral_sq_sub_prod_eq_two_mul_variance` — the manuscript's identity
  `E[(Z¹ − Z²)²] = 2 Var(Z)` for a bounded measurable coordinate on the independent product,
  proved by Fubini (`integral_prod_mul`) and `ProbabilityTheory.variance_eq_sub`.
* `ae_eq_integral_of_ae_prod_eq` — two independent copies that agree a.s. have zero variance
  (via the identity above) and are therefore a.s. equal to their own mean. This is the exact
  step `E[(Z¹ − Z²)² ∣ ℍ] = 2 Var(Z¹ ∣ ℍ) = 0` followed by "each bounded coordinate is
  `ℍ`-measurable"; boundedness is what makes the mean available without moment assumptions.
* `unmarkedValue` — the descended field: the arctangent code of each real coordinate of each
  cell label is averaged over the grid and the arctangent is inverted. It is measurable in the
  environment alone (`measurable_unmarkedValue`) and it is a genuine *inverse* of the coding on
  the point masses (`unmarkedValue_eq_of_ae_eq`).
* `ae_ae_eq_unmarkedValue` — **the descent**: if the two independent grid copies give the same
  field almost surely, then for a.e. environment the marked field is a.s. equal to the
  environment-measurable field `unmarkedValue`.
* `unmarkedCellField`, `exists_unmarked_cellField` — packaged as the `EnvironmentFields.CellField`
  that `HarmonicMainStatement.IsHarmonicCoordinate` quantifies over: measurable on `Env`, zero at
  absent labels, a.s. equal to the marked field.
* `DescentGood`, `descentField`, `descentCellField` — the manuscript's last paragraph: the set of
  environments whose grid-conditional law is a point mass is measurable and has full measure, the
  field is taken to be that point mass there and zero elsewhere, and this unmarked field transports
  exactly under any measure-preserving grid action of a similarity (`GridTransfer`), hence the good
  set is similarity invariant (`similarityInvariant_descentGood`) and the field is covariant
  (`descentField_covariant`).

## Scope

The grid-equivariance data (`GridTransfer` / `SimilarityGridEquivariant`) and the independent-copy
equality (`hcopies`) are hypotheses: they are owed by the grid-dilation producer
(`Geometry/UniformGridDilationInvariance`) and by the remaining harmonic-energy inputs of
`Corrector/HarmonicGridIndependence` respectively. No harmonicity, energy, or convergence property
is used or asserted anywhere below: this is exactly the measure-theoretic descent.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace UnmarkedCoordinateDescent

open MeasureTheory Filter
open Code EnvironmentFields EnvironmentLaws DyadicApproximation HarmonicMainStatement

/-! ### Bounded coordinates of the plane -/

/-- One real coordinate of a plane vector. -/
noncomputable def planeCoord (x : Plane) (i : Fin 2) : ℝ :=
  (WithLp.ofLp : Plane → (Fin 2 → ℝ)) x i

/-- A plane vector assembled from its two real coordinates. -/
noncomputable def ofCoords (f : Fin 2 → ℝ) : Plane := WithLp.toLp 2 f

@[simp] theorem planeCoord_ofCoords (f : Fin 2 → ℝ) (i : Fin 2) :
    planeCoord (ofCoords f) i = f i := rfl

@[simp] theorem planeCoord_zero (i : Fin 2) : planeCoord (0 : Plane) i = 0 := by
  simp [planeCoord]

theorem measurable_planeCoord (i : Fin 2) : Measurable fun x : Plane => planeCoord x i :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 2 → ℝ))

theorem plane_ext {x y : Plane} (h : ∀ i, planeCoord x i = planeCoord y i) : x = y := by
  apply WithLp.ofLp_injective 2
  funext i
  exact h i

/-- `tan` is measurable; it is the inverse used to undo the arctangent coding. -/
theorem measurable_tan : Measurable Real.tan := by
  have h : Real.tan = fun x => Real.sin x / Real.cos x := funext Real.tan_eq_sin_div_cos
  rw [h]
  exact Real.measurable_sin.div Real.measurable_cos

/-- The arctangent code is bounded, uniformly in everything. -/
theorem abs_arctan_le_pi_div_two (x : ℝ) : |Real.arctan x| ≤ Real.pi / 2 :=
  abs_le.2 ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩

/-! ### The abstract product-space descent

`β` is the auxiliary randomness (the dyadic grid) and the two independent copies live on
`σ.prod σ`. -/

section Abstract

variable {β : Type*} [MeasurableSpace β]

/-- A bounded measurable real function on a finite measure space is integrable. -/
theorem integrable_of_abs_le {γ : Type*} [MeasurableSpace γ] {μ : Measure γ} [IsFiniteMeasure μ]
    {f : γ → ℝ} (K : ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ K) : Integrable f μ :=
  memLp_one_iff_integrable.1
    (MemLp.of_bound hf.aestronglyMeasurable K
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x))

/-- A bounded measurable real function on a finite measure space is square integrable. -/
theorem memLp_two_of_abs_le {γ : Type*} [MeasurableSpace γ] {μ : Measure γ} [IsFiniteMeasure μ]
    {f : γ → ℝ} (K : ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ K) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable K
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

/-- **The manuscript's conditional-variance identity**, on the independent product:
`E[(Z¹ − Z²)²] = 2 Var(Z)`. Conditioning on the environment is evaluation at a fixed
environment, so this is exactly `E[(Z¹−Z²)² ∣ ℍ] = 2 Var(Z¹ ∣ ℍ)` for the coded coordinate. -/
theorem integral_sq_sub_prod_eq_two_mul_variance (σ : Measure β) [IsProbabilityMeasure σ]
    (h : β → ℝ) (C : ℝ) (hmeas : Measurable h) (hbdd : ∀ b, |h b| ≤ C) :
    (∫ q : β × β, (h q.1 - h q.2) ^ 2 ∂σ.prod σ) = 2 * ProbabilityTheory.variance h σ := by
  have hsqbdd : ∀ x : β, |h x ^ 2| ≤ C * C := by
    intro x
    have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (h x)) (hbdd x)
    calc |h x ^ 2| = |h x| * |h x| := by rw [sq, abs_mul]
      _ ≤ C * C := mul_le_mul (hbdd x) (hbdd x) (abs_nonneg _) hC0
  have hmulbdd : ∀ q : β × β, |2 * (h q.1 * h q.2)| ≤ 2 * (C * C) := by
    intro q
    have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (h q.1)) (hbdd q.1)
    have : |h q.1 * h q.2| ≤ C * C :=
      calc |h q.1 * h q.2| = |h q.1| * |h q.2| := abs_mul _ _
        _ ≤ C * C := mul_le_mul (hbdd _) (hbdd _) (abs_nonneg _) hC0
    calc |2 * (h q.1 * h q.2)| = 2 * |h q.1 * h q.2| := by
          rw [abs_mul]; norm_num
      _ ≤ 2 * (C * C) := by linarith
  -- integrability of the three pieces on the product
  have i1 : Integrable (fun q : β × β => h q.1 ^ 2) (σ.prod σ) :=
    integrable_of_abs_le (C * C) ((hmeas.comp measurable_fst).pow_const 2) fun q => hsqbdd q.1
  have i2 : Integrable (fun q : β × β => h q.2 ^ 2) (σ.prod σ) :=
    integrable_of_abs_le (C * C) ((hmeas.comp measurable_snd).pow_const 2) fun q => hsqbdd q.2
  have i3 : Integrable (fun q : β × β => 2 * (h q.1 * h q.2)) (σ.prod σ) :=
    integrable_of_abs_le (2 * (C * C))
      (((hmeas.comp measurable_fst).mul (hmeas.comp measurable_snd)).const_mul 2) hmulbdd
  have hmem : MemLp h 2 σ := memLp_two_of_abs_le C hmeas hbdd
  -- the three product integrals
  have e1 : (∫ q : β × β, h q.1 ^ 2 ∂σ.prod σ) = ∫ x, h x ^ 2 ∂σ := by
    have := integral_prod_mul (μ := σ) (ν := σ) (fun x => h x ^ 2) (fun _ => (1 : ℝ))
    simpa using this
  have e2 : (∫ q : β × β, h q.2 ^ 2 ∂σ.prod σ) = ∫ x, h x ^ 2 ∂σ := by
    have := integral_prod_mul (μ := σ) (ν := σ) (fun _ => (1 : ℝ)) (fun y => h y ^ 2)
    simpa using this
  have e3 : (∫ q : β × β, h q.1 * h q.2 ∂σ.prod σ) = (∫ x, h x ∂σ) * ∫ x, h x ∂σ :=
    integral_prod_mul (μ := σ) (ν := σ) h h
  have hvar : ProbabilityTheory.variance h σ = (∫ x, h x ^ 2 ∂σ) - (∫ x, h x ∂σ) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    simp only [Pi.pow_apply]
  have expand : (∫ q : β × β, (h q.1 - h q.2) ^ 2 ∂σ.prod σ) =
      ∫ q : β × β, (h q.1 ^ 2 + h q.2 ^ 2 - 2 * (h q.1 * h q.2)) ∂σ.prod σ := by
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    ring
  -- integrability of the sum, stated in the exact `fun q => _ + _` shape `integral_sub` needs
  have hsq' : ∀ x : β, h x ^ 2 ≤ C * C := fun x => (le_abs_self _).trans (hsqbdd x)
  have hsumbdd : ∀ q : β × β, |h q.1 ^ 2 + h q.2 ^ 2| ≤ C * C + C * C := by
    intro q
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ h q.1 ^ 2 + h q.2 ^ 2)]
    exact add_le_add (hsq' q.1) (hsq' q.2)
  have iadd : Integrable (fun q : β × β => h q.1 ^ 2 + h q.2 ^ 2) (σ.prod σ) :=
    integrable_of_abs_le (C * C + C * C)
      (((hmeas.comp measurable_fst).pow_const 2).add ((hmeas.comp measurable_snd).pow_const 2))
      hsumbdd
  have hsub : (∫ q : β × β, (h q.1 ^ 2 + h q.2 ^ 2 - 2 * (h q.1 * h q.2)) ∂σ.prod σ)
      = (∫ q : β × β, (h q.1 ^ 2 + h q.2 ^ 2) ∂σ.prod σ)
        - ∫ q : β × β, 2 * (h q.1 * h q.2) ∂σ.prod σ := integral_sub iadd i3
  have hadd : (∫ q : β × β, (h q.1 ^ 2 + h q.2 ^ 2) ∂σ.prod σ)
      = (∫ q : β × β, h q.1 ^ 2 ∂σ.prod σ) + ∫ q : β × β, h q.2 ^ 2 ∂σ.prod σ :=
    integral_add i1 i2
  have hcmul : (∫ q : β × β, 2 * (h q.1 * h q.2) ∂σ.prod σ)
      = 2 * ∫ q : β × β, h q.1 * h q.2 ∂σ.prod σ := integral_const_mul _ _
  rw [expand, hsub, hadd, hcmul, e1, e2, e3, hvar]
  ring

/-- **Zero conditional variance from agreeing independent copies.** If two independent copies of
a bounded measurable coordinate agree almost surely, then the coordinate is almost surely equal
to its mean — the mean being a measurable function of whatever the copies are conditioned on.
This is the manuscript's `E[(Z¹−Z²)² ∣ ℍ] = 2 Var(Z¹ ∣ ℍ) = 0`. -/
theorem ae_eq_integral_of_ae_prod_eq (σ : Measure β) [IsProbabilityMeasure σ]
    (h : β → ℝ) (C : ℝ) (hmeas : Measurable h) (hbdd : ∀ b, |h b| ≤ C)
    (hcopy : ∀ᵐ q : β × β ∂σ.prod σ, h q.1 = h q.2) :
    ∀ᵐ b ∂σ, h b = ∫ b', h b' ∂σ := by
  have hzero : (∫ q : β × β, (h q.1 - h q.2) ^ 2 ∂σ.prod σ) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hcopy] with q hq
    simp [hq]
  have hid := integral_sq_sub_prod_eq_two_mul_variance σ h C hmeas hbdd
  rw [hid] at hzero
  have hvar : ProbabilityTheory.variance h σ = 0 := by linarith
  exact ProbabilityTheory.ae_eq_integral_of_variance_eq_zero (memLp_two_of_abs_le C hmeas hbdd)
    hvar

end Abstract

/-! ### The coordinate coding of the marked field -/

/-- The arctangent code of one real coordinate of one canonical cell label. Absent labels carry
the value `0`, whose code is again `0`. -/
noncomputable def codedCoordinate (Ψ : MarkedEnvironment → ℕ → Plane) (n : ℕ) (i : Fin 2)
    (ω : MarkedEnvironment) : ℝ :=
  Real.arctan (planeCoord (Ψ ω n) i)

theorem abs_codedCoordinate_le (Ψ : MarkedEnvironment → ℕ → Plane) (n : ℕ) (i : Fin 2)
    (ω : MarkedEnvironment) : |codedCoordinate Ψ n i ω| ≤ Real.pi / 2 :=
  abs_arctan_le_pi_div_two _

theorem measurable_codedCoordinate {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    (n : ℕ) (i : Fin 2) : Measurable (codedCoordinate Ψ n i) :=
  Real.measurable_arctan.comp ((measurable_planeCoord i).comp ((measurable_pi_apply n).comp hΨ))

theorem measurable_codedCoordinate_grid {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    (n : ℕ) (i : Fin 2) (e : Env) :
    Measurable fun D : Grid => codedCoordinate Ψ n i (e, D) :=
  (measurable_codedCoordinate hΨ n i).comp (measurable_const.prodMk measurable_id)

/-- **The descended field.** Each real coordinate of each cell label is averaged over the grid
*after* the bounded arctangent coding, and the coding is then inverted. No moment assumption on
the vertex values is used, exactly as the manuscript requires. -/
noncomputable def unmarkedValue (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane)
    (e : Env) (n : ℕ) : Plane :=
  ofCoords fun i => Real.tan (∫ D, codedCoordinate Ψ n i (e, D) ∂σ)

theorem planeCoord_unmarkedValue (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane)
    (e : Env) (n : ℕ) (i : Fin 2) :
    planeCoord (unmarkedValue σ Ψ e n) i = Real.tan (∫ D, codedCoordinate Ψ n i (e, D) ∂σ) := rfl

/-- The descended field is measurable **in the environment alone**: this is the conclusion
"measurable functions of `ℍ` alone" of `s:prop:gridindependence`. -/
theorem measurable_unmarkedValue (σ : Measure Grid) [SFinite σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ) :
    Measurable (unmarkedValue σ Ψ) := by
  refine Measurable.of_eval fun n => ?_
  have hcoords : Measurable fun e : Env =>
      (fun i : Fin 2 => Real.tan (∫ D, codedCoordinate Ψ n i (e, D) ∂σ)) := by
    refine Measurable.of_eval fun i => ?_
    refine measurable_tan.comp ?_
    have hint := (measurable_codedCoordinate hΨ n i).stronglyMeasurable.integral_prod_right'
      (ν := σ)
    exact hint.measurable
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp hcoords

/-- **Inversion of the coding on a point mass.** If the grid-conditional law of the marked field
is the point mass at `c`, the descended field is exactly `c`. -/
theorem unmarkedValue_eq_of_ae_eq (σ : Measure Grid) [IsProbabilityMeasure σ]
    (Ψ : MarkedEnvironment → ℕ → Plane) (e : Env) (c : ℕ → Plane)
    (h : ∀ᵐ D ∂σ, Ψ (e, D) = c) : unmarkedValue σ Ψ e = c := by
  funext n
  refine plane_ext fun i => ?_
  have hint : (∫ D, codedCoordinate Ψ n i (e, D) ∂σ) = Real.arctan (planeCoord (c n) i) := by
    have hae : ∀ᵐ D ∂σ, codedCoordinate Ψ n i (e, D) = Real.arctan (planeCoord (c n) i) := by
      filter_upwards [h] with D hD
      simp [codedCoordinate, hD]
    rw [integral_congr_ae hae, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [planeCoord_unmarkedValue, hint, Real.tan_arctan]

/-! ### The descent theorem -/

/-- **The measure-theoretic descent.** Two independent grid copies that produce the same field
almost surely force the marked field to be, for almost every environment, almost surely equal to
the environment-measurable field `unmarkedValue`. The proof is the manuscript's: bounded
arctangent coding, zero conditional variance, inversion of the coding. -/
theorem ae_ae_eq_unmarkedValue (ν : Measure Env) [SFinite ν] (σ : Measure Grid)
    [IsProbabilityMeasure σ] {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    (hcopies : ∀ᵐ p : Env × Grid × Grid ∂ν.prod (σ.prod σ),
      Ψ (p.1, p.2.1) = Ψ (p.1, p.2.2)) :
    ∀ᵐ e ∂ν, ∀ᵐ D ∂σ, Ψ (e, D) = unmarkedValue σ Ψ e := by
  have hsplit := Measure.ae_ae_of_ae_prod hcopies
  filter_upwards [hsplit] with e he
  have key : ∀ (n : ℕ) (i : Fin 2), ∀ᵐ D ∂σ,
      codedCoordinate Ψ n i (e, D) = ∫ D', codedCoordinate Ψ n i (e, D') ∂σ := by
    intro n i
    refine ae_eq_integral_of_ae_prod_eq σ (fun D => codedCoordinate Ψ n i (e, D)) (Real.pi / 2)
      (measurable_codedCoordinate_grid hΨ n i e) (fun D => abs_codedCoordinate_le Ψ n i (e, D)) ?_
    filter_upwards [he] with q hq
    simp [codedCoordinate, hq]
  have key2 : ∀ᵐ D ∂σ, ∀ (n : ℕ) (i : Fin 2),
      codedCoordinate Ψ n i (e, D) = ∫ D', codedCoordinate Ψ n i (e, D') ∂σ :=
    ae_all_iff.2 fun n => ae_all_iff.2 fun i => key n i
  filter_upwards [key2] with D hD
  funext n
  refine plane_ext fun i => ?_
  rw [planeCoord_unmarkedValue, ← hD n i]
  simp [codedCoordinate, Real.tan_arctan]

/-! ### The invariant good set and the exactly covariant version -/

/-- Equality of two measurable countable-label fields is a measurable event; the equality is
tested on the countably many real coordinates. -/
theorem measurableSet_fieldEq {α : Type*} [MeasurableSpace α] {f g : α → ℕ → Plane}
    (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} := by
  have hset : {x | f x = g x} =
      ⋂ n : ℕ, ⋂ i : Fin 2, {x | planeCoord (f x n) i = planeCoord (g x n) i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h _ _
      rw [h]
    · intro h
      funext n
      exact plane_ext fun i => h n i
  rw [hset]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun i => measurableSet_eq_fun ?_ ?_
  · exact (measurable_planeCoord i).comp ((measurable_pi_apply n).comp hf)
  · exact (measurable_planeCoord i).comp ((measurable_pi_apply n).comp hg)

/-- The manuscript's good set: the unmarked environments whose grid-conditional field law is the
point mass at the descended value. -/
def DescentGood (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane) : Set Env :=
  {e | ∀ᵐ D ∂σ, Ψ (e, D) = unmarkedValue σ Ψ e}

theorem mem_descentGood_iff (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane) (e : Env) :
    e ∈ DescentGood σ Ψ ↔ ∀ᵐ D ∂σ, Ψ (e, D) = unmarkedValue σ Ψ e := Iff.rfl

theorem measurableSet_descentGood (σ : Measure Grid) [SFinite σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ) :
    MeasurableSet (DescentGood σ Ψ) := by
  set S : Set MarkedEnvironment := {ω | Ψ ω = unmarkedValue σ Ψ ω.1} with hS
  have hSmeas : MeasurableSet S :=
    measurableSet_fieldEq hΨ ((measurable_unmarkedValue σ hΨ).comp measurable_fst)
  have hfun : Measurable fun e : Env => σ (Prod.mk e ⁻¹' Sᶜ) :=
    measurable_measure_prodMk_left hSmeas.compl
  have hEq : DescentGood σ Ψ = (fun e : Env => σ (Prod.mk e ⁻¹' Sᶜ)) ⁻¹' {0} := by
    ext e
    simp only [DescentGood, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff, ae_iff]
    rfl
  rw [hEq]
  exact hfun (measurableSet_singleton 0)

/-- Almost every environment is good: immediate from the descent. -/
theorem ae_mem_descentGood (ν : Measure Env) [SFinite ν] (σ : Measure Grid)
    [IsProbabilityMeasure σ] {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    (hcopies : ∀ᵐ p : Env × Grid × Grid ∂ν.prod (σ.prod σ),
      Ψ (p.1, p.2.1) = Ψ (p.1, p.2.2)) :
    ∀ᵐ e ∂ν, e ∈ DescentGood σ Ψ :=
  ae_ae_eq_unmarkedValue ν σ hΨ hcopies

/-- The transport data of one similarity: a measure-preserving action on grids under which the
marked field at `e'` is the image of the marked field at `e`. A similarity sends a uniform grid
to a uniform grid and the marked field transforms covariantly, so this is what the grid-dilation
producer supplies; nothing about it is proved here. -/
def GridTransfer (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane)
    (T : (ℕ → Plane) → (ℕ → Plane)) (e e' : Env) : Prop :=
  ∃ act : Grid → Grid, MeasurePreserving act σ σ ∧ ∀ D : Grid, Ψ (e', act D) = T (Ψ (e, D))

/-- **Exact transport of the descended value.** A grid-conditional point mass is carried to a
grid-conditional point mass, and the descended field is carried by the same map `T`. -/
theorem unmarkedValue_eq_of_gridTransfer (σ : Measure Grid) [IsProbabilityMeasure σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    {T : (ℕ → Plane) → (ℕ → Plane)} {e e' : Env} (htr : GridTransfer σ Ψ T e e')
    (he : e ∈ DescentGood σ Ψ) :
    e' ∈ DescentGood σ Ψ ∧ unmarkedValue σ Ψ e' = T (unmarkedValue σ Ψ e) := by
  obtain ⟨act, hact, hcov⟩ := htr
  have h1 : ∀ᵐ D ∂σ, Ψ (e', act D) = T (unmarkedValue σ Ψ e) := by
    filter_upwards [he] with D hD
    rw [hcov D, hD]
  have hSm : MeasurableSet {D : Grid | Ψ (e', D) = T (unmarkedValue σ Ψ e)} :=
    measurableSet_fieldEq (hΨ.comp (measurable_const.prodMk measurable_id)) measurable_const
  have h2 : ∀ᵐ D ∂σ, Ψ (e', D) = T (unmarkedValue σ Ψ e) := by
    have hpush := (ae_map_iff (μ := σ) hact.measurable.aemeasurable hSm).2 h1
    rwa [hact.map_eq] at hpush
  have hval : unmarkedValue σ Ψ e' = T (unmarkedValue σ Ψ e) :=
    unmarkedValue_eq_of_ae_eq σ Ψ e' _ h2
  refine ⟨?_, hval⟩
  rw [mem_descentGood_iff, hval]
  exact h2

/-- The good set is invariant under any similarity for which the grid actions exist in both
directions. -/
theorem mem_descentGood_iff_of_gridTransfer (σ : Measure Grid) [IsProbabilityMeasure σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    {T T' : (ℕ → Plane) → (ℕ → Plane)} {e e' : Env} (htr : GridTransfer σ Ψ T e e')
    (htr' : GridTransfer σ Ψ T' e' e) :
    e ∈ DescentGood σ Ψ ↔ e' ∈ DescentGood σ Ψ :=
  ⟨fun he => (unmarkedValue_eq_of_gridTransfer σ hΨ htr he).1,
   fun he' => (unmarkedValue_eq_of_gridTransfer σ hΨ htr' he').1⟩

/-- **The exactly covariant unmarked field**: the value of the grid-conditional point mass on the
invariant good set, and the zero field elsewhere. -/
noncomputable def descentField (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane) :
    Env → ℕ → Plane :=
  Set.indicator (DescentGood σ Ψ) (unmarkedValue σ Ψ)

theorem descentField_of_mem (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane) {e : Env}
    (he : e ∈ DescentGood σ Ψ) : descentField σ Ψ e = unmarkedValue σ Ψ e :=
  Set.indicator_of_mem he _

theorem descentField_of_notMem (σ : Measure Grid) (Ψ : MarkedEnvironment → ℕ → Plane) {e : Env}
    (he : e ∉ DescentGood σ Ψ) : descentField σ Ψ e = 0 :=
  Set.indicator_of_notMem he _

theorem measurable_descentField (σ : Measure Grid) [IsProbabilityMeasure σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ) :
    Measurable (descentField σ Ψ) :=
  (measurable_unmarkedValue σ hΨ).indicator (measurableSet_descentGood σ hΨ)

/-- On almost every environment the covariant field still is the marked field. -/
theorem ae_ae_eq_descentField (ν : Measure Env) [SFinite ν] (σ : Measure Grid)
    [IsProbabilityMeasure σ] {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    (hcopies : ∀ᵐ p : Env × Grid × Grid ∂ν.prod (σ.prod σ),
      Ψ (p.1, p.2.1) = Ψ (p.1, p.2.2)) :
    ∀ᵐ e ∂ν, ∀ᵐ D ∂σ, Ψ (e, D) = descentField σ Ψ e := by
  filter_upwards [ae_ae_eq_unmarkedValue ν σ hΨ hcopies,
    ae_mem_descentGood ν σ hΨ hcopies] with e he hgood
  rw [descentField_of_mem σ Ψ hgood]
  exact he

/-- **Exact covariance of the unmarked field.** With the grid actions in both directions the
covariant field commutes with the transport map `T`, on the good set by transport of the point
mass and off it because both sides are the zero field. -/
theorem descentField_covariant (σ : Measure Grid) [IsProbabilityMeasure σ]
    {Ψ : MarkedEnvironment → ℕ → Plane} (hΨ : Measurable Ψ)
    {T T' : (ℕ → Plane) → (ℕ → Plane)} {e e' : Env} (htr : GridTransfer σ Ψ T e e')
    (htr' : GridTransfer σ Ψ T' e' e) (hT0 : T 0 = 0) :
    descentField σ Ψ e' = T (descentField σ Ψ e) := by
  by_cases he : e ∈ DescentGood σ Ψ
  · obtain ⟨he', hval⟩ := unmarkedValue_eq_of_gridTransfer σ hΨ htr he
    rw [descentField_of_mem σ Ψ he', descentField_of_mem σ Ψ he, hval]
  · have he' : e' ∉ DescentGood σ Ψ := fun h =>
      he ((mem_descentGood_iff_of_gridTransfer σ hΨ htr htr').2 h)
    rw [descentField_of_notMem σ Ψ he', descentField_of_notMem σ Ψ he, hT0]

end UnmarkedCoordinateDescent

end ReflectedGMS
