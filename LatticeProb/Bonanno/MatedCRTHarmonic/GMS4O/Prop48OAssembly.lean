/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4O.Prop48OAssembly at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48Statement

/-!
# Proposition 4.8 without the uniform regularity event

[18] proves Proposition 4.8 on the uniform event `E^ε ⊂ ⋂_{z ∈ B_ρ} F^ε(z)` of Proposition 4.5
, whose degree part needs the
superpolynomial tail of Lemma 4.6. Here the uniform event is replaced by a **per-point truncation
estimate**: for a test pair `(D, f)` with `N = ‖f‖_∞` and a threshold `thr`, let

* `B = {∫⁻_D f(z) 1_{F(z)^c} u_*(z) dz ≤ thr}` (`p48oSmallError`),
* `localEvent z = F(z) ∪ B`, `goodEvent = B ∩ {∫⁻_{B_ρ} u_* < ∞}` (`p48oGood`).

On `goodEvent` every local event holds, so the truncated and untruncated integrals agree; the
record fluctuation differs from the source fluctuation `∫_D f (1_F u_* − m)` by at most `thr`
(`p48o_fluct_sq_le`); and Markov plus Tonelli bound `P(B^c)` by the pointwise truncation errors
`E[1_{F(z)^c} u_*(z)]` (`p48o_smallError_compl_le`). With `thr = ε^{2α} N`:

* `p48o_fixedTestInputs`: the record's lower inputs (`Prop48WholePlaneFixedTestInputs`) follow from
  a pointwise truncation bound `E[1_{F(z)^c} u_*(z)] ≤ C₁ ε^{3α}` (for `z ∈ B_ρ`) and the source
  second-moment bound `E[(∫_D f(1_F u_* − m))²] ≤ C₀ ε^{3α} N²`;
* `p48o_allScalesProducer`: the all-scales producer `GMS4.Prop48WholePlaneAllScalesProducer` of
  the `GMS4/Prop48Statement.lean`, with the exponent chosen before `ρ`.

The conditional mean `m` is any jointly measurable version bounded by the constant `A` of (4.27)
(on the canonical coupling: `p48oCondMeanJoint` of `GMS4O/Prop48OCondMean.lean`).

**Caveats.** (1) The legacy target does not pin the realized density: its realization record fixes
only the domain, test and mean constant, so it is also satisfied by a zero record. The canonical
statement (`GMS4.Canonical.*`) supersedes it; this file records the per-point truncation mechanism.
(2) The pointwise truncation bound needs an unmasked moment of `u_*(z)` (a crude, polynomial-in-`ε⁻¹`
bound uniform over `z ∈ B_ρ` suffices), hence degree moments at single points; it saves the union
bound behind the uniform event of Proposition 4.5, not the degree tails themselves.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4O

open MatedCRTHarmonic.GMS4

/-! ### Fixed-scale data -/

/-- Fixed-scale data of the localized observable of Proposition 4.8 on `(Ω, P)`, for test
pairs supported in `B_ρ(0)`. `uStar` is the density `u_*^ε`, `F z` the local event `F^ε(z)`, and `m`
a version of the conditional mean (4.27), bounded by `A`. -/
structure P48OScaleData {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ρ : ℝ) where
  uStar : Ω → ℂ → ℝ
  F : ℂ → Set Ω
  m : Ω → ℂ → ℝ
  A : ℝ
  measurable_uStar : Measurable fun p : Ω × ℂ => uStar p.1 p.2
  measurableSet_F : MeasurableSet {p : Ω × ℂ | p.1 ∈ F p.2}
  measurable_m : Measurable fun p : Ω × ℂ => m p.1 p.2
  uStar_nonneg : ∀ ω z, 0 ≤ uStar ω z
  m_nonneg : ∀ ω z, 0 ≤ m ω z
  m_le : ∀ ω z, m ω z ≤ A
  ae_lintegral_lt_top :
    ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) ρ, ENNReal.ofReal (uStar ω z) < ⊤

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ρ : ℝ}

/-- The test function extended by zero outside `B_ρ(0)`; it is measurable for admissible pairs. -/
def p48oTestExt (ρ : ℝ) (f : ℂ → ℝ) : ℂ → ℝ := (ball (0 : ℂ) ρ).indicator f

lemma measurable_p48oTestExt {f : ℂ → ℝ}
    (hf : Measurable fun z : ball (0 : ℂ) ρ => f z) : Measurable (p48oTestExt ρ f) := by
  refine measurable_of_restrict_of_restrict_compl (measurableSet_ball (x := (0 : ℂ)) (ε := ρ)) ?_ ?_
  · have e : (ball (0 : ℂ) ρ).domRestrict (p48oTestExt ρ f) = fun z : ball (0 : ℂ) ρ => f z := by
      funext z
      simp [p48oTestExt, Set.domRestrict, z.2]
    rw [e]
    exact hf
  · have e : (ball (0 : ℂ) ρ)ᶜ.domRestrict (p48oTestExt ρ f) = fun _ => (0 : ℝ) := by
      funext z
      simp [p48oTestExt, Set.domRestrict, (Set.mem_compl_iff _ _).1 z.2]
    rw [e]
    exact measurable_const

lemma p48oTestExt_eq_of_mem {f : ℂ → ℝ} {z : ℂ} (hz : z ∈ ball (0 : ℂ) ρ) :
    p48oTestExt ρ f z = f z := by
  simp [p48oTestExt, hz]

/-! ### The localized observable record

The source's test functions are measurable on `B_ρ(0) ⊂ ℂ`. Since the c10 repair this is the
admissibility clause `Prop48TestPairAdmissible.test_measurable` (it previously ranged over
`Metric.ball (0 : ℕ) ρ` and was vacuous); `P48OTestMeasurable` names the same statement. -/

/-- The source's measurability of a test function: measurable on `B_ρ(0) ⊂ ℂ`. -/
def P48OTestMeasurable (ρ : ℝ) (f : ℂ → ℝ) : Prop :=
  Measurable fun z : ball (0 : ℂ) ρ => f z

section Record

variable (S : P48OScaleData P ρ) {D : Set ℂ} {f : ℂ → ℝ}

lemma p48o_volume_lt_top_of_admissible (hadm : Prop48TestPairAdmissible ρ D f) :
    volume D < ⊤ :=
  (measure_mono hadm.domain_subset_ball).trans_lt measure_ball_lt_top

lemma p48o_abs_test_le (hadm : Prop48TestPairAdmissible ρ D f) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) ρ) : |f z| ≤ prop48TestSupNorm ρ f :=
  abs_le_prop48TestSupNorm hadm.test_bounded hz

lemma p48o_test_nonneg (hadm : Prop48TestPairAdmissible ρ D f) {z : ℂ} (hz : z ∈ D) :
    0 ≤ f z :=
  hadm.test_nonnegative z (hadm.domain_subset_ball hz)

/-- `f · g` is integrable on `D` for bounded measurable `g`. -/
lemma p48o_integrableOn_test_mul (hadm : Prop48TestPairAdmissible ρ D f)
    (hfm : P48OTestMeasurable ρ f) {g : ℂ → ℝ}
    (hg : Measurable g) {M : ℝ} (hgM : ∀ z, |g z| ≤ M) :
    IntegrableOn (fun z => f z * g z) D := by
  have hint : IntegrableOn (fun z => p48oTestExt ρ f z * g z) D := by
    refine IntegrableOn.of_bound (p48o_volume_lt_top_of_admissible hadm)
      (((measurable_p48oTestExt hfm).mul hg).aestronglyMeasurable)
      (prop48TestSupNorm ρ f * M) ?_
    refine (ae_restrict_iff' hadm.domain_borel).2 (Eventually.of_forall fun z hz => ?_)
    rw [Real.norm_eq_abs, abs_mul, p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]
    exact mul_le_mul (p48o_abs_test_le hadm (hadm.domain_subset_ball hz)) (hgM z)
      (abs_nonneg _) ((abs_nonneg _).trans (p48o_abs_test_le hadm (hadm.domain_subset_ball hz)))
  refine hint.congr_fun (fun z hz => ?_) hadm.domain_borel
  simp only
  rw [p48oTestExt_eq_of_mem (hadm.domain_subset_ball hz)]

end Record

/-! ### The two estimates -/

section Estimates

variable (S : P48OScaleData P ρ) {D : Set ℂ} {f : ℂ → ℝ}

lemma p48o_volume_le_pi (hadm : Prop48TestPairAdmissible ρ D f) (hρ : ρ ≤ 1) :
    volume D ≤ ENNReal.ofReal Real.pi := by
  calc volume D ≤ volume (ball (0 : ℂ) 1) :=
        measure_mono (hadm.domain_subset_ball.trans (ball_subset_ball hρ))
    _ = ENNReal.ofReal Real.pi := by
        rw [Complex.volume_ball, ENNReal.ofReal_one, one_pow, one_mul, ← NNReal.coe_real_pi,
          ENNReal.ofReal_coe_nnreal]

end Estimates

/-! ### Fixed-scale bounds and the producers -/

section Producer

variable {R : GMSA.WholePlaneRootedLQGLaw Ω}

end Producer

/-! ### All scales -/

end MatedCRTHarmonic.GMS4O
