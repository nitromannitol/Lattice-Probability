/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108K1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryLaw
import Mathlib.Probability.Moments.Covariance

/-!
# CONF Lemma 2.10 (FKG for the zero-boundary GFF) and Proposition 2.8 in frozen form

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`: Proposition 2.8 (`prop-fkg-metric`, C:656–661,
proof C:748–752), Lemma 2.10 (`lem-fkg-gff`, C:712–742), and its use in Step 3 of Lemma 3.3
(C:1236–1243): "under the conditional law given `h|_{ℂ∖U}`, both `𝟙_{G^U}` and `𝟙_{F_r(z)}` are
non-increasing functions of the metric … a.s. continuous … By Proposition 2.8, the events
`F_r(z)` and `G^U` are positively correlated under the conditional law given `h|_{ℂ∖U}`."

* `IsZBExtField U X P`: `X : Ω → 𝒟'(ℂ)` is the zero-boundary GFF on `U` extended by `0`, as a
  law statement (`φ ↦ ⟨X, φ⟩`, `φ ∈ 𝓓(ℂ)`, is centred Gaussian with covariance
  `⟨φ 1_U, ψ 1_U⟩_{H⁻¹(U)}`; cf. `IsZBGFFProcessExt.extZero`);
* `IsFKGFunZB P X Φ`: `Φ : 𝒟'(ℂ) → ℝ` bounded, measurable, a.s. non-decreasing at `X` along
  continuous perturbations `X + f`, and a.s. continuous at `X` along continuous perturbations
  tending to `0` locally uniformly (CONF L2.10's hypotheses);
* `CONFLem2_10`: **CONF Lemma 2.10** (the statement of a published result; open node);
* `prob_mul_le_of_cov_nonneg`: `Cov(𝟙_A(X), 𝟙_B(X)) ≥ 0 ⇒ P[X ∈ A] P[X ∈ B] ≤ P[X ∈ A ∩ B]`;
* `fkg_sets_zb_of_lem2_10`: two a.s.-decreasing, a.s.-continuous events of the zero-boundary GFF
  are positively correlated (from `CONFLem2_10` applied to `−𝟙_A`, `−𝟙_B`);
* **`confProp2_8_frozen`**: the frozen form consumed by `condFKG_freeze2` (S3D108A,
  hypothesis `hfkg`): for `SG, SF ⊆ β × 𝒟'(ℂ)` whose sections are, for a.e. frozen `w`,
  a.s. decreasing and a.s. continuous in the zero-boundary field, for a.e. `w`
  `P_X(SG_w) P_X(SF_w) ≤ P_X(SG_w ∩ SF_w)`.

Modelling (proposed DEVIATIONS entry DV-CONFFKG-1): the field is `𝒟'(ℂ)`-valued (the
zero-boundary GFF extended by `0`; CONF: a distribution on `U`) so that the metric `D_{𝔥 + x}`
is defined, and its law is pinned on all of `𝓓(ℂ)`: with only `X|_U` a zero-boundary GFF and
`X = 0` off `cl U`, a random dipole layer on `∂U` independent of `X|_U` would be detected by a
shift-invariant measurable functional and break the lemma. The perturbations in `IsFKGFunZB`
are `f ∈ C(ℂ, ℝ)` (CONF: continuous functions on `U`), because Weyl scaling (Axiom III)
`IsWeakLQGMetric.weyl` is stated for `f ∈ C(ℂ, ℝ)`; monotonicity and continuity are required
almost surely at the sample `X` (CONF: for every distribution), because for metric events they
come from the a.s. Weyl identity. "a.s. continuous" is read with deterministic sequences
`fₙ → 0` in `C(ℂ, ℝ)` (compact-open topology) under a single a.s. quantifier, which covers
CONF's random sequences.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

/-- `X : Ω → 𝒟'(ℂ)` is the zero-boundary GFF on `U` extended by `0` (law statement): its
pairings with `𝓓(ℂ)` form a centred Gaussian process with covariance
`zeroGFFTestCov U (φ 1_U) (ψ 1_U)` (the process of `IsZBGFFProcessExt.extZero`) -/
structure IsZBExtField {Ω : Type} [MeasurableSpace Ω] (U : TopologicalSpace.Opens ℂ)
    (X : Ω → DistC) (P : Measure Ω) : Prop where
  measurable : Measurable X
  gaussian : IsGaussianProcess (fun (φ : TestC) ω => X ω φ) P
  centered : ∀ φ : TestC, ∫ ω, X ω φ ∂P = 0
  covariance_eq : ∀ φ ψ : TestC, cov[fun ω => X ω φ, fun ω => X ω ψ; P] =
    QuantumZipper.zeroGFFTestCov U ((U : Set ℂ).indicator φ) ((U : Set ℂ).indicator ψ)

/-- the hypotheses of CONF Lemma 2.10 on a functional `Φ : 𝒟'(ℂ) → ℝ` at the field `X`
(C:715–718): bounded, measurable, non-decreasing under continuous non-negative perturbations, and
continuous along continuous perturbations tending to `0` (a.s. at the sample of `X`) -/
structure IsFKGFunZB {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → DistC) (Φ : DistC → ℝ) : Prop where
  meas : Measurable Φ
  bdd : ∃ C : ℝ, ∀ x, |Φ x| ≤ C
  mono : ∀ᵐ ω ∂P, ∀ f g : C(ℂ, ℝ), f ≤ g → Φ (addFun (X ω) f) ≤ Φ (addFun (X ω) g)
  cont : ∀ᵐ ω ∂P, ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
    Tendsto (fun n => Φ (addFun (X ω) (fn n))) atTop (𝓝 (Φ (X ω)))

section Events

variable {Ω α : Type} [MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- a nonnegative covariance of two indicators is positive correlation of the events -/
lemma prob_mul_le_of_cov_nonneg {X : Ω → α} (hX : Measurable X) {A B : Set α}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hcov : 0 ≤ cov[fun ω => A.indicator (1 : α → ℝ) (X ω),
      fun ω => B.indicator (1 : α → ℝ) (X ω); P]) :
    P.map X A * P.map X B ≤ P.map X (A ∩ B) := by
  have ei : ∀ S : Set α, (fun ω => S.indicator (1 : α → ℝ) (X ω)) = (X ⁻¹' S).indicator 1 :=
    fun S => funext fun ω => rfl
  have hL : ∀ S : Set α, MeasurableSet S → MemLp (fun ω => S.indicator (1 : α → ℝ) (X ω)) 2 P :=
    fun S hS => by
      rw [ei S]
      exact (memLp_const (1 : ℝ)).indicator (hX hS)
  rw [covariance_eq_sub (hL A hA) (hL B hB)] at hcov
  have hmul : (fun ω => A.indicator (1 : α → ℝ) (X ω)) * (fun ω => B.indicator (1 : α → ℝ) (X ω))
      = (X ⁻¹' (A ∩ B)).indicator 1 := by
    rw [ei A, ei B, preimage_inter, inter_indicator_one]
  rw [hmul, ei A, ei B, integral_indicator_one (hX (hA.inter hB)),
    integral_indicator_one (hX hA), integral_indicator_one (hX hB)] at hcov
  rw [Measure.map_apply hX hA, Measure.map_apply hX hB, Measure.map_apply hX (hA.inter hB),
    ← ofReal_measureReal (measure_ne_top _ _), ← ofReal_measureReal (measure_ne_top _ _),
    ← ofReal_measureReal (measure_ne_top _ _),
    ← ENNReal.ofReal_mul measureReal_nonneg]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end Events

section FKGSets

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : TopologicalSpace.Opens ℂ}

omit [IsProbabilityMeasure P] in
/-- the indicator of an a.s.-decreasing, a.s.-continuous event, negated, satisfies the hypotheses
of CONF Lemma 2.10 -/
lemma isFKGFunZB_neg_indicator {X : Ω → DistC} {A : Set DistC} (hA : MeasurableSet A)
    (hmono : ∀ᵐ ω ∂P, ∀ f g : C(ℂ, ℝ), f ≤ g → addFun (X ω) g ∈ A → addFun (X ω) f ∈ A)
    (hcont : ∀ᵐ ω ∂P, ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
      ∀ᶠ n in atTop, (addFun (X ω) (fn n) ∈ A ↔ X ω ∈ A)) :
    IsFKGFunZB P X (fun x => -A.indicator (1 : DistC → ℝ) x) := by
  refine ⟨(measurable_const.indicator hA).neg, ⟨1, fun x => ?_⟩, ?_, ?_⟩
  · by_cases hx : x ∈ A <;> simp [hx]
  · filter_upwards [hmono] with ω hω f g hfg
    by_cases hg : addFun (X ω) g ∈ A
    · simp [hg, hω f g hfg hg]
    · simp only [hg, not_false_eq_true, indicator_of_notMem, neg_zero, Left.neg_nonpos_iff]
      exact indicator_nonneg (fun _ _ => zero_le_one) _
  · filter_upwards [hcont] with ω hω fn hfn
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω fn hfn] with n hn
    by_cases hx : X ω ∈ A
    · simp [hx, hn.2 hx]
    · simp [hx, mt hn.1 hx]

end FKGSets

section Congr

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

/-- positive correlation passes to a.e.-equal events -/
lemma mul_le_inter_congr_ae {ν : Measure α} {A A' B B' : Set α} (hA : A =ᵐ[ν] A')
    (hB : B =ᵐ[ν] B') (h : ν A' * ν B' ≤ ν (A' ∩ B')) : ν A * ν B ≤ ν (A ∩ B) := by
  rw [measure_congr hA, measure_congr hB, measure_congr (hA.inter hB)]
  exact h

/-- the frozen positive correlation passes to events whose sections are a.e. equal for a.e.
frozen datum (e.g. a `D_{G w + x}`-event and the same event written through the zero-boundary
metric of CONF Remark 1.2) -/
lemma frozen_fkg_congr_ae {μ : Measure β} {ν : Measure α} {SG SF SG' SF' : Set (β × α)}
    (hG : ∀ᵐ w ∂μ, Prod.mk w ⁻¹' SG =ᵐ[ν] Prod.mk w ⁻¹' SG')
    (hF : ∀ᵐ w ∂μ, Prod.mk w ⁻¹' SF =ᵐ[ν] Prod.mk w ⁻¹' SF')
    (h : ∀ᵐ w ∂μ, ν (Prod.mk w ⁻¹' SG') * ν (Prod.mk w ⁻¹' SF') ≤
      ν (Prod.mk w ⁻¹' SG' ∩ Prod.mk w ⁻¹' SF')) :
    ∀ᵐ w ∂μ, ν (Prod.mk w ⁻¹' SG) * ν (Prod.mk w ⁻¹' SF) ≤
      ν (Prod.mk w ⁻¹' SG ∩ Prod.mk w ⁻¹' SF) := by
  filter_upwards [hG, hF, h] with w h1 h2 h3
  exact mul_le_inter_congr_ae h1 h2 h3

end Congr

end LQGMetric.CONF
