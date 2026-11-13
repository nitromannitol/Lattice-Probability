/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase1.Transfer at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase1.JointLaw
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop410
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.SmallRootMass

/-!
# [18] Proposition 4.10, Case 1: the Hölder transfer of (4.40)

Source: [18, Proposition 4.10, Cases 1–2]. With `h₀` the unit-normalized
whole-plane GFF of the coupling and `h₁` the rooted field (`JointLaw.lean`):

* "Since `μ_{h₀}(𝔻)` has a finite `p`th moment for some `p > 1` [RV14, Theorem 2.11] and by
  Hölder's inequality, (4.40) for `h = h₁` … follows from (4.40) for `h = h₀`" — here
  `case1Moment_lt_top` (every `p < 4/γ²`, and `4/γ² > 1`) and `case1_rooted_event_le`: for
  every measurable event `G` of the whole-plane data,
  `P⊗λ[(h₁, aux) ∈ G] ≤ (E[(μ_{h₀}(𝔻)/π)^p])^{1/p} · P[(h₀, aux) ∈ G]^{1/q}`.
* "(4.40) also holds with `h` sampled from the conditional law of `h₁` given `{z ∈ B_{ε^ξ}(0)}`"
  — `case1_smallRoot_event_le`: conditioning on the root event divides by its mass
  `rootMeasure (B_r(0)) = r²` (`GMS4.GMSA.normalizedLebesgueOnRootingDisk_ball`).
* Almost-sure properties of the unrooted data transfer to the rooted data
  (`ae_rootedWPData_of_ae`): the rooted law is absolutely continuous.

The events `G` are arbitrary Borel sets of `WPData`; in particular they may read the GMC area of
The field, the area-time curve (the area-scaling construction's `JointScalingO.parEval γ h ηL`), and the full IG field
`hIG₀ + U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase1

open LQGMetric MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-! ## Event form of the Case 1 law -/

/-- The probability of a data event under the unrooted law is its mass under the data law. -/
theorem measure_wpData_preimage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {G : Set WPData} (hG : MeasurableSet G) :
    P (wpData X₀ hIG₀ U ηL ⁻¹' G) = P.map (wpData X₀ hIG₀ U ηL) G :=
  (Measure.map_apply_of_aemeasurable (aemeasurable_wpData D hγ) hG).symm

/-- **Case 1, event form.** The rooted probability of a data event is its area-weighted unrooted
mass. -/
theorem measure_rootedWPData_preimage
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {G : Set WPData} (hG : MeasurableSet G) :
    Canon.rootedLaw P (rootedWPData γ X₀ hIG₀ U ηL ⁻¹' G) =
      (P.map (wpData X₀ hIG₀ U ηL)).withDensity (fun x => areaDensity γ x.1) G := by
  rw [← map_rootedWPData_eq_withDensity D hγ,
    Measure.map_apply_of_aemeasurable (aemeasurable_rootedWPData D hγ) hG]

/-! ## The density moment -/

/-- The `p`-th moment of the Case 1 density `μ_{h₀}(𝔻)/π`. -/
def case1Moment (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ((Canon.referenceSample D hγ ω).wholePlaneArea (ball 0 1) /
    ENNReal.ofReal Real.pi) ^ p ∂P

/-- The moment computed on the data carrier with the measurable density. -/
theorem lintegral_areaDensity_rpow_eq_case1Moment
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (p : ℝ) :
    ∫⁻ x, areaDensity γ x.1 ^ p ∂(P.map (wpData X₀ hIG₀ U ηL)) = case1Moment D hγ p := by
  rw [lintegral_map' (f := fun x : WPData => areaDensity γ x.1 ^ p)
    (((measurable_areaDensity γ).comp measurable_fst).pow_const p).aemeasurable
    (aemeasurable_wpData D hγ)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_areaDensity_wpField_eq D hγ] with ω hω
  change areaDensity γ (wpField X₀ ω) ^ p = _
  rw [hω]

/-- **[RV14, Theorem 2.11] as used by [18] Case 1**: the density `μ_{h₀}(𝔻)/π` has finite
moments of every order `0 < p < 4/γ²`. -/
theorem case1Moment_lt_top
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {p : ℝ} (hp0 : 0 < p) (hp : p < 4 / γ ^ 2) :
    case1Moment D hγ p < ⊤ := by
  have hm := lintegral_unitDiskMass_rpow_lt_top (isNormalizedWPGFF_wpField D) hγ hp0 hp
  have hpi : (ENNReal.ofReal Real.pi)⁻¹ ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0.le
      (ENNReal.inv_ne_top.2 (ne_of_gt (ENNReal.ofReal_pos.2 Real.pi_pos)))
  have e : ∀ ω, ((Canon.referenceSample D hγ ω).wholePlaneArea (ball 0 1) /
      ENNReal.ofReal Real.pi) ^ p =
      CellScaling.lqgArea γ (wpField X₀ ω) (ball 0 1) ^ p * (ENNReal.ofReal Real.pi)⁻¹ ^ p := by
    intro ω
    rw [div_eq_mul_inv, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    rfl
  rw [case1Moment, lintegral_congr fun ω => e ω, lintegral_mul_const' _ _ hpi]
  exact ENNReal.mul_lt_top hm (lt_top_iff_ne_top.2 hpi)

/-- A Hölder exponent `1 < p < 4/γ²` exists for every `γ ∈ (0, 2)`. -/
theorem exists_case1_exponent (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    ∃ p : ℝ, 1 < p ∧ p < 4 / γ ^ 2 := by
  have hγ2 : γ ^ 2 < 4 := by nlinarith [hγ.1, hγ.2]
  have h1 : 1 < 4 / γ ^ 2 := (one_lt_div (pow_pos hγ.1 2)).2 hγ2
  exact ⟨(1 + 4 / γ ^ 2) / 2, by linarith, by linarith⟩

/-! ## The Hölder transfer -/

/-- **[18] Proposition 4.10, Case 1 (Hölder step).** For every Borel event `G` of the whole-plane
data and Hölder conjugates `p, q`, a bound `P[(h₀, aux) ∈ G] ≤ δ` implies
`P⊗λ[(h₁, aux) ∈ G] ≤ (E[(μ_{h₀}(𝔻)/π)^p])^{1/p} · δ^{1/q}`. -/
theorem case1_rooted_event_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {G : Set WPData} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {δ : ℝ≥0∞}
    (hbad : P (wpData X₀ hIG₀ U ηL ⁻¹' G) ≤ δ) :
    Canon.rootedLaw P (rootedWPData γ X₀ hIG₀ U ηL ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) := by
  rw [measure_rootedWPData_preimage D hγ hG, ← lintegral_areaDensity_rpow_eq_case1Moment D hγ]
  rw [measure_wpData_preimage D hγ hG] at hbad
  exact GMS4.withDensity_badEvent_le_holder _ _
    ((measurable_areaDensity γ).comp measurable_fst).aemeasurable hG hpq hbad

/-! ## Conditioning on a small root -/

/-- The marked-root event `{z ∈ B_r(0)}` on the marked carrier. -/
def smallRootEvent (Ω : Type) (r : ℝ) : Set (Ω × ℂ) := univ ×ˢ ball (0 : ℂ) r

theorem measurableSet_smallRootEvent (r : ℝ) : MeasurableSet (smallRootEvent Ω r) :=
  MeasurableSet.univ.prod measurableSet_ball

/-- The small-root event has probability `rootMeasure (B_r(0))` (`= r²` for `r ≤ 1`). -/
theorem rootedLaw_smallRootEvent
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (r : ℝ) :
    Canon.rootedLaw P (smallRootEvent Ω r) = Canon.rootMeasure (ball (0 : ℂ) r) := by
  have : IsProbabilityMeasure P := D.isProbabilityMeasure
  rw [Canon.rootedLaw, smallRootEvent, Measure.prod_prod, measure_univ, one_mul]

/-- **Case 1, conditioned on a small root.** Under the conditional law of `P⊗λ` given
`{z ∈ B_r(0)}`, the rooted event has probability at most its unconditional probability divided by
The root mass. -/
theorem cond_smallRoot_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (r : ℝ)
    (A : Set (Ω × ℂ)) :
    (Canon.rootedLaw P)[|smallRootEvent Ω r] A ≤
      Canon.rootedLaw P A / Canon.rootMeasure (ball (0 : ℂ) r) := by
  calc (Canon.rootedLaw P)[|smallRootEvent Ω r] A
        = (Canon.rootMeasure (ball (0 : ℂ) r))⁻¹ *
            Canon.rootedLaw P (smallRootEvent Ω r ∩ A) := by
          rw [cond_apply (measurableSet_smallRootEvent r), rootedLaw_smallRootEvent D r]
    _ ≤ (Canon.rootMeasure (ball (0 : ℂ) r))⁻¹ * Canon.rootedLaw P A := by
          gcongr
          exact inter_subset_right
    _ = Canon.rootedLaw P A / Canon.rootMeasure (ball (0 : ℂ) r) := by
          rw [div_eq_mul_inv, mul_comm]

/-- **[18] Case 1, last paragraph.** (4.40) for `h₁` sampled from its conditional law given
`{z ∈ B_r(0)}`: the Case 1 bound divided by `rootMeasure (B_r(0)) = r²` (`0 ≤ r ≤ 1`). -/
theorem case1_smallRoot_event_le
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {G : Set WPData} (hG : MeasurableSet G)
    {p q : ℝ} (hpq : p.HolderConjugate q) {δ : ℝ≥0∞}
    (hbad : P (wpData X₀ hIG₀ U ηL ⁻¹' G) ≤ δ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (Canon.rootedLaw P)[|smallRootEvent Ω r] (rootedWPData γ X₀ hIG₀ U ηL ⁻¹' G) ≤
      case1Moment D hγ p ^ (1 / p) * δ ^ (1 / q) / ENNReal.ofReal (r ^ 2) := by
  have hmass : Canon.rootMeasure (ball (0 : ℂ) r) = ENNReal.ofReal (r ^ 2) :=
    GMS4.GMSA.normalizedLebesgueOnRootingDisk_ball r hr0 hr1
  refine (cond_smallRoot_le D r _).trans ?_
  rw [hmass]
  exact ENNReal.div_le_div_right (case1_rooted_event_le D hγ hG hpq hbad) _

end MatedCRTHarmonic.GMSCase1
