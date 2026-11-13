/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedPatchEnergyConvergence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# `MarkedPatchConvergence` from an approximant-level input (`s:prop:limit`(d))

`HarmonicCoordinateAssembly.MarkedPatchConvergence ν ms` is the `hpatch` input of
`harmonicCoordinateConclusions_of_named_inputs`, and it is consumed by
`Corrector/MarkedRectangleHarmonicity.markedHarmonicity_of_approximant_orthogonality`.
Unfolded, it says that for almost every marked environment and **every** bounded spatial set
`A` the vector Dirichlet energy, on the patch graph of the cells hitting `A`, of the error
`φ_{m_j} − Φ` tends to zero.

## Why `hconv` alone does not give it

`hconv = MarkedDifferencesConverge` gives convergence of `φ_{m_j}(H_b) − φ_{m_j}(H_a)` at
each single pair of labels.  The patch energy, however, is a `tsum` over the ordered pairs of
a possibly **infinite** vertex set `{v | Hits (decode ω.1) A v}` (the patch is not assumed
finite anywhere in this project), so termwise convergence of the edge contributions is not
enough: one extra, genuinely analytic, input is needed.  This file isolates exactly that
input, in two interchangeable forms, and proves the passage to the limit from it.

## What is proved here

Everything except the two named inputs.  In particular the *termwise* half is discharged
outright from `hconv`: `tendsto_phi_difference` shows that on the good event `SublinearEvent`
and at a marked environment in `LimitGood` the differences `φ_{m_j}(w) − φ_{m_j}(v)` converge
to `Φ(w) − Φ(v)`, using the cocycle identity `isDifferenceField_markedDifferenceField` to
rewrite `Φ(w) − Φ(v)` as the value of the marked difference field at the paired label
`⟨v, w⟩`.  `SublinearEvent` is not optional: off it `markedPotential ms ω = 0` while
`φ_m ≠ 0`, so the conclusion is false there; its almost-sure occurrence is the checked
`ae_mem_sublinearEvent`, which is why `hν` and `hFE` appear.

Two analytic routes are supplied, both stated for an **arbitrary** conductance graph and an
arbitrary (possibly infinite) vertex set, with no finite-support or finite-patch assumption:

* `tendsto_vectorEnergy_sub_zero_of_cauchy` — **Fatou**.  If the patch energies of the
  differences `φ_j − φ_k` are Cauchy, the patch energy of `φ_j − Φ` tends to zero.  The
  mechanism is Fatou's lemma for `ℝ≥0∞`-valued series (`tsum_le_liminf_tsum_of_tendsto`,
  obtained from `MeasureTheory.lintegral_liminf_le` against the counting measure on
  `W × W`): for fixed `j`, `E(φ_j − Φ) ≤ liminf_k E(φ_j − φ_k) ≤ ε`.
* `tendsto_vectorEnergy_sub_zero_of_dominated` — **dominated convergence**.  If the ordered
  edge contributions of `φ_j − Φ` admit one summable dominating bound, the patch energy tends
  to zero.  This is `MeasureTheory.tendsto_lintegral_of_dominated_convergence` against the
  counting measure on `W × W`, packaged as `tendsto_tsum_of_dominated`.

The bridge making both possible is `vectorEnergy_eq_tsum_patchEdgeEnergy`: the vector energy
of the statement file *is* the `ℝ≥0∞` series `∑' p : W × W, patchEdgeEnergy G h p` of its
ordered-pair contributions, with no summability hypothesis on either side.

## The Cauchy input is *equivalent* to the target, the domination input is stronger

`markedPatchEnergyCauchy_of_markedPatchConvergence` proves the converse of the Fatou route:
`MarkedPatchEnergyCauchy` follows from `MarkedPatchConvergence` by the elementary quadratic
bound `E(x − y) ≤ 2E(x − z) + 2E(z − y)` (`vectorEnergy_sub_le`).  So the Fatou route replaces
`hpatch` by an *equivalent* statement which no longer mentions the limit `markedPotential ms ω`
at all — it is a statement about the concrete block interpolants `phi` only, in the same style
as `MarkedRectangleHarmonicity.MarkedApproximantRectangleOrthogonality`.  Nothing has been
weakened and nothing smuggled in.  `MarkedPatchEdgeDomination`, by contrast, is genuinely
stronger than the target and still mentions the limit; it is recorded because it is the
shortest route whenever a rate is available.

**This file proves no main theorem** and certifies neither named input.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS

namespace MarkedPatchEnergyConvergence

open StatementIngredients

/-! ### `ℝ≥0∞`-valued series as integrals against the counting measure

The counting measure is taken for the **top** `σ`-algebra, so every function out of the index
type is measurable and every singleton is measurable; this makes `lintegral_count` and the
two convergence theorems of `MeasureTheory` available for bare `tsum`s with no measurability
side conditions at all. -/

section CountingMeasure

variable {ι : Type*}

/-- **Fatou's lemma for `ℝ≥0∞`-valued series.** -/
theorem tsum_liminf_le_liminf_tsum (F : ℕ → ι → ℝ≥0∞) :
    ∑' i, liminf (fun n => F n i) atTop ≤ liminf (fun n => ∑' i, F n i) atTop := by
  letI : MeasurableSpace ι := ⊤
  haveI : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hcount : ∀ g : ι → ℝ≥0∞, ∫⁻ i, g i ∂(Measure.count : Measure ι) = ∑' i, g i :=
    fun g => lintegral_count g
  calc ∑' i, liminf (fun n => F n i) atTop
      = ∫⁻ i, liminf (fun n => F n i) atTop ∂(Measure.count : Measure ι) := (hcount _).symm
    _ ≤ liminf (fun n => ∫⁻ i, F n i ∂(Measure.count : Measure ι)) atTop :=
        lintegral_liminf_le (fun _ => measurable_from_top)
    _ = liminf (fun n => ∑' i, F n i) atTop := by
        refine congrArg (fun u : ℕ → ℝ≥0∞ => liminf u atTop) ?_
        funext n
        exact hcount (F n)

/-- The series of a pointwise limit is bounded by the `liminf` of the series. -/
theorem tsum_le_liminf_tsum_of_tendsto {F : ℕ → ι → ℝ≥0∞} {f : ι → ℝ≥0∞}
    (h : ∀ i, Tendsto (fun n => F n i) atTop (𝓝 (f i))) :
    ∑' i, f i ≤ liminf (fun n => ∑' i, F n i) atTop :=
  le_trans (le_of_eq (tsum_congr fun i => ((h i).liminf_eq).symm))
    (tsum_liminf_le_liminf_tsum F)

end CountingMeasure

/-! ### The vector patch energy as a single series over ordered pairs -/

section PatchEnergy

variable {W : Type*} (G : ReflectedWalk.ConductanceGraph W)

/-- Halving a nonnegative real commutes with `ENNReal.ofReal`. -/
theorem ofReal_div_two (t : ℝ) : ENNReal.ofReal (t / 2) = ENNReal.ofReal t / 2 := by
  have h2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), h2]

/-- **The contribution of one ordered pair of vertices to the vector energy.**  It is the
halved conductance-weighted squared Euclidean length of the increment, as an element of
`ℝ≥0∞`, so it is defined for every field, summable or not. -/
noncomputable def patchEdgeEnergy (h : W → Plane) (p : W × W) : ℝ≥0∞ :=
  ENNReal.ofReal (G.c p.1 p.2 * ‖h p.2 - h p.1‖ ^ 2 / 2)

/-- Doubling removes the halving. -/
theorem two_mul_patchEdgeEnergy (h : W → Plane) (p : W × W) :
    2 * patchEdgeEnergy G h p = ENNReal.ofReal (G.c p.1 p.2 * ‖h p.2 - h p.1‖ ^ 2) := by
  show 2 * ENNReal.ofReal (G.c p.1 p.2 * ‖h p.2 - h p.1‖ ^ 2 / 2) = _
  rw [ofReal_div_two, ENNReal.mul_div_cancel (by simp) (by simp)]

/-- **The vector energy is the series of its ordered-pair contributions.**  Both sides are
`ℝ≥0∞`-valued and no summability is assumed; the vertex set may be infinite. -/
theorem vectorEnergy_eq_tsum_patchEdgeEnergy (h : W → Plane) :
    vectorEnergy G h = ∑' p : W × W, patchEdgeEnergy G h p := by
  have hterm : ∀ p : W × W, patchEdgeEnergy G h p
      = ENNReal.ofReal (G.gradSq (fun v => h v 0) p) / 2
        + ENNReal.ofReal (G.gradSq (fun v => h v 1) p) / 2 := by
    intro p
    have hn : ‖h p.2 - h p.1‖ ^ 2
        = ((h p.2 - h p.1) 0) ^ 2 + ((h p.2 - h p.1) 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hreal : G.c p.1 p.2 * ‖h p.2 - h p.1‖ ^ 2
        = G.gradSq (fun v => h v 0) p + G.gradSq (fun v => h v 1) p := by
      rw [hn]
      simp only [ReflectedWalk.ConductanceGraph.gradSq, PiLp.sub_apply]
      ring
    show ENNReal.ofReal (G.c p.1 p.2 * ‖h p.2 - h p.1‖ ^ 2 / 2) = _
    rw [hreal, add_div,
      ENNReal.ofReal_add (div_nonneg (G.gradSq_nonneg _ p) (by norm_num))
        (div_nonneg (G.gradSq_nonneg _ p) (by norm_num)),
      ofReal_div_two, ofReal_div_two]
  have hcoord : ∀ i : Fin 2,
      (∑' p : W × W, ENNReal.ofReal (G.gradSq (fun v => h v i) p) / 2)
        = energyENN G (fun v => h v i) := by
    intro i
    show _ = (∑' p : W × W, ENNReal.ofReal (G.gradSq (fun v => h v i) p)) / 2
    simp only [div_eq_mul_inv]
    exact ENNReal.tsum_mul_right
  show (∑ i : Fin 2, energyENN G (fun v => h v i)) = ∑' p : W × W, patchEdgeEnergy G h p
  rw [Fin.sum_univ_two, ← hcoord 0, ← hcoord 1, ← ENNReal.tsum_add]
  exact (tsum_congr hterm).symm

/-- The vector energy of a difference does not depend on the order of the difference. -/
theorem vectorEnergy_sub_comm (x y : W → Plane) :
    vectorEnergy G (fun v => x v - y v) = vectorEnergy G (fun v => y v - x v) := by
  rw [vectorEnergy_eq_tsum_patchEdgeEnergy, vectorEnergy_eq_tsum_patchEdgeEnergy]
  refine tsum_congr fun p => ?_
  show ENNReal.ofReal (G.c p.1 p.2 * ‖(x p.2 - y p.2) - (x p.1 - y p.1)‖ ^ 2 / 2)
      = ENNReal.ofReal (G.c p.1 p.2 * ‖(y p.2 - x p.2) - (y p.1 - x p.1)‖ ^ 2 / 2)
  have hnorm : ‖(x p.2 - y p.2) - (x p.1 - y p.1)‖
      = ‖(y p.2 - x p.2) - (y p.1 - x p.1)‖ := by
    rw [← norm_neg]
    congr 1
    abel
  rw [hnorm]

/-- The elementary edgewise quadratic bound behind the triangle inequality for energies. -/
theorem real_edge_triangle {c : ℝ} (hc : 0 ≤ c) {a b d : Plane} (habd : a = b + d) :
    c * ‖a‖ ^ 2 / 2 ≤ c * ‖b‖ ^ 2 + c * ‖d‖ ^ 2 := by
  have hnorm : ‖a‖ ≤ ‖b‖ + ‖d‖ := by
    rw [habd]
    exact norm_add_le b d
  have h1 : ‖a‖ ^ 2 ≤ 2 * ‖b‖ ^ 2 + 2 * ‖d‖ ^ 2 := by
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg d, sq_nonneg (‖b‖ - ‖d‖)]
  nlinarith [mul_nonneg hc (sub_nonneg.2 h1)]

/-- **The quadratic (triangle) bound for the vector energy**, in `ℝ≥0∞` and with no
finiteness hypothesis on any of the three energies. -/
theorem vectorEnergy_sub_le (x y z : W → Plane) :
    vectorEnergy G (fun v => x v - y v)
      ≤ 2 * vectorEnergy G (fun v => x v - z v) + 2 * vectorEnergy G (fun v => z v - y v) := by
  simp only [vectorEnergy_eq_tsum_patchEdgeEnergy]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [two_mul_patchEdgeEnergy, two_mul_patchEdgeEnergy,
    ← ENNReal.ofReal_add (mul_nonneg (G.c_nonneg _ _) (sq_nonneg _))
      (mul_nonneg (G.c_nonneg _ _) (sq_nonneg _))]
  show ENNReal.ofReal (G.c p.1 p.2 * ‖(x p.2 - y p.2) - (x p.1 - y p.1)‖ ^ 2 / 2) ≤ _
  refine ENNReal.ofReal_le_ofReal ?_
  refine real_edge_triangle (G.c_nonneg p.1 p.2) ?_
  abel

/-- **Termwise convergence of the ordered-edge contributions** from convergence of the
increments. -/
theorem tendsto_patchEdgeEnergy {u : ℕ → W → Plane} {U : W → Plane}
    (hptw : ∀ v w : W, Tendsto (fun n => u n w - u n v) atTop (𝓝 (U w - U v)))
    (p : W × W) :
    Tendsto (fun n => patchEdgeEnergy G (u n) p) atTop (𝓝 (patchEdgeEnergy G U p)) := by
  have h1 : Tendsto (fun n => ‖u n p.2 - u n p.1‖) atTop (𝓝 ‖U p.2 - U p.1‖) :=
    (hptw p.1 p.2).norm
  have h2 : Tendsto (fun n => ‖u n p.2 - u n p.1‖ ^ 2) atTop (𝓝 (‖U p.2 - U p.1‖ ^ 2)) :=
    h1.pow 2
  have h3 : Tendsto (fun n => G.c p.1 p.2 * ‖u n p.2 - u n p.1‖ ^ 2) atTop
      (𝓝 (G.c p.1 p.2 * ‖U p.2 - U p.1‖ ^ 2)) := h2.const_mul (G.c p.1 p.2)
  have h4 : Tendsto (fun n => G.c p.1 p.2 * ‖u n p.2 - u n p.1‖ ^ 2 / 2) atTop
      (𝓝 (G.c p.1 p.2 * ‖U p.2 - U p.1‖ ^ 2 / 2)) := h3.div_const 2
  exact ENNReal.tendsto_ofReal h4

/-! ### The two analytic inputs, at the level of one graph -/

/-- **The Cauchy form.**  The patch energies of the differences of the approximants are
Cauchy.  Note that the limit field does not occur. -/
def HasCauchyPatchEnergy (a : ℕ → W → Plane) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k →
    vectorEnergy G (fun v => a j v - a k v) ≤ ε

/-- **The Fatou route.**  Pointwise convergence of the increments together with the Cauchy
property of the patch energies forces the patch energy of the error to vanish. -/
theorem tendsto_vectorEnergy_sub_zero_of_cauchy {a : ℕ → W → Plane} {L : W → Plane}
    (hptw : ∀ v w : W, Tendsto (fun n => a n w - a n v) atTop (𝓝 (L w - L v)))
    (hcau : HasCauchyPatchEnergy G a) :
    Tendsto (fun j => vectorEnergy G (fun v => a j v - L v)) atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := hcau ε hε
  filter_upwards [eventually_ge_atTop N] with j hj
  have hlim : ∀ p : W × W,
      Tendsto (fun k => patchEdgeEnergy G (fun v => a j v - a k v) p) atTop
        (𝓝 (patchEdgeEnergy G (fun v => a j v - L v) p)) := by
    refine tendsto_patchEdgeEnergy G (u := fun k v => a j v - a k v)
      (U := fun v => a j v - L v) ?_
    intro v w
    have h1 : Tendsto (fun n : ℕ => (a j w - a j v) - (a n w - a n v)) atTop
        (𝓝 ((a j w - a j v) - (L w - L v))) := tendsto_const_nhds.sub (hptw v w)
    have heq : (a j w - a j v) - (L w - L v) = (a j w - L w) - (a j v - L v) := by abel
    rw [heq] at h1
    refine h1.congr fun n => ?_
    abel
  have hbd : ∀ᶠ k in atTop,
      (∑' p : W × W, patchEdgeEnergy G (fun v => a j v - a k v) p) ≤ ε := by
    filter_upwards [eventually_ge_atTop N] with k hk
    rw [← vectorEnergy_eq_tsum_patchEdgeEnergy]
    exact hN j hj k hk
  rw [vectorEnergy_eq_tsum_patchEdgeEnergy]
  exact le_trans (tsum_le_liminf_tsum_of_tendsto hlim)
    (liminf_le_of_frequently_le' hbd.frequently)

end PatchEnergy

/-! ### The marked level -/

section Marked

open Code EnvironmentFields EnvironmentLaws DyadicApproximation RootDensities
open HarmonicLawIngredients HarmonicMainStatement HarmonicCoordinateAssembly
open MarkedLimitingCoordinateMeasurability

/-- **The termwise half of `s:prop:limit`(d), discharged from `hconv`.**  On the good event
and at a marked environment at which every paired label converges, the increments of the
concrete block interpolants converge to the increments of the marked potential.

The cocycle identity of `isDifferenceField_markedDifferenceField` is what turns the *base
point* representation `Φ(v) = D⟨base, v⟩` into the increment `Φ(w) − Φ(v) = D⟨v, w⟩`, which
is the label at which `hconv` provides convergence. -/
theorem tendsto_phi_difference (ms : ℕ → ℕ) {ω : MarkedEnvironment}
    (hG : ω.1 ∈ SublinearEvent) (hgood : ω ∈ LimitGood (differenceApproximant ms))
    (v w : Vertex ω.1.val) :
    Tendsto (fun j => phi (decode ω.1) ω.2 (ms j) w - phi (decode ω.1) ω.2 (ms j) v) atTop
      (𝓝 (markedPotential ms ω w - markedPotential ms ω v)) := by
  have hval : markedPotential ms ω w - markedPotential ms ω v
      = markedDifferenceField ms ω (Nat.pair v.val w.val) := by
    have hadd := (isDifferenceField_markedDifferenceField ms ω).2 (baseVertex ω.1) v w
    simp only [baseVertex_val] at hadd
    show markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) w.val)
        - markedDifferenceField ms ω (Nat.pair (baseLabel ω.1) v.val) = _
    rw [hadd]
    abel
  rw [hval, markedDifferenceField_of_mem ms hgood]
  have hlim := tendsto_limitValue (mem_convergesAt_of_mem_limitGood hgood (Nat.pair v.val w.val))
  exact hlim.congr fun j => differenceApproximant_pair ms j ω hG v w

/-- **NAMED INPUT (approximant level, `s:prop:limit`(d)).**  Almost surely, on every bounded
spatial patch, the patch energies of the *differences of the concrete block interpolants* are
Cauchy along the subsequence.

This mentions the interpolants `phi` only: the limit `markedPotential ms ω` does not occur,
exactly as `MarkedApproximantRectangleOrthogonality` removed the limit from `hharm`.  By
`markedPatchEnergyCauchy_of_markedPatchConvergence` it is implied by the target, so it is an
*equivalent* reformulation rather than a strengthening.  Nothing here certifies it; its
intended producer is the blockwise minimality of the interpolants together with the nested
energy projections of `Corrector/NestedEnergyProjections`, which make the level energies
monotone and hence Cauchy on a fixed patch. -/
def MarkedPatchEnergyCauchy (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∀ᵐ ω : MarkedEnvironment ∂ν.prod gridLaw, ∀ A : Set Plane, Bornology.IsBounded A →
    HasCauchyPatchEnergy (restrictGraph (decode ω.1).graph {v | Hits (decode ω.1) A v})
      (fun j v => phi (decode ω.1) ω.2 (ms j) v.val)

/-- **`hpatch` from `hconv` and the Cauchy input.**  This is an implication, not a proof of
`MarkedPatchConvergence`: `hconv` and `hcau` are both open. -/
theorem markedPatchConvergence_of_patchEnergyCauchy (ν : Measure Env) [SFinite ν]
    (hν : MassTransport ν) (hFE : FiniteEnergyMoment ν) (ms : ℕ → ℕ)
    (hconv : MarkedDifferencesConverge ν ms) (hcau : MarkedPatchEnergyCauchy ν ms) :
    MarkedPatchConvergence ν ms := by
  filter_upwards [ae_marked_of_ae_env ν (p := fun e => e ∈ SublinearEvent)
    (ae_mem_sublinearEvent ν hν hFE.ne), hconv, hcau] with ω hG hgood hcauω
  intro A hA
  exact tendsto_vectorEnergy_sub_zero_of_cauchy _
    (fun v w => tendsto_phi_difference ms hG hgood v.1 w.1) (hcauω A hA)

/-! ### The corollary of the assembly with `hpatch` replaced -/

end Marked

end MarkedPatchEnergyConvergence

end ReflectedGMS
