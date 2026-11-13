/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.GridIndependenceDifferenceBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.GridIndependenceCoupling
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly

/-!
# From grid-copy potentials to `hcopies` — the difference-field bridge

`HarmonicCoordinateAssembly.DifferenceFieldGridIndependent ν ms` (the input `hcopies` of
`harmonicCoordinateConclusions_of_named_inputs`) is a statement about the **paired-label**
difference field `markedDifferenceField ms`, whose value at `Nat.pair a b` is the limit of
`φ(H_b) − φ(H_a)`.  The checked comparison chain of `Corrector/GridIndependenceCoupling`
concludes instead with an almost-sure equality of **vertex** fields
(`ae_eq_of_ae_setLIntegral_closedBall_eq_zero`).  Its `ℕ`-label bridge
`aeProd_marked_copies_of_orthogonality` reads a field at label `v.val`, which for the paired
difference field is meaningless, so it cannot deliver `hcopies` directly.  This module supplies
the missing glue and the composition.

## What is proved

* `markedPotential_baseVertex` — the marked potential vanishes at the base vertex, for **every**
  marked environment.  Hence the anchoring hypothesis `hanchor` of the coupling chain is
  **discharged** for the two grid copies.
* `markedDifferenceField_pair` — on every marked environment the difference field at a pair of
  active labels is the increment of the marked potential (from the difference-field identities
  alone, no convergence assumed).
* `markedDifferenceField_eq_zero_of_not_active` — it vanishes at pairs that are not both active.
* `markedDifferenceField_eq_of_markedPotential_eq` and
  `differenceFieldGridIndependent_of_ae_markedPotential_eq` — **equal potentials give equal
  difference fields**, so `hcopies` follows from an almost-sure equality of the two grid-copy
  potentials.
* `differenceFieldGridIndependent_of_ae_disk` — `hcopies` from the almost-sure vanishing of every
  disk integral of the rooted specific energy of `firstPotential − secondPotential`.
* `ae_disk_eq_zero_of_weakMaximal` — the manuscript's maximal-function step: a weak-`L¹`
  maximal inequality and a vanishing expected density at the origin make every disk integral
  vanish almost surely.
* `differenceFieldGridIndependent_of_orthogonality` — **the composition**: `hcopies` from the four
  cross specific-orthogonality relations with their integrability (`GridIndependenceCoupling`'s
  own inputs) and the single maximal input `CopyDifferenceWeakMaximal`.

## Why the maximal route and not `hstationary`

`GridIndependenceCoupling.ae_setLIntegral_closedBall_eq_zero` passes from the origin to the disks
through `hstationary : E ∫_{B̄_r} ρ_θ = |B̄_r| · E ρ_θ(0)`.  That identity says `z ↦ E ρ_θ(z)` is
constant, i.e. it is a **stationarity** property.  The main theorem assumes only
`EnvironmentLaws.MassTransport ν`, whose kernels must be covariant under dilations as well as
translations; the ball kernel `1{|z − w| ≤ r}` is not.  A stationary law rescaled by a factor
depending on the root cell still satisfies `MassTransport` but in general violates the identity
for scale-invariant rooted densities.  For the actual `θ` the identity does hold, but only because
`θ = 0` almost surely — i.e. only through the conclusion.  So `hstationary` is not a law-only input
here and is not used.  The manuscript's own route is `s:eq:maximal`, which *is* a consequence of
mass transport; it is exposed below as `CopyDifferenceWeakMaximal`, stated only for the grid-copy
difference (it is false for non-covariant fields).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace ReflectedGMS.GridIndependenceDifferenceBridge

open Code DyadicApproximation RootDensities HarmonicMainStatement
open MarkedLimitingCoordinateMeasurability HarmonicCoordinateAssembly GridIndependenceCoupling

/-! ### The difference field is the increment of the marked potential -/

/-- The marked potential vanishes at the base vertex, on every marked environment. -/
theorem markedPotential_baseVertex (ms : ℕ → ℕ) (ω : MarkedEnvironment) :
    markedPotential ms ω (baseVertex ω.1) = 0 :=
  (isDifferenceField_markedDifferenceField ms ω).1 (baseVertex ω.1)

/-- **The difference field at active labels is the increment of the marked potential.** -/
theorem markedDifferenceField_pair (ms : ℕ → ℕ) (ω : MarkedEnvironment) (v w : Vertex ω.1.val) :
    markedDifferenceField ms ω (Nat.pair v.val w.val)
      = markedPotential ms ω w - markedPotential ms ω v := by
  obtain ⟨hdiag, hadd⟩ := isDifferenceField_markedDifferenceField ms ω
  have h1 := hadd v (baseVertex ω.1) w
  have h2 := hadd (baseVertex ω.1) v (baseVertex ω.1)
  rw [hdiag (baseVertex ω.1)] at h2
  have hneg : markedDifferenceField ms ω (Nat.pair v.val (baseVertex ω.1).val)
      = -markedDifferenceField ms ω (Nat.pair (baseVertex ω.1).val v.val) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h2.symm
  show markedDifferenceField ms ω (Nat.pair v.val w.val)
      = markedDifferenceField ms ω (Nat.pair (baseVertex ω.1).val w.val)
        - markedDifferenceField ms ω (Nat.pair (baseVertex ω.1).val v.val)
  rw [h1, hneg]
  abel

/-- The difference field vanishes at pairs of labels that are not both active. -/
theorem markedDifferenceField_eq_zero_of_not_active (ms : ℕ → ℕ) (ω : MarkedEnvironment) (k : ℕ)
    (hk : ¬ ((ω.1.val.1 (Nat.unpair k).1).isSome ∧ (ω.1.val.1 (Nat.unpair k).2).isSome)) :
    markedDifferenceField ms ω k = 0 := by
  by_cases h : ω ∈ LimitGood (differenceApproximant ms)
  · rw [markedDifferenceField_of_mem ms h]
    exact limitValue_eq_zero_of_approximants_zero fun j =>
      differenceApproximant_of_not ms j ω k fun h' => hk h'.2
  · rw [markedDifferenceField_of_notMem ms h]
    rfl

/-- **Equal potentials give equal difference fields.** -/
theorem markedDifferenceField_eq_of_markedPotential_eq (ms : ℕ → ℕ) {e : Env} {D₁ D₂ : Grid}
    (h : markedPotential ms (e, D₁) = markedPotential ms (e, D₂)) :
    markedDifferenceField ms (e, D₁) = markedDifferenceField ms (e, D₂) := by
  funext k
  by_cases hk : (e.val.1 (Nat.unpair k).1).isSome ∧ (e.val.1 (Nat.unpair k).2).isSome
  · obtain ⟨h1, h2⟩ := hk
    have hk' : Nat.pair (⟨(Nat.unpair k).1, h1⟩ : Vertex e.val).val
        (⟨(Nat.unpair k).2, h2⟩ : Vertex e.val).val = k := Nat.pair_unpair k
    rw [← hk', markedDifferenceField_pair ms (e, D₁) ⟨(Nat.unpair k).1, h1⟩ ⟨(Nat.unpair k).2, h2⟩,
      markedDifferenceField_pair ms (e, D₂) ⟨(Nat.unpair k).1, h1⟩ ⟨(Nat.unpair k).2, h2⟩, h]
  · rw [markedDifferenceField_eq_zero_of_not_active ms (e, D₁) k hk,
      markedDifferenceField_eq_zero_of_not_active ms (e, D₂) k hk]

/-- **`hcopies` from an almost-sure equality of the two grid-copy potentials.** -/
theorem differenceFieldGridIndependent_of_ae_markedPotential_eq (ν : Measure Env) (ms : ℕ → ℕ)
    (h : ∀ᵐ p : Env × Grid × Grid ∂ν.prod (gridLaw.prod gridLaw),
      markedPotential ms (p.1, p.2.1) = markedPotential ms (p.1, p.2.2)) :
    DifferenceFieldGridIndependent ν ms := by
  unfold DifferenceFieldGridIndependent
  filter_upwards [h] with p hp
  exact markedDifferenceField_eq_of_markedPotential_eq ms hp

/-! ### The two grid-copy potentials on the coupled space -/

/-- The marked potential of the first grid copy, as a vertex field on the coupled space. -/
noncomputable def firstPotential (ms : ℕ → ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  markedPotential ms (p.1, p.2.1)

/-- The marked potential of the second grid copy, as a vertex field on the coupled space. -/
noncomputable def secondPotential (ms : ℕ → ℕ) (p : CoupledSpace) : Vertex p.1.val → Plane :=
  markedPotential ms (p.1, p.2.2)

/-- **`hcopies` from the vanishing of the disk integrals**, with the anchoring discharged. -/
theorem differenceFieldGridIndependent_of_ae_disk (ν : Measure Env) (ms : ℕ → ℕ)
    (hdisk : ∀ᵐ p ∂ν.prod (gridLaw.prod gridLaw), ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r,
        rootedSpecificEnergyDensity (decode p.1)
          (fun u => firstPotential ms p u - secondPotential ms p u) z ∂volume) = 0) :
    DifferenceFieldGridIndependent ν ms := by
  have hanchor : ∀ᵐ p ∂ν.prod (gridLaw.prod gridLaw),
      ∃ v₀ : Vertex p.1.val, firstPotential ms p v₀ = secondPotential ms p v₀ :=
    Filter.Eventually.of_forall fun p => ⟨baseVertex p.1,
      (markedPotential_baseVertex ms (p.1, p.2.1)).trans
        (markedPotential_baseVertex ms (p.1, p.2.2)).symm⟩
  exact differenceFieldGridIndependent_of_ae_markedPotential_eq ν ms
    (ae_eq_of_ae_setLIntegral_closedBall_eq_zero (ν.prod (gridLaw.prod gridLaw))
      (firstPotential ms) (secondPotential ms) hdisk hanchor)

/-! ### The maximal-function step -/

/-- **The weak-`L¹` maximal step.**  If the expected rooted density at the origin vanishes and a
weak-type maximal inequality holds for the disk integrals, every disk integral vanishes almost
surely, simultaneously for all radii. -/
theorem ae_disk_eq_zero_of_weakMaximal (μ : Measure CoupledSpace)
    (θ : (p : CoupledSpace) → Vertex p.1.val → Plane)
    (hzero : (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (θ p) 0 ∂μ) = 0)
    (hmax : ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : ℝ, 0 < t →
      μ {p | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
          < ∫⁻ z in Metric.closedBall (0 : Plane) r,
              rootedSpecificEnergyDensity (decode p.1) (θ p) z ∂volume}
        ≤ C * (∫⁻ p, rootedSpecificEnergyDensity (decode p.1) (θ p) 0 ∂μ)
            / ENNReal.ofReal t) :
    ∀ᵐ p ∂μ, ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r,
        rootedSpecificEnergyDensity (decode p.1) (θ p) z ∂volume) = 0 := by
  obtain ⟨C, -, hbound⟩ := hmax
  have hn : ∀ n : ℕ, ∀ᵐ p ∂μ, ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r,
        rootedSpecificEnergyDensity (decode p.1) (θ p) z ∂volume)
        ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1) * r ^ 2) := by
    intro n
    have ht : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have h0 := hbound _ ht
    rw [hzero, mul_zero, ENNReal.zero_div] at h0
    rw [ae_iff]
    refine measure_mono_null ?_ (le_antisymm h0 (by simp))
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    push_neg at hp
    exact hp
  filter_upwards [ae_all_iff.2 hn] with p hp r hr
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1) * r ^ 2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (r ^ 2)
    rw [zero_mul] at h
    simpa using ENNReal.tendsto_ofReal h
  exact le_antisymm (ge_of_tendsto' htend fun n => hp n r hr) (by simp)

/-- **OPEN INPUT (`s:eq:maximal` for the grid-copy difference).**  The manuscript's weak-`L¹`
maximal inequality for the rooted specific-energy density of the difference of the two grid-copy
potentials, on the joint law of the environment and two independent uniform grids.  It is stated
only for this field: the inequality needs the density to be a covariant rooted observable, which
the grid-copy potentials are (their gradients transport, by `hcov`, now closed in
`Corrector/BlockInterpolationSimilarity`).  Its producer route is
`Spatial/SpatialMaximalInequality.measure_ballMaximal_gt_le` on the coupled space, fed by the
specific-energy re-rooting identity (the `s = 1` case of
`Corrector/SpecificEnergyDensitySimilarity.rootedSpecificEnergyDensity_translate`). -/
def CopyDifferenceWeakMaximal (ν : Measure Env) (ms : ℕ → ℕ) : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ t : ℝ, 0 < t →
    (ν.prod (gridLaw.prod gridLaw)) {p | ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal (t * r ^ 2)
        < ∫⁻ z in Metric.closedBall (0 : Plane) r,
            rootedSpecificEnergyDensity (decode p.1)
              (fun u => firstPotential ms p u - secondPotential ms p u) z ∂volume}
      ≤ C * (∫⁻ p, rootedSpecificEnergyDensity (decode p.1)
            (fun u => firstPotential ms p u - secondPotential ms p u) 0
              ∂ν.prod (gridLaw.prod gridLaw)) / ENNReal.ofReal t

end ReflectedGMS.GridIndependenceDifferenceBridge
