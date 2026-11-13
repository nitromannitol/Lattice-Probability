/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MeasurableBlockMinimizer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.MeasurableDirichletConstruction

/-!
# Measurable anchored minimizers on a *varying* finite block with a *varying* boundary

`Forms/MeasurableDirichletConstruction.lean` produces a measurable field of anchored
Dirichlet minimizers for one **fixed** finite vertex type and one **fixed** finite anchor
set: `MeasurableDirichletConstruction.exists_measurable_anchored_minimizer`. The actual
blockwise harmonic coordinates of the manuscript are not of that shape. The labels of a
selected dyadic block and the labels of its boundary skeleton both move with the
environment, so the finite system itself — its vertex set, its matrix size and its anchor
set — is random.

This module removes that restriction. The only structure used is that a finite label set
is a `Finset` of a countable label type, so the pair (block labels, boundary labels) takes
countably many values: the parameter space is partitioned into the countably many
measurable events on which the finite system is constant, and on each event the already
checked explicit finite solution `MeasurableDirichletConstruction.anchoredSolution` of the
nonsingular Dirichlet system applies verbatim. No measurable selection theorem is used and
no continuity in the data is assumed; the conductances, the connectivity pattern, the block
and the boundary may all vary arbitrarily and measurably.

The results are:

* `blockSolution`, the anchored minimizer of the restricted graph on a finite label set
  `s` with anchors the labels in `b`, extended off the block by the reference function, and
  `blockSolution_spec`, its trace, interior discrete harmonicity and *restricted energy*
  minimality — the last stated with `FiniteDirichletEnergyLimit.restrictedEnergy`, i.e. in
  exactly the form consumed by the canonical exhaustion machinery
  (`FiniteDirichletEnergyLimit.tendsto_levelEnergy_of_tendsto_pointwise`), so that the
  varying-block minimizers of a varying exhaustion can be fed to the pointwise limit;
* `exists_measurable_varying_block_minimizer`, the same conclusions for measurably varying
  `S B : Ω → Finset V`, together with measurability of the field, vertex by vertex and into
  the product;
* `exists_measurable_varying_block_minimizer_anchorSet`, the form actually needed by a
  truncation: the boundary is an arbitrary measurable **set**-valued anchor family
  `A : Ω → Set V` (a skeleton is not given as a finset), traced onto the block through
  `anchorFinset`, and the anchoring hypothesis and the conclusions are stated with
  `AnchoredFiniteExhaustion.inducedAnchorSet`.

What is *not* proved here: nothing is claimed about infinite block patches, about the
measurability of the selected block labels or of the anchor labels themselves (these are
hypotheses `hS`, `hB`, `hA`), and nothing is claimed for plane-valued fields.
-/

set_option autoImplicit false

namespace ReflectedGMS

namespace MeasurableBlockMinimizer

open MeasureTheory
open FiniteDirichletEnergyLimit MeasurableDirichletConstruction

/-! ### A countable-selector measurability criterion

The one general tool needed. `Environment/CanonicalSimilarityMeasurable.lean` contains a
countable-pieces criterion of the same kind, but that module is not available as a
dependency here; this is the three-line selector form used below. -/

/-- **Selecting among countably many measurable functions by a measurable index.** If the
index `p ω` has measurable fibres and every `g i` is measurable, then `ω ↦ g (p ω) ω` is
measurable. -/
theorem measurable_select_of_countable {Ω α ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [Countable ι] {p : Ω → ι}
    (hp : ∀ i : ι, MeasurableSet {ω | p ω = i}) {g : ι → Ω → α} (hg : ∀ i : ι, Measurable (g i)) :
    Measurable fun ω => g (p ω) ω := by
  intro t ht
  have hset : (fun ω => g (p ω) ω) ⁻¹' t = ⋃ i : ι, {ω | p ω = i} ∩ g i ⁻¹' t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro hω
      exact ⟨p ω, rfl, hω⟩
    · rintro ⟨i, hi, hmem⟩
      rw [hi]
      exact hmem
  rw [hset]
  exact MeasurableSet.iUnion fun i => (hp i).inter (hg i ht)

/-! ### The anchored minimizer of one finite block -/

section FixedBlock

variable {V : Type*} [DecidableEq V]

/-- The boundary labels of a block, as an anchor finset of the block's vertex subtype. -/
def blockAnchors (s b : Finset V) : Finset ↥(s : Set V) :=
  Finset.univ.filter fun x : ↥(s : Set V) => (x : V) ∈ b

@[simp] theorem mem_blockAnchors {s b : Finset V} {x : ↥(s : Set V)} :
    x ∈ blockAnchors s b ↔ (x : V) ∈ b :=
  ⟨fun h => (Finset.mem_filter.1 h).2, fun h => Finset.mem_filter.2 ⟨Finset.mem_univ x, h⟩⟩

/-- The anchors of the block are exactly the induced anchor set of the boundary labels. -/
theorem coe_blockAnchors (s b : Finset V) :
    ((blockAnchors s b : Finset ↥(s : Set V)) : Set ↥(s : Set V))
      = AnchoredFiniteExhaustion.inducedAnchorSet ((b : Set V)) ((s : Set V)) := by
  ext x
  simp only [Finset.mem_coe, mem_blockAnchors,
    AnchoredFiniteExhaustion.mem_inducedAnchorSet]

/-- **The anchored minimizer of the finite block `s` with boundary labels `b`**: the
explicit solution of the nonsingular finite Dirichlet system inside the block, and the
reference function outside it. -/
noncomputable def blockSolution (G : ReflectedWalk.ConductanceGraph V) (s b : Finset V)
    (u : V → ℝ) : V → ℝ := fun x =>
  if hx : x ∈ s then
    anchoredSolution (restrictGraph G ((s : Set V))) (blockAnchors s b)
      (fun y : ↥(s : Set V) => u ↑y) ⟨x, Finset.mem_coe.2 hx⟩
  else u x

theorem blockSolution_apply_mem (G : ReflectedWalk.ConductanceGraph V) (s b : Finset V)
    (u : V → ℝ) {x : V} (hx : x ∈ s) :
    blockSolution G s b u x =
      anchoredSolution (restrictGraph G ((s : Set V))) (blockAnchors s b)
        (fun y : ↥(s : Set V) => u ↑y) ⟨x, Finset.mem_coe.2 hx⟩ := dif_pos hx

theorem blockSolution_apply_not_mem (G : ReflectedWalk.ConductanceGraph V) (s b : Finset V)
    (u : V → ℝ) {x : V} (hx : x ∉ s) : blockSolution G s b u x = u x := dif_neg hx

/-- Inside the block the extended field is the explicit finite solution. -/
theorem blockSolution_restrict (G : ReflectedWalk.ConductanceGraph V) (s b : Finset V)
    (u : V → ℝ) :
    (fun y : ↥(s : Set V) => blockSolution G s b u ↑y)
      = anchoredSolution (restrictGraph G ((s : Set V))) (blockAnchors s b)
          (fun y : ↥(s : Set V) => u ↑y) := by
  funext y
  rw [blockSolution_apply_mem G s b u (Finset.mem_coe.1 y.2), Subtype.coe_eta]

/-- **The block solution is the anchored minimizer of the block.** It carries the
prescribed values at the boundary labels of the block, is discrete harmonic in the
restricted graph at every non-boundary label of the block, and minimizes the restricted
Dirichlet energy against every globally defined competitor with those boundary values. -/
theorem blockSolution_spec (G : ReflectedWalk.ConductanceGraph V) {s b : Finset V}
    (hA : BoundaryAnchored (restrictGraph G ((s : Set V)))
      (AnchoredFiniteExhaustion.inducedAnchorSet ((b : Set V)) ((s : Set V))))
    (u : V → ℝ) :
    (∀ a ∈ b, a ∈ s → blockSolution G s b u a = u a) ∧
      (restrictGraph G ((s : Set V))).IsHarmonicOn
        (fun y : ↥(s : Set V) => blockSolution G s b u ↑y)
        (AnchoredFiniteExhaustion.inducedAnchorSet ((b : Set V)) ((s : Set V)))ᶜ ∧
      (∀ w : V → ℝ, (∀ a ∈ b, a ∈ s → w a = u a) →
        restrictedEnergy G ((s : Set V)) (blockSolution G s b u)
          ≤ restrictedEnergy G ((s : Set V)) w) := by
  have hA' : BoundaryAnchored (restrictGraph G ((s : Set V)))
      ((blockAnchors s b : Finset ↥(s : Set V)) : Set ↥(s : Set V)) := by
    rw [coe_blockAnchors]
    exact hA
  obtain ⟨h1, h2, h3⟩ :=
    anchoredSolution_spec (restrictGraph G ((s : Set V))) hA' (fun y : ↥(s : Set V) => u ↑y)
  refine ⟨?_, ?_, ?_⟩
  · intro a hab has
    rw [blockSolution_apply_mem G s b u has]
    exact h1 ⟨a, Finset.mem_coe.2 has⟩ (mem_blockAnchors.2 hab)
  · rw [blockSolution_restrict, ← coe_blockAnchors]
    exact h2
  · intro w hw
    have hleft : restrictedEnergy G ((s : Set V)) (blockSolution G s b u)
        = (restrictGraph G ((s : Set V))).Energy
            (anchoredSolution (restrictGraph G ((s : Set V))) (blockAnchors s b)
              (fun y : ↥(s : Set V) => u ↑y)) := by
      show (restrictGraph G ((s : Set V))).Energy
          (fun y : ↥(s : Set V) => blockSolution G s b u ↑y) = _
      rw [blockSolution_restrict]
    have hright : restrictedEnergy G ((s : Set V)) w
        = (restrictGraph G ((s : Set V))).Energy (fun y : ↥(s : Set V) => w ↑y) := rfl
    rw [hleft, hright]
    exact h3 (fun y : ↥(s : Set V) => w ↑y) fun a ha =>
      hw (a : V) (mem_blockAnchors.1 ha) (Finset.mem_coe.1 a.2)

end FixedBlock

/-! ### Measurability of the block solution in the data -/

section MeasurableBlock

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]

/-- **For a fixed block and fixed boundary labels the block solution is measurable in the
data**, vertex by vertex: inside the block it is the explicit solution of the finite
Dirichlet system, whose entries are measurable by
`MeasurableDirichletConstruction.measurable_anchoredSolution`. -/
theorem measurable_blockSolution {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) (s b : Finset V)
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) (x : V) :
    Measurable fun ω => blockSolution (G ω) s b (u ω) x := by
  have hGs : ∀ p q : ↥(s : Set V),
      Measurable fun ω => (restrictGraph (G ω) ((s : Set V))).c p q :=
    fun p q => hG ↑p ↑q
  by_cases hx : x ∈ s
  · have hpt : ∀ ω : Ω, blockSolution (G ω) s b (u ω) x
        = anchoredSolution (restrictGraph (G ω) ((s : Set V))) (blockAnchors s b)
            (fun y : ↥(s : Set V) => u ω ↑y) ⟨x, Finset.mem_coe.2 hx⟩ :=
      fun ω => blockSolution_apply_mem (G ω) s b (u ω) hx
    simp only [hpt]
    exact measurable_anchoredSolution hGs (blockAnchors s b)
      (fun y : ↥(s : Set V) => hu ↑y) ⟨x, Finset.mem_coe.2 hx⟩
  · have hpt : ∀ ω : Ω, blockSolution (G ω) s b (u ω) x = u ω x :=
      fun ω => blockSolution_apply_not_mem (G ω) s b (u ω) hx
    simp only [hpt]
    exact hu x

/-- The anchored minimizer of a **varying** finite block with **varying** boundary labels. -/
noncomputable def varyingBlockSolution (G : Ω → ReflectedWalk.ConductanceGraph V)
    (S B : Ω → Finset V) (u : Ω → V → ℝ) (ω : Ω) : V → ℝ :=
  blockSolution (G ω) (S ω) (B ω) (u ω)

/-- **The varying block solution is measurable.** The finite system has countably many
possible shapes, and the parameter space is partitioned into the measurable events on which
it is constant. -/
theorem measurable_varyingBlockSolution [Countable V]
    {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {S B : Ω → Finset V}
    (hS : ∀ s : Finset V, MeasurableSet {ω | S ω = s})
    (hB : ∀ b : Finset V, MeasurableSet {ω | B ω = b})
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) (x : V) :
    Measurable fun ω => varyingBlockSolution G S B u ω x := by
  have hp : ∀ i : Finset V × Finset V, MeasurableSet {ω | (S ω, B ω) = i} := by
    rintro ⟨s, b⟩
    have hEq : {ω | (S ω, B ω) = (s, b)} = {ω | S ω = s} ∩ {ω | B ω = b} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Prod.mk.injEq]
    rw [hEq]
    exact (hS s).inter (hB b)
  show Measurable fun ω => blockSolution (G ω) (S ω) (B ω) (u ω) x
  exact measurable_select_of_countable hp
    fun i => measurable_blockSolution hG i.1 i.2 hu x

/-- **Measurable anchored minimizers on a varying finite block with a varying boundary.**

For conductance data and reference data depending measurably on a parameter, and for a
block `S ω` and boundary label set `B ω` which vary measurably among the countably many
finite label sets, there is a *measurable* field of functions which, at every parameter
value, carries the prescribed values at the boundary labels of the block, is discrete
harmonic in the restricted graph at every other label of the block, minimizes the
restricted Dirichlet energy among all functions with those boundary values, and is the
reference function outside the block.

The only pointwise hypothesis is that the restricted graph is anchored at the induced
boundary set; the conductances, the connectivity pattern, the block and its boundary may
all vary arbitrarily. -/
theorem exists_measurable_varying_block_minimizer [Countable V]
    {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {S B : Ω → Finset V}
    (hS : ∀ s : Finset V, MeasurableSet {ω | S ω = s})
    (hB : ∀ b : Finset V, MeasurableSet {ω | B ω = b})
    (hanchor : ∀ ω : Ω, BoundaryAnchored (restrictGraph (G ω) (((S ω : Finset V) : Set V)))
      (AnchoredFiniteExhaustion.inducedAnchorSet (((B ω : Finset V) : Set V))
        (((S ω : Finset V) : Set V))))
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) :
    ∃ f : Ω → V → ℝ, Measurable f ∧ (∀ x : V, Measurable fun ω => f ω x) ∧
      ∀ ω : Ω,
        (∀ a ∈ B ω, a ∈ S ω → f ω a = u ω a) ∧
        (restrictGraph (G ω) (((S ω : Finset V) : Set V))).IsHarmonicOn
          (fun y : ↥((S ω : Finset V) : Set V) => f ω ↑y)
          (AnchoredFiniteExhaustion.inducedAnchorSet (((B ω : Finset V) : Set V))
            (((S ω : Finset V) : Set V)))ᶜ ∧
        (∀ w : V → ℝ, (∀ a ∈ B ω, a ∈ S ω → w a = u ω a) →
          restrictedEnergy (G ω) (((S ω : Finset V) : Set V)) (f ω)
            ≤ restrictedEnergy (G ω) (((S ω : Finset V) : Set V)) w) ∧
        (∀ x : V, x ∉ S ω → f ω x = u ω x) := by
  refine ⟨varyingBlockSolution G S B u,
    Measurable.of_eval fun x => measurable_varyingBlockSolution hG hS hB hu x,
    fun x => measurable_varyingBlockSolution hG hS hB hu x, fun ω => ?_⟩
  obtain ⟨h1, h2, h3⟩ := blockSolution_spec (G ω) (hanchor ω) (u ω)
  exact ⟨h1, h2, h3, fun x hx => blockSolution_apply_not_mem (G ω) (S ω) (B ω) (u ω) hx⟩

end MeasurableBlock

/-! ### A varying boundary given as a measurable family of sets

A block boundary is produced as a *set* of labels — the labels whose cells meet a spatial
boundary — not as a finset. Tracing such a family onto the finite block gives a varying
finite anchor set to which the previous theorem applies. -/

section AnchorSet

variable {V : Type*} [DecidableEq V] {Ω : Type*} [MeasurableSpace Ω]

/-- The labels of a finite block that lie in an arbitrary anchor set. -/
noncomputable def anchorFinset (A : Set V) (s : Finset V) : Finset V :=
  @Finset.filter V (fun x => x ∈ A) (Classical.decPred _) s

@[simp] theorem mem_anchorFinset {A : Set V} {s : Finset V} {x : V} :
    x ∈ anchorFinset A s ↔ x ∈ s ∧ x ∈ A := by
  simp only [anchorFinset, Finset.mem_filter]

/-- Tracing the anchor set onto the block does not change the induced anchor set. -/
theorem inducedAnchorSet_anchorFinset (A : Set V) (s : Finset V) :
    AnchoredFiniteExhaustion.inducedAnchorSet
        (((anchorFinset A s : Finset V) : Set V)) ((s : Set V))
      = AnchoredFiniteExhaustion.inducedAnchorSet A ((s : Set V)) := by
  ext x
  simp only [AnchoredFiniteExhaustion.mem_inducedAnchorSet, Finset.mem_coe, mem_anchorFinset]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_coe.1 x.2, h⟩⟩

/-- **The traced anchor family is measurably varying.** Its value is determined by the
finitely many measurable events `{ω | x ∈ A ω}` with `x` in the block. -/
theorem measurableSet_anchorFinset_eq {A : Ω → Set V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω}) (s b : Finset V) :
    MeasurableSet {ω | anchorFinset (A ω) s = b} := by
  by_cases hsub : b ⊆ s
  · have hset : {ω | anchorFinset (A ω) s = b}
        = ⋂ x ∈ (s : Set V), {ω | (x ∈ A ω) ↔ (x ∈ b)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_coe]
      constructor
      · intro h x hx
        constructor
        · intro hxA
          have hxs : x ∈ anchorFinset (A ω) s := mem_anchorFinset.2 ⟨hx, hxA⟩
          rw [h] at hxs
          exact hxs
        · intro hxb
          have hxs : x ∈ anchorFinset (A ω) s := by rw [h]; exact hxb
          exact (mem_anchorFinset.1 hxs).2
      · intro h
        ext y
        rw [mem_anchorFinset]
        constructor
        · rintro ⟨hy, hyA⟩
          exact (h y hy).1 hyA
        · intro hyb
          exact ⟨hsub hyb, (h y (hsub hyb)).2 hyb⟩
    rw [hset]
    refine MeasurableSet.biInter s.finite_toSet.countable fun x _ => ?_
    by_cases hxb : x ∈ b
    · have hEq : {ω | (x ∈ A ω) ↔ (x ∈ b)} = {ω | x ∈ A ω} := by
        ext ω
        simp [hxb]
      rw [hEq]
      exact hA x
    · have hEq : {ω | (x ∈ A ω) ↔ (x ∈ b)} = {ω | x ∈ A ω}ᶜ := by
        ext ω
        simp [hxb]
      rw [hEq]
      exact (hA x).compl
  · have hset : {ω | anchorFinset (A ω) s = b} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      refine hsub fun y hy => ?_
      have hy' : y ∈ anchorFinset (A ω) s := by rw [h]; exact hy
      exact (mem_anchorFinset.1 hy').1
    rw [hset]
    exact MeasurableSet.empty

/-- **The anchor family traced onto a varying block is measurably varying.** -/
theorem measurableSet_anchorFinset_block_eq [Countable V] {A : Ω → Set V} {S : Ω → Finset V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω})
    (hS : ∀ s : Finset V, MeasurableSet {ω | S ω = s}) (b : Finset V) :
    MeasurableSet {ω | anchorFinset (A ω) (S ω) = b} := by
  have hset : {ω | anchorFinset (A ω) (S ω) = b}
      = ⋃ s : Finset V, {ω | S ω = s} ∩ {ω | anchorFinset (A ω) s = b} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨S ω, rfl, h⟩
    · rintro ⟨s, hs, h⟩
      rw [hs]
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun s => (hS s).inter (measurableSet_anchorFinset_eq hA s b)

/-- **Measurable anchored minimizers on a varying finite block whose boundary is given by a
measurable family of label sets.** This is the form needed by an actual truncation: the
boundary skeleton is a set of labels, and only the measurability of the events
`{ω | x ∈ A ω}` is assumed, together with the pointwise anchoring of the block. -/
theorem exists_measurable_varying_block_minimizer_anchorSet [Countable V]
    {G : Ω → ReflectedWalk.ConductanceGraph V}
    (hG : ∀ x y : V, Measurable fun ω => (G ω).c x y) {S : Ω → Finset V}
    (hS : ∀ s : Finset V, MeasurableSet {ω | S ω = s}) {A : Ω → Set V}
    (hA : ∀ x : V, MeasurableSet {ω | x ∈ A ω})
    (hanchor : ∀ ω : Ω, BoundaryAnchored (restrictGraph (G ω) (((S ω : Finset V) : Set V)))
      (AnchoredFiniteExhaustion.inducedAnchorSet (A ω) (((S ω : Finset V) : Set V))))
    {u : Ω → V → ℝ} (hu : ∀ x : V, Measurable fun ω => u ω x) :
    ∃ f : Ω → V → ℝ, Measurable f ∧ (∀ x : V, Measurable fun ω => f ω x) ∧
      ∀ ω : Ω,
        (∀ a ∈ A ω, a ∈ S ω → f ω a = u ω a) ∧
        (restrictGraph (G ω) (((S ω : Finset V) : Set V))).IsHarmonicOn
          (fun y : ↥((S ω : Finset V) : Set V) => f ω ↑y)
          (AnchoredFiniteExhaustion.inducedAnchorSet (A ω) (((S ω : Finset V) : Set V)))ᶜ ∧
        (∀ w : V → ℝ, (∀ a ∈ A ω, a ∈ S ω → w a = u ω a) →
          restrictedEnergy (G ω) (((S ω : Finset V) : Set V)) (f ω)
            ≤ restrictedEnergy (G ω) (((S ω : Finset V) : Set V)) w) ∧
        (∀ x : V, x ∉ S ω → f ω x = u ω x) := by
  obtain ⟨f, hfmeas, hfeval, hf⟩ :=
    exists_measurable_varying_block_minimizer (G := G) hG (B := fun ω => anchorFinset (A ω) (S ω))
      hS (fun b => measurableSet_anchorFinset_block_eq hA hS b)
      (fun ω => by rw [inducedAnchorSet_anchorFinset]; exact hanchor ω) hu
  refine ⟨f, hfmeas, hfeval, fun ω => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hf ω
  rw [inducedAnchorSet_anchorFinset] at h2
  refine ⟨fun a haA haS => h1 a (mem_anchorFinset.2 ⟨haS, haA⟩) haS, h2, ?_, h4⟩
  intro w hw
  exact h3 w fun a ha haS => hw a (mem_anchorFinset.1 ha).2 haS

end AnchorSet

end MeasurableBlockMinimizer

end ReflectedGMS
