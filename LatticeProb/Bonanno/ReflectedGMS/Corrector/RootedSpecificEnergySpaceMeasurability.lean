/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.RootedSpecificEnergySpaceMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability

/-!
# Joint measurability of the rooted specific-energy density in the **space** variable

`Corrector/MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`
proves that `ω ↦ ρ_{Φ(ω)}(H_0)` is measurable: the rooted specific-energy density of a
label-indexed field, read at the **origin**.  Every consumer of
`HarmonicCoordinateAssembly.MarkedDensityMeasurability` needs only that.

`Spatial/SpatialMaximalInequality.EnvironmentGrid` needs more.  Its `measurable_density`
field asks for joint measurability of `(ω, z) ↦ ρ_ω(z)` in the environment **and the point**,
because the manuscript's weak-`L¹` maximal inequality `s:eq:maximal` integrates the density
over balls of the plane and then applies Tonelli
(`SpatialMaximalInequality.measurable_ballAverage`).  That is the single input recorded as
open in the docstring of `Corrector/SmallBlockResidualProducer` and in the hypothesis `hjoint`
of `Corrector/SpecificEnergyWeakMaximal.measure_densityMaximal_gt_le`; it is the statement
proved here.

## The route

Exactly the slot-sum technique of `Spatial/RootedFiniteEnergyDensityMeasurable` and of
`Corrector/MarkedRootedSpecificEnergyMeasurability`, with the constant point `0` replaced by
an arbitrary measurable point map `Z : Ω → Plane`.  Nothing about the label observable changes,
so `MarkedRootedSpecificEnergyMeasurability.slotSpecificEnergyDensity` and its three lemmas
(`slotSpecificEnergyDensity_of_absent`, `slotSpecificEnergyDensity_eq`,
`measurable_slotSpecificEnergyDensity`) are reused verbatim — the point variable enters only
through

* `rootSlotSetAt`, the event `Z ω ∈ int H_n`, measurable by
  `Spatial.measurableSet_cellInterior`, which is already **jointly** measurable in the cell and
  the point (this is why no new geometry is needed);
* `maskAtPoint`, the event `Z ω ∈ ∂𝓗(E ω)`, the pullback of
  `RootedFiniteEnergyDensityMeasurable.maskSet ⊆ Env × Plane` along `ω ↦ (E ω, Z ω)`.

The disjoint-interiors clause of `Geometry`, which holds at **every** environment, again makes
at most one label qualify, so the slot sum collapses to the root term off the boundary mask.

`measurable_rootedSpecificEnergyDensity_prod` is the product form: instantiating the parameter
space at `Ω × Plane`, with `E`, `Ψ` read through the first coordinate and `Z = Prod.snd`, is
literally the `measurable_density`/`hjoint` shape.  Because the parameter space carries an
arbitrary `MeasurableSpace` instance, it may be instantiated at a **sub**-sigma-field — which
is how `EnvironmentGrid` states its field, and how `Spatial/GoodMarkedSpace` instantiates it.

## Scope

Unconditional, and the field `Ψ` is arbitrary: no harmonicity, no bound, no finite energy, no
mass transport, no moment and no almost-sure hypothesis.  In particular nothing here asserts
that `DyadicApproximation.phi` is measurable — that is the separate assembly input `hmeas`,
and it enters the consumer module only as a hypothesis.  Taking `Z = fun _ => 0` recovers
`MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`, which is
therefore not reproved but generalised.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.RootedSpecificEnergySpaceMeasurability

open Code StatementIngredients RootDensities
open RootedFiniteEnergyDensityMeasurable MarkedRootedSpecificEnergyMeasurability

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The root slot at a varying point -/

/-- The event that the sampled point `Z ω` lies in the interior of the cell of slot `n`.
Off the global boundary mask exactly one label qualifies, and it is the root label at
`Z ω`. -/
def rootSlotSetAt (E : Ω → Env) (Z : Ω → Plane) (n : ℕ) : Set Ω :=
  {ω : Ω | Z ω ∈ interior (slotCell (E ω) n : Set Plane)}

theorem measurableSet_rootSlotSetAt {E : Ω → Env} (hE : Measurable E)
    {Z : Ω → Plane} (hZ : Measurable Z) (n : ℕ) :
    MeasurableSet (rootSlotSetAt E Z n) := by
  have hpair : Measurable fun ω : Ω => (slotCell (E ω) n, Z ω) :=
    ((measurable_slotCell_env n).comp hE).prodMk hZ
  have hpre : rootSlotSetAt E Z n
      = (fun ω : Ω => (slotCell (E ω) n, Z ω)) ⁻¹'
        {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} := rfl
  rw [hpre]
  exact hpair Spatial.measurableSet_cellInterior

/-- **The slot sum at a varying point**: the label observable summed over the labels whose
cell interior contains `Z ω`.  At most one term is nonzero. -/
noncomputable def slotSpecificSumAt (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (Z : Ω → Plane)
    (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, (rootSlotSetAt E Z n).indicator
    (fun ω' : Ω => slotSpecificEnergyDensity E Ψ ω' n) ω

theorem measurable_slotSpecificSumAt {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n)
    {Z : Ω → Plane} (hZ : Measurable Z) :
    Measurable (slotSpecificSumAt E Ψ Z) :=
  Measurable.ennreal_tsum fun n =>
    (measurable_slotSpecificEnergyDensity hE hΨ n).indicator
      (measurableSet_rootSlotSetAt hE hZ n)

/-! ### The boundary mask at a varying point -/

/-- The global boundary mask read at the sampled point, as an event of the parameter
space. -/
def maskAtPoint (E : Ω → Env) (Z : Ω → Plane) : Set Ω :=
  {ω : Ω | Z ω ∈ boundaryMask (decode (E ω))}

theorem measurableSet_maskAtPoint {E : Ω → Env} (hE : Measurable E)
    {Z : Ω → Plane} (hZ : Measurable Z) : MeasurableSet (maskAtPoint E Z) := by
  have hpre : maskAtPoint E Z = (fun ω : Ω => ((E ω, Z ω) : Env × Plane)) ⁻¹' maskSet := rfl
  rw [hpre]
  exact (hE.prodMk hZ) measurableSet_maskSet

/-- **Off the boundary mask the slot sum is the rooted specific energy at the sampled
point.** -/
theorem slotSpecificSumAt_eq_of_notMem_boundaryMask (E : Ω → Env) (Ψ : Ω → ℕ → Plane)
    (Z : Ω → Plane) (ω : Ω) (hz : Z ω ∉ boundaryMask (decode (E ω))) :
    slotSpecificSumAt E Ψ Z ω
      = rootedSpecificEnergyDensity (decode (E ω))
          (fun v : Vertex (E ω).val => Ψ ω v.val) (Z ω) := by
  have hgeom := decode_geometry (E ω)
  obtain ⟨v, hv, hint⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
  have huniq := existsUnique_interiorRoot_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
  have hsingle : ∀ n : ℕ, n ≠ v.val →
      (rootSlotSetAt E Z n).indicator
        (fun ω' : Ω => slotSpecificEnergyDensity E Ψ ω' n) ω = 0 := by
    intro n hn
    cases hcase : (E ω).val.1 n with
    | none =>
        by_cases hmem : ω ∈ rootSlotSetAt E Z n
        · rw [Set.indicator_of_mem hmem,
            slotSpecificEnergyDensity_of_absent E Ψ ω hcase]
        · rw [Set.indicator_of_notMem hmem]
    | some K =>
        have hsome : ((E ω).val.1 n).isSome := by rw [hcase]; rfl
        have hne : (⟨n, hsome⟩ : Vertex (E ω).val) ≠ v := fun h => hn (congrArg Subtype.val h)
        have hnot : ω ∉ rootSlotSetAt E Z n := by
          intro hmem
          have hmem' : Z ω ∈ interior ((decode (E ω)).cell ⟨n, hsome⟩ : Set Plane) := by
            rw [← slotCell_eq_cell (E ω) ⟨n, hsome⟩]
            exact hmem
          exact hne (huniq.unique hmem' hint)
        rw [Set.indicator_of_notMem hnot]
  have hmemv : ω ∈ rootSlotSetAt E Z v.val := by
    show Z ω ∈ interior (slotCell (E ω) v.val : Set Plane)
    rw [slotCell_eq_cell]
    exact hint
  rw [slotSpecificSumAt, tsum_eq_single v.val hsingle, Set.indicator_of_mem hmemv,
    slotSpecificEnergyDensity_eq, rootedSpecificEnergyDensity, hv]
  rfl

/-! ### The masked observable and its measurability -/

/-- **The rooted specific energy at the sampled point is the mask-complement indicator of the
slot sum.** -/
theorem rootedSpecificEnergyDensity_at_eq_indicator (E : Ω → Env) (Ψ : Ω → ℕ → Plane)
    (Z : Ω → Plane) (ω : Ω) :
    rootedSpecificEnergyDensity (decode (E ω)) (fun v : Vertex (E ω).val => Ψ ω v.val) (Z ω)
      = Set.indicator (maskAtPoint E Z)ᶜ (slotSpecificSumAt E Ψ Z) ω := by
  by_cases hz : Z ω ∈ boundaryMask (decode (E ω))
  · have hmem : ω ∉ (maskAtPoint E Z)ᶜ := fun h => h hz
    rw [Set.indicator_of_notMem hmem]
    exact rootedSpecificEnergyDensity_eq_zero_of_mem_boundaryMask (decode (E ω)) _ hz
  · have hmem : ω ∈ (maskAtPoint E Z)ᶜ := hz
    rw [Set.indicator_of_mem hmem]
    exact (slotSpecificSumAt_eq_of_notMem_boundaryMask E Ψ Z ω hz).symm

/-- **Measurability of the rooted specific-energy density of a label-indexed field at a
varying point.**

Unconditional: only measurability of the parameter map into `Env`, of every label of the
field, and of the point map is used.  The field is arbitrary — no harmonicity, no bound and
no finite energy.  With `Z = fun _ => 0` this is
`MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`. -/
theorem measurable_rootedSpecificEnergyDensity_at {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n)
    {Z : Ω → Plane} (hZ : Measurable Z) :
    Measurable fun ω : Ω =>
      rootedSpecificEnergyDensity (decode (E ω))
        (fun v : Vertex (E ω).val => Ψ ω v.val) (Z ω) := by
  have hEq : (fun ω : Ω => rootedSpecificEnergyDensity (decode (E ω))
        (fun v : Vertex (E ω).val => Ψ ω v.val) (Z ω))
      = Set.indicator (maskAtPoint E Z)ᶜ (slotSpecificSumAt E Ψ Z) :=
    funext (rootedSpecificEnergyDensity_at_eq_indicator E Ψ Z)
  rw [hEq]
  exact (measurable_slotSpecificSumAt hE hΨ hZ).indicator
    (measurableSet_maskAtPoint hE hZ).compl

/-- **The `EnvironmentGrid.measurable_density` shape: joint measurability in the parameter
and the point.**

This is `measurable_rootedSpecificEnergyDensity_at` at the parameter space `Ω × Plane`.  The
`MeasurableSpace Ω` instance is arbitrary, so the statement may be instantiated at a
sub-sigma-field — which is how `Spatial/SpatialMaximalInequality.EnvironmentGrid` states its
`measurable_density` field and how `Corrector/SpecificEnergyWeakMaximal` states its `hjoint`
hypothesis. -/
theorem measurable_rootedSpecificEnergyDensity_prod {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) :
    Measurable fun q : Ω × Plane =>
      rootedSpecificEnergyDensity (decode (E q.1))
        (fun v : Vertex (E q.1).val => Ψ q.1 v.val) q.2 := by
  have hE' : Measurable fun q : Ω × Plane => E q.1 := hE.comp measurable_fst
  have hΨ' : ∀ n : ℕ, Measurable fun q : Ω × Plane => Ψ q.1 n :=
    fun n => (hΨ n).comp measurable_fst
  have hZ' : Measurable fun q : Ω × Plane => q.2 := measurable_snd
  exact measurable_rootedSpecificEnergyDensity_at hE' hΨ' hZ'

/-- The origin case, recovered: this is defeq to
`MarkedRootedSpecificEnergyMeasurability.measurable_rootedSpecificEnergyDensity`, recorded
here only to certify that the generalisation is one. -/
theorem measurable_rootedSpecificEnergyDensity_zero {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) :
    Measurable fun ω : Ω =>
      rootedSpecificEnergyDensity (decode (E ω)) (fun v : Vertex (E ω).val => Ψ ω v.val) 0 :=
  measurable_rootedSpecificEnergyDensity_at hE hΨ (Z := fun _ => (0 : Plane)) measurable_const

end ReflectedGMS.RootedSpecificEnergySpaceMeasurability
