/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.MarkedRootedSpecificEnergyMeasurability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable
import LatticeProb.Bonanno.ReflectedGMS.HarmonicCoordinateAssembly

/-!
# Measurability of the rooted specific-energy density of a label-indexed field

`RootDensities.rootedSpecificEnergyDensity (decode e) Φ 0` reads the vertex observable
`ρ_Φ(H) = (2 a_H)⁻¹ ∑_{H' ∼ H} c(H,H') ‖Φ(H') − Φ(H)‖²` at the root cell of the origin.  It
is not measurable by construction: the vertex type `Code.Vertex e.val` varies with the
environment, and the root is selected by the *geometric* test `RootDensities.rootAt`, which
is a choice.  Three of the four clauses of
`HarmonicCoordinateAssembly.MarkedDensityMeasurability` are instances of exactly this
observable, and the assembly records that the project has no producer for any of them.

This module supplies the producer, for an arbitrary parameter space.

## The route

It is the slot-sum technique of `Spatial/RootedFiniteEnergyDensityMeasurable`, transported
from the (FE) density to the specific energy of a field:

* `slotSpecificEnergyDensity` is the observable written at a **code label**: the series over
  all labels `k` of `ofReal c(n,k) · ofReal ‖Ψ_k − Ψ_n‖²`, divided by twice the volume of the
  cell stored in slot `n`.  Absent labels carry zero conductance by the `absent` clause of
  `Code.AdmissibleConductance`, so the series agrees with the sum over the decoded vertex type
  (`slotSpecificEnergyDensity_eq`) and vanishes identically at an absent slot
  (`slotSpecificEnergyDensity_of_absent`).  Its measurability is `Measurable.ennreal_tsum`
  together with `Spatial.measurable_cellVolume`.
* `rootSlotSet E n` is the event that the origin lies in the interior of the cell of slot `n`;
  it is measurable by `Spatial.measurableSet_cellInterior`.  The disjoint-interiors clause of
  `Geometry`, which holds at *every* environment, makes at most one label qualify, so the sum
  `slotSpecificSum` of the corresponding indicators collapses to the root term off the global
  boundary mask.
* On the boundary mask the rooted density is zero by convention, so the masked observable is
  the mask-complement indicator of the slot sum
  (`rootedSpecificEnergyDensity_eq_indicator`), and the mask is measurable by
  `RootedFiniteEnergyDensityMeasurable.measurableSet_maskSet`.

The conclusion `measurable_rootedSpecificEnergyDensity` is **unconditional**: it assumes only
that the parameter map into `Env` and each label of the field are measurable.  No mass
transport, no moment condition and no almost-sure hypothesis is used, and the field is
completely arbitrary — in particular it is not assumed harmonic, bounded or of finite energy.

## Scope

Nothing here asserts that any particular field has finite specific energy, nor that the
concrete interpolants `DyadicApproximation.phi` are measurable at all: the latter is the
separate input `hmeas` of the harmonic-coordinate assembly, and it enters below only as a
hypothesis.  This file is the measurable-representative step between them.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.MarkedRootedSpecificEnergyMeasurability

open Code StatementIngredients RootDensities
open RootedFiniteEnergyDensityMeasurable

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The specific-energy density read at a code label -/

/-- **The specific-energy density at a code label.**  The series runs over *all* labels;
absent labels contribute nothing because their conductance row vanishes.  The cell of an
absent slot reads as `Spatial.referenceCell`, which is never used: the whole expression
vanishes there. -/
noncomputable def slotSpecificEnergyDensity (E : Ω → Env) (Ψ : Ω → ℕ → Plane)
    (ω : Ω) (n : ℕ) : ℝ≥0∞ :=
  (∑' k : ℕ, ENNReal.ofReal ((E ω).val.2 n k) * ENNReal.ofReal (‖Ψ ω k - Ψ ω n‖ ^ 2)) /
    (2 * volume (slotCell (E ω) n : Set Plane))

/-- The summand is supported on active labels. -/
theorem support_slotSpecificSummand (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω) (n : ℕ) :
    Function.support (fun k : ℕ =>
        ENNReal.ofReal ((E ω).val.2 n k) * ENNReal.ofReal (‖Ψ ω k - Ψ ω n‖ ^ 2))
      ⊆ {k : ℕ | ((E ω).val.1 k).isSome} := by
  intro k hk
  by_contra hmem
  have hnone : (E ω).val.1 k = none := by
    rw [← Option.not_isSome_iff_eq_none]
    exact hmem
  have hc : (E ω).val.2 n k = 0 := (admissible (E ω)).absent n k (Or.inr hnone)
  exact hk (by simp [hc])

/-- **An absent slot contributes nothing.** -/
theorem slotSpecificEnergyDensity_of_absent (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω)
    {n : ℕ} (hn : (E ω).val.1 n = none) : slotSpecificEnergyDensity E Ψ ω n = 0 := by
  have hz : ∀ k : ℕ,
      ENNReal.ofReal ((E ω).val.2 n k) * ENNReal.ofReal (‖Ψ ω k - Ψ ω n‖ ^ 2) = 0 := by
    intro k
    rw [(admissible (E ω)).absent n k (Or.inl hn)]
    simp
  rw [slotSpecificEnergyDensity, tsum_congr hz, tsum_zero, ENNReal.zero_div]

/-- **The label form is the decoded form.**  At an active label the slot observable is
`RootDensities.specificEnergyDensity` of the decoded environment, for the field obtained by
reading `Ψ` at the labels of the vertices. -/
theorem slotSpecificEnergyDensity_eq (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω)
    (v : Vertex (E ω).val) :
    slotSpecificEnergyDensity E Ψ ω v.val
      = specificEnergyDensity (decode (E ω)) (fun w : Vertex (E ω).val => Ψ ω w.val) v := by
  have htsum := tsum_subtype_eq_of_support_subset (support_slotSpecificSummand E Ψ ω v.val)
  have harea : (2 : ℝ≥0∞) * volume (slotCell (E ω) v.val : Set Plane)
      = 2 * ENNReal.ofReal (cellArea (decode (E ω)) v) := by
    rw [slotCell_eq_cell, cellArea,
      ENNReal.ofReal_toReal
        (cellVolume_pos_lt_top (decode (E ω)) (decode_geometry (E ω)) v).2.ne]
  calc slotSpecificEnergyDensity E Ψ ω v.val
      = (∑' k : ℕ,
            ENNReal.ofReal ((E ω).val.2 v.val k) * ENNReal.ofReal (‖Ψ ω k - Ψ ω v.val‖ ^ 2)) /
          (2 * ENNReal.ofReal (cellArea (decode (E ω)) v)) := by
        rw [slotSpecificEnergyDensity, harea]
    _ = (∑' k : {k : ℕ | ((E ω).val.1 k).isSome},
            ENNReal.ofReal ((E ω).val.2 v.val k.val) *
              ENNReal.ofReal (‖Ψ ω k.val - Ψ ω v.val‖ ^ 2)) /
          (2 * ENNReal.ofReal (cellArea (decode (E ω)) v)) := by
        rw [htsum]
    _ = (∑' w : Vertex (E ω).val, ENNReal.ofReal ((E ω).val.2 v.val w.val) *
            ENNReal.ofReal (‖Ψ ω w.val - Ψ ω v.val‖ ^ 2)) /
          (2 * ENNReal.ofReal (cellArea (decode (E ω)) v)) := rfl
    _ = specificEnergyDensity (decode (E ω)) (fun w : Vertex (E ω).val => Ψ ω w.val) v := rfl

theorem measurable_slotSpecificEnergyDensity {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) (n : ℕ) :
    Measurable fun ω : Ω => slotSpecificEnergyDensity E Ψ ω n := by
  have hnum : ∀ k : ℕ, Measurable fun ω : Ω =>
      ENNReal.ofReal ((E ω).val.2 n k) * ENNReal.ofReal (‖Ψ ω k - Ψ ω n‖ ^ 2) :=
    fun k => (((measurable_conductance_env n k).comp hE).ennreal_ofReal).mul
      ((((hΨ k).sub (hΨ n)).norm.pow_const 2).ennreal_ofReal)
  have hden : Measurable fun ω : Ω => (2 : ℝ≥0∞) * volume (slotCell (E ω) n : Set Plane) :=
    measurable_const.mul
      (Spatial.measurable_cellVolume.comp ((measurable_slotCell_env n).comp hE))
  exact (Measurable.ennreal_tsum hnum).div hden

/-! ### The root slot and the slot sum -/

/-- The event that the origin lies in the interior of the cell of slot `n`.  Off the global
boundary mask exactly one label qualifies, and it is the root label. -/
def rootSlotSet (E : Ω → Env) (n : ℕ) : Set Ω :=
  {ω : Ω | (0 : Plane) ∈ interior (slotCell (E ω) n : Set Plane)}

theorem measurableSet_rootSlotSet {E : Ω → Env} (hE : Measurable E) (n : ℕ) :
    MeasurableSet (rootSlotSet E n) :=
  ((((measurable_slotCell_env n).comp hE).prodMk measurable_const))
    Spatial.measurableSet_cellInterior

/-- **The slot sum**: the label observable summed over the labels whose cell interior
contains the origin.  At most one term is nonzero. -/
noncomputable def slotSpecificSum (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω) : ℝ≥0∞ :=
  ∑' n : ℕ, (rootSlotSet E n).indicator
    (fun ω' : Ω => slotSpecificEnergyDensity E Ψ ω' n) ω

theorem measurable_slotSpecificSum {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) :
    Measurable (slotSpecificSum E Ψ) :=
  Measurable.ennreal_tsum fun n =>
    (measurable_slotSpecificEnergyDensity hE hΨ n).indicator (measurableSet_rootSlotSet hE n)

/-- **Off the boundary mask the slot sum is the rooted specific energy.** -/
theorem slotSpecificSum_eq_of_notMem_boundaryMask (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω)
    (hz : (0 : Plane) ∉ boundaryMask (decode (E ω))) :
    slotSpecificSum E Ψ ω
      = rootedSpecificEnergyDensity (decode (E ω))
          (fun v : Vertex (E ω).val => Ψ ω v.val) 0 := by
  have hgeom := decode_geometry (E ω)
  obtain ⟨v, hv, hint⟩ := rootAt_eq_some_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
  have huniq := existsUnique_interiorRoot_of_not_mem_boundaryMask (decode (E ω)) hgeom hz
  have hsingle : ∀ n : ℕ, n ≠ v.val →
      (rootSlotSet E n).indicator
        (fun ω' : Ω => slotSpecificEnergyDensity E Ψ ω' n) ω = 0 := by
    intro n hn
    cases hcase : (E ω).val.1 n with
    | none =>
        by_cases hmem : ω ∈ rootSlotSet E n
        · rw [Set.indicator_of_mem hmem,
            slotSpecificEnergyDensity_of_absent E Ψ ω hcase]
        · rw [Set.indicator_of_notMem hmem]
    | some K =>
        have hsome : ((E ω).val.1 n).isSome := by rw [hcase]; rfl
        have hne : (⟨n, hsome⟩ : Vertex (E ω).val) ≠ v := fun h => hn (congrArg Subtype.val h)
        have hnot : ω ∉ rootSlotSet E n := by
          intro hmem
          have hmem' : (0 : Plane) ∈ interior ((decode (E ω)).cell ⟨n, hsome⟩ : Set Plane) := by
            rw [← slotCell_eq_cell (E ω) ⟨n, hsome⟩]
            exact hmem
          exact hne (huniq.unique hmem' hint)
        rw [Set.indicator_of_notMem hnot]
  have hmemv : ω ∈ rootSlotSet E v.val := by
    show (0 : Plane) ∈ interior (slotCell (E ω) v.val : Set Plane)
    rw [slotCell_eq_cell]
    exact hint
  rw [slotSpecificSum, tsum_eq_single v.val hsingle, Set.indicator_of_mem hmemv,
    slotSpecificEnergyDensity_eq, rootedSpecificEnergyDensity, hv]
  rfl

/-! ### The masked observable and its measurability -/

/-- The global boundary mask at the origin, as an event of the parameter space. -/
def maskAt (E : Ω → Env) : Set Ω :=
  {ω : Ω | (0 : Plane) ∈ boundaryMask (decode (E ω))}

theorem measurableSet_maskAt {E : Ω → Env} (hE : Measurable E) : MeasurableSet (maskAt E) := by
  have hpre : maskAt E = (fun ω : Ω => ((E ω, (0 : Plane)) : Env × Plane)) ⁻¹' maskSet := rfl
  rw [hpre]
  exact (hE.prodMk measurable_const) measurableSet_maskSet

/-- **The rooted specific energy is the mask-complement indicator of the slot sum.** -/
theorem rootedSpecificEnergyDensity_eq_indicator (E : Ω → Env) (Ψ : Ω → ℕ → Plane) (ω : Ω) :
    rootedSpecificEnergyDensity (decode (E ω)) (fun v : Vertex (E ω).val => Ψ ω v.val) 0
      = Set.indicator (maskAt E)ᶜ (slotSpecificSum E Ψ) ω := by
  by_cases hz : (0 : Plane) ∈ boundaryMask (decode (E ω))
  · have hmem : ω ∉ (maskAt E)ᶜ := fun h => h hz
    rw [Set.indicator_of_notMem hmem]
    exact rootedSpecificEnergyDensity_eq_zero_of_mem_boundaryMask (decode (E ω)) _ hz
  · have hmem : ω ∈ (maskAt E)ᶜ := hz
    rw [Set.indicator_of_mem hmem]
    exact (slotSpecificSum_eq_of_notMem_boundaryMask E Ψ ω hz).symm

/-- **Measurability of the rooted specific-energy density of a label-indexed field.**

Unconditional: only measurability of the parameter map into `Env` and of every label of the
field is used.  The field is arbitrary — no harmonicity, no bound and no finite energy. -/
theorem measurable_rootedSpecificEnergyDensity {E : Ω → Env} (hE : Measurable E)
    {Ψ : Ω → ℕ → Plane} (hΨ : ∀ n : ℕ, Measurable fun ω : Ω => Ψ ω n) :
    Measurable fun ω : Ω =>
      rootedSpecificEnergyDensity (decode (E ω)) (fun v : Vertex (E ω).val => Ψ ω v.val) 0 := by
  have hEq : (fun ω : Ω =>
        rootedSpecificEnergyDensity (decode (E ω)) (fun v : Vertex (E ω).val => Ψ ω v.val) 0)
      = Set.indicator (maskAt E)ᶜ (slotSpecificSum E Ψ) :=
    funext (rootedSpecificEnergyDensity_eq_indicator E Ψ)
  rw [hEq]
  exact (measurable_slotSpecificSum hE hΨ).indicator (measurableSet_maskAt hE).compl

end ReflectedGMS.MarkedRootedSpecificEnergyMeasurability
