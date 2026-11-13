/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Spatial.RootedFiniteEnergyDensityMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NullBoundaryRoots
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds

/-!
# Joint measurability of the boundary-masked (FE) density

The rooted finite-energy density `ρ_FE(𝓗, z) = 1_{z ∉ ∂𝓗} (d² / a)(H_z) (π + π*)(H_z)` of
`RootDensities.rootedFiniteEnergyDensity` is defined through the root selector
`RootDensities.rootAt`, which is a choice; it is not measurable by construction.  This file
proves that `(e, z) ↦ ρ_FE(decode e, z)` is jointly measurable for the product of the trace
sigma algebra of `Code.Env` and the Borel sigma algebra of the plane, and specialises to the
environment observable `e ↦ ρ_FE(decode e, 0)`.

The route is the slot-sum technique of `Spatial.boundaryTransport`: every code slot `n : ℕ`
contributes the jointly measurable term
`1_{z ∈ int H_n} · d(H_n)² / a(H_n) · (∑_m ofReal c(n, m) + ∑_m ofReal c(n, m)⁻¹)`,
read through `Option.getD referenceCell`.  Absent slots contribute nothing because their
conductance rows vanish (`Code.AdmissibleConductance.absent`), and off the boundary mask the
unique interior root is the only present slot whose interior indicator is nonzero
(`Geometry`'s disjoint interiors).  The boundary mask itself is the countable union of the
measurable present-slot frontier conditions.  The masked density is then the indicator of the
mask complement applied to the slot sum.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS.RootedFiniteEnergyDensityMeasurable

open Code Spatial

/-! ### Slot-indexed ingredients -/

/-- The cell read at code slot `n`, with the reference cell at absent slots. -/
noncomputable def slotCell (e : Env) (n : ℕ) : CompactCell :=
  (e.val.1 n).getD referenceCell

theorem measurable_slotCell_env (n : ℕ) : Measurable fun e : Env => slotCell e n :=
  measurable_slotCell.comp
    ((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion))

theorem slotCell_eq_cell (e : Env) (v : Vertex e.val) :
    slotCell e v.val = (decode e).cell v := by
  have hv : e.val.1 v.val = some ((decode e).cell v) := (Option.some_get v.property).symm
  rw [slotCell, hv, Option.getD_some]

/-- The admissibility witness of a valid code. -/
theorem admissible (e : Env) : AdmissibleConductance e.val := e.property.choose

theorem measurable_conductance_env (n m : ℕ) : Measurable fun e : Env => e.val.2 n m :=
  (measurable_pi_apply m).comp
    ((measurable_pi_apply n).comp (measurable_snd.comp measurable_inclusion))

/-- The slot form of `ofReal (π(H_n))`: the conductance row summed over all slots. -/
noncomputable def slotConductanceMass (e : Env) (n : ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal (e.val.2 n m)

/-- The slot form of `ofReal (π*(H_n))`: the reciprocal conductance row summed over all
slots. -/
noncomputable def slotResistanceMass (e : Env) (n : ℕ) : ℝ≥0∞ :=
  ∑' m : ℕ, ENNReal.ofReal ((e.val.2 n m)⁻¹)

theorem measurable_slotConductanceMass (n : ℕ) :
    Measurable fun e : Env => slotConductanceMass e n :=
  Measurable.ennreal_tsum fun m => (measurable_conductance_env n m).ennreal_ofReal

theorem measurable_slotResistanceMass (n : ℕ) :
    Measurable fun e : Env => slotResistanceMass e n :=
  Measurable.ennreal_tsum fun m => (measurable_conductance_env n m).inv.ennreal_ofReal

theorem slotConductanceMass_of_absent (e : Env) {n : ℕ} (hn : e.val.1 n = none) :
    slotConductanceMass e n = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun m => ?_
  rw [(admissible e).absent n m (Or.inl hn), ENNReal.ofReal_zero]

theorem slotResistanceMass_of_absent (e : Env) {n : ℕ} (hn : e.val.1 n = none) :
    slotResistanceMass e n = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun m => ?_
  rw [(admissible e).absent n m (Or.inl hn), inv_zero, ENNReal.ofReal_zero]

/-- The conductance row of a present slot is supported on present slots. -/
theorem support_conductance_row_subset (e : Env) (n : ℕ) :
    Function.support (fun m : ℕ => ENNReal.ofReal (e.val.2 n m))
      ⊆ {m : ℕ | (e.val.1 m).isSome} := by
  intro m hm
  by_contra hnone
  have hmn : e.val.1 m = none := Option.not_isSome_iff_eq_none.mp hnone
  apply hm
  show ENNReal.ofReal (e.val.2 n m) = 0
  rw [(admissible e).absent n m (Or.inr hmn), ENNReal.ofReal_zero]

theorem support_resistance_row_subset (e : Env) (n : ℕ) :
    Function.support (fun m : ℕ => ENNReal.ofReal ((e.val.2 n m)⁻¹))
      ⊆ {m : ℕ | (e.val.1 m).isSome} := by
  intro m hm
  by_contra hnone
  have hmn : e.val.1 m = none := Option.not_isSome_iff_eq_none.mp hnone
  apply hm
  show ENNReal.ofReal ((e.val.2 n m)⁻¹) = 0
  rw [(admissible e).absent n m (Or.inr hmn), inv_zero, ENNReal.ofReal_zero]

theorem ofReal_pi_eq_slotConductanceMass (e : Env) (v : Vertex e.val) :
    ENNReal.ofReal (RootDensities.pi (decode e) v) = slotConductanceMass e v.val := by
  have hnn : ∀ w : Vertex e.val, 0 ≤ e.val.2 v.val w.val := fun w =>
    (admissible e).nonneg v.val w.val
  have hsum : Summable fun w : Vertex e.val => e.val.2 v.val w.val :=
    (decode e).graph.summable_c v
  calc ENNReal.ofReal (RootDensities.pi (decode e) v)
      = ENNReal.ofReal (∑' w : Vertex e.val, e.val.2 v.val w.val) := rfl
    _ = ∑' w : Vertex e.val, ENNReal.ofReal (e.val.2 v.val w.val) :=
        ENNReal.ofReal_tsum_of_nonneg hnn hsum
    _ = ∑' m : {m : ℕ | (e.val.1 m).isSome}, ENNReal.ofReal (e.val.2 v.val m.val) := rfl
    _ = ∑' m : ℕ, ENNReal.ofReal (e.val.2 v.val m) :=
        tsum_subtype_eq_of_support_subset (support_conductance_row_subset e v.val)

theorem ofReal_piStar_eq_slotResistanceMass (e : Env) (v : Vertex e.val) :
    ENNReal.ofReal (RootDensities.piStar (decode e) v) = slotResistanceMass e v.val := by
  have hnn : ∀ w : Vertex e.val, 0 ≤ (e.val.2 v.val w.val)⁻¹ := fun w =>
    inv_nonneg.mpr ((admissible e).nonneg v.val w.val)
  have hsum : Summable fun w : Vertex e.val => (e.val.2 v.val w.val)⁻¹ := by
    apply summable_of_hasFiniteSupport
    show (Function.support fun w : Vertex e.val => (e.val.2 v.val w.val)⁻¹).Finite
    rw [Function.support_inv]
    exact ((admissible e).finiteRow v.val).preimage Subtype.val_injective.injOn
  calc ENNReal.ofReal (RootDensities.piStar (decode e) v)
      = ENNReal.ofReal (∑' w : Vertex e.val, (e.val.2 v.val w.val)⁻¹) := rfl
    _ = ∑' w : Vertex e.val, ENNReal.ofReal ((e.val.2 v.val w.val)⁻¹) :=
        ENNReal.ofReal_tsum_of_nonneg hnn hsum
    _ = ∑' m : {m : ℕ | (e.val.1 m).isSome}, ENNReal.ofReal ((e.val.2 v.val m.val)⁻¹) := rfl
    _ = ∑' m : ℕ, ENNReal.ofReal ((e.val.2 v.val m)⁻¹) :=
        tsum_subtype_eq_of_support_subset (support_resistance_row_subset e v.val)

/-- The slot form of the vertex integrand `d² / a · (π + π*)` at slot `n`. -/
noncomputable def slotEnergyDensity (e : Env) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (slotCell e n : Set Plane) ^ 2) /
      volume (slotCell e n : Set Plane) *
    (slotConductanceMass e n + slotResistanceMass e n)

theorem measurable_slotEnergyDensity (n : ℕ) :
    Measurable fun e : Env => slotEnergyDensity e n := by
  have hdiam : Measurable fun e : Env =>
      ENNReal.ofReal (Metric.diam (slotCell e n : Set Plane) ^ 2) :=
    ((measurable_cellDiam.comp (measurable_slotCell_env n)).pow_const 2).ennreal_ofReal
  have hvol : Measurable fun e : Env => volume (slotCell e n : Set Plane) :=
    measurable_cellVolume.comp (measurable_slotCell_env n)
  exact (hdiam.div hvol).mul
    ((measurable_slotConductanceMass n).add (measurable_slotResistanceMass n))

theorem slotEnergyDensity_of_absent (e : Env) {n : ℕ} (hn : e.val.1 n = none) :
    slotEnergyDensity e n = 0 := by
  rw [slotEnergyDensity, slotConductanceMass_of_absent e hn, slotResistanceMass_of_absent e hn,
    add_zero, mul_zero]

theorem slotEnergyDensity_eq_finiteEnergyDensity (e : Env) (v : Vertex e.val) :
    slotEnergyDensity e v.val = RootDensities.finiteEnergyDensity (decode e) v := by
  have harea : ENNReal.ofReal (StatementIngredients.cellArea (decode e) v)
      = volume ((decode e).cell v : Set Plane) := by
    rw [StatementIngredients.cellArea,
      ENNReal.ofReal_toReal (cellVolume_pos_lt_top (decode e) (decode_geometry e) v).2.ne]
  rw [slotEnergyDensity, RootDensities.finiteEnergyDensity, slotCell_eq_cell, harea,
    ofReal_pi_eq_slotConductanceMass, ofReal_piStar_eq_slotResistanceMass]

/-! ### The slot sum and the boundary mask on `Env × Plane` -/

/-- The contribution of slot `n` at the pair `(e, z)`: the interior indicator of the slot
cell times the slot energy density. -/
noncomputable def slotTerm (q : Env × Plane) (n : ℕ) : ℝ≥0∞ :=
  Set.indicator (interior (slotCell q.1 n : Set Plane)) (fun _ => (1 : ℝ≥0∞)) q.2 *
    slotEnergyDensity q.1 n

theorem measurable_slotTerm (n : ℕ) : Measurable fun q : Env × Plane => slotTerm q n := by
  have hpair : Measurable fun q : Env × Plane => (slotCell q.1 n, q.2) :=
    ((measurable_slotCell_env n).comp measurable_fst).prodMk measurable_snd
  have hind : Measurable fun q : Env × Plane =>
      Set.indicator {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)}
        (fun _ => (1 : ℝ≥0∞)) (slotCell q.1 n, q.2) :=
    (measurable_const.indicator measurableSet_cellInterior).comp hpair
  have hEq : (fun q : Env × Plane =>
        Set.indicator (interior (slotCell q.1 n : Set Plane)) (fun _ => (1 : ℝ≥0∞)) q.2)
      = fun q : Env × Plane =>
        Set.indicator {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)}
          (fun _ => (1 : ℝ≥0∞)) (slotCell q.1 n, q.2) := by
    funext q
    by_cases hq : q.2 ∈ interior (slotCell q.1 n : Set Plane)
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem
        (show (slotCell q.1 n, q.2) ∈
          {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} from hq)]
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem
        (show (slotCell q.1 n, q.2) ∉
          {p : CompactCell × Plane | p.2 ∈ interior (p.1 : Set Plane)} from hq)]
  have hind' : Measurable fun q : Env × Plane =>
      Set.indicator (interior (slotCell q.1 n : Set Plane)) (fun _ => (1 : ℝ≥0∞)) q.2 := by
    rw [hEq]
    exact hind
  exact hind'.mul ((measurable_slotEnergyDensity n).comp measurable_fst)

/-- The unmasked slot sum `∑_n 1_{z ∈ int H_n} d(H_n)² / a(H_n) (π + π*)(H_n)`. -/
noncomputable def slotDensitySum (q : Env × Plane) : ℝ≥0∞ :=
  ∑' n : ℕ, slotTerm q n

theorem measurable_slotDensitySum : Measurable slotDensitySum :=
  Measurable.ennreal_tsum measurable_slotTerm

/-- The boundary mask as a subset of the product space. -/
def maskSet : Set (Env × Plane) :=
  {q | q.2 ∈ RootDensities.boundaryMask (decode q.1)}

/-- The covered part of the product space, as a countable union over code slots.  Its complement is
the uncovered part of the boundary mask. -/
def coveredProdSet : Set (Env × Plane) :=
  ⋃ n : ℕ, ({q : Env × Plane | (q.1.val.1 n).isSome} ∩
    {q : Env × Plane | q.2 ∈ (slotCell q.1 n : Set Plane)})

theorem mem_coveredProdSet_iff (e : Env) (z : Plane) :
    ((e, z) ∈ coveredProdSet) ↔ z ∈ ⋃ v, ((decode e).cell v : Set Plane) := by
  constructor
  · intro hq
    obtain ⟨n, hn, hz⟩ := mem_iUnion.mp hq
    refine mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩
    rw [← slotCell_eq_cell e ⟨n, hn⟩]
    exact hz
  · intro hz
    obtain ⟨v, hv⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨v.val, v.property, ?_⟩
    show z ∈ (slotCell e v.val : Set Plane)
    rw [slotCell_eq_cell e v]
    exact hv

theorem measurableSet_coveredProdSet : MeasurableSet coveredProdSet := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_
  · exact (((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)).comp
      measurable_fst) measurableSet_slotIsSome
  · exact (((measurable_slotCell_env n).comp measurable_fst).prodMk measurable_snd)
      measurableSet_cellMem

/-- The mask splits into the slotwise frontier part and the complement of the covered part; the
second summand is what the weakened covering clause of `Geometry` contributes. -/
theorem maskSet_eq_iUnion :
    maskSet = (⋃ n : ℕ, ({q : Env × Plane | (q.1.val.1 n).isSome} ∩
      {q : Env × Plane | q.2 ∈ frontier (slotCell q.1 n : Set Plane)})) ∪ coveredProdSetᶜ := by
  ext ⟨e, z⟩
  show (z ∈ (⋃ v, frontier ((decode e).cell v : Set Plane)) ∪ uncoveredSet (decode e)) ↔ _
  constructor
  · rintro (hfr | hunc)
    · obtain ⟨v, hv⟩ := mem_iUnion.mp hfr
      refine Or.inl (mem_iUnion.mpr ⟨v.val, v.property, ?_⟩)
      show z ∈ frontier (slotCell e v.val : Set Plane)
      rw [slotCell_eq_cell e v]
      exact hv
    · exact Or.inr fun hc => hunc ((mem_coveredProdSet_iff e z).mp hc)
  · rintro (hfr | hnc)
    · obtain ⟨n, hn, hz⟩ := mem_iUnion.mp hfr
      refine Or.inl (mem_iUnion.mpr ⟨⟨n, hn⟩, ?_⟩)
      rw [← slotCell_eq_cell e ⟨n, hn⟩]
      exact hz
    · exact Or.inr fun hc => hnc ((mem_coveredProdSet_iff e z).mpr hc)

theorem measurableSet_maskSet : MeasurableSet maskSet := by
  rw [maskSet_eq_iUnion]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => MeasurableSet.inter ?_ ?_)
    measurableSet_coveredProdSet.compl
  · exact (((measurable_pi_apply n).comp (measurable_fst.comp measurable_inclusion)).comp
      measurable_fst) measurableSet_slotIsSome
  · exact (((measurable_slotCell_env n).comp measurable_fst).prodMk measurable_snd)
      measurableSet_cellFrontier

/-! ### The pointwise identity and the measurability theorems -/

/-- Off the boundary mask the slot sum collapses to the root term. -/
theorem slotDensitySum_eq_of_not_mem_boundaryMask (e : Env) {z : Plane}
    (hz : z ∉ RootDensities.boundaryMask (decode e)) :
    slotDensitySum (e, z) = RootDensities.rootedFiniteEnergyDensity (decode e) z := by
  have hgeom := decode_geometry e
  obtain ⟨v, hv, hint⟩ :=
    RootDensities.rootAt_eq_some_of_not_mem_boundaryMask (decode e) hgeom hz
  have huniq := RootDensities.existsUnique_interiorRoot_of_not_mem_boundaryMask
    (decode e) hgeom hz
  have hsingle : ∀ n : ℕ, n ≠ v.val → slotTerm (e, z) n = 0 := by
    intro n hn
    cases hcase : e.val.1 n with
    | none =>
        show Set.indicator (interior (slotCell e n : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
          slotEnergyDensity e n = 0
        rw [slotEnergyDensity_of_absent e hcase, mul_zero]
    | some K =>
        have hsome : (e.val.1 n).isSome := by rw [hcase]; rfl
        have hne : (⟨n, hsome⟩ : Vertex e.val) ≠ v := fun h => hn (congrArg Subtype.val h)
        have hnot : z ∉ interior (slotCell e n : Set Plane) := by
          rw [slotCell_eq_cell e ⟨n, hsome⟩]
          intro hmem
          exact hne (huniq.unique hmem hint)
        show Set.indicator (interior (slotCell e n : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
          slotEnergyDensity e n = 0
        rw [Set.indicator_of_notMem hnot, zero_mul]
  have hroot : slotTerm (e, z) v.val = RootDensities.finiteEnergyDensity (decode e) v := by
    show Set.indicator (interior (slotCell e v.val : Set Plane)) (fun _ => (1 : ℝ≥0∞)) z *
      slotEnergyDensity e v.val = RootDensities.finiteEnergyDensity (decode e) v
    rw [slotCell_eq_cell e v, Set.indicator_of_mem hint, one_mul,
      slotEnergyDensity_eq_finiteEnergyDensity]
  rw [slotDensitySum, tsum_eq_single v.val hsingle, hroot, RootDensities.rootedFiniteEnergyDensity,
    hv]
  rfl

/-- The masked density is the mask-complement indicator of the slot sum. -/
theorem rootedFiniteEnergyDensity_eq_indicator (q : Env × Plane) :
    RootDensities.rootedFiniteEnergyDensity (decode q.1) q.2
      = Set.indicator maskSetᶜ slotDensitySum q := by
  obtain ⟨e, z⟩ := q
  by_cases hz : z ∈ RootDensities.boundaryMask (decode e)
  · have hmem : (e, z) ∉ maskSetᶜ := fun h => h hz
    rw [Set.indicator_of_notMem hmem]
    exact RootDensities.rootedFiniteEnergyDensity_eq_zero_of_mem_boundaryMask (decode e) hz
  · have hmem : (e, z) ∈ maskSetᶜ := hz
    rw [Set.indicator_of_mem hmem]
    exact (slotDensitySum_eq_of_not_mem_boundaryMask e hz).symm

/-- Joint measurability of the boundary-masked (FE) density in the environment and the
point, for the product of the trace sigma algebra of `Env` and the Borel sigma algebra of the
plane. -/
theorem measurable_rootedFiniteEnergyDensity :
    Measurable fun q : Env × Plane =>
      RootDensities.rootedFiniteEnergyDensity (decode q.1) q.2 := by
  have hEq : (fun q : Env × Plane => RootDensities.rootedFiniteEnergyDensity (decode q.1) q.2)
      = Set.indicator maskSetᶜ slotDensitySum :=
    funext rootedFiniteEnergyDensity_eq_indicator
  rw [hEq]
  exact measurable_slotDensitySum.indicator measurableSet_maskSet.compl

/-- The environment observable `e ↦ ρ_FE(decode e, 0)` is measurable on `Env`.

The composition is bridged through `Function.comp_def` with an explicitly typed `have`: a bare
`.comp` unifies against the deep `Code.decode` and the enlarged boundary mask, and exhausts the
`whnf` budget. -/
theorem measurable_rootedFiniteEnergyDensity_zero :
    Measurable fun e : Env => RootDensities.rootedFiniteEnergyDensity (decode e) 0 := by
  have h : Measurable ((fun q : Env × Plane =>
      RootDensities.rootedFiniteEnergyDensity (decode q.1) q.2) ∘
      fun e : Env => ((e, (0 : Plane)) : Env × Plane)) :=
    measurable_rootedFiniteEnergyDensity.comp (measurable_id.prodMk measurable_const)
  simpa only [Function.comp_def] using h

end ReflectedGMS.RootedFiniteEnergyDensityMeasurable
