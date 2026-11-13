/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.AELineConnectivity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.Geometry
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.AENullSet

/-! # Almost-everywhere line connectivity -/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS

/-- The closed horizontal segment `[a,b] × {y}` in the Euclidean plane. -/
def horizontal (a b y : ℝ) : Set Plane :=
  {z | a ≤ z 0 ∧ z 0 ≤ b ∧ z 1 = y}

/-- The closed vertical segment `{x} × [a,b]` in the Euclidean plane. -/
def vertical (x a b : ℝ) : Set Plane :=
  {z | z 0 = x ∧ a ≤ z 1 ∧ z 1 ≤ b}

theorem vertical_nonempty {x a b : ℝ} (hab : a ≤ b) :
    (vertical x a b).Nonempty := by
  refine ⟨WithLp.toLp 2 ![x, a], ?_⟩
  simp [vertical, hab]

/-- Every nondegenerate horizontal segment at offset `y` is reachable. -/
def HorizontalGood {V : Type*} (F : IndexedCells V) (y : ℝ) : Prop :=
  ∀ a b : ℝ, a < b → SegmentReachable F (horizontal a b y)

/-- Every nondegenerate vertical segment at offset `x` is reachable. -/
def VerticalGood {V : Type*} (F : IndexedCells V) (x : ℝ) : Prop :=
  ∀ a b : ℝ, a < b → SegmentReachable F (vertical x a b)

theorem horizontalGood_iff_finiteWalk {V : Type*} (F : IndexedCells V) (y : ℝ) :
    HorizontalGood F y ↔
      ∀ a b : ℝ, a < b → ∀ v w,
        Hits F (horizontal a b y) v → Hits F (horizontal a b y) w →
          ∃ p : F.graph.toSimpleGraph.Walk v w,
            ∀ z ∈ p.support, Hits F (horizontal a b y) z := by
  constructor
  · intro h a b hab
    exact (segmentReachable_iff_finiteWalk F (horizontal a b y)).mp (h a b hab)
  · intro h a b hab
    exact (segmentReachable_iff_finiteWalk F (horizontal a b y)).mpr (h a b hab)

theorem verticalGood_iff_finiteWalk {V : Type*} (F : IndexedCells V) (x : ℝ) :
    VerticalGood F x ↔
      ∀ a b : ℝ, a < b → ∀ v w,
        Hits F (vertical x a b) v → Hits F (vertical x a b) w →
          ∃ p : F.graph.toSimpleGraph.Walk v w,
            ∀ z ∈ p.support, Hits F (vertical x a b) z := by
  constructor
  · intro h a b hab
    exact (segmentReachable_iff_finiteWalk F (vertical x a b)).mp (h a b hab)
  · intro h a b hab
    exact (segmentReachable_iff_finiteWalk F (vertical x a b)).mpr (h a b hab)

/-- Almost every offset is good simultaneously for every real endpoint pair. -/
def AELineConnected {V : Type*} (F : IndexedCells V) : Prop :=
  (∀ᵐ y ∂volume, HorizontalGood F y) ∧
    ∀ᵐ x ∂volume, VerticalGood F x

/-- AE-LC via two measurable null exceptional sets. -/
def AELineConnectedOutsideNullSets {V : Type*} (F : IndexedCells V) : Prop :=
  ∃ Nh Nv : Set ℝ,
    MeasurableSet Nh ∧ volume Nh = 0 ∧
    MeasurableSet Nv ∧ volume Nv = 0 ∧
    (∀ y, y ∉ Nh → HorizontalGood F y) ∧
    ∀ x, x ∉ Nv → VerticalGood F x

theorem aeLineConnected_iff_exists_measurable_null_sets {V : Type*}
    (F : IndexedCells V) :
    AELineConnected F ↔ AELineConnectedOutsideNullSets F := by
  constructor
  · rintro ⟨hh, hv⟩
    rcases (ae_iff_exists_measurable_null_set volume (HorizontalGood F)).mp hh with
      ⟨Nh, hNhMeasurable, hNhNull, hNh⟩
    rcases (ae_iff_exists_measurable_null_set volume (VerticalGood F)).mp hv with
      ⟨Nv, hNvMeasurable, hNvNull, hNv⟩
    exact ⟨Nh, Nv, hNhMeasurable, hNhNull, hNvMeasurable, hNvNull, hNh, hNv⟩
  · rintro ⟨Nh, Nv, hNhMeasurable, hNhNull, hNvMeasurable, hNvNull, hNh, hNv⟩
    constructor
    · exact (ae_iff_exists_measurable_null_set volume (HorizontalGood F)).mpr
        ⟨Nh, hNhMeasurable, hNhNull, hNh⟩
    · exact (ae_iff_exists_measurable_null_set volume (VerticalGood F)).mpr
        ⟨Nv, hNvMeasurable, hNvNull, hNv⟩

end ReflectedGMS
