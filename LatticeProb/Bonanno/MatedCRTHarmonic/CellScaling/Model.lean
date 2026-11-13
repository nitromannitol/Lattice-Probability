/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.Model at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.MesoInterfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs

/-!
# The SLE/LQG cone realization of the unit-mesh model, and the named inputs of the scaling and cell-count estimates

`MesoModel.MatedCRTUnitMesoModel γ` is an abstract unit-mesh model whose
`radius ω k` is an arbitrary positive number. the scaling and cell-count estimates concern the **SLE/LQG cell model**:
the field is the circle-average embedding `h` of a γ-quantum cone, `η` is an independent whole-plane
space-filling SLE parameterized by `A^γ_h`-area, the cells are `H^ε_x = η([ε(x−1), εx])`, and `R_{2^k}` is the cone
scale of that cone. `ConeRealization M` records that `M` *is* this model: it carries the cone data (whole-plane GFF `X`,
radial Brownian motions `B, B'`, curve `η`) with their defining laws, and the identifications of `M`'s radius and cells
(the mesh multigraphs are identified by the model family's own `M.coupled.meshGraph_eq`).
This also identifies the data needed for Lemma 2.7 with the coupling `MatingOfTreesInput`.

The named inputs have the following sources:
* **Coupling fields (SLE-dependent):** `BoundaryLengthCovariance` (field `boundaryLength`),
  `AreaParametrization` (bundle field `areaParam`, with `η(0) = 0`).
* **Composite:** `ConeJointScaling` (the joint-scaling identity as printed), from the SLE-free
  [14, Prop 4.13(i)], random-dilation area covariance, and the coupling fields
  `igMap`, `indep_curve`, and `areaParam`.
* **SLE-free, to prove:** `AreaScalingLaw` ([14, Prop 4.13(i)] + [SW, Thm 1.4]; CS1 + LR1), `AreaBallMoment`
  ([16, Lemma A.3]), `MeshGridEventMeasurable` (measurability of the scaled-grid estimate event as a function of the data).
* **Produced downstream (the mesoscopic argument):** `UnitCellDiamEventually` (clause (1) of the a.s. eventual unit-scale
  the scaled-grid estimate event, which `MesoModel.matedCRTUnitMesoscopicInput_of_interfaces` derives as `hEventuallyScaled`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- **The SLE/LQG cone realization of a unit-mesh model.** On the sample space of `M`:
* `X` is a whole-plane GFF and `B, B'` are standard Brownian motions, with `X ⊥ (B, B')` and `B ⊥ B'`: this is the
  definition of the circle-average embedding `h = coneFieldOf γ X B B'` of the γ-quantum cone (DMS
  Def 4.10, Rem 4.4);
* `curve` is the space-filling SLE `η` parameterized by `A^γ_h`-area, measurable;
* `M.radius ω k = R_{2^k}`, `M`'s unit cells are `η([x − 1, x])`, and the mesh-`2^{-k}`
  cells of `M`'s random family are `η([2^{-k}(x − 1), 2^{-k}x])`, almost surely.

The identification of the mesh-`2^{-k}` graphs of the family with the mated-CRT multigraphs `G^{2^{-k}}` of
`M.coupled.bm` ([18] (1.1); multiplicities matter for the walk) was this
structure's field `meshGraph_eq`; since it is carried by the model's family itself,
`M.coupled.meshGraph_eq` (`CellFamily.MultigraphCoupledRandomFamily`). -/
structure ConeRealization {γ : ℝ} (M : MesoModel.MatedCRTUnitMesoModel γ) where
  /-- The whole-plane GFF whose lateral part is the lateral part of the cone field. -/
  X : M.coupled.family.Ω → LQGMetric.DistC
  /-- The radial Brownian motion for `r ≤ 1` (`A_t = B_t + γt`, `t ≥ 0`). -/
  B : ℝ≥0 → M.coupled.family.Ω → ℝ
  /-- The radial Brownian motion for `r ≥ 1` (conditioned through its last zero, DMS Rem 4.4). -/
  B' : ℝ≥0 → M.coupled.family.Ω → ℝ
  /-- The space-filling SLE `η`, parameterized by LQG area with `η(0) = 0`. -/
  curve : M.coupled.family.Ω → C(ℝ, ℂ)
  gff : LQGMetric.IsWholePlaneGFF X M.coupled.family.P
  brownian : IsBrownianReal B M.coupled.family.P
  brownian' : IsBrownianReal B' M.coupled.family.P
  indep : IndepFun X (fun ω => ((fun t => B t ω), (fun t => B' t ω))) M.coupled.family.P ∧
    IndepFun (fun ω t => B t ω) (fun ω t => B' t ω) M.coupled.family.P
  measurable_curve : Measurable curve
  radius_eq : ∀ᵐ ω ∂M.coupled.family.P, ∀ k : ℕ,
    M.radius ω k = coneScale γ γ (fun t => B t ω) (fun t => B' t ω) ((2 : ℝ) ^ k)
  cell_eq : ∀ᵐ ω ∂M.coupled.family.P, ∀ x : ℤ, M.coupled.cell ω x = curve ω '' Icc ((x : ℝ) - 1) x
  meshCell_eq : ∀ k : ℕ, ∀ᵐ ω ∂M.coupled.family.P, ∀ x : ℤ,
    (M.coupled.family.H k ω).cell x = meshCells (CellFamily.mesh k) (curve ω) x

namespace ConeRealization

variable {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M)

/-- The γ-quantum cone field `h` (circle-average embedding) of the realization. -/
def field (ω : M.coupled.family.Ω) : LQGMetric.DistC :=
  coneFieldOf γ (D.X ω) (fun t => D.B t ω) (fun t => D.B' t ω)

/-- The cone scale `R_b`. -/
def scale (b : ℝ) (ω : M.coupled.family.Ω) : ℝ :=
  coneScale γ γ (fun t => D.B t ω) (fun t => D.B' t ω) b

/-- The γ-LQG area `μ_h = A^γ_h` of the cone field. -/
def area (ω : M.coupled.family.Ω) : Measure ℂ := lqgArea γ (D.field ω)

end ConeRealization

/-! ### Joint scaling as printed, and the SLE-dependent bundle fields -/

/-- **Area parametrization of space-filling SLE:** `η(0) = 0` and
`A^γ_h(η([s, t])) = t − s` for `s ≤ t`. This combines the coupling's `areaParam`
and `spaceFilling` fields. -/
def AreaParametrization {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ᵐ ω ∂M.coupled.family.P, D.curve ω 0 = 0 ∧ ∀ s t : ℝ, s ≤ t →
    D.area ω (D.curve ω '' Icc s t) = ENNReal.ofReal (t - s)

/-! ### SLE-free inputs (to prove) -/

/-- **Area scaling law of the cone:** for every `b > 0`,
`b⁻¹ μ_h(B_{R_b}(0))` has the law of `μ_h(B_1(0))`. Sources: `μ_{h_b}(A) = b⁻¹ μ_h(R_b A)`
a.s. for all Borel `A` ([SW] Sheffield–Wang Thm 1.1/1.4, `1605.06171v2.`, the random-dilation
coordinate change; note [17] prints this formula inverted, the area-scaling discussion), and `h_b =d h`
([14, Prop 4.13(i)]; [17] (2.8)) applied to the measurable
functional `h ↦ μ_h(B_1(0))`. No SLE is involved (GFF, circle averages, GMC). -/
def AreaScalingLaw {γ : ℝ} {M : MesoModel.MatedCRTUnitMesoModel γ} (D : ConeRealization M) : Prop :=
  ∀ b : ℝ, 0 < b → ∀ S : Set ℝ≥0∞, MeasurableSet S →
    M.coupled.family.P {ω | ENNReal.ofReal b⁻¹ * D.area ω (ball 0 (D.scale b ω)) ∈ S} =
      M.coupled.family.P {ω | D.area ω (ball 0 1) ∈ S}

/-! ### Produced downstream -/

end MatedCRTHarmonic.CellScaling
