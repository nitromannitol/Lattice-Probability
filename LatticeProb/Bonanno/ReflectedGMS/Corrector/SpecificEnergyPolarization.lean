/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SpecificEnergyPolarization at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.BracketSpecificEnergy
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Polarization of the specific energy density

The manuscript's specific energy `‖θ‖_*² = E[ρ_θ]` is the expectation of the rooted vertex
density `ρ_θ(H) = (2 a_H)⁻¹ ∑_{H' ∼ H} c(H,H') |θ(H') - θ(H)|²`, i.e. the existing
`RootDensities.rootedSpecificEnergyDensity`.  This file supplies its bilinear polarization

`ρ_{θ+η} = ρ_θ + 2 ⟨θ, η⟩ + ρ_η`

together with the integrability of the *signed* pairing density under the actual rooted law,
and the resulting identity for the expected densities

`E[ρ_{θ+η}] = E[ρ_θ] + 2 E[⟨θ, η⟩] + E[ρ_η]`.

The file works with the existing `ℝ≥0∞`-valued density; the real-valued quadratic form
`quadDensity` is introduced only as the (always finite, by local finiteness of the cell graph)
real representative of `specificEnergyDensity`, and every `toReal` step is justified by an
actual finiteness statement.  The integrability of the signed pairing is deduced from the
**expected** specific energies `E[ρ_θ], E[ρ_η] < ∞` of the two fields, never from finiteness
of a global graph energy.

Consumers: `Corrector/NestedEnergyProjections` (`e_m`, `e_0`) and
`Corrector/LimitingHarmonicPotential` (`e_∞`); the expected Pythagoras identity
`E[ρ_θ] = E[ρ_ψ] + E[ρ_{θ-ψ}]` is available here as soon as the expected pairing vanishes,
which is the separately staffed probabilistic input.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ReflectedGMS.SpecificEnergyPolarization

open RootDensities

variable {V : Type*} [Countable V]

/-! ### Finite-support summability of the neighbour sums -/

/-- Every neighbour sum whose summand vanishes where the conductance does is a finite sum,
by the local finiteness clause of `Geometry`. -/
theorem summable_of_conductance_support (F : IndexedCells V) (hF : Geometry F) (v : V)
    {f : V → ℝ} (hf : ∀ w, F.graph.c v w = 0 → f w = 0) : Summable f := by
  apply summable_of_hasFiniteSupport
  refine (hF.2.2.2.2.2.2.1 v).subset ?_
  intro w hw
  simp only [Function.mem_support] at hw
  rw [SimpleGraph.mem_neighborSet, ReflectedWalk.ConductanceGraph.toSimpleGraph_adj]
  have hc : F.graph.c v w ≠ 0 := fun hc => hw (hf w hc)
  exact lt_of_le_of_ne (F.graph.c_nonneg v w) hc.symm

theorem summable_conductance_mul_normSq (F : IndexedCells V) (hF : Geometry F)
    (Θ : V → Plane) (v : V) :
    Summable fun w : V => F.graph.c v w * ‖Θ w - Θ v‖ ^ 2 :=
  summable_of_conductance_support F hF v (fun w hw => by simp [hw])

theorem summable_conductance_mul_inner (F : IndexedCells V) (hF : Geometry F)
    (Θ H : V → Plane) (v : V) :
    Summable fun w : V => F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v) :=
  summable_of_conductance_support F hF v (fun w hw => by simp [hw])

theorem summable_abs_conductance_mul_inner (F : IndexedCells V) (hF : Geometry F)
    (Θ H : V → Plane) (v : V) :
    Summable fun w : V => |F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)| :=
  summable_of_conductance_support F hF v (fun w hw => by simp [hw])

theorem summable_conductance_mul_addNormSq (F : IndexedCells V) (hF : Geometry F)
    (Θ H : V → Plane) (v : V) :
    Summable fun w : V =>
      F.graph.c v w * (‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2) / 2 :=
  summable_of_conductance_support F hF v (fun w hw => by simp [hw])

/-! ### The real quadratic and bilinear densities -/

/-- Real representative of `RootDensities.specificEnergyDensity`. -/
noncomputable def quadDensity (F : IndexedCells V) (Θ : V → Plane) (v : V) : ℝ :=
  (2 * StatementIngredients.cellArea F v)⁻¹ *
    ∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2

/-- The signed vertex pairing density polarizing `quadDensity`: the manuscript's
`⟨θ, η⟩` integrand, with the same `(2 a_H)⁻¹` normalization. -/
noncomputable def pairingDensity (F : IndexedCells V) (Θ H : V → Plane) (v : V) : ℝ :=
  (2 * StatementIngredients.cellArea F v)⁻¹ *
    ∑' w : V, F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)

theorem quadDensity_nonneg (F : IndexedCells V) (hF : Geometry F) (Θ : V → Plane) (v : V) :
    0 ≤ quadDensity F Θ v := by
  have harea : 0 < StatementIngredients.cellArea F v := StatementIngredients.cellArea_pos F hF v
  refine mul_nonneg (inv_nonneg.mpr (by linarith)) ?_
  exact tsum_nonneg fun w => mul_nonneg (F.graph.c_nonneg v w) (sq_nonneg _)

/-- **Polarization of the vertex specific-energy density.** -/
theorem quadDensity_add (F : IndexedCells V) (hF : Geometry F) (Θ H : V → Plane) (v : V) :
    quadDensity F (fun u => Θ u + H u) v
      = quadDensity F Θ v + 2 * pairingDensity F Θ H v + quadDensity F H v := by
  have hsplit : ∀ w : V, F.graph.c v w * ‖(Θ w + H w) - (Θ v + H v)‖ ^ 2
      = F.graph.c v w * ‖Θ w - Θ v‖ ^ 2
        + 2 * (F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v))
        + F.graph.c v w * ‖H w - H v‖ ^ 2 := by
    intro w
    have hrw : (Θ w + H w) - (Θ v + H v) = (Θ w - Θ v) + (H w - H v) := by abel
    rw [hrw, norm_add_sq_real]
    ring
  have h1 := summable_conductance_mul_normSq F hF Θ v
  have h3 := summable_conductance_mul_normSq F hF H v
  have h2 : Summable fun w : V => 2 * (F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)) :=
    (summable_conductance_mul_inner F hF Θ H v).mul_left 2
  simp only [quadDensity, pairingDensity]
  rw [tsum_congr hsplit, (h1.add h2).tsum_add h3, h1.tsum_add h2, tsum_mul_left]
  ring

/-- The signed pairing density is controlled by the two quadratic densities; this is the
arithmetic-geometric bound `2|⟨a,b⟩| ≤ ‖a‖² + ‖b‖²`, applied termwise. -/
theorem abs_pairingDensity_le (F : IndexedCells V) (hF : Geometry F) (Θ H : V → Plane)
    (v : V) :
    |pairingDensity F Θ H v| ≤ (quadDensity F Θ v + quadDensity F H v) / 2 := by
  have harea : 0 < StatementIngredients.cellArea F v := StatementIngredients.cellArea_pos F hF v
  have hinv : (0 : ℝ) ≤ (2 * StatementIngredients.cellArea F v)⁻¹ :=
    inv_nonneg.mpr (by linarith)
  have hterm : ∀ w : V, |F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)|
      ≤ F.graph.c v w * (‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2) / 2 := by
    intro w
    rw [abs_mul, abs_of_nonneg (F.graph.c_nonneg v w)]
    have hcs : |inner ℝ (Θ w - Θ v) (H w - H v)| ≤ ‖Θ w - Θ v‖ * ‖H w - H v‖ :=
      abs_real_inner_le_norm _ _
    have hamgm : 2 * ‖Θ w - Θ v‖ * ‖H w - H v‖
        ≤ ‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2 := two_mul_le_add_sq _ _
    have hc := F.graph.c_nonneg v w
    nlinarith [hcs, hamgm, hc, abs_nonneg (inner ℝ (Θ w - Θ v) (H w - H v) : ℝ)]
  have hsum : ∑' w : V, |F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)|
      ≤ ∑' w : V, F.graph.c v w * (‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2) / 2 :=
    (summable_abs_conductance_mul_inner F hF Θ H v).tsum_le_tsum hterm
      (summable_conductance_mul_addNormSq F hF Θ H v)
  have habs : |∑' w : V, F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)|
      ≤ ∑' w : V, |F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)| := by
    have h := norm_tsum_le_tsum_norm
      (f := fun w : V => F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v))
      (by simpa [Real.norm_eq_abs] using summable_abs_conductance_mul_inner F hF Θ H v)
    simpa [Real.norm_eq_abs] using h
  have hsplit : ∑' w : V, F.graph.c v w * (‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2) / 2
      = ((∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2)
          + ∑' w : V, F.graph.c v w * ‖H w - H v‖ ^ 2) / 2 := by
    have hcongr : ∀ w : V, F.graph.c v w * (‖Θ w - Θ v‖ ^ 2 + ‖H w - H v‖ ^ 2) / 2
        = 2⁻¹ * (F.graph.c v w * ‖Θ w - Θ v‖ ^ 2 + F.graph.c v w * ‖H w - H v‖ ^ 2) := by
      intro w
      ring
    rw [tsum_congr hcongr, tsum_mul_left,
      (summable_conductance_mul_normSq F hF Θ v).tsum_add
        (summable_conductance_mul_normSq F hF H v)]
    ring
  have hbound : |∑' w : V, F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)|
      ≤ ((∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2)
          + ∑' w : V, F.graph.c v w * ‖H w - H v‖ ^ 2) / 2 := by
    rw [← hsplit]
    exact habs.trans hsum
  rw [pairingDensity, abs_mul, abs_of_nonneg hinv, quadDensity, quadDensity]
  calc (2 * StatementIngredients.cellArea F v)⁻¹ *
        |∑' w : V, F.graph.c v w * inner ℝ (Θ w - Θ v) (H w - H v)|
      ≤ (2 * StatementIngredients.cellArea F v)⁻¹ *
        (((∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2)
          + ∑' w : V, F.graph.c v w * ‖H w - H v‖ ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left hbound hinv
    _ = ((2 * StatementIngredients.cellArea F v)⁻¹ *
          ∑' w : V, F.graph.c v w * ‖Θ w - Θ v‖ ^ 2
        + (2 * StatementIngredients.cellArea F v)⁻¹ *
          ∑' w : V, F.graph.c v w * ‖H w - H v‖ ^ 2) / 2 := by ring

/-! ### Identification with the existing `ℝ≥0∞` density -/

/-- The existing `ℝ≥0∞` specific-energy density is the `ENNReal.ofReal` of `quadDensity`;
in particular it is finite at every vertex of a locally finite cell graph. -/
theorem specificEnergyDensity_eq_ofReal_quadDensity (F : IndexedCells V) (hF : Geometry F)
    (Θ : V → Plane) (v : V) :
    specificEnergyDensity F Θ v = ENNReal.ofReal (quadDensity F Θ v) := by
  have harea : 0 < StatementIngredients.cellArea F v := StatementIngredients.cellArea_pos F hF v
  have h2pos : (0 : ℝ) < 2 * StatementIngredients.cellArea F v := by linarith
  have hnn : ∀ w : V, 0 ≤ F.graph.c v w * ‖Θ w - Θ v‖ ^ 2 :=
    fun w => mul_nonneg (F.graph.c_nonneg v w) (sq_nonneg _)
  have h2A : ENNReal.ofReal (2 * StatementIngredients.cellArea F v)
      = 2 * ENNReal.ofReal (StatementIngredients.cellArea F v) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  rw [quadDensity, ← div_eq_inv_mul, ENNReal.ofReal_div_of_pos h2pos,
    ENNReal.ofReal_tsum_of_nonneg hnn (summable_conductance_mul_normSq F hF Θ v), h2A,
    specificEnergyDensity]
  simp_rw [ENNReal.ofReal_mul (F.graph.c_nonneg v _)]

/-! ### Rooted (boundary-masked) versions -/

/-- Boundary-masked real quadratic density. -/
noncomputable def rootedQuadDensity (F : IndexedCells V) (Θ : V → Plane) (z : Plane) : ℝ :=
  (rootAt F z).elim 0 (quadDensity F Θ)

/-- Boundary-masked signed pairing density. -/
noncomputable def rootedPairingDensity (F : IndexedCells V) (Θ H : V → Plane) (z : Plane) : ℝ :=
  (rootAt F z).elim 0 (pairingDensity F Θ H)

theorem rootedQuadDensity_nonneg (F : IndexedCells V) (hF : Geometry F) (Θ : V → Plane)
    (z : Plane) : 0 ≤ rootedQuadDensity F Θ z := by
  cases hroot : rootAt F z with
  | none => simp [rootedQuadDensity, hroot]
  | some v =>
      simpa [rootedQuadDensity, hroot] using quadDensity_nonneg F hF Θ v

theorem rootedSpecificEnergyDensity_eq_ofReal (F : IndexedCells V) (hF : Geometry F)
    (Θ : V → Plane) (z : Plane) :
    rootedSpecificEnergyDensity F Θ z = ENNReal.ofReal (rootedQuadDensity F Θ z) := by
  cases hroot : rootAt F z with
  | none => simp [rootedSpecificEnergyDensity, rootedQuadDensity, hroot]
  | some v =>
      simpa [rootedSpecificEnergyDensity, rootedQuadDensity, hroot] using
        specificEnergyDensity_eq_ofReal_quadDensity F hF Θ v

theorem rootedSpecificEnergyDensity_ne_top (F : IndexedCells V) (hF : Geometry F)
    (Θ : V → Plane) (z : Plane) : rootedSpecificEnergyDensity F Θ z ≠ ∞ := by
  rw [rootedSpecificEnergyDensity_eq_ofReal F hF Θ z]
  exact ENNReal.ofReal_ne_top

theorem toReal_rootedSpecificEnergyDensity (F : IndexedCells V) (hF : Geometry F)
    (Θ : V → Plane) (z : Plane) :
    (rootedSpecificEnergyDensity F Θ z).toReal = rootedQuadDensity F Θ z := by
  rw [rootedSpecificEnergyDensity_eq_ofReal F hF Θ z,
    ENNReal.toReal_ofReal (rootedQuadDensity_nonneg F hF Θ z)]

/-- **Rooted polarization**, the pointwise form of `ρ_{θ+η} = ρ_θ + 2⟨θ,η⟩ + ρ_η`. -/
theorem rootedQuadDensity_add (F : IndexedCells V) (hF : Geometry F) (Θ H : V → Plane)
    (z : Plane) :
    rootedQuadDensity F (fun u => Θ u + H u) z
      = rootedQuadDensity F Θ z + 2 * rootedPairingDensity F Θ H z
        + rootedQuadDensity F H z := by
  cases hroot : rootAt F z with
  | none => simp [rootedQuadDensity, rootedPairingDensity, hroot]
  | some v =>
      simpa [rootedQuadDensity, rootedPairingDensity, hroot] using
        quadDensity_add F hF Θ H v

theorem abs_rootedPairingDensity_le (F : IndexedCells V) (hF : Geometry F) (Θ H : V → Plane)
    (z : Plane) :
    |rootedPairingDensity F Θ H z|
      ≤ (rootedQuadDensity F Θ z + rootedQuadDensity F H z) / 2 := by
  cases hroot : rootAt F z with
  | none => simp [rootedQuadDensity, rootedPairingDensity, hroot]
  | some v =>
      simpa [rootedQuadDensity, rootedPairingDensity, hroot] using
        abs_pairingDensity_le F hF Θ H v

/-- Pointwise polarization of the actual `ℝ≥0∞` rooted density, read through `toReal`
(legitimate: the density is finite at every vertex, by local finiteness). -/
theorem toReal_rootedSpecificEnergyDensity_add (F : IndexedCells V) (hF : Geometry F)
    (Θ H : V → Plane) (z : Plane) :
    (rootedSpecificEnergyDensity F (fun u => Θ u + H u) z).toReal
      = (rootedSpecificEnergyDensity F Θ z).toReal
        + 2 * rootedPairingDensity F Θ H z
        + (rootedSpecificEnergyDensity F H z).toReal := by
  rw [toReal_rootedSpecificEnergyDensity F hF _ z, toReal_rootedSpecificEnergyDensity F hF Θ z,
    toReal_rootedSpecificEnergyDensity F hF H z, rootedQuadDensity_add F hF Θ H z]

/-- The quadratic bound `ρ_{θ+η} ≤ 2ρ_θ + 2ρ_η`, used only to see that the expected energy of
the sum is finite. -/
theorem rootedSpecificEnergyDensity_add_le (F : IndexedCells V) (hF : Geometry F)
    (Θ H : V → Plane) (z : Plane) :
    rootedSpecificEnergyDensity F (fun u => Θ u + H u) z
      ≤ 2 * rootedSpecificEnergyDensity F Θ z + 2 * rootedSpecificEnergyDensity F H z := by
  have hnnΘ := rootedQuadDensity_nonneg F hF Θ z
  have hnnH := rootedQuadDensity_nonneg F hF H z
  have hq : rootedQuadDensity F (fun u => Θ u + H u) z
      ≤ 2 * rootedQuadDensity F Θ z + 2 * rootedQuadDensity F H z := by
    have hpair := abs_rootedPairingDensity_le F hF Θ H z
    have hle : rootedPairingDensity F Θ H z ≤ |rootedPairingDensity F Θ H z| := le_abs_self _
    rw [rootedQuadDensity_add F hF Θ H z]
    linarith
  rw [rootedSpecificEnergyDensity_eq_ofReal F hF _ z,
    rootedSpecificEnergyDensity_eq_ofReal F hF Θ z,
    rootedSpecificEnergyDensity_eq_ofReal F hF H z]
  calc ENNReal.ofReal (rootedQuadDensity F (fun u => Θ u + H u) z)
      ≤ ENNReal.ofReal (2 * rootedQuadDensity F Θ z + 2 * rootedQuadDensity F H z) :=
        ENNReal.ofReal_le_ofReal hq
    _ = 2 * ENNReal.ofReal (rootedQuadDensity F Θ z)
          + 2 * ENNReal.ofReal (rootedQuadDensity F H z) := by
        rw [ENNReal.ofReal_add (by linarith) (by linarith),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num

/-! ### Expected polarization under the actual rooted law

The environment type is left abstract: `cells ω` is the indexed cell family of the sample `ω`
(its vertex type may depend on `ω`, as it does for `Environment.Code.decode`), `root ω` is the
sampled root, and the expected specific energies are the actual
`∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ`. -/

section Expected

variable {Ω : Type*} [MeasurableSpace Ω] {Vtx : Ω → Type*} [∀ ω, Countable (Vtx ω)]

/-- The rooted pairing density is `μ`-integrable as soon as both expected specific energies
are finite: this is the termwise bound `2|⟨θ,η⟩| ≤ ρ_θ + ρ_η` combined with the two finite
expectations.  No global finite graph energy is used. -/
theorem integrable_rootedPairingDensity (μ : Measure Ω) (cells : ∀ ω, IndexedCells (Vtx ω))
    (Θ H : ∀ ω, Vtx ω → Plane) (root : Ω → Plane)
    (hcells : ∀ ω, Geometry (cells ω))
    (hΘmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)) μ)
    (hHmeas : AEMeasurable
      (fun ω => rootedSpecificEnergyDensity (cells ω) (H ω) (root ω)) μ)
    (hPmeas : AEStronglyMeasurable
      (fun ω => rootedPairingDensity (cells ω) (Θ ω) (H ω) (root ω)) μ)
    (hΘ : (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω) ∂μ) ≠ ∞)
    (hH : (∫⁻ ω, rootedSpecificEnergyDensity (cells ω) (H ω) (root ω) ∂μ) ≠ ∞) :
    Integrable (fun ω => rootedPairingDensity (cells ω) (Θ ω) (H ω) (root ω)) μ := by
  have hintΘ : Integrable
      (fun ω => (rootedSpecificEnergyDensity (cells ω) (Θ ω) (root ω)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hΘmeas hΘ
  have hintH : Integrable
      (fun ω => (rootedSpecificEnergyDensity (cells ω) (H ω) (root ω)).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hHmeas hH
  refine Integrable.mono' ((hintΘ.add hintH).div_const 2) hPmeas ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, toReal_rootedSpecificEnergyDensity (cells ω) (hcells ω) (Θ ω) (root ω),
    toReal_rootedSpecificEnergyDensity (cells ω) (hcells ω) (H ω) (root ω)]
  exact abs_rootedPairingDensity_le (cells ω) (hcells ω) (Θ ω) (H ω) (root ω)

end Expected

end ReflectedGMS.SpecificEnergyPolarization
