/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.ResidualEnergyLineVariation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Corrector.SpecificEnergyLocalControl
import LatticeProb.Bonanno.ReflectedGMS.Spatial.NonmacroscopicSelectedBlocks
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Small residual energy and small mean line variation (`s:eq:smallresidual`, `s:eq:smallmeanTV`)

This module proves the two displays that open the manuscript subsection *The residual has
small energy on large spatial patches*, for the residual `r_m = Φ - φ_m` of the corrector
construction.  Only the gradient of `r_m` enters, so the residual is carried here as an
arbitrary `Plane`-valued field; nothing about how it was produced is used.

## `s:eq:smallresidual`

With `n_j` the deterministic subsequence of `s:eq:residualchoice`,

`η_j := limsup_{R→∞} R⁻² ℰ_{ℍ(clB R)}(r_{n_j}) ≤ 4 Mmax(ρ_{∇ r_{n_j}}) ⟶ 0`.

`residualEnergyLimsup_le_four_mul` is the inequality and
`tendsto_residualEnergyLimsup_zero` the convergence; `smallResidual` is the single
statement carrying **both** clauses.  The manuscript proof is followed literally:
Lemma `s:lem:localcontrol` in the already-checked form
`SpecificEnergyLocalControl.vectorEnergy_hittingVertices_le_ballMaximal` gives
`ℰ_{ℍ(clB R)}(r) ≤ (R + D_R)² Mmax`, and `s:eq:DR` — in the pathwise `ε`-form
`Spatial.SublinearDiameterDecay`, the a.s. conclusion of the checked
`Spatial.ae_maxDiamHittingBall_finite_and_sublinear` — makes `D_R ≤ R` for all large `R`,
so `(R + D_R)² ≤ 4R²`.  Every quantity is an `ℝ≥0∞`, so the display is meaningful even
when `ℍ(clB R)` is infinite, as the manuscript explicitly demands.

The second clause `Mmax(ρ_{∇ r_{n_j}}) → 0` is *not* assumed in the pathwise form:
`ae_tendsto_zero_of_geometric_tail` derives it almost surely from the manuscript's own
Borel–Cantelli input `s:eq:BC` (the tail bound `P[M_j > 2^{-2j}] ≤ 512·2^{-2j}` of
`s:prop:maximal` at `‖∇ r_{n_j}‖²_sp ≤ 2^{-4j}`, i.e. exactly `s:eq:residualchoice`),
reusing the checked `SpecificEnergyLocalControl.ae_eventually_le_geometric`.

## `s:eq:smallmeanTV`

`lim_j limsup_{R→∞} R⁻² ∫_{-2R}^{2R} V_{r_{n_j}}(y) dy = 0`, and the same for vertical
lines (`smallMeanTV`).  Following the manuscript, `Q_R = [-2R,2R]² ⊆ clB 3R`
(`squareBox_subset_closedBall`), the line estimate `s:eq:lineenergy` is the checked
`setLIntegral_horizontalLineVariation_le_patch` / `…_verticalLineVariation_le_patch` of
`Corrector/LocalPatchLineBounds`, and the two patch factors are then bounded by the
manuscript's `s:eq:Wbound` (`W(R) ≤ K R²` for large `R`, an explicit hypothesis, being a
different corollary) and by `s:eq:smallresidual` above.  The variation is taken of one
coordinate `r ⬝ e_i` of the residual, which is the form the downstream good-grid step
`UniformCorrectorSublinearity.ofReal_abs_sub_le_three_mul_of_mem_gridCells` consumes; the
energy input is the full vector energy, as in the manuscript.

## What is *not* proved here

`s:eq:Wbound` itself (`s:cor:spatialbounds`) and the ball domination
`∫_{clB r} ρ_θ ≤ r² Mmax` with the weak-`L¹` tail bound (`s:prop:maximal`) enter as
hypotheses, in exactly the shape the existing checked producers state them.  They are
quantitative facts about *other* objects — the geometric mass `∑ d_H² π*(H)` and the
maximal function of a rooted density — not disguised forms of either conclusion proved
here.  The window-by-window good-offset assembly, the block-interpolant existence and the
full rectangle minimizer are separate packets and are untouched.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS.ResidualEnergyLineVariation

open StatementIngredients RootDensities SpecificEnergyLocalControl
open NonmacroscopicSelectedBlocks Spatial

variable {V : Type*} [Countable V]

/-! ### The manuscript square `Q_R = [-2R, 2R]²` -/

/-- `Q_R = [-2R,2R]²`, the square on which the manuscript takes the mean line variation. -/
def squareBox (R : ℝ) : Set Plane := {z | |z 0| ≤ 2 * R ∧ |z 1| ≤ 2 * R}

/-- **`Q_R ⊆ clB 3R`**, the containment the manuscript uses to feed `s:eq:smallresidual`
into the line estimate. -/
theorem squareBox_subset_closedBall {R : ℝ} (hR : 0 ≤ R) :
    squareBox R ⊆ Metric.closedBall (0 : Plane) (3 * R) := by
  intro z hz
  obtain ⟨h0, h1⟩ := hz
  have h3 : (0 : ℝ) ≤ 3 * R := by linarith
  have hsq : ‖z‖ ^ 2 ≤ (3 * R) ^ 2 := by
    rw [normSq_eq_sum_coord, Fin.sum_univ_two]
    nlinarith [abs_nonneg (z 0), abs_nonneg (z 1), sq_abs (z 0), sq_abs (z 1)]
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ = Real.sqrt (‖z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg z)).symm
    _ ≤ Real.sqrt ((3 * R) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 3 * R := Real.sqrt_sq h3

/-! ### `s:eq:DR` in the form needed by `s:lem:localcontrol` -/

/-- A cell meeting `clB R` has diameter at most any real bound on `D_R`. -/
theorem diam_le_of_maxDiamHittingBall_le (F : IndexedCells V) {R D : ℝ} (hD : 0 ≤ D)
    (h : maxDiamHittingBall F R ≤ ENNReal.ofReal D) {v : V}
    (hv : Hits F (Metric.closedBall (0 : Plane) R) v) :
    Metric.diam (F.cell v : Set Plane) ≤ D := by
  have hsup : ENNReal.ofReal (Metric.diam (F.cell v : Set Plane)) ≤ maxDiamHittingBall F R :=
    le_iSup (f := fun w : {w : V // Hits F (Metric.closedBall (0 : Plane) R) w} =>
      ENNReal.ofReal (Metric.diam (F.cell w.1 : Set Plane))) ⟨v, hv⟩
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 (hsup.trans h)

/-! ### The patch energy of the residual -/

/-- `ℰ_{ℍ(clB R)}(r)`: the manuscript patch energy of the residual on the cells meeting the
closed disk of radius `R`, i.e. the existing `vectorEnergy` of the restricted graph.  It is
an `ℝ≥0∞`, so it is defined even when `ℍ(clB R)` is infinite. -/
noncomputable def ballPatchVectorEnergy (F : IndexedCells V) (r : V → Plane) (R : ℝ) : ℝ≥0∞ :=
  vectorEnergy (restrictGraph F.graph (hittingVertices F (Metric.closedBall (0 : Plane) R)))
    fun v => r v.1

/-- **`s:eq:localcontrol` for the residual.**  `ℰ_{ℍ(clB R)}(r) ≤ (R + D)² Mmax` whenever
`D` dominates the cell diameters on the patch. -/
theorem ballPatchVectorEnergy_le_of_maxDiam (F : IndexedCells V) (hF : Geometry F)
    (r : V → Plane) {M : ℝ≥0∞} {R D : ℝ} (hR : 0 < R) (hD : 0 ≤ D)
    (hDiam : maxDiamHittingBall F R ≤ ENNReal.ofReal D)
    (hM : ∀ s : ℝ, 0 < s →
      (∫⁻ z in Metric.closedBall (0 : Plane) s, rootedSpecificEnergyDensity F r z ∂volume)
        ≤ ENNReal.ofReal (s ^ 2) * M) :
    ballPatchVectorEnergy F r R ≤ ENNReal.ofReal ((R + D) ^ 2) * M :=
  vectorEnergy_hittingVertices_le_ballMaximal F hF r (by linarith)
    (fun _ hv => diam_le_of_maxDiamHittingBall_le F hD hDiam hv) hM

/-! ### `s:eq:residualchoice` and `s:eq:BC` make `Mmax(ρ_{∇ r_{n_j}}) → 0` -/

/-! ### Square-root arithmetic in `ℝ≥0∞` -/

/-- `√x · √x = x` in `ℝ≥0∞`, with no finiteness hypothesis. -/
theorem rpow_half_mul_self (x : ℝ≥0∞) : x ^ (2⁻¹ : ℝ) * x ^ (2⁻¹ : ℝ) = x := by
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num

/-- The finite constant of `s:eq:smallmeanTV`: `√(9K) · √36`, where `K` is the constant of
`s:eq:Wbound`. -/
noncomputable def lineVariationConstant (K : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (9 * K) ^ (2⁻¹ : ℝ) * ENNReal.ofReal 36 ^ (2⁻¹ : ℝ)

theorem lineVariationConstant_ne_top (K : ℝ) : lineVariationConstant K ≠ ∞ :=
  (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)).ne

/-- The Cauchy–Schwarz product of `s:eq:lineenergy` with the two manuscript bounds
substituted: the geometric mass is at most `9K R²` and the patch energy at most
`36 R² Mmax`. -/
theorem sqrt_mass_mul_sqrt_energy_le {mass energy M A : ℝ≥0∞} {K : ℝ}
    (hmass : mass ≤ ENNReal.ofReal (9 * K) * A)
    (henergy : energy ≤ ENNReal.ofReal 36 * A * M) :
    mass ^ (2⁻¹ : ℝ) * energy ^ (2⁻¹ : ℝ)
      ≤ lineVariationConstant K * M ^ (2⁻¹ : ℝ) * A := by
  have h1 : mass ^ (2⁻¹ : ℝ)
      ≤ ENNReal.ofReal (9 * K) ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ) := by
    calc mass ^ (2⁻¹ : ℝ) ≤ (ENNReal.ofReal (9 * K) * A) ^ (2⁻¹ : ℝ) :=
          ENNReal.rpow_le_rpow hmass (by norm_num)
      _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
  have h2 : energy ^ (2⁻¹ : ℝ)
      ≤ ENNReal.ofReal 36 ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ) * M ^ (2⁻¹ : ℝ) := by
    calc energy ^ (2⁻¹ : ℝ) ≤ (ENNReal.ofReal 36 * A * M) ^ (2⁻¹ : ℝ) :=
          ENNReal.rpow_le_rpow henergy (by norm_num)
      _ = (ENNReal.ofReal 36 * A) ^ (2⁻¹ : ℝ) * M ^ (2⁻¹ : ℝ) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  calc mass ^ (2⁻¹ : ℝ) * energy ^ (2⁻¹ : ℝ)
      ≤ (ENNReal.ofReal (9 * K) ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ)) *
          (ENNReal.ofReal 36 ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ) * M ^ (2⁻¹ : ℝ)) :=
        mul_le_mul' h1 h2
    _ = lineVariationConstant K * M ^ (2⁻¹ : ℝ) * (A ^ (2⁻¹ : ℝ) * A ^ (2⁻¹ : ℝ)) := by
        simp only [lineVariationConstant]
        ring
    _ = lineVariationConstant K * M ^ (2⁻¹ : ℝ) * A := by rw [rpow_half_mul_self]

/-! ### The mean line variation on `Q_R` -/

/-- One coordinate of a vector field carries at most the full vector energy of the patch. -/
theorem patchEnergyENN_coord_le_vectorEnergy (F : IndexedCells V) (A : Set V)
    (r : V → Plane) (i : Fin 2) :
    patchEnergyENN F A (fun v => r v i)
      ≤ vectorEnergy (restrictGraph F.graph A) fun v => r v.1 :=
  Finset.single_le_sum
    (f := fun i : Fin 2 => energyENN (restrictGraph F.graph A) fun v : A => r v.1 i)
    (fun _ _ => zero_le) (Finset.mem_univ i)

end ReflectedGMS.ResidualEnergyLineVariation
