/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Corrector.SpecificEnergyLocalControl at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.BracketSpecificEnergy
import LatticeProb.Bonanno.ReflectedGMS.Corrector.ActiveBlockEdges
import LatticeProb.Bonanno.ReflectedGMS.Corrector.LocalPatchLineBounds
import LatticeProb.Bonanno.ReflectedGMS.Spatial.RootedMassBounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Specific-energy convergence controls spatial patches (`s:lem:localcontrol`)

This module proves the manuscript lemma *Specific-energy convergence controls spatial
patches* (`s:lem:localcontrol`, manuscript section "The limit: local convergence and free
boundary conditions"), for the *actual* objects of the project: the indexed cell family
`ReflectedGMS.IndexedCells`, the manuscript specific-energy density

`ρ_θ(ω, z) = (2 a_{H_z})⁻¹ ∑_{H' ∼ H_z} c(H_z, H') |θ(H_z, H')|²`

realised as the boundary-masked `RootDensities.rootedSpecificEnergyDensity`, and the patch
energy `∑_{e ∈ E(ℍ(B̄_R))} c(e)|θ(e)|²` realised as the existing
`StatementIngredients.vectorEnergy` of `ReflectedGMS.restrictGraph` on the hitting set
`ReflectedGMS.hittingVertices F (B̄_R)`.  Nothing about the energy normalisation is
redefined: `vectorEnergy` is already half the ordered-edge sum, which is exactly the
manuscript's "once per unoriented edge" convention.

## The three manuscript clauses

* **`s:eq:localcontrol`.**  `vectorEnergy_hittingVertices_le_setLIntegral_closedBall` is the
  first inequality

  `∑_{e ∈ E(ℍ(B̄_R))} c(e)|θ(e)|² ≤ ∫_{B̄_{R+D_R}} ρ_θ(z) dz`,

  and `vectorEnergy_hittingVertices_le_ballMaximal` composes it with the ball bound
  `∫_{B̄_r} ρ_θ ≤ r² M(ρ_θ)` to give the full display.  The manuscript proof is followed
  literally: every cell of `ℍ(B̄_R)` is contained in `B̄_{R+D_R}`
  (`cell_subset_closedBall_of_hits`), and integrating its endpoint density over its own
  cell returns *half* its endpoint energy, so that an edge with both endpoints in the patch
  is counted twice and contributes its full energy
  (`cellVolume_mul_specificEnergyDensity`, `tsum_cellEnergy_le_setLIntegral`).  The
  interiors of distinct cells are disjoint and the global boundary mask is Lebesgue null,
  which is what turns the cellwise bound into an integral bound.

* **Zero specific norm kills every edge.**
  `apply_eq_of_setLIntegral_closedBall_eq_zero` is the manuscript's "on integer-radius
  disks `s:eq:localcontrol` then detects every edge and makes its value zero": a cell is
  compact, hence contained in some disk, and it has *positive area*, so a vanishing disk
  integral forces the whole endpoint sum at that cell to vanish and therefore
  `Φ w = Φ v` across every edge of positive conductance.

* **`s:eq:BC` and its consequence.**  `ae_eventually_le_geometric` is the Borel–Cantelli
  step: the manuscript bounds the failure probability of `M(ρ_{θ_j}) ≤ 2^{-2j}` by
  `512 · 2^{-2j}` — which is `s:prop:maximal` applied with `‖θ_j‖² ≤ 2^{-4j}` — and that
  sequence is summable.  `tsum_rpow_half_le_of_geometric` and
  `tsum_rpow_half_ne_top_of_eventually` then perform the manuscript's actual *use* of the
  lemma in `s:prop:limit`: on each bounded spatial patch the square roots of the patch
  energies of the successive differences are summable, because
  `E_j ≤ (R+D_R)² 2^{-2j} = ((R+D_R) 2^{-j})²`.  `ae_tsum_rpow_half_ne_top` assembles the
  two into the almost-sure statement.

## Inputs that are *not* proved here

The ball domination `∫_{B̄_r} ρ_θ ≤ r² M` and the weak-`L¹` tail bound
`P[M(ρ_{θ_j}) > λ] ≤ 512 E[F_j]/λ` are the manuscript's spatial maximal inequality
`s:prop:maximal`; they enter as explicit hypotheses in exactly the form produced by
`ReflectedGMS.SpatialMaximalInequality` (`ballAverage_le_ballMaximal` and
`measure_ballMaximal_gt_le`).  They are quantitative estimates about a *different*
object (the maximal function of a rooted density), not disguised forms of the local
conclusion proved here.  Nothing about the limiting gradient `g`, the harmonic potential
`Φ`, or the nested projection identity is used or reproved.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS.SpecificEnergyLocalControl

open StatementIngredients RootDensities ActiveBlockEdges

variable {V : Type*} [Countable V]

/-! ### The vector edge contribution in closed form -/

/-- The squared Euclidean norm on the plane is the sum of the squared coordinates. -/
theorem normSq_eq_sum_coord (x : Plane) : ‖x‖ ^ 2 = ∑ i : Fin 2, x i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]

/-- The ordered-pair vector energy contribution `c(e)|θ(e)|²` of
`ActiveBlockEdges.vectorGradSq`, written with the manuscript's squared vector increment
instead of the two coordinate increments. -/
theorem vectorGradSq_eq_ofReal_mul (G : ReflectedWalk.ConductanceGraph V) (u : V → Plane)
    (p : V × V) :
    vectorGradSq G u p
      = ENNReal.ofReal (G.c p.1 p.2) * ENNReal.ofReal (‖u p.2 - u p.1‖ ^ 2) := by
  have hc : 0 ≤ G.c p.1 p.2 := G.c_nonneg _ _
  calc vectorGradSq G u p
      = ∑ i : Fin 2, ENNReal.ofReal (G.c p.1 p.2 * (u p.2 i - u p.1 i) ^ 2) := by
        simp only [vectorGradSq, ReflectedWalk.ConductanceGraph.gradSq]
    _ = ∑ i : Fin 2, ENNReal.ofReal (G.c p.1 p.2) *
          ENNReal.ofReal ((u p.2 i - u p.1 i) ^ 2) :=
        Finset.sum_congr rfl fun i _ => ENNReal.ofReal_mul hc
    _ = ENNReal.ofReal (G.c p.1 p.2) *
          ∑ i : Fin 2, ENNReal.ofReal ((u p.2 i - u p.1 i) ^ 2) := by
        rw [Finset.mul_sum]
    _ = ENNReal.ofReal (G.c p.1 p.2) *
          ENNReal.ofReal (∑ i : Fin 2, (u p.2 i - u p.1 i) ^ 2) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    _ = ENNReal.ofReal (G.c p.1 p.2) * ENNReal.ofReal (‖u p.2 - u p.1‖ ^ 2) := by
        rw [normSq_eq_sum_coord]
        simp only [PiLp.sub_apply]

/-! ### One cell carries half of its endpoint energy -/

/-- **The manuscript's factor `1/2`.**  Integrating the endpoint density `ρ_θ` over one
cell returns *half* of the endpoint energy of that cell.  Summing over both endpoints of
an edge therefore returns its full energy `c(e)|θ(e)|²`. -/
theorem cellVolume_mul_specificEnergyDensity (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) (v : V) :
    volume ((F.cell v : Set Plane)) * specificEnergyDensity F Φ v
      = (∑' w : V, ENNReal.ofReal (F.graph.c v w) *
          ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2)) / 2 := by
  have hvol := cellVolume_pos_lt_top F hF v
  have hA : volume ((F.cell v : Set Plane))
      = ENNReal.ofReal (StatementIngredients.cellArea F v) :=
    (ENNReal.ofReal_toReal hvol.2.ne).symm
  have hne0 : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ 0 := fun h =>
    absurd (ENNReal.ofReal_eq_zero.1 h) (not_le.2 (StatementIngredients.cellArea_pos F hF v))
  have hnet : ENNReal.ofReal (StatementIngredients.cellArea F v) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [hA]
  unfold specificEnergyDensity
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [show ENNReal.ofReal (StatementIngredients.cellArea F v) *
        ((∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2)) *
          ((2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹))
      = (∑' w : V, ENNReal.ofReal (F.graph.c v w) * ENNReal.ofReal (‖Φ w - Φ v‖ ^ 2)) *
          (2 : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (StatementIngredients.cellArea F v) *
            (ENNReal.ofReal (StatementIngredients.cellArea F v))⁻¹) from by ring,
    ENNReal.mul_inv_cancel hne0 hnet, mul_one]

/-! ### The cellwise sum is dominated by the integral over any region containing the cells -/

/-- **Integrating the endpoint density over a region containing the cells.**  If every cell
of `A` is contained in `B`, then the total endpoint energy carried by the cells of `A` is at
most the integral of `ρ_θ` over `B`.  The interiors of distinct cells are disjoint and the
union of the cell frontiers is Lebesgue null, so the cellwise indicators add up below the
rooted density almost everywhere. -/
theorem tsum_cellEnergy_le_setLIntegral (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) {A : Set V} {B : Set Plane}
    (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B) :
    (∑' v : A, volume ((F.cell v.1 : Set Plane)) * specificEnergyDensity F Φ v.1)
      ≤ ∫⁻ z in B, rootedSpecificEnergyDensity F Φ z ∂volume := by
  classical
  have hmask : volume (boundaryMask F) = 0 := by
    -- The mask is the frontier union together with the uncovered set; both are Lebesgue-null,
    -- the second by the covering clause of `Geometry`.
    show volume ((⋃ v : V, frontier (F.cell v : Set Plane)) ∪ uncoveredSet F) = 0
    exact measure_union_null (measure_iUnion_null fun v => hF.2.2.1 v) (volume_uncoveredSet hF)
  have hmeasInt : ∀ v : V, MeasurableSet (interior (F.cell v : Set Plane)) :=
    fun v => isOpen_interior.measurableSet
  have hterm : ∀ v : A,
      (∫⁻ z in B, Set.indicator (interior (F.cell v.1 : Set Plane))
          (fun _ => specificEnergyDensity F Φ v.1) z ∂volume)
        = volume ((F.cell v.1 : Set Plane)) * specificEnergyDensity F Φ v.1 := by
    intro v
    rw [lintegral_indicator_const (hmeasInt v.1), Measure.restrict_apply (hmeasInt v.1),
      Set.inter_eq_self_of_subset_left (subset_trans interior_subset (hAB v.1 v.2)),
      ReflectedGMS.Spatial.volume_interior_eq_of_frontier_null (hF.2.2.1 v.1)]
    exact mul_comm _ _
  have hsum : (∑' v : A, volume ((F.cell v.1 : Set Plane)) * specificEnergyDensity F Φ v.1)
      = ∫⁻ z in B, ∑' v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
          (fun _ => specificEnergyDensity F Φ v.1) z ∂volume := by
    rw [lintegral_tsum fun v : A =>
      ((measurable_const.indicator (hmeasInt v.1)).aemeasurable)]
    exact (tsum_congr hterm).symm
  rw [hsum]
  refine lintegral_mono_ae ?_
  have hae : ∀ᵐ z ∂(volume.restrict B), z ∉ boundaryMask F := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simpa using hmask
  filter_upwards [hae] with z hz
  by_cases hex : ∃ v : A, z ∈ interior (F.cell v.1 : Set Plane)
  · obtain ⟨v₀, hv₀⟩ := hex
    have hsingle : (∑' v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
        (fun _ => specificEnergyDensity F Φ v.1) z)
        = specificEnergyDensity F Φ v₀.1 := by
      refine (tsum_eq_single v₀ ?_).trans (Set.indicator_of_mem hv₀ _)
      intro b hb
      refine Set.indicator_of_notMem (fun hbz => ?_) _
      have hne : b.1 ≠ v₀.1 := fun h => hb (Subtype.ext h)
      exact (Set.disjoint_left.1 (hF.2.2.2.1 hne) hbz) hv₀
    rw [hsingle]
    have hroot : rootAt F z = some v₀.1 := (rootAt_eq_some_iff F hF z v₀.1).2 ⟨hz, hv₀⟩
    simp [rootedSpecificEnergyDensity, hroot]
  · push_neg at hex
    have hzero : ∀ v : A, Set.indicator (interior (F.cell v.1 : Set Plane))
        (fun _ => specificEnergyDensity F Φ v.1) z = 0 :=
      fun v => Set.indicator_of_notMem (hex v) _
    simp only [hzero, tsum_zero]
    exact zero_le

/-! ### The patch energy is a cellwise sum -/

/-- **An edge inside the patch is counted at both of its endpoints.**  The restricted
vector energy of a patch `A` is at most the total endpoint energy of the cells of `A`; the
factor `1/2` of `vectorEnergy` is exactly compensated by the double counting. -/
theorem vectorEnergy_restrict_le_tsum_cellEnergy (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) (A : Set V) :
    vectorEnergy (restrictGraph F.graph A) (fun v : A => Φ v.1)
      ≤ ∑' v : A, volume ((F.cell v.1 : Set Plane)) * specificEnergyDensity F Φ v.1 := by
  rw [vectorEnergy_eq_tsum_vectorGradSq, ENNReal.tsum_prod']
  have hle : ∀ v : A, (∑' w : A, vectorGradSq (restrictGraph F.graph A)
        (fun u : A => Φ u.1) (v, w))
      ≤ ∑' w : V, ENNReal.ofReal (F.graph.c v.1 w) * ENNReal.ofReal (‖Φ w - Φ v.1‖ ^ 2) := by
    intro v
    have hcongr : ∀ w : A, vectorGradSq (restrictGraph F.graph A)
        (fun u : A => Φ u.1) (v, w)
        = ENNReal.ofReal (F.graph.c v.1 w.1) *
            ENNReal.ofReal (‖Φ w.1 - Φ v.1‖ ^ 2) := fun w =>
      vectorGradSq_eq_ofReal_mul (restrictGraph F.graph A) (fun u : A => Φ u.1) (v, w)
    have hinj : (∑' w : A, ENNReal.ofReal (F.graph.c v.1 w.1) *
          ENNReal.ofReal (‖Φ w.1 - Φ v.1‖ ^ 2))
        ≤ ∑' w : V, ENNReal.ofReal (F.graph.c v.1 w) *
          ENNReal.ofReal (‖Φ w - Φ v.1‖ ^ 2) :=
      ENNReal.tsum_comp_le_tsum_of_injective (f := fun w : A => (w : V))
        Subtype.coe_injective
        (fun w : V => ENNReal.ofReal (F.graph.c v.1 w) *
          ENNReal.ofReal (‖Φ w - Φ v.1‖ ^ 2))
    rw [tsum_congr hcongr]
    exact hinj
  calc (∑' (v : A) (w : A),
        vectorGradSq (restrictGraph F.graph A) (fun u : A => Φ u.1) (v, w)) / 2
      ≤ (∑' v : A, ∑' w : V, ENNReal.ofReal (F.graph.c v.1 w) *
            ENNReal.ofReal (‖Φ w - Φ v.1‖ ^ 2)) / 2 :=
        ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hle) 2
    _ = ∑' v : A, (∑' w : V, ENNReal.ofReal (F.graph.c v.1 w) *
            ENNReal.ofReal (‖Φ w - Φ v.1‖ ^ 2)) / 2 := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.tsum_mul_right]
    _ = ∑' v : A, volume ((F.cell v.1 : Set Plane)) * specificEnergyDensity F Φ v.1 :=
        tsum_congr fun v => (cellVolume_mul_specificEnergyDensity F hF Φ v.1).symm

/-- **The patch energy is dominated by the integral of the density over any region
containing the patch cells.**  This is `s:eq:localcontrol` for a general region. -/
theorem vectorEnergy_restrict_le_setLIntegral (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) {A : Set V} {B : Set Plane}
    (hAB : ∀ v ∈ A, (F.cell v : Set Plane) ⊆ B) :
    vectorEnergy (restrictGraph F.graph A) (fun v : A => Φ v.1)
      ≤ ∫⁻ z in B, rootedSpecificEnergyDensity F Φ z ∂volume :=
  le_trans (vectorEnergy_restrict_le_tsum_cellEnergy F hF Φ A)
    (tsum_cellEnergy_le_setLIntegral F hF Φ hAB)

/-! ### Every cell of `ℍ(B̄_R)` lies in `B̄_{R+D_R}` -/

/-- **`Every cell in ℍ(B̄_R) is contained in B̄_{R+D_R}`.**  A cell meeting the closed
disk of radius `R` and of diameter at most `D_R` is contained in the closed disk of radius
`R + D_R`. -/
theorem cell_subset_closedBall_of_hits (F : IndexedCells V) {R DR : ℝ} {v : V}
    (hv : Hits F (Metric.closedBall (0 : Plane) R) v)
    (hd : Metric.diam (F.cell v : Set Plane) ≤ DR) :
    (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (R + DR) := by
  obtain ⟨y, hyc, hyB⟩ := hv
  intro x hx
  have hdist : dist x y ≤ Metric.diam (F.cell v : Set Plane) :=
    Metric.dist_le_diam_of_mem (F.cell v).isCompact.isBounded hx hyc
  rw [Metric.mem_closedBall] at hyB ⊢
  calc dist x 0 ≤ dist x y + dist y 0 := dist_triangle _ _ _
    _ ≤ DR + R := add_le_add (le_trans hdist hd) hyB
    _ = R + DR := by ring

/-- **`s:eq:localcontrol`, first inequality.**  The patch energy of `θ = ∇Φ` over the cells
meeting `B̄_R` is at most the integral of the endpoint density `ρ_θ` over `B̄_{R+D_R}`. -/
theorem vectorEnergy_hittingVertices_le_setLIntegral_closedBall (F : IndexedCells V)
    (hF : Geometry F) (Φ : V → Plane) {R DR : ℝ}
    (hD : ∀ v ∈ hittingVertices F (Metric.closedBall (0 : Plane) R),
      Metric.diam (F.cell v : Set Plane) ≤ DR) :
    vectorEnergy (restrictGraph F.graph (hittingVertices F (Metric.closedBall (0 : Plane) R)))
        (fun v => Φ v.1)
      ≤ ∫⁻ z in Metric.closedBall (0 : Plane) (R + DR),
          rootedSpecificEnergyDensity F Φ z ∂volume :=
  vectorEnergy_restrict_le_setLIntegral F hF Φ
    (fun v hv => cell_subset_closedBall_of_hits F hv (hD v hv))

/-- **`s:eq:localcontrol`, full display.**  Composing the first inequality with the ball
bound `∫_{B̄_r} ρ_θ ≤ r² M` of the spatial maximal inequality gives

`∑_{e ∈ E(ℍ(B̄_R))} c(e)|θ(e)|² ≤ (R+D_R)² M(ρ_θ)`. -/
theorem vectorEnergy_hittingVertices_le_ballMaximal (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane) {R DR : ℝ} {M : ℝ≥0∞} (hpos : 0 < R + DR)
    (hD : ∀ v ∈ hittingVertices F (Metric.closedBall (0 : Plane) R),
      Metric.diam (F.cell v : Set Plane) ≤ DR)
    (hM : ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r, rootedSpecificEnergyDensity F Φ z ∂volume)
        ≤ ENNReal.ofReal (r ^ 2) * M) :
    vectorEnergy (restrictGraph F.graph (hittingVertices F (Metric.closedBall (0 : Plane) R)))
        (fun v => Φ v.1)
      ≤ ENNReal.ofReal ((R + DR) ^ 2) * M :=
  le_trans (vectorEnergy_hittingVertices_le_setLIntegral_closedBall F hF Φ hD) (hM _ hpos)

/-! ### A zero specific norm kills every edge -/

/-- **A vanishing density on every disk makes `θ` vanish on every edge.**  This is the
manuscript's "`s:eq:localcontrol`, on integer-radius disks, then detects every edge and
makes its value zero": a cell is compact, so it lies in some disk, and its area is
positive, so the whole endpoint sum at that cell must vanish. -/
theorem apply_eq_of_setLIntegral_closedBall_eq_zero (F : IndexedCells V) (hF : Geometry F)
    (Φ : V → Plane)
    (h : ∀ r : ℝ, 0 < r →
      (∫⁻ z in Metric.closedBall (0 : Plane) r, rootedSpecificEnergyDensity F Φ z ∂volume)
        = 0)
    {v w : V} (hc : 0 < F.graph.c v w) : Φ w = Φ v := by
  obtain ⟨r, hr⟩ := (F.cell v).isCompact.isBounded.subset_closedBall (0 : Plane)
  have hr1 : (F.cell v : Set Plane) ⊆ Metric.closedBall (0 : Plane) (max r 1) :=
    hr.trans (Metric.closedBall_subset_closedBall (le_max_left r 1))
  have hpos : (0 : ℝ) < max r 1 := lt_of_lt_of_le one_pos (le_max_right r 1)
  have hle := tsum_cellEnergy_le_setLIntegral F hF Φ (A := ({v} : Set V))
    (B := Metric.closedBall (0 : Plane) (max r 1))
    (fun u hu => by
      have huv : u = v := hu
      subst huv
      exact hr1)
  rw [h _ hpos] at hle
  have hsingle : volume ((F.cell v : Set Plane)) * specificEnergyDensity F Φ v
      ≤ ∑' u : ({v} : Set V),
        volume ((F.cell u.1 : Set Plane)) * specificEnergyDensity F Φ u.1 :=
    ENNReal.le_tsum (f := fun u : ({v} : Set V) =>
      volume ((F.cell u.1 : Set Plane)) * specificEnergyDensity F Φ u.1) ⟨v, rfl⟩
  have hterm : volume ((F.cell v : Set Plane)) * specificEnergyDensity F Φ v = 0 :=
    le_antisymm (le_trans hsingle hle) zero_le
  rw [cellVolume_mul_specificEnergyDensity F hF Φ v] at hterm
  rcases ENNReal.div_eq_zero_iff.1 hterm with hzero | htop
  · have hw := ENNReal.tsum_eq_zero.1 hzero w
    rcases mul_eq_zero.1 hw with h1 | h2
    · exact absurd (ENNReal.ofReal_eq_zero.1 h1) (not_le.2 hc)
    · have hnorm : ‖Φ w - Φ v‖ ^ 2 ≤ 0 := ENNReal.ofReal_eq_zero.1 h2
      have hz : ‖Φ w - Φ v‖ = 0 := by nlinarith [norm_nonneg (Φ w - Φ v)]
      exact sub_eq_zero.1 (norm_eq_zero.1 hz)
  · exact absurd htop (by simp)

/-! ### Summable square roots on a bounded patch -/

/-- A constant times a geometric series with ratio `< 1` is finite. -/
theorem tsum_const_mul_pow_ne_top {c q : ℝ≥0∞} (hc : c ≠ ∞) (hq : q < 1) :
    (∑' j : ℕ, c * q ^ j) ≠ ∞ := by
  have h1 : (1 : ℝ≥0∞) - q ≠ 0 := fun h => absurd (tsub_eq_zero_iff_le.1 h) (not_le.2 hq)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top hc (ENNReal.inv_ne_top.2 h1)

/-! ### `s:eq:BC`: Borel–Cantelli on the maximal function -/

end ReflectedGMS.SpecificEnergyLocalControl
