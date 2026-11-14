import LatticeProb.Prob.CellConfigCappedSquareErgodic

/-!
# The dyadic squares around the origin are capped squares

Let `H` be a cell configuration and `D` an independent uniform dyadic system of the plane, with
coordinates `q ∈ DyadicCoord`. Gwynne, Miller and Sheffield (*An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, Lemma 2.7, (2.3)) state the ergodic lemma along
the squares `S_k` of the dyadic system containing the origin, using that each `S_k` is one of the
capped squares `S_m^0` of (2.1).

For every configuration and almost every dyadic system, the cell mass of the square of generation
`j` containing the origin is finite, strictly increasing in `j ∈ ℤ` and tends to `∞` (the cells
are compact, of positive area, locally finite and cover the plane, and the squares around the
origin exhaust the plane). Hence each square around the origin is the capped square of its own
cell mass, and the uniform average over it is the capped-square average of that mass. With the
conditional ergodic lemma for the capped-square averages along real masses this gives (2.3) along
the squares around the origin, in the conditional form.

## Main results
* `ae_strictMono_cellMass_squareAt_origin`, `ae_tendsto_cellMass_squareAt_origin_atTop`: the cell
  mass of the squares around the origin is strictly increasing and tends to `∞`, almost surely.
* `ae_originCappedSquare_cellMass_squareAt_eq`: almost surely every square around the origin is
  the capped square `S_m^0` for `m` its cell mass.
* `ae_cappedSquareAverage_cellMass_squareAt_eq`: the uniform average over the square of generation
  `j` around the origin is the capped-square average of its cell mass.
* `ae_ae_tendsto_squareAt_average_condExp`: for `μ`-almost every configuration and almost every
  dyadic system, `|S_k|⁻¹ ∫_{S_k} G(H, D, z) dz → E[G(H, D, 0) | 𝓘]` as `k → ∞`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- Extended reals that are finite and tend to `∞` have real parts tending to `+∞`. -/
theorem tendsto_toReal_atTop_of_tendsto_top {α : Type*} {l : Filter α} {f : α → ℝ≥0∞}
    (hf : Tendsto f l (𝓝 ∞)) (hfin : ∀ a, f a ≠ ∞) : Tendsto (fun a => (f a).toReal) l atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hf.eventually (lt_mem_nhds (ENNReal.ofReal_ne_top (r := max b 0)).lt_top)]
    with a ha
  calc b ≤ max b 0 := le_max_left b 0
    _ = (ENNReal.ofReal (max b 0)).toReal := (ENNReal.toReal_ofReal (le_max_right b 0)).symm
    _ ≤ (f a).toReal := ENNReal.toReal_mono (hfin a) ha.le

/-! ### The cell mass of the squares around the origin -/

/-- The cell mass of every square of the dyadic system around the origin is finite (the cells
form a locally finite family and the square is compact). -/
theorem cellMass_squareAt_ne_top (H : GMSSpace) (q : DyadicCoord) (j : ℤ) :
    cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0) ≠ ∞ :=
  cellMass_ne_top volume _ (locallyFinite_complexCells H.2) (isCompact_squareAt j 0)

/-- For every cell configuration and almost every dyadic system, the cell mass of the square of
generation `j` containing the origin is strictly increasing in `j ∈ ℤ` (arXiv 1807.07515, proof of
Lemma 2.2). -/
theorem ae_strictMono_cellMass_squareAt_origin (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, StrictMono fun j : ℤ =>
      cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0) := by
  have := countable_cells H.2
  filter_upwards [ae_isCompatible_isOffGrid_system 0] with q hq
  exact strictMono_cellMass_squareAt hq.1 hq.2.1 hq.2.2 (locallyFinite_complexCells H.2)
    (iUnion_complexCells H.2) fun K => (isCompact_complexCells K).measure_lt_top.ne

/-- For every cell configuration and almost every dyadic system, the cell mass of the square of
generation `j` containing the origin tends to `∞` as `j → ∞`: the squares around the origin
exhaust the plane, and there are infinitely many cells, of positive area. -/
theorem ae_tendsto_cellMass_squareAt_origin_atTop (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, Tendsto (fun j : ℤ =>
      cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0)) atTop (𝓝 ∞) := by
  have hinf := infinite_of_iUnion_eq_univ (iUnion_complexCells H.2) isCompact_complexCells
  filter_upwards [ae_isCompatible_isOffGrid_system 0, ae_iUnion_squareAt_eq_univ]
    with q hq hexh
  exact tendsto_cellMass_atTop volume (complexCells H.1) (squareAt_mono hq.1 hq.2.1 hq.2.2)
    (hexh 0) (volume_complexCells_ne_zero H.2) fun K => (isCompact_complexCells K).measure_lt_top.ne

/-- **The squares around the origin are capped squares**: for every cell configuration and almost
every dyadic system, for every `j ∈ ℤ`, the square of generation `j` containing the origin is the
capped square `S_m^0` of (2.1) of arXiv 1807.07515 for `m` its own cell mass. -/
theorem ae_originCappedSquare_cellMass_squareAt_eq (H : GMSSpace) :
    ∀ᵐ q ∂dyadicLaw, ∀ j : ℤ,
      originCappedSquare (cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0)) H q =
        squareAt q.1 q.2.1 q.2.2 j 0 := by
  have := countable_cells H.2
  filter_upwards [ae_isCompatible_isOffGrid_system 0, ae_strictMono_cellMass_squareAt_origin H]
    with q hq hmono j
  exact ((isCappedSquare_squareAt_iff_cellMass hq.1 hq.2.1 hq.2.2
    (locallyFinite_complexCells H.2) (iUnion_complexCells H.2)
    (fun K => (isCompact_complexCells K).measure_lt_top.ne) j).2
    ⟨le_rfl, hmono (lt_add_one j)⟩).cappedSquare_eq

/-- For every cell configuration and almost every dyadic system, for every `j ∈ ℤ`, the uniform
average of `G` over the square of generation `j` containing the origin is the capped-square average
of its cell mass. -/
theorem ae_cappedSquareAverage_cellMass_squareAt_eq (H : GMSSpace)
    (G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞) :
    ∀ᵐ q ∂dyadicLaw, ∀ j : ℤ,
      cappedSquareAverage (cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0))
          G H q =
        ∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z) := by
  filter_upwards [ae_originCappedSquare_cellMass_squareAt_eq H] with q hq j
  rw [cappedSquareAverage, hq j]

/-! ### The ergodic lemma along the squares around the origin -/

section SquareLimit

variable {μ : Measure GMSSpace}

/-- **Conditional ergodic lemma along the squares around the origin** (arXiv 1807.07515, Lemma 2.7,
(2.3), conditional form): under the mass-transport principle, for every measurable
similarity-invariant `G ≥ 0` with `E[G(H, D, 0)] < ∞`, for `μ`-almost every configuration `H` and
almost every dyadic system `D`, the uniform averages `|S_k|⁻¹ ∫_{S_k} G(H, D, z) dz` over the squares
`S_k` of generation `k` containing the origin converge to `E[G(H, D, 0) | 𝓘](H, D)` as `k → ∞`. -/
theorem ae_ae_tendsto_squareAt_average_condExp [IsFiniteMeasure μ] (hMT : MassTransport μ)
    {G : GMSSpace × DyadicCoord × ℂ → ℝ≥0∞} (hG : Measurable G)
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace), IsSimilar s u hs H H' →
      ∀ q : DyadicCoord, IsCompatible q.2.1 → IsCompatible q.2.2 → ∀ w : ℂ,
        G (H', similarityCoord s u q, s • w + similarityOffset s u) = G (H, q, w))
    (hfin : ∫⁻ p, G (p.1, p.2, 0) ∂μ.prod dyadicLaw ≠ ∞) :
    ∀ᵐ H ∂μ, ∀ᵐ q ∂dyadicLaw,
      Tendsto (fun j : ℤ => (∫⁻ z, (volume (squareAt q.1 q.2.1 q.2.2 j 0))⁻¹ *
          (squareAt q.1 q.2.1 q.2.2 j 0).indicator (fun _ => (1 : ℝ≥0∞)) z * G (H, q, z)).toReal)
        atTop
        (𝓝 ((μ.prod dyadicLaw)[fun p => (G (p.1, p.2, 0)).toReal | cappedSquareTailSigma]
          (H, q))) := by
  filter_upwards [ae_ae_tendsto_cappedSquareAverage_ofReal hMT hG hinv hfin] with H hH
  filter_upwards [hH, ae_tendsto_cellMass_squareAt_origin_atTop H,
    ae_cappedSquareAverage_cellMass_squareAt_eq H G] with q hq htop havg
  have hreal := tendsto_toReal_atTop_of_tendsto_top htop fun j => cellMass_squareAt_ne_top H q j
  refine (hq.comp hreal).congr fun j => ?_
  simp only [Function.comp_apply, ENNReal.ofReal_toReal (cellMass_squareAt_ne_top H q j), havg j]

end SquareLimit

end LatticeProb.CellConfigCappedSquare
