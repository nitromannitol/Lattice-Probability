import LatticeProb.Prob.CellConfigSquareMeasurable

/-!
# The capped square as a measurable selection

For a cell configuration and the uniform dyadic system with coordinates `q = (s, o¹, o²)`, the
capped square `Ŝ_m^w` (Gwynne, Miller and Sheffield, *An invariance principle for ergodic
scale-free random environments*, arXiv 1807.07515, (2.1)) is almost surely the square of the
generation `j` around `w` for which `m` lies between the cell masses of the generations `j` and
`j + 1`. Since these cell masses increase with the generation, this generation is unique, so every
function of `Ŝ_m^w` is almost surely equal to the sum over the generations of the indicator of
this selection event times the function of the square of that generation. The latter is a
measurable function of the configuration, the dyadic system and the point.

This is applied to the uniform-average kernel `|Ŝ_m^{w₀}|⁻¹ 1(w₁ ∈ Ŝ_m^{w₀})` of the mass transport
argument for Lemma 2.3 of that paper (formula (B.6)).

## Main statements

* `LatticeProb.CellConfigCappedSquare.selectedSum_eq_of_mem`: the sum over the selected generations
  is the value at the selected generation.
* `LatticeProb.CellConfigCappedSquare.ae_selectedSum_eq_cappedSquare`: almost surely, for every
  mass `m ∈ (0, ∞)` and every function `g`, the sum is `g (Ŝ_m^w)`.
* `LatticeProb.CellConfigCappedSquare.measurable_averageKernel` and `ae_averageKernel_eq`: the
  uniform-average kernel in the measurable form, and its almost sure equality with
  `|Ŝ_m^{w₀}|⁻¹ 1(w₁ ∈ Ŝ_m^{w₀})`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- The coordinates `(s, o¹, o²)` of the uniform dyadic system. -/
abbrev DyadicCoord : Type := ℝ × (ℕ → ℝ) × (ℕ → ℝ)

section Selection

variable {ι : Type*} (c : ι → Set ℂ) (m : ℝ≥0∞) (q : DyadicCoord) (w : ℂ)

/-- The generations `j` for which `m` lies between the cell masses of the squares of the
generations `j` and `j + 1` around `w`. -/
def selectionSet : Set ℤ :=
  {j | cellMass volume c (squareAt q.1 q.2.1 q.2.2 j w) ≤ m ∧
    m < cellMass volume c (squareAt q.1 q.2.1 q.2.2 (j + 1) w)}

/-- A function of the square of the selected generation, written as a sum over the generations. -/
noncomputable def selectedSum (g : Set ℂ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' j : ℤ, (selectionSet c m q w).indicator (fun j => g (squareAt q.1 q.2.1 q.2.2 j w)) j

variable {c m q w}

/-- If the cell masses of the squares around `w` increase with the generation, at most one
generation is selected. -/
theorem selectionSet_subset_singleton
    (hmono : Monotone fun j => cellMass volume c (squareAt q.1 q.2.1 q.2.2 j w))
    {j : ℤ} (hj : j ∈ selectionSet c m q w) : selectionSet c m q w ⊆ {j} := by
  intro j' hj'
  rcases lt_trichotomy j' j with h | h | h
  · exact absurd (lt_of_lt_of_le hj'.2 ((hmono (Int.add_one_le_iff.2 h)).trans hj.1))
      (lt_irrefl m)
  · exact h
  · exact absurd (lt_of_lt_of_le hj.2 ((hmono (Int.add_one_le_iff.2 h)).trans hj'.1))
      (lt_irrefl m)

/-- The sum over the selected generations is the value at the selected generation. -/
theorem selectedSum_eq_of_mem
    (hmono : Monotone fun j => cellMass volume c (squareAt q.1 q.2.1 q.2.2 j w))
    {j : ℤ} (hj : j ∈ selectionSet c m q w) (g : Set ℂ → ℝ≥0∞) :
    selectedSum c m q w g = g (squareAt q.1 q.2.1 q.2.2 j w) := by
  unfold selectedSum
  rw [tsum_eq_single j fun j' hj' => Set.indicator_of_notMem
    (fun h => hj' (selectionSet_subset_singleton hmono hj h)) _, Set.indicator_of_mem hj]

/-- For compatible offsets and an off-grid point, the cell masses of the squares around the point
increase with the generation. -/
theorem monotone_cellMass_squareAt (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2)
    (hw : IsOffGrid q.1 q.2.1 q.2.2 w) :
    Monotone fun j => cellMass volume c (squareAt q.1 q.2.1 q.2.2 j w) :=
  fun _ _ h => cellMass_mono (μ := volume) (c := c) (squareAt_mono h₁ h₂ hw h)

end Selection

/-- **The capped square is almost surely the selected square**: for a fixed point `w` and a
countable locally finite cover of the plane by compact cells of positive area, almost surely, for
every mass `m ∈ (0, ∞)` and every function `g` of a square, the sum over the selected generations
is `g (Ŝ_m^w)`. -/
theorem ae_selectedSum_eq_cappedSquare {ι : Type*} [Countable ι] {c : ι → Set ℂ} (w : ℂ)
    (hc : LocallyFinite c) (hcover : ⋃ i, c i = univ) (hcpt : ∀ i, IsCompact (c i))
    (hpos : ∀ i, volume (c i) ≠ 0) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∀ g : Set ℂ → ℝ≥0∞, selectedSum c m q w g =
        g (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume c) m w) := by
  filter_upwards [ae_isCompatible_isOffGrid_system w,
    ae_exists_isCappedSquare_squareAt_cellMass w hc hcover hcpt hpos] with q hq hex
  intro m hm0 hmtop g
  obtain ⟨j, hj1, hj2, hcap⟩ := hex m hm0 hmtop
  rw [selectedSum_eq_of_mem (monotone_cellMass_squareAt hq.1 hq.2.1 hq.2.2) ⟨hj1, hj2⟩ g,
    hcap.cappedSquare_eq]

/-- The same for the cells of a cell configuration, pulled back to `ℂ`. -/
theorem ae_selectedSum_eq_cappedSquare_complexCells {H : CellConfig}
    (hH : H.IsCellConfiguration) (w : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ →
      ∀ g : Set ℂ → ℝ≥0∞, selectedSum (complexCells H) m q w g =
        g (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2) (cellMass volume (complexCells H)) m w) := by
  have := countable_cells hH
  exact ae_selectedSum_eq_cappedSquare w (locallyFinite_complexCells hH) (iUnion_complexCells hH)
    isCompact_complexCells (volume_complexCells_ne_zero hH)

/-! ### The uniform-average kernel -/

theorem measurable_indicator_apply {β γ : Type*} [MeasurableSpace β] {A : β → Set γ}
    {f : β → γ → ℝ≥0∞} (j : γ) (hA : MeasurableSet {b | j ∈ A b})
    (hf : Measurable fun b => f b j) : Measurable fun b => (A b).indicator (f b) j := by
  have h : (fun b => (A b).indicator (f b) j) = {b | j ∈ A b}.indicator (fun b => f b j) := by
    funext b
    by_cases hb : j ∈ A b
    · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show b ∈ {b | j ∈ A b} from hb)]
    · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (show b ∉ {b | j ∈ A b} from hb)]
  rw [h]
  exact hf.indicator hA

/-- The area of the dyadic square of generation `j` around `w` is measurable in `(q, w)`. -/
theorem measurable_volume_squareAt (j : ℤ) :
    Measurable fun x : DyadicCoord × ℂ => volume (squareAt x.1.1 x.1.2.1 x.1.2.2 j x.2) := by
  have h := measurable_setLIntegral_squareAt j (G := fun _ => (1 : ℝ≥0∞)) measurable_const
  simpa only [setLIntegral_one] using h

/-- **The uniform-average kernel of the capped square** `|Ŝ_m^{w₀}|⁻¹ 1(w₁ ∈ Ŝ_m^{w₀})` of a cell
configuration `H` and the dyadic system `q`, in the measurable form; the argument is
`(H, (q, w₀), w₁)`. -/
noncomputable def averageKernel (m : ℝ≥0∞) (p : GMSSpace × ((DyadicCoord × ℂ) × ℂ)) : ℝ≥0∞ :=
  selectedSum (complexCells p.1.1) m p.2.1.1 p.2.1.2
    fun S => (volume S)⁻¹ * S.indicator (fun _ => (1 : ℝ≥0∞)) p.2.2

/-- **The uniform-average kernel is measurable** in the configuration, the dyadic system and the
two points. -/
theorem measurable_averageKernel (m : ℝ≥0∞) : Measurable (averageKernel m) := by
  unfold averageKernel selectedSum
  refine Measurable.tsum fun j => measurable_indicator_apply
    (A := fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) =>
      selectionSet (complexCells p.1.1) m p.2.1.1 p.2.1.2)
    (f := fun p j => (volume (squareAt p.2.1.1.1 p.2.1.1.2.1 p.2.1.1.2.2 j p.2.1.2))⁻¹ *
      (squareAt p.2.1.1.1 p.2.1.1.2.1 p.2.1.1.2.2 j p.2.1.2).indicator
        (fun _ => (1 : ℝ≥0∞)) p.2.2) j ?_ ?_
  · have h := (measurableSet_cellMass_squareAt_le_lt j m).preimage
      (measurable_fst.prodMk measurable_snd.fst :
        Measurable fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) => (p.1, p.2.1))
    exact h
  · have h := ((measurable_volume_squareAt j).comp measurable_snd.fst).inv.mul
      ((measurable_const.indicator (measurableSet_squareAt_graph j)).comp measurable_snd :
        Measurable fun p : GMSSpace × ((DyadicCoord × ℂ) × ℂ) =>
          {p : (DyadicCoord × ℂ) × ℂ | p.2 ∈ squareAt p.1.1.1 p.1.1.2.1 p.1.1.2.2 j p.1.2}.indicator
            (fun _ => (1 : ℝ≥0∞)) p.2)
    exact h

/-- **The kernel is almost surely the uniform average over the capped square**: for a fixed
configuration and a fixed point `w₀`, almost surely in the dyadic system, for every mass
`m ∈ (0, ∞)` and every `w₁`, the kernel is `|Ŝ_m^{w₀}|⁻¹ 1(w₁ ∈ Ŝ_m^{w₀})`. -/
theorem ae_averageKernel_eq (H : GMSSpace) (w₀ : ℂ) :
    ∀ᵐ q ∂(unifIco 1).prod (offsetLaw.prod offsetLaw), ∀ m : ℝ≥0∞, m ≠ 0 → m ≠ ∞ → ∀ w₁ : ℂ,
      averageKernel m (H, (q, w₀), w₁) =
        (volume (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m w₀))⁻¹ *
        (cappedSquare (dyadicSquares q.1 q.2.1 q.2.2)
          (cellMass volume (complexCells H.1)) m w₀).indicator (fun _ => (1 : ℝ≥0∞)) w₁ := by
  filter_upwards [ae_selectedSum_eq_cappedSquare_complexCells H.2 w₀] with q hq
  intro m hm0 hmtop w₁
  exact hq m hm0 hmtop _

end LatticeProb.CellConfigCappedSquare
