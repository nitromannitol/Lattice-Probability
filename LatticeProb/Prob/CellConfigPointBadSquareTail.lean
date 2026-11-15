import LatticeProb.Prob.CellConfigCovariantDyadicRelatives

/-!
# Point-dependent bad-square tails

For a square event which also depends on a marked point, record whether some square around
that point is bad and has cell mass above a threshold. The construction is measurable and
similarity invariant when the event is, and is eventually empty at a root where the event holds
for all sufficiently large squares.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace LatticeProb.CellConfigCappedSquare

open ReflectedGMS ReflectedGMS.GMS CellMass CappedSquare DyadicOffset

/-- Bad squares around a marked point with at least the specified cell mass. -/
def pointBadSquareMassTail (E : Set ℂ → GMSSpace → ℂ → Prop) (m : ℝ≥0∞) :
    Set (GMSSpace × DyadicCoord × ℂ) :=
  {p | ∃ j : ℤ, ¬ E (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) p.1 p.2.2 ∧
    m ≤ cellMass volume (complexCells p.1.1)
      (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2)}

/-- The tail decreases as the mass threshold increases. -/
theorem pointBadSquareMassTail_antitone (E : Set ℂ → GMSSpace → ℂ → Prop) :
    Antitone (pointBadSquareMassTail E) := by
  intro m n hmn p hp
  obtain ⟨j, hbad, hm⟩ := hp
  exact ⟨j, hbad, hmn.trans hm⟩

/-- Joint measurability follows from measurability in square coordinates, configuration and point. -/
theorem measurableSet_pointBadSquareMassTail {E : Set ℂ → GMSSpace → ℂ → Prop}
    (hE : MeasurableSet {p : (ℝ × ℝ × ℝ) × GMSSpace × ℂ |
      E (cornerSquare p.1.1 p.1.2.1 p.1.2.2) p.2.1 p.2.2}) (m : ℝ≥0∞) :
    MeasurableSet (pointBadSquareMassTail E m) := by
  have he (j : ℤ) : MeasurableSet {p : GMSSpace × DyadicCoord × ℂ |
      E (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2) p.1 p.2.2} := by
    have hs : Measurable fun p : GMSSpace × DyadicCoord × ℂ => p.2.1.1 :=
      measurable_snd.fst.fst
    have hw : Measurable fun p : GMSSpace × DyadicCoord × ℂ => p.2.2 :=
      measurable_snd.snd
    have hf := ((measurable_gridFloor j hs measurable_snd.fst.snd.fst
        (Complex.measurable_re.comp hw)).prodMk
      ((measurable_gridFloor j hs measurable_snd.fst.snd.snd
        (Complex.measurable_im.comp hw)).prodMk
        ((measurable_const : Measurable fun _ : GMSSpace × DyadicCoord × ℂ => (2 : ℝ)).pow
          (hs.add_const (j : ℝ))))).prodMk (measurable_fst.prodMk hw)
    exact hE.preimage hf
  have hm (j : ℤ) : MeasurableSet {p : GMSSpace × DyadicCoord × ℂ |
      m ≤ cellMass volume (complexCells p.1.1)
        (squareAt p.2.1.1 p.2.1.2.1 p.2.1.2.2 j p.2.2)} := by
    exact measurableSet_le measurable_const ((measurable_cellMass_squareAt j).comp
      (measurable_fst.prodMk measurable_snd))
  convert (MeasurableSet.iUnion fun j : ℤ => (he j).compl.inter (hm j)) using 1
  ext p
  simp only [pointBadSquareMassTail, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_compl_iff]

/-- A covariant event gives an invariant bad-square tail. -/
theorem pointBadSquareMassTail_similarity {E : Set ℂ → GMSSpace → ℂ → Prop}
    (hE : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace),
      IsSimilar s u hs H H' → ∀ (S : Set ℂ) (w : ℂ),
        (E ((fun z : ℂ => s • z + similarityOffset s u) '' S) H'
          (s • w + similarityOffset s u) ↔ E S H w))
    (m : ℝ≥0∞) (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : GMSSpace)
    (hHH' : IsSimilar s u hs H H') (q : DyadicCoord)
    (h₁ : IsCompatible q.2.1) (h₂ : IsCompatible q.2.2) (w : ℂ) :
    ((H', similarityCoord s u q, s • w + similarityOffset s u) ∈
      pointBadSquareMassTail E m ↔ (H, q, w) ∈ pointBadSquareMassTail E m) := by
  let δ : ℤ := ⌊q.1 + Real.logb 2 s⌋
  have hsq (j : ℤ) := squareAt_similarityCoord s u hs q h₁ h₂ j w
  have hmass (j : ℤ) :
      cellMass volume (complexCells H'.1)
        (squareAt (similarityCoord s u q).1 (similarityCoord s u q).2.1
          (similarityCoord s u q).2.2 (j + δ) (s • w + similarityOffset s u)) =
      cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j w) := by
    rw [hsq j, show H'.1 = H.1.similarity s u hs from hHH',
      cellMass_complexCells_similarity_image]
  have hindex (j : ℤ) :
      (¬ E (squareAt (similarityCoord s u q).1 (similarityCoord s u q).2.1
        (similarityCoord s u q).2.2 (j + δ) (s • w + similarityOffset s u)) H'
          (s • w + similarityOffset s u) ∧
        m ≤ cellMass volume (complexCells H'.1)
          (squareAt (similarityCoord s u q).1 (similarityCoord s u q).2.1
            (similarityCoord s u q).2.2 (j + δ) (s • w + similarityOffset s u))) ↔
      (¬ E (squareAt q.1 q.2.1 q.2.2 j w) H w ∧
        m ≤ cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j w)) := by
    rw [hmass j, hsq j, hE s u hs H H' hHH']
  change (∃ j : ℤ, _) ↔ ∃ j : ℤ, _
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j - δ, (hindex (j - δ)).1 (by simpa using hj)⟩
  · rintro ⟨j, hj⟩
    exact ⟨j + δ, (hindex j).2 hj⟩

/-- Eventual goodness at the origin makes the rooted tail empty above a finite threshold. -/
theorem exists_forall_ge_not_mem_pointBadSquareMassTail {E : Set ℂ → GMSSpace → ℂ → Prop}
    (H : GMSSpace) (q : DyadicCoord) (h₁ : IsCompatible q.2.1)
    (h₂ : IsCompatible q.2.2)
    (hE : ∀ᶠ j : ℤ in atTop, E (squareAt q.1 q.2.1 q.2.2 j 0) H 0) :
    ∃ N : ℕ, ∀ m : ℝ≥0∞, (N : ℝ≥0∞) ≤ m →
      (H, q, 0) ∉ pointBadSquareMassTail E m := by
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hE
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (cellMass_squareAt_ne_top H q J)
  refine ⟨N, fun m hm hbad => ?_⟩
  obtain ⟨j, hj, hjm⟩ := hbad
  have hjJ : j < J := lt_of_not_ge fun h => hj (hJ j h)
  have hsub := squareAt_mono_of_isCompatible (s := q.1) h₁ h₂ 0 hjJ.le
  have hmass := cellMass_mono volume (complexCells H.1) hsub
  exact (not_lt_of_ge (hm.trans (hjm.trans hmass))) hN

/-- A bad start in a square with sufficient cell mass is in the tail, almost everywhere. -/
theorem ae_mem_pointBadSquareMassTail_of_bad {E : Set ℂ → GMSSpace → ℂ → Prop}
    (H : GMSSpace) (q : DyadicCoord) (j : ℤ) (m : ℝ≥0∞)
    (hm : m ≤ cellMass volume (complexCells H.1) (squareAt q.1 q.2.1 q.2.2 j 0)) :
    ∀ᵐ z ∂volume, z ∈ squareAt q.1 q.2.1 q.2.2 j 0 →
      ¬ E (squareAt q.1 q.2.1 q.2.2 j 0) H z →
      (H, q, z) ∈ pointBadSquareMassTail E m := by
  filter_upwards [ae_isOffGrid_volume q.1 q.2.1 q.2.2] with z hz hzS hbad
  have heq := squareAt_eq_of_mem hz hzS
  exact ⟨j, heq ▸ hbad, heq ▸ hm⟩

end LatticeProb.CellConfigCappedSquare
