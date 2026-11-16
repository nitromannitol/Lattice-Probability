import LatticeProb.Probability.Percolation.DualDecayRectangle
import LatticeProb.Vendor.FormalMathPercolation.Literature.KestenTheoremProofs

/-!
# Conditional rectangle crossing adapter

This module compares the planar rectangle estimate with the definitions in
`Percolation-Rigidity` and its Lattice-Probability dependency at revision
`7512f4fbbc3e3d3ecf3e1af8a450ca7f4f082069`. The definitions below reproduce
definitions equivalent to the pinned model and crossing text, since that revision and the
present library are not available together as imports. The final estimate
is conditional on a lower bound for the consumer critical probability.
-/

open MeasureTheory ProbabilityTheory Percolation.Literature
open scoped ProbabilityTheory

noncomputable section

namespace RigidityCrossingAdapter

namespace Hist

open LatticeProb

variable {d : ℕ}

/-- Integer-coordinate vertices of the lattice. -/
abbrev Vertex (d : ℕ) := Fin d → ℤ

/-- The ℓ¹ distance, using integer absolute values, rather than a Euclidean or sup distance. -/
def latticeL1Dist (x y : Vertex d) : ℤ := ∑ i, |x i - y i|

/-- Unordered nearest-neighbor bonds, with the literal ℓ¹-distance-one carrier. -/
abbrev Bond (d : ℕ) :=
  {e : Sym2 (Vertex d) // ∃ x y : Vertex d,
    e = s(x, y) ∧ (∑ i, |x i - y i|) = 1}

/-- A deterministic assignment of open or closed status to every genuine lattice bond. -/
abbrev Configuration (d : ℕ) := Bond d → Bool

/-- The nearest-neighbor graph already supplied by the lattice library. -/
abbrev nearestNeighborGraph (d : ℕ) := lattice d

/-- The unit-vector lattice adjacency is exactly ℓ¹ distance one. -/
theorem lattice_adj_iff_l1Dist {x y : Vertex d} :
    (nearestNeighborGraph d).Adj x y ↔ latticeL1Dist x y = 1 := by
  constructor
  · rintro ⟨i, rfl | rfl⟩ <;>
      simp [latticeL1Dist, unit, Pi.single_apply, apply_ite abs]
  · intro hsum
    have hex : ∃ i, x i - y i ≠ 0 := by
      by_contra! h
      have hz : latticeL1Dist x y = 0 := by simp [latticeL1Dist, h]
      omega
    obtain ⟨i, hi⟩ := hex
    have hle : |x i - y i| ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (fun j _ => abs_nonneg (x j - y j)) (Finset.mem_univ i)
    have hone : |x i - y i| = 1 := by
      have := abs_pos.mpr hi
      omega
    have herase : ∑ j ∈ Finset.univ.erase i, |x j - y j| = 0 := by
      have he := Finset.sum_erase_add Finset.univ (fun j => |x j - y j|)
        (Finset.mem_univ i)
      change (∑ j, |x j - y j|) = 1 at hsum
      omega
    have hother : ∀ j, j ≠ i → x j = y j := by
      intro j hj
      have hjle := Finset.single_le_sum (fun k _ => abs_nonneg (x k - y k))
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      rw [herase] at hjle
      have hz := abs_nonneg (x j - y j)
      have heq : |x j - y j| = 0 := le_antisymm hjle hz
      exact sub_eq_zero.mp (abs_eq_zero.mp heq)
    have hor : x i - y i = 1 ∨ x i - y i = -1 := (abs_eq (by norm_num)).mp hone
    refine ⟨i, ?_⟩
    rcases hor with hp | hm
    · right
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj]
        exact (hother j hj).trans (add_zero _).symm
    · left
      funext j
      by_cases hj : j = i
      · subst j
        simp only [Pi.add_apply, unit, Pi.single_eq_same]
        omega
      · simp only [Pi.add_apply, unit, Pi.single_eq_of_ne hj]
        exact (hother j hj).symm.trans (add_zero _).symm

/-- The bond determined by adjacent vertices; no endpoint ordering is chosen. -/
def bondOfAdjacent {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) : Bond d :=
  ⟨s(x, y), x, y, rfl, lattice_adj_iff_l1Dist.mp h⟩

/-- Reversing the endpoint presentation does not change its bond. -/
theorem bondOfAdjacent_symm {x y : Vertex d} (h : (nearestNeighborGraph d).Adj x y) :
    bondOfAdjacent h.symm = bondOfAdjacent h := by
  apply Subtype.ext
  exact Sym2.eq_swap

/-- The canonical product Bernoulli law on genuine nearest-neighbor bonds. -/
noncomputable def latticeBondLaw (d : ℕ) (p : unitInterval) : Measure (Configuration d) :=
  Measure.infinitePi (fun _ : Bond d => bernoulliMeasure true (!true) p)

/-- The graph retaining exactly the bonds assigned `true` by the configuration. -/
def openGraph (ω : Configuration d) : SimpleGraph (Vertex d) where
  Adj x y := ∃ h : (nearestNeighborGraph d).Adj x y, ω (bondOfAdjacent h) = true
  symm := ⟨fun _ _ ⟨h, ho⟩ => ⟨h.symm, by rw [bondOfAdjacent_symm]; exact ho⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h.ne rfl⟩

end Hist

namespace Consumer

open Hist

/-- The rectangle `x + R`, where `R` is `[0, m]` in direction `i` and `[0, n]` in the other one. -/
def crossingRectangle (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Set (Vertex 2) :=
  {y | ∀ j, x j ≤ y j ∧ y j ≤ x j + (if j = i then (m : ℤ) else n)}

/-- An open path inside `x + R` joins its two faces orthogonal to direction `i`. -/
def HasOpenCrossing (ω : Configuration 2) (x : Vertex 2) (m n : ℕ) (i : Fin 2) : Prop :=
  ∃ (y z : Vertex 2) (hy : y ∈ crossingRectangle x m n i) (hz : z ∈ crossingRectangle x m n i),
    y i = x i ∧ z i = x i + m ∧
      ((Hist.openGraph ω).induce (crossingRectangle x m n i)).Reachable ⟨y, hy⟩ ⟨z, hz⟩

/-- The consumer crossing statement with its critical value as a parameter. -/
def KestenRectangleCrossingAt (pc : ℝ) : Prop :=
  ∀ p : unitInterval, pc < (p : ℝ) →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Vertex 2) (m n : ℕ) (i : Fin 2),
      latticeBondLaw 2 p {ω | ¬ HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n)))

end Consumer

open DualDecayRectangle

/-- Exponential decay of the dual one-arm event. -/
def OneArm (p : unitInterval) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
    (bondPercolation (LatticeModels.zdGraph 2) (unitInterval.symm p)).real
      (siteToBoundary 2 n) ≤ C * Real.exp (-(c * n))

/-- The Boolean product law has the literal Bernoulli coordinates. -/
theorem source_law_literal (p : unitInterval) :
    Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p) =
      Measure.infinitePi (fun _ : Bond => bernoulliMeasure true (!true) p) := rfl

/-- The pinned and planar Boolean configuration carriers agree. -/
theorem carrier_eq : Hist.Configuration 2 = (Bond → Bool) := rfl

/-- The pinned Boolean bond law is the planar product law. -/
theorem pinned_law_eq (p : unitInterval) :
    Hist.latticeBondLaw 2 p = Measure.infinitePi (fun _ : Bond =>
      bernoulliMeasure (decide ((0 : ℕ) = 0)) (decide ((0 : ℕ) = 1)) p) := rfl

/-- The edge configuration reads the corresponding Boolean bond. -/
theorem to_edge_config_iff (ω : Bond → Bool) (e : (LatticeModels.zdGraph 2).edgeSet) :
    toEdgeConfig ω e ↔ ω (bondEquiv.symm e) = true := Iff.rfl

/-- The inverse edge identification preserves the unordered pair. -/
theorem bond_equiv_symm_val (e : (LatticeModels.zdGraph 2).edgeSet) :
    (bondEquiv.symm e).1 = e.1 := rfl

/-- The two rectangle definitions agree. -/
theorem coordinate_rectangle_eq (v : LatticeModels.Site 2) (m n : ℕ) (i : Fin 2) :
    coordinateRectangle v m n i = Consumer.crossingRectangle v m n i := rfl

/-- The two open graphs on the Boolean configuration agree. -/
theorem open_graph_eq (ω : Hist.Configuration 2) :
    openGraph (EdgeCrossing.extend (LatticeModels.zdGraph 2) (toEdgeConfig ω)) =
      Hist.openGraph ω := by
  ext x y
  rw [extended_openGraph_adj_iff_lattice]
  exact Iff.rfl

/-- The planar crossing event agrees with the pinned crossing text. -/
theorem coordinate_crossing_iff_consumer (ω : Bond → Bool) (v : LatticeModels.Site 2)
    (m n : ℕ) (i : Fin 2) :
    coordinateCrossing ω v m n i ↔ Consumer.HasOpenCrossing ω v m n i := by
  unfold coordinateCrossing Consumer.HasOpenCrossing
  rw [open_graph_eq]
  exact Iff.rfl

/-- The two crossing failure events agree. -/
theorem failure_set_eq (v : LatticeModels.Site 2) (m n : ℕ) (i : Fin 2) :
    {ω : Bond → Bool | ¬ coordinateCrossing ω v m n i} =
      {ω : Hist.Configuration 2 | ¬ Consumer.HasOpenCrossing ω v m n i} := by
  ext ω
  simp only [Set.mem_ofPred_eq, coordinate_crossing_iff_consumer]

/-- Dual one-arm decay implies the pinned-text rectangle estimate. -/
theorem consumer_bound (p : unitInterval) (h : OneArm p) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (x : Hist.Vertex 2) (m n : ℕ) (i : Fin 2),
      Hist.latticeBondLaw 2 p {ω | ¬ Consumer.HasOpenCrossing ω x m n i} ≤
        ENNReal.ofReal (C * (m + 1) * Real.exp (-(c * n))) := by
  obtain ⟨C, c, hC, hc, hb⟩ := exists_coordinate_crossing_failure_bound p h
  refine ⟨C, c, hC, hc, fun x m n i => ?_⟩
  rw [← failure_set_eq]
  exact hb x m n i

/-- Dual decay above a threshold gives the corresponding rectangle estimate. -/
theorem consumer_of_one_arm (pc : ℝ) (h : ∀ p : unitInterval, pc < (p : ℝ) → OneArm p) :
    Consumer.KestenRectangleCrossingAt pc :=
  fun p hp => consumer_bound p (h p hp)

/-- The complementary parameter has one-arm decay above one half. -/
theorem one_arm_of_half_lt (p : unitInterval) (hp : (1 : ℝ) / 2 < p) : OneArm p := by
  have hlt : ((unitInterval.symm p : unitInterval) : ℝ) <
      criticalProb (LatticeModels.zdGraph 2) 0 := by
    rw [kesten_criticalProb_Z2_holds, unitInterval.coe_symm_eq]
    linarith
  obtain ⟨c, hc, h⟩ := DCT16.perc_sharpness_holds (d := 2) le_rfl (unitInterval.symm p) hlt
  exact ⟨1, c, one_pos, hc, fun n => by simpa [neg_mul] using h n⟩

/-- The pinned-text rectangle estimate holds above one half. -/
theorem consumer_at_half : Consumer.KestenRectangleCrossingAt (1 / 2) :=
  consumer_of_one_arm _ one_arm_of_half_lt

/-- Raising the threshold preserves the rectangle estimate. -/
theorem consumer_antitone {pc pc' : ℝ} (hle : pc ≤ pc')
    (h : Consumer.KestenRectangleCrossingAt pc) : Consumer.KestenRectangleCrossingAt pc' :=
  fun p hp => h p (lt_of_le_of_lt hle hp)

/-- A threshold at least one half gives the pinned-text rectangle estimate. -/
theorem consumer_of_half_le {pc : ℝ} (hpc : 1 / 2 ≤ pc) : Consumer.KestenRectangleCrossingAt pc :=
  consumer_antitone hpc consumer_at_half

end RigidityCrossingAdapter
