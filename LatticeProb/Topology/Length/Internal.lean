/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/Internal.lean.
-/
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.ENNReal.Lemmas
import LatticeProb.Topology.Length.LengthSpace

/-!
# The internal metric of a subset as a metric space

For a pseudo-emetric space `X` and `Y : Set X`, the internal metric `internalEDist Y` (the infimum
of the lengths of paths that stay in `Y`) is studied as a metric in its own right.

* `curveLength_eq_iSup_internalEDist`: for a continuous curve in `Y`, its length equals the
  supremum over partitions of the sums of the internal distances between consecutive points
  (Burago–Burago–Ivanov, Prop. 2.3.12(1)). The proof follows Burago–Burago–Ivanov: `d ≤ d(·,·;Y)` termwise, and
  `d(P(t_i), P(t_{i+1}); Y) ≤ length(P|[t_i, t_{i+1}])`, with additivity of length.
* `internalEDist_eq_top_of_notMem_right` and `internalEDist_eq_top_of_notMem_left`: no path in `Y`
  reaches a point outside `Y`, so the internal distance to such a point is `∞`.
* `internalEDist_eq_edist_of_ball_subset` (locality): in a length space, if the ball `B(x, r)`
  lies in `Y` and `d(x, y) < r`, then `d(x, y; Y) = d(x, y)`.
* `InternalSpace Y`: the type `Y` with `edist := internalEDist Y`. `continuous_mk` and
  `continuous_internalEDist`: for `Y` open in a length space, the map `Y → InternalSpace Y` is
  continuous, and `d(·,·;Y)` is continuous on `Y × Y`. Only continuity is proved here: the file
  does not claim that this map is a homeomorphism.

Sources: Burago–Burago–Ivanov, *A course in metric geometry* (2001), §2.3.3, Prop. 2.3.12;
Petrunin, *Pure metric geometry* (arXiv:2007.09846), §1 "Length spaces" (induced length metric).
-/

open Set Filter Topology unitInterval
open scoped ENNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X]

/-! ### Curves in `Y` and the internal metric -/

/-- A continuous curve `P : [a, b] → Y` bounds the internal distance of its endpoints. -/
theorem internalEDist_le_curveLength {Y : Set X} {P : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hY : MapsTo P (Icc a b) Y) :
    internalEDist Y (P a) (P b) ≤ curveLength P a b := by
  obtain ⟨γ, hγ, hr⟩ := exists_path_of_curve hab hP
  rw [← hγ]
  refine internalEDist_le_pathLength γ fun t => ?_
  obtain ⟨s, hs, hst⟩ := hr ⟨t, rfl⟩
  exact hst ▸ hY hs

/-- Telescoping additivity of length along a monotone sequence of times. -/
theorem sum_curveLength_eq (P : ℝ → X) {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, curveLength P (u i) (u (i + 1)) = curveLength P (u 0) (u n) := by
  induction n with
  | zero => simp [curveLength_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      curveLength_add P (hu (Nat.zero_le n)) (hu (Nat.le_succ n))]

/-- Partition sums of the internal metric along a curve in `Y` are bounded by its length
(Burago–Burago–Ivanov, proof of Prop. 2.3.12). -/
theorem sum_internalEDist_le_curveLength {Y : Set X} {P : ℝ → X} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hY : MapsTo P (Icc a b) Y) {u : ℕ → ℝ} (hu : Monotone u)
    (hmem : ∀ i, u i ∈ Icc a b) (n : ℕ) :
    ∑ i ∈ Finset.range n, internalEDist Y (P (u (i + 1))) (P (u i)) ≤ curveLength P a b := by
  calc ∑ i ∈ Finset.range n, internalEDist Y (P (u (i + 1))) (P (u i))
      ≤ ∑ i ∈ Finset.range n, curveLength P (u i) (u (i + 1)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hsub : Icc (u i) (u (i + 1)) ⊆ Icc a b :=
          Icc_subset_Icc (hmem i).1 (hmem (i + 1)).2
        rw [internalEDist_comm]
        exact internalEDist_le_curveLength (hu (Nat.le_succ i)) (hP.mono hsub) (hY.mono_left hsub)
    _ = curveLength P (u 0) (u n) := sum_curveLength_eq P hu n
    _ ≤ curveLength P a b := curveLength_mono P (hmem 0).1 (hmem n).2

/-- **Burago–Burago–Ivanov Prop. 2.3.12(1).** The length of a continuous curve in `Y` equals its
length with respect to the internal metric `d(·,·;Y)` (supremum of partition sums of `d(·,·;Y)`). -/
theorem curveLength_eq_iSup_internalEDist {Y : Set X} {P : ℝ → X} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) (hY : MapsTo P (Icc a b) Y) :
    curveLength P a b = ⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
      ∑ i ∈ Finset.range p.1, internalEDist Y (P (p.2.1 (i + 1))) (P (p.2.1 i)) := by
  refine le_antisymm ?_ ?_
  · exact iSup_mono fun p => Finset.sum_le_sum fun i _ => edist_le_internalEDist Y _ _
  · exact iSup_le fun p => sum_internalEDist_le_curveLength hP hY p.2.2.1 p.2.2.2 p.1

/-- No path in `Y` reaches a point outside `Y`, so the internal distance to such a point is `∞`. -/
theorem internalEDist_eq_top_of_notMem_right {Y : Set X} {x y : X} (hy : y ∉ Y) :
    internalEDist Y x y = ∞ := by
  refine iInf_eq_top.2 fun γ => absurd ?_ hy
  simpa using γ.2 1

/-- No path in `Y` starts at a point outside `Y`, so the internal distance from such a point is
`∞`. -/
theorem internalEDist_eq_top_of_notMem_left {Y : Set X} {x y : X} (hx : x ∉ Y) :
    internalEDist Y x y = ∞ := by
  rw [internalEDist_comm]; exact internalEDist_eq_top_of_notMem_right hx

/-! ### Locality -/

/-- **Locality**: in a length space, if the ball `B(x, r)` lies in `Y` and `d(x, y) < r`, then
near-minimal paths from `x` to `y` stay in `Y`, so `d(x, y; Y) = d(x, y)`. -/
theorem internalEDist_eq_edist_of_ball_subset (hX : IsLengthSpace X) {Y : Set X} {x y : X}
    {r : ℝ≥0∞} (hball : Metric.eball x r ⊆ Y) (hxy : edist x y < r) :
    internalEDist Y x y = edist x y := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_)
    (edist_le_internalEDist Y x y)
  obtain ⟨δ, hδ, hδr⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  obtain ⟨γ, hγ⟩ := hX x y (min ε δ : NNReal) (by exact_mod_cast lt_min hε hδ)
  rw [ENNReal.ofReal_coe_nnreal] at hγ
  have hlen : pathLength γ < r :=
    hγ.trans_lt (lt_of_le_of_lt (add_le_add le_rfl (by exact_mod_cast min_le_right ε δ)) hδr)
  have hmem : ∀ t, γ t ∈ Y := fun t => hball <| by
    rw [Metric.mem_eball, edist_comm]
    have h1 := edist_le_curveLength γ.extend t.2.1
    rw [Path.extend_zero, Path.extend_extends'] at h1
    exact (h1.trans (curveLength_mono γ.extend le_rfl t.2.2)).trans_lt hlen
  exact (internalEDist_le_pathLength γ hmem).trans
    (hγ.trans (add_le_add le_rfl (by exact_mod_cast min_le_left ε δ)))

/-! ### The internal metric space -/

/-- The set `Y` carrying its internal metric `d(·,·;Y)`. -/
def InternalSpace (Y : Set X) : Type _ := Y

namespace InternalSpace

variable {Y : Set X}

/-- The point of `InternalSpace Y` given by a point of `Y`. -/
def mk (x : Y) : InternalSpace Y := x

/-- The underlying point of `X`. -/
def val (x : InternalSpace Y) : X := (show Y from x).1

omit [PseudoEMetricSpace X] in
/-- The underlying point of `X` of a point of `InternalSpace Y` lies in `Y`. -/
theorem val_mem (x : InternalSpace Y) : x.val ∈ Y := (show Y from x).2

omit [PseudoEMetricSpace X] in
/-- The underlying point of `X` of `mk x` is `x`. -/
@[simp] theorem val_mk (x : Y) : (mk x).val = x.1 := rfl

omit [PseudoEMetricSpace X] in
/-- The underlying point map `InternalSpace Y → X` is injective. -/
theorem val_injective : Function.Injective (val : InternalSpace Y → X) :=
  fun _ _ h => Subtype.ext (p := (· ∈ Y)) h

/-- The internal metric `d(·,·;Y)` makes `InternalSpace Y` a pseudo-emetric space. -/
noncomputable instance : PseudoEMetricSpace (InternalSpace Y) where
  edist x y := internalEDist Y x.val y.val
  edist_self x := internalEDist_self x.val_mem
  edist_comm x y := internalEDist_comm Y _ _
  edist_triangle x y z := internalEDist_triangle Y _ _ _

/-- The emetric of `InternalSpace Y` is the internal distance of the underlying points. -/
theorem edist_def (x y : InternalSpace Y) : edist x y = internalEDist Y x.val y.val := rfl

/-- The metric of `X` is at most the internal metric of `InternalSpace Y`. -/
theorem edist_val_le (x y : InternalSpace Y) : edist x.val y.val ≤ edist x y :=
  edist_le_internalEDist Y _ _

/-- The internal metric of a subset of an emetric space is an emetric. -/
noncomputable instance {X : Type*} [EMetricSpace X] {Y : Set X} : EMetricSpace (InternalSpace Y) :=
  { (inferInstance : PseudoEMetricSpace (InternalSpace Y)) with
    eq_of_edist_eq_zero := fun {x y} h =>
      val_injective (edist_eq_zero.1 (le_antisymm ((edist_val_le x y).trans h.le) bot_le)) }

/-- **Continuity**: for `Y` open in a length space, `mk : Y → InternalSpace Y` is continuous. -/
theorem continuous_mk (hX : IsLengthSpace X) (hY : IsOpen Y) :
    Continuous (mk : Y → InternalSpace Y) := by
  refine EMetric.continuous_iff.2 fun x ε hε => ?_
  obtain ⟨r, hr, hball⟩ := EMetric.isOpen_iff.1 hY x.1 x.2
  refine ⟨min ε r, lt_min hε hr, fun y hy => ?_⟩
  have hy' : edist x.1 y.1 < min ε r := by rw [edist_comm]; exact hy
  rw [edist_def, val_mk, val_mk, internalEDist_comm,
    internalEDist_eq_edist_of_ball_subset hX hball (hy'.trans_le (min_le_right _ _))]
  exact hy'.trans_le (min_le_left _ _)

/-- **Continuity** of the internal metric: `d(·,·;Y)` is continuous on `Y × Y` for `Y` open in a
length space. -/
theorem continuous_internalEDist (hX : IsLengthSpace X) (hY : IsOpen Y) :
    Continuous (fun p : Y × Y => internalEDist Y p.1 p.2) :=
  continuous_edist.comp ((continuous_mk hX hY).prodMap (continuous_mk hX hY))

end InternalSpace

end LatticeProb.MetricGeometry
