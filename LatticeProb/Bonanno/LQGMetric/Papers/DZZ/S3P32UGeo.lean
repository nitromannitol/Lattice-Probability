/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UGeo at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32Up

/-!
# DZZ P3.2 upper bound, ball crossing: geometric tools (P2-DZZ32U)

Tools for the crossing claim of DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1071–1079) with
Euclidean balls (l. 1098–1101):

* `exists_cover_of_phiLe`: `Φ_{B,δ} ≤ λ` gives `≤ λ` balls of mass `≤ δ²` covering `∂B`;
* `isPathConnected_frontier_closedBox`: `∂B` is path-connected (four edges);
* `frontier_inter_of_neighbour`: neighbouring boxes of the same level have meeting boundaries;
* `lgdMinSet_le_of_cover`: a path-connected set joining `A` to `B` and covered by a finite family of
  balls of mass `≤ δ²` (arbitrary centres) bounds `min D_δ(A,B)` by the number of balls
  (shrinking to rational centres via compactness).

Own elementary arguments (DZZ treat these points as evident).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-! ### The boundary of a rectangle -/

/-- The boundary of the rectangle `[a,a'] × [b,b']`. -/
def rectBd (a a' b b' : ℝ) : Set ℂ :=
  {z | a ≤ z.re ∧ z.re ≤ a' ∧ b ≤ z.im ∧ z.im ≤ b' ∧
    (z.re = a ∨ z.re = a' ∨ z.im = b ∨ z.im = b')}

lemma frontier_closedBox_eq (B : DyBox) :
    frontier B.closedBox = rectBd (B.j * B.side) ((B.j + 1) * B.side) (B.k * B.side)
      ((B.k + 1) * B.side) := by
  ext z
  constructor
  · intro hz
    have hzB : z ∈ B.closedBox := (isClosed_closedBox B).frontier_subset hz
    obtain ⟨h1, h2, h3, h4⟩ := hzB
    refine ⟨h1, h2, h3, h4, ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨n1, n2, n3, n4⟩ := hne
    have hO : IsOpen {w : ℂ | B.j * B.side < w.re ∧ w.re < (B.j + 1) * B.side ∧
        B.k * B.side < w.im ∧ w.im < (B.k + 1) * B.side} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        ((isOpen_lt Complex.continuous_re continuous_const).inter
          ((isOpen_lt continuous_const Complex.continuous_im).inter
            (isOpen_lt Complex.continuous_im continuous_const)))
    have hsub : {w : ℂ | B.j * B.side < w.re ∧ w.re < (B.j + 1) * B.side ∧
        B.k * B.side < w.im ∧ w.im < (B.k + 1) * B.side} ⊆ B.closedBox :=
      fun w ⟨a1, a2, a3, a4⟩ => ⟨a1.le, a2.le, a3.le, a4.le⟩
    have hint : z ∈ interior B.closedBox := interior_maximal hsub hO
      ⟨lt_of_le_of_ne h1 (Ne.symm n1), lt_of_le_of_ne h2 n2, lt_of_le_of_ne h3 (Ne.symm n3),
        lt_of_le_of_ne h4 n4⟩
    exact hz.2 hint
  · rintro ⟨h1, h2, h3, h4, e⟩
    exact mem_frontier_of_edge ⟨h1, h2, h3, h4⟩ e

/-! ### From a ball cover to `lgdDZZ` -/

lemma exists_shrink_cover {K : Set ℂ} (hK : IsCompact K) {T : Finset (ℂ × ℝ)}
    (hcov : K ⊆ ⋃ q ∈ T, Metric.ball q.1 q.2) :
    ∃ η > 0, ∀ z ∈ K, ∃ q ∈ T, dist z q.1 < q.2 - η := by
  set U : ℕ → Set ℂ := fun n => ⋃ q ∈ T, Metric.ball q.1 (q.2 - 1 / ((n : ℝ) + 1)) with hU
  have hcov' : K ⊆ ⋃ n, U n := by
    intro z hz
    have := hcov hz
    simp only [mem_iUnion, Metric.mem_ball] at this
    obtain ⟨q, hq, h⟩ := this
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h)
    simp only [hU, mem_iUnion, Metric.mem_ball]
    exact ⟨n, q, hq, by linarith⟩
  have hdir : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le fun n n' hnn => ?_
    refine iUnion₂_mono fun q _ => Metric.ball_subset_ball ?_
    have : (n : ℝ) ≤ n' := by exact_mod_cast hnn
    have : 1 / ((n' : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  obtain ⟨n, hn⟩ := hK.elim_directed_cover U
    (fun n => isOpen_biUnion fun q _ => Metric.isOpen_ball) hcov' hdir
  refine ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz => ?_⟩
  have := hn hz
  simp only [hU, mem_iUnion, Metric.mem_ball] at this
  obtain ⟨q, hq, h⟩ := this
  exact ⟨q, hq, h⟩

/-- **A ball cover of a connecting set bounds `min D_δ(A,B)`.** -/
theorem lgdMinSet_le_of_cover {μ : Measure ℂ} {δ : ℝ} {A B K : Set ℂ} {x y : ℂ} (hx : x ∈ A)
    (hy : y ∈ B) (hK : JoinedIn K x y) {T : Finset (ℂ × ℝ)}
    (hcov : K ⊆ ⋃ q ∈ T, Metric.ball q.1 q.2)
    (hT : ∀ q ∈ T, μ (Metric.ball q.1 q.2) ≤ ENNReal.ofReal (δ ^ 2)) :
    lgdMinSet μ δ A B ≤ T.card := by
  classical
  obtain ⟨γ, hγK⟩ := hK
  obtain ⟨η, hη, hsh⟩ := exists_shrink_cover (isCompact_range γ.continuous)
    ((range_subset_iff.2 hγK).trans hcov)
  choose c hc using fun q : ℂ × ℝ => exists_ratPt_dist_lt q.1 (half_pos hη)
  set T' := T.filter fun q => η < q.2 with hT'
  set e := T'.equivFin
  refine (iInf₂_le_of_le x hx (iInf₂_le y hy)).trans ?_
  refine (show lgdDZZ μ δ x y ≤ (T'.card : ℕ∞) from ?_).trans
    (by exact_mod_cast Finset.card_filter_le _ _)
  unfold lgdDZZ
  refine iInf₂_le T'.card ⟨fun i => c (e.symm i).1, fun i => (e.symm i).1.2 - η / 2, γ,
    fun i => ⟨?_, ?_⟩, fun t => ?_⟩
  · have := (Finset.mem_filter.1 (e.symm i).2).2
    linarith
  · refine (measure_mono fun z hz => ?_).trans (hT _ (Finset.mem_filter.1 (e.symm i).2).1)
    rw [Metric.mem_ball] at hz ⊢
    have := hc (e.symm i).1
    linarith [dist_triangle z (ratPt (c (e.symm i).1)) (e.symm i).1.1]
  · obtain ⟨q, hq, h⟩ := hsh (γ t) ⟨t, rfl⟩
    have hq' : q ∈ T' := Finset.mem_filter.2 ⟨hq, by linarith [dist_nonneg (x := γ t) (y := q.1)]⟩
    refine ⟨e ⟨q, hq'⟩, ?_⟩
    simp only [Equiv.symm_apply_apply, Metric.mem_ball]
    have := hc q
    rw [dist_comm] at this
    linarith [dist_triangle (γ t) q.1 (ratPt (c q))]

end DZZ
end LQGMetric
