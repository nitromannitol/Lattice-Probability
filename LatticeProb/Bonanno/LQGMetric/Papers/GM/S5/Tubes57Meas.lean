/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes57Meas at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Det

/-!
# GM Lemma 5.7, measurability ingredients (task P2-M2L2)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.7
(l. 2997–3018). GM treat the measurability of `F_r(z)` as evident; these are the elementary facts
behind it (own arguments, see `DEVIATIONS.md`):

* `isOpen_setOf_mem_nearComp`: for `V` open, `{u | w ∈ O_u}` is open (`O_u` the component of
  `V ∩ B_δ(u)` containing `u`): a path from `u₀` to `w` inside `O_{u₀}` has a uniform
  neighbourhood in `V ∩ B_δ(u₀)`, and a short segment joins nearby `u` to it;
* `ratio_of_ratios`: `c_*(g) = cs`, `C_*(g) = Cs > 0` give `cs D_g ≤ D̃_g ≤ Cs D_g` pointwise
  (definition (1.21) of `c_*`, `C_*`, GM l. 660);
* `ratio_of_dense`: these bounds on the pairs of a dense sequence hold everywhere (continuity).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `{u | w ∈ O_u}` is open -/
theorem isOpen_setOf_mem_nearComp {V : Set ℂ} (hV : IsOpen V) (δ : ℝ) (w : ℂ) :
    IsOpen {u | w ∈ nearComp V δ u} := by
  rw [isOpen_iff_mem_nhds]
  intro u₀ hw
  change w ∈ connectedComponentIn (V ∩ ball u₀ δ) u₀ at hw
  set O := V ∩ ball u₀ δ with hOdef
  have hO : IsOpen O := hV.inter isOpen_ball
  have hu₀O : u₀ ∈ O := by
    by_contra h
    rw [connectedComponentIn_eq_empty h] at hw
    exact hw
  have hCo : IsOpen (connectedComponentIn O u₀) := hO.connectedComponentIn
  have hCc : IsConnected (connectedComponentIn O u₀) :=
    isConnected_connectedComponentIn_iff.2 hu₀O
  have hpc := (hCo.isConnected_iff_isPathConnected).1 hCc
  have hj := hpc.joinedIn u₀ (mem_connectedComponentIn hu₀O) w hw
  set γ := hj.somePath
  set K := range γ with hK
  have hKO : K ⊆ O := by
    rintro _ ⟨t, rfl⟩; exact connectedComponentIn_subset _ _ (hj.somePath_mem t)
  have hKc : IsCompact K := isCompact_range γ.continuous
  have hu₀K : u₀ ∈ K := ⟨0, γ.source⟩
  have hwK : w ∈ K := ⟨1, γ.target⟩
  obtain ⟨ε, hε, hth⟩ := hKc.exists_thickening_subset_open hO hKO
  obtain ⟨x₁, hx₁K, hmax⟩ := hKc.exists_isMaxOn ⟨u₀, hu₀K⟩
    (continuous_id.dist continuous_const).continuousOn
  set M := dist x₁ u₀
  have hM : M < δ := by have := (hKO hx₁K).2; rwa [mem_ball] at this
  have hM0 : 0 ≤ M := dist_nonneg
  set ρ := min ε (δ - M) / 2 with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]; exact half_pos (lt_min hε (by linarith))
  have hρε : ρ ≤ ε := by
    have := min_le_left ε (δ - M); rw [hρ]; linarith
  have hρδ : 2 * ρ ≤ δ - M := by
    have := min_le_right ε (δ - M); rw [hρ]; linarith
  refine Filter.mem_of_superset (ball_mem_nhds u₀ hρ0) fun u hu => ?_
  rw [mem_ball] at hu
  change w ∈ connectedComponentIn (V ∩ ball u δ) u
  set S := segment ℝ u u₀ ∪ K
  have hS : IsPreconnected S :=
    (convex_segment u u₀).isPreconnected.union u₀ (right_mem_segment ℝ u u₀) hu₀K
      (isPreconnected_range γ.continuous)
  have hseg : segment ℝ u u₀ ⊆ ball u₀ ρ :=
    (convex_ball u₀ ρ).segment_subset (mem_ball.2 hu) (mem_ball_self hρ0)
  have hSsub : S ⊆ V ∩ ball u δ := by
    rintro y (hy | hy)
    · have hy' := mem_ball.1 (hseg hy)
      refine ⟨(hth (mem_thickening_iff.2 ⟨u₀, hu₀K, hy'.trans_le hρε⟩)).1, ?_⟩
      rw [mem_ball]
      have := dist_triangle y u₀ u
      rw [dist_comm u₀ u] at this
      linarith
    · refine ⟨(hKO hy).1, ?_⟩
      rw [mem_ball]
      have h1 : dist y u₀ ≤ M := hmax hy
      have := dist_triangle y u₀ u
      rw [dist_comm u₀ u] at this
      linarith
  exact hS.subset_connectedComponentIn (Or.inl (left_mem_segment ℝ u u₀)) hSsub (Or.inr hwK)

/-- `c_*(g) = cs`, `C_*(g) = Cs`, `0 < cs ≤ Cs` give `cs D_g ≤ D̃_g ≤ Cs D_g` -/
theorem ratio_of_ratios {D D' : DistC → ContMetric} {g : DistC} {cs Cs : ℝ} (hcs : 0 < cs)
    (hCs : cs ≤ Cs) (hl : lowerRatio D D' g = cs) (hu : upperRatio D D' g = Cs) (x y : ℂ) :
    cs * (D g).1 (x, y) ≤ (D' g).1 (x, y) ∧ (D' g).1 (x, y) ≤ Cs * (D g).1 (x, y) := by
  by_cases hxy : x = y
  · subst hxy
    rw [(D g).2.self_eq_zero, (D' g).2.self_eq_zero, mul_zero, mul_zero]
    exact ⟨le_rfl, le_rfl⟩
  have hp : 0 < (D g).1 (x, y) := lt_of_le_of_ne (Tight.cmetric_nonneg (D g).2 _)
    fun h0 => hxy ((D g).2.eq_of_eq_zero x y h0.symm)
  set f : {p : ℂ × ℂ // p.1 ≠ p.2} → ℝ := fun p => (D' g).1 p.1 / (D g).1 p.1
  have hb : BddBelow (range f) := ⟨0, by
    rintro _ ⟨p, rfl⟩; exact div_nonneg (Tight.cmetric_nonneg (D' g).2 _)
      (Tight.cmetric_nonneg (D g).2 _)⟩
  have ha : BddAbove (range f) := by
    by_contra hna
    have h0 : upperRatio D D' g = 0 := Real.iSup_of_not_bddAbove hna
    linarith
  have h1 : cs ≤ f ⟨(x, y), hxy⟩ := hl ▸ ciInf_le hb _
  have h2 : f ⟨(x, y), hxy⟩ ≤ Cs := hu ▸ le_ciSup ha _
  exact ⟨(le_div_iff₀ hp).1 h1, (div_le_iff₀ hp).1 h2⟩

/-- the ratio bounds on the pairs of a dense sequence hold everywhere -/
theorem ratio_of_dense {d d' : ContMetric} {cs Cs : ℝ}
    (h : ∀ i j, cs * d.1 (LocalEvent.qd i, LocalEvent.qd j) ≤ d'.1 (LocalEvent.qd i, LocalEvent.qd j) ∧
      d'.1 (LocalEvent.qd i, LocalEvent.qd j) ≤ Cs * d.1 (LocalEvent.qd i, LocalEvent.qd j))
    (x y : ℂ) : cs * d.1 (x, y) ≤ d'.1 (x, y) ∧ d'.1 (x, y) ≤ Cs * d.1 (x, y) := by
  have hd : DenseRange (Prod.map LocalEvent.qd LocalEvent.qd) :=
    LocalEvent.denseRange_qd.prodMap LocalEvent.denseRange_qd
  have hc : Continuous fun p : ℂ × ℂ => d.1 p := d.1.continuous
  have hc' : Continuous fun p : ℂ × ℂ => d'.1 p := d'.1.continuous
  have c1 : IsClosed {p : ℂ × ℂ | cs * d.1 p ≤ d'.1 p} :=
    isClosed_le (continuous_const.mul hc) hc'
  have c2 : IsClosed {p : ℂ × ℂ | d'.1 p ≤ Cs * d.1 p} :=
    isClosed_le hc' (continuous_const.mul hc)
  have s1 : range (Prod.map LocalEvent.qd LocalEvent.qd) ⊆ {p : ℂ × ℂ | cs * d.1 p ≤ d'.1 p} := by
    rintro _ ⟨⟨i, j⟩, rfl⟩; exact (h i j).1
  have s2 : range (Prod.map LocalEvent.qd LocalEvent.qd) ⊆ {p : ℂ × ℂ | d'.1 p ≤ Cs * d.1 p} := by
    rintro _ ⟨⟨i, j⟩, rfl⟩; exact (h i j).2
  exact ⟨c1.closure_subset_iff.2 s1 (hd.closure_range ▸ mem_univ (x, y)),
    c2.closure_subset_iff.2 s2 (hd.closure_range ▸ mem_univ (x, y))⟩

end LQGMetric.GM
