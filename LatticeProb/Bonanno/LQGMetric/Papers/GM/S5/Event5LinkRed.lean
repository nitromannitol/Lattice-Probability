/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event5LinkRed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event5Link
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event5C6

/-!
# GM Lemma 5.9: conditions (1)–(3) of `E_r` are measurable (task P2-M2M8)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, Lemma 5.9
(`lem-geo-event-msrble`, l. 3293–3302). `linkEvent` (conditions (1)–(3), l. 3044–3062) quantifies
over all `x, y ∈ ∂B_{2r}(0)`; the end points enter only through `U x y` (finitely many values,
`sqTubes`) and through condition (2), `SepDiscNear (U x y) (20ε₀r) u x y (ε₀r)`. Own elementary
countable reduction (GM: "by inspection"):

* the sets `O_{u'}` (`u'` near `u ∈ 𝔸_{(1−4ρ)r,(1+4ρ)r}(0)`) lie in `B_M(0)`, `M = (1+4ρ)r + 20ε₀r`,
  so every connected subset of `G = W ∩ {‖w‖ > M}` lies in one component of `W ∖ O_{u'}`; hence
  condition (2) at `(x, y)` only depends on the components of `G` containing `x` and `y`
  (`sepPair_congr`, `linkXY_congr`);
* the components of the open set `G` are open, so each one contains a point of the dense sequence
  `qd`; `linkEvent` is the intersection of `linkXY W (qd m) (qd n)` over a countable index set
  (`linkEvent_eq_iInter`), each universally measurable on `D̃⁻¹' lenSet` (`Event5Link.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- the part of `W` outside `B_M(0)` -/
def outPart (W : Set ℂ) (M : ℝ) : Set ℂ := W ∩ {w | M < ‖w‖}

lemma isOpen_outPart {W : Set ℂ} (hW : IsOpen W) (M : ℝ) : IsOpen (outPart W M) :=
  hW.inter (isOpen_lt continuous_const continuous_norm)

lemma mem_of_mem_comp_e5 {F : Set ℂ} {x x' : ℂ} (h : x' ∈ connectedComponentIn F x) : x ∈ F := by
  by_contra hx
  rw [connectedComponentIn_eq_empty hx] at h
  exact h

lemma mem_comp_symm_e5 {F : Set ℂ} {x x' : ℂ} (h : x' ∈ connectedComponentIn F x) :
    x ∈ connectedComponentIn F x' := by
  rw [← connectedComponentIn_eq h]; exact mem_connectedComponentIn (mem_of_mem_comp_e5 h)

/-- the disconnection data at `(x, y)` only depend on the components of `outPart W M` -/
lemma sepPair_congr {W O : Set ℂ} {M d : ℝ} (hO : ∀ w ∈ O, ‖w‖ < M) {x x' y y' : ℂ}
    (hx : x' ∈ connectedComponentIn (outPart W M) x)
    (hy : y' ∈ connectedComponentIn (outPart W M) y) :
    (SepFrom W O x d ∧ y ∉ connectedComponentIn (W \ O) x) ↔
      (SepFrom W O x' d ∧ y' ∉ connectedComponentIn (W \ O) x') := by
  have hGs : outPart W M ⊆ W \ O := fun w hw => ⟨hw.1, fun h => lt_asymm (hO w h) hw.2⟩
  have hyG := mem_of_mem_comp_e5 hy
  have ex : connectedComponentIn (W \ O) x = connectedComponentIn (W \ O) x' :=
    connectedComponentIn_eq (connectedComponentIn_mono x hGs hx)
  have hy'y : y' ∈ connectedComponentIn (W \ O) y := connectedComponentIn_mono y hGs hy
  have ey : connectedComponentIn (W \ O) y = connectedComponentIn (W \ O) y' :=
    connectedComponentIn_eq hy'y
  have hiff : y ∈ connectedComponentIn (W \ O) x ↔ y' ∈ connectedComponentIn (W \ O) x := by
    constructor
    · intro h; rw [connectedComponentIn_eq h]; exact hy'y
    · intro h; rw [connectedComponentIn_eq h, ← ey]; exact mem_connectedComponentIn (hGs hyG)
  unfold SepFrom
  rw [hiff, ex]

/-- condition (2) at `u ∈ B_R(0)` only depends on the components of `outPart W (R + δ)` containing
the end points -/
lemma sepDiscNear_congr {W : Set ℂ} {δ d R : ℝ} {u : ℂ} (hu : ‖u‖ < R) {x x' y y' : ℂ}
    (hx : x' ∈ connectedComponentIn (outPart W (R + δ)) x)
    (hy : y' ∈ connectedComponentIn (outPart W (R + δ)) y) :
    SepDiscNear W δ u x y d ↔ SepDiscNear W δ u x' y' d := by
  have hev : ∀ᶠ u' in 𝓝 u, ‖u'‖ < R := (isOpen_lt continuous_norm continuous_const).mem_nhds hu
  unfold SepDiscNear
  refine Filter.eventually_congr (hev.mono fun u' hu' => sepPair_congr (fun w hw => ?_) hx hy)
  have h1 := (connectedComponentIn_subset _ _ hw).2
  rw [mem_ball, dist_eq_norm] at h1
  have := norm_sub_norm_le w u'
  linarith

lemma linkXY_subset_congr {D D' : DistC → ContMetric} {cs Cs c₁ η ρ b ε r : ℝ} {W : Set ℂ}
    {x x' y y' : ℂ}
    (hx : x' ∈ connectedComponentIn (outPart W ((1 + 4 * ρ) * r + 20 * ε * r)) x)
    (hy : y' ∈ connectedComponentIn (outPart W ((1 + 4 * ρ) * r + 20 * ε * r)) y) :
    linkXY D D' cs Cs c₁ η ρ b ε r W x y ⊆ linkXY D D' cs Cs c₁ η ρ b ε r W x' y' := by
  rintro g ⟨u, hu, v, hv, h1, h2, h3, h4, h5, hs1, hs2, h6, h7⟩
  have nu : ‖u‖ < (1 + 4 * ρ) * r := (mem_annulus_iff_e5.1 hu.1).2
  have nv : ‖v‖ < (1 + 4 * ρ) * r := (mem_annulus_iff_e5.1 hv.1).2
  exact ⟨u, hu, v, hv, h1, h2, h3, h4, h5, (sepDiscNear_congr nu hx hy).1 hs1,
    (sepDiscNear_congr nv hy hx).1 hs2, h6, h7⟩

/-- **`linkXY` only depends on the components of the end points** -/
lemma linkXY_congr {D D' : DistC → ContMetric} {cs Cs c₁ η ρ b ε r : ℝ} {W : Set ℂ}
    {x x' y y' : ℂ}
    (hx : x' ∈ connectedComponentIn (outPart W ((1 + 4 * ρ) * r + 20 * ε * r)) x)
    (hy : y' ∈ connectedComponentIn (outPart W ((1 + 4 * ρ) * r + 20 * ε * r)) y) :
    linkXY D D' cs Cs c₁ η ρ b ε r W x y = linkXY D D' cs Cs c₁ η ρ b ε r W x' y' :=
  (linkXY_subset_congr hx hy).antisymm
    (linkXY_subset_congr (mem_comp_symm_e5 hx) (mem_comp_symm_e5 hy))

/-- the countable index set of the reduction -/
def linkIdx (ρ δ ε r : ℝ) (U : ℂ → ℂ → Set ℂ) : Set (Set ℂ × ℕ × ℕ) :=
  {j | ∃ x ∈ sphere (0 : ℂ) (2 * r), ∃ y ∈ sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ ∧
    j.1 = U x y ∧
    qd j.2.1 ∈ connectedComponentIn (outPart (U x y) ((1 + 4 * ρ) * r + 20 * ε * r)) x ∧
    qd j.2.2 ∈ connectedComponentIn (outPart (U x y) ((1 + 4 * ρ) * r + 20 * ε * r)) y}

/-- a point of an open set has a point of `qd` in its component -/
lemma exists_qd_mem_comp {G : Set ℂ} (hG : IsOpen G) {x : ℂ} (hx : x ∈ G) :
    ∃ n, qd n ∈ connectedComponentIn G x :=
  denseRange_qd.exists_mem_open hG.connectedComponentIn ⟨x, mem_connectedComponentIn hx⟩

/-- **the countable reduction** -/
theorem linkEvent_eq_iInter {D D' : DistC → ContMetric} {S : EData} (hS : S.Ranges) {r : ℝ}
    (hr : 0 < r) {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) :
    linkEvent D D' S.cs S.Cs S.c₁ S.η S.δ S.ρ S.b S.ε₀ r U =
      ⋂ j ∈ linkIdx S.ρ S.δ S.ε₀ r U,
        linkXY D D' S.cs S.Cs S.c₁ S.η S.ρ S.b S.ε₀ r j.1 (qd j.2.1) (qd j.2.2) := by
  obtain ⟨-, -, hb, hρ, hε, -⟩ := hS
  ext g
  simp only [mem_iInter, mem_linkEvent_iff_e5]
  constructor
  · rintro H ⟨W, m, n⟩ ⟨x, hx, y, hy, hxy, rfl, hm, hn⟩
    rw [← linkXY_congr hm hn]
    exact H x hx y hy hxy
  · intro H x hx y hy hxy
    obtain ⟨hUo, -, -, -, hxU, hyU, -⟩ := hU x hx y hy hxy
    have hG := isOpen_outPart hUo ((1 + 4 * S.ρ) * r + 20 * S.ε₀ * r)
    have hM : (1 + 4 * S.ρ) * r + 20 * S.ε₀ * r < 2 * r := by
      nlinarith [hb.2, hρ.2, hε.2, hε.1]
    have hxG : x ∈ outPart (U x y) ((1 + 4 * S.ρ) * r + 20 * S.ε₀ * r) :=
      ⟨hxU, by rw [mem_ofPred_eq, ← dist_zero_right, ← mem_sphere.1 hx] at *; exact hM⟩
    have hyG : y ∈ outPart (U x y) ((1 + 4 * S.ρ) * r + 20 * S.ε₀ * r) :=
      ⟨hyU, by rw [mem_ofPred_eq, ← dist_zero_right, ← mem_sphere.1 hy] at *; exact hM⟩
    obtain ⟨m, hm⟩ := exists_qd_mem_comp hG hxG
    obtain ⟨n, hn⟩ := exists_qd_mem_comp hG hyG
    rw [linkXY_congr hm hn]
    exact H (U x y, m, n) ⟨x, hx, y, hy, hxy, rfl, hm, hn⟩

lemma linkIdx_countable {S : EData} (hS : S.Ranges) {r : ℝ} (hr : 0 < r)
    {U : ℂ → ℂ → Set ℂ} (hU : IsTubeFam S U r) : (linkIdx S.ρ S.δ S.ε₀ r U).Countable := by
  have hε0 : 0 < S.ε₀ * r := mul_pos hS.2.2.2.2.1.1 hr
  have hT := sqTubes_finite_m2m2 (S.ε₀ * r) (squareSet_finite_m2m2 (R := 3 * r) hε0
    (X := {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r}) (fun w hw => by
      rw [mem_ball, dist_zero_right]; linarith [hw.2]))
  refine (hT.countable.prod (countable_univ (α := ℕ × ℕ))).mono ?_
  rintro ⟨W, m, n⟩ ⟨x, hx, y, hy, hxy, rfl, -, -⟩
  exact ⟨tube_mem_sqTubes_m2m2 (hU x hx y hy hxy).2.2.2.1, mem_univ _⟩

/-- **conditions (1)–(3) are null-measurable** for the law of every whole-plane GFF -/
theorem l59MeasOf_eventL (h38 : DFGPSLem3_8) : L59MeasOf eventL := by
  intro γ D D' c cs Cs hPS _ _ _ S _ _ _ _ hS r hr U fb gb hU _ Ω _ P _ h hh
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  set J := linkIdx S.ρ S.δ S.ε₀ r U
  have hJ := linkIdx_countable hS hr hU
  have hJo : ∀ j ∈ J, IsOpen j.1 := by
    rintro ⟨W, m, n⟩ ⟨x, hx, y, hy, hxy, rfl, -, -⟩
    exact (hU x hx y hy hxy).1
  set B := ⋂ j ∈ J, linkXYB D D' S.cs S.Cs S.c₁ S.η S.ρ S.b S.ε₀ r j.1 (qd j.2.1) (qd j.2.2)
  have hB : UMeasurableSet B := by
    simp only [B, biInter_eq_iInter]
    have := hJ.to_subtype
    exact UMeasurableSet.iInter fun j =>
      uMeasurableSet_linkXYB hD.measurable hD'.measurable _ _ _ _ _ _ _ _ (hJo j.1 j.2) _ _
  refine (hB.nullMeasurableSet (P.map h)).congr ?_
  filter_upwards [(ae_map_iff hh.measurable.aemeasurable
    (measurableSet_lenSet.preimage hD'.measurable)).2 (ae_mem_lenSet h38 hγ0 hγ2 hD' P h hh)]
    with g hg
  refine propext ?_
  show g ∈ B ↔ g ∈ linkEvent D D' S.cs S.Cs S.c₁ S.η S.δ S.ρ S.b S.ε₀ r U
  rw [linkEvent_eq_iInter hS hr hU]
  simp only [B, mem_iInter]
  exact forall₂_congr fun j hj => (mem_linkXY_iff_B (hJo j hj) hg).symm

/-! ## GM Lemma 5.9 -/

/-- **GM Lemma 5.9** (`lem-geo-event-msrble`, l. 3293–3302), with `DFGPSLem3_8` for GM.S1.1 -/
theorem gm_L5_9 (h38 : DFGPSLem3_8) : L5_9 :=
  gm_L5_9_of_parts h38 (l59MeasOf_eventL h38) (l59MeasOf_eventC4 h38) (l59MeasOf_eventC5 h38)
    l59MeasOf_eventC6 (l59MeasOf_eventC7 h38) (l59MeasOf_eventC8 h38) (l59MeasOf_eventC9 h38)

end LQGMetric.GM
