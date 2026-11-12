/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.LGDBasic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Instances.Rat

/-!
# Basic facts on DZZ's Liouville graph distance `lgdDZZ` (task P2-GMC, WP-24)

`lgdDZZ μ δ u v` (Statement/Dimension.lean; DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`
l. 121–124) is the least number of open Euclidean balls with rational centres, each of
`μ`-mass `≤ δ²`, whose union contains a path from `u` to `v`. DZZ uses without comment:

* `lgdDZZ_antitone` : `D_{γ,δ}` is non-increasing in `δ` (used in DZZ Thm 1.1's
  "amalgamation", l. 135–141, and the Borel–Cantelli step along dyadic `δ`);
* `one_le_lgdDZZ` : `D_{γ,δ}(u,v) ≥ 1` (so `log D ≥ 0`, DZZ L2.12, l. 740–759);
* `lgdDZZ_lt_top` : finiteness for a measure without atoms, finite on compact subsets of an
  open set containing a path from `u` to `v` (implicit in the definition, DZZ l. 121);
  `lgdDZZ_lt_top_of_convex` for convex open sets such as the open unit square.

All proofs are own elementary arguments (the paper states these facts implicitly): monotonicity
of the infimum, `Fin 0` is empty, and compactness of the path plus density of rational points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

/-- `D_{γ,δ}` is non-increasing in `δ ≥ 0`: a cover admissible for `δ` is admissible for
`δ' ≥ δ`. -/
theorem lgdDZZ_antitone (μ : Measure ℂ) {δ δ' : ℝ} (hδ : 0 ≤ δ) (hδδ' : δ ≤ δ') (u v : ℂ) :
    lgdDZZ μ δ' u v ≤ lgdDZZ μ δ u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  refine iInf₂_le N ⟨c, ρ, P, fun i => ⟨(h1 i).1, (h1 i).2.trans ?_⟩, h2⟩
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hδ hδδ' 2)

/-- `D_{γ,δ}(u,v) ≥ 1`: a cover of a path has at least one ball. -/
theorem one_le_lgdDZZ (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) : 1 ≤ lgdDZZ μ δ u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, -, h2⟩ := hN
  obtain ⟨i, -⟩ := h2 0
  have : 0 < N := Fin.pos i
  exact_mod_cast this

/-- rational points are dense -/
lemma exists_ratPt_dist_lt (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℚ × ℚ, dist (ratPt c) x < ε := by
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x.re - ε / 2 < x.re + ε / 2 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x.im - ε / 2 < x.im + ε / 2 by linarith)
  refine ⟨(a, b), ?_⟩
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  simp only [ratPt, Complex.sub_re, Complex.sub_im]
  have h1 : |(a : ℝ) - x.re| < ε / 2 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  have h2 : |(b : ℝ) - x.im| < ε / 2 := abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/-- around every point of an open set where `μ` is finite on compacts and has no atom, a ball
with rational centre containing it has mass `≤ δ²` -/
lemma exists_ratBall_small {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfin : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) {x : ℂ} (hx : x ∈ U) (hat : μ {x} = 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℚ × ℚ, ∃ ρ : ℝ, 0 < ρ ∧ μ (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) ∧
      x ∈ Metric.ball (ratPt c) ρ := by
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU x hx
  -- `μ (closedBall x (R/2 · 1/(n+1))) → μ {x} = 0`
  set s : ℕ → Set ℂ := fun n => Metric.closedBall x (R / 2 / (n + 1)) with hs
  have hanti : Antitone s := fun m n hmn => Metric.closedBall_subset_closedBall
    (div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast by omega))
  have hsub : s 0 ⊆ U := fun y hy => hRU (by
    have : dist y x ≤ R / 2 / ((0 : ℕ) + 1) := Metric.mem_closedBall.mp hy
    rw [Metric.mem_ball]; simp at this; linarith)
  have hinter : ⋂ n, s n = {x} := by
    ext y
    simp only [mem_iInter, mem_singleton_iff, hs, Metric.mem_closedBall]
    constructor
    · intro h
      by_contra hne
      have hd : 0 < dist y x := dist_pos.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 / dist y x)
      have h1 := h n
      have h2 : R / 2 / (n + 1) < dist y x := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hd] at hn
        nlinarith
      linarith
    · rintro rfl n; simp only [dist_self]; positivity
  have htend : Tendsto (fun n => μ (s n)) atTop (𝓝 (μ {x})) := by
    rw [← hinter]
    exact tendsto_measure_iInter_atTop (fun n => measurableSet_closedBall.nullMeasurableSet)
      hanti ⟨0, (hfin _ (isCompact_closedBall x _) hsub).ne⟩
  rw [hat] at htend
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (δ ^ 2) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hpos)).exists
  set ρ : ℝ := R / 2 / (n + 1) / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  obtain ⟨c, hc⟩ := exists_ratPt_dist_lt x hρpos
  refine ⟨c, ρ, hρpos, (measure_mono ?_).trans hn.le, ?_⟩
  · intro y hy
    rw [Metric.mem_ball] at hy
    show dist y x ≤ R / 2 / (n + 1)
    have := dist_triangle y (ratPt c) x
    linarith
  · rw [Metric.mem_ball, dist_comm]; exact hc

/-- **Finiteness of `D_{γ,δ}(u,v)`** for `δ > 0`, a measure finite on compact subsets of an open
set `U` and without atoms there, and a path from `u` to `v` inside `U`. -/
theorem lgdDZZ_lt_top {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfin : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) (hat : ∀ x ∈ U, μ {x} = 0)
    {δ : ℝ} (hδ : 0 < δ) {u v : ℂ} (P : Path u v) (hP : ∀ t, P t ∈ U) :
    lgdDZZ μ δ u v < ⊤ := by
  choose c ρ hρ hμ hmem using fun t : unitInterval =>
    exists_ratBall_small hU hfin (hP t) (hat _ (hP t)) hδ
  obtain ⟨s, hs⟩ := (isCompact_range P.continuous).elim_finite_subcover
    (fun t => Metric.ball (ratPt (c t)) (ρ t)) (fun _ => Metric.isOpen_ball)
    (by rintro _ ⟨t, rfl⟩; exact mem_iUnion.mpr ⟨t, hmem t⟩)
  let e := s.equivFin
  have hle : lgdDZZ μ δ u v ≤ (s.card : ℕ∞) := by
    unfold lgdDZZ
    refine iInf₂_le s.card ⟨fun i => c (e.symm i), fun i => ρ (e.symm i), P,
      fun i => ⟨hρ _, hμ _⟩, fun t => ?_⟩
    obtain ⟨t', ht', hmem'⟩ := mem_iUnion₂.mp (hs (mem_range_self t))
    exact ⟨e ⟨t', ht'⟩, by simpa using hmem'⟩
  exact hle.trans_lt (ENat.natCast_lt_top _)

/-- Finiteness of `D_{γ,δ}(u,v)` for `u, v` in a convex open set `U` (e.g. the open unit
square), `μ` finite on compact subsets of `U` and without atoms there. -/
theorem lgdDZZ_lt_top_of_convex {μ : Measure ℂ} {U : Set ℂ} (hU : IsOpen U) (hUc : Convex ℝ U)
    (hfin : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤) (hat : ∀ x ∈ U, μ {x} = 0)
    {δ : ℝ} (hδ : 0 < δ) {u v : ℂ} (hu : u ∈ U) (hv : v ∈ U) :
    lgdDZZ μ δ u v < ⊤ := by
  have hJ : JoinedIn U u v := (hUc.isPathConnected ⟨u, hu⟩).joinedIn u hu v hv
  exact lgdDZZ_lt_top hU hfin hat hδ hJ.somePath hJ.somePath_mem

lemma convex_openSquare : Convex ℝ openSquare := by
  intro x hx y hy a b ha hb hab
  simp only [openSquare, mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    add_zero] at hx hy ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hx
  obtain ⟨h5, h6, h7, h8⟩ := hy
  rcases ha.eq_or_lt with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp; exact ⟨h5, h6, h7, h8⟩
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

lemma isOpen_openSquare' : IsOpen openSquare := by
  have h1 : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {z : ℂ | z.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have h3 : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have h4 : IsOpen {z : ℂ | z.im < 1} := isOpen_lt Complex.continuous_im continuous_const
  have : openSquare = {z : ℂ | 0 < z.re} ∩ ({z : ℂ | z.re < 1} ∩ ({z : ℂ | 0 < z.im} ∩
      {z : ℂ | z.im < 1})) := by ext z; simp [openSquare]
  rw [this]; exact h1.inter (h2.inter (h3.inter h4))

/-- Finiteness of `D_{γ,δ}(u,v)` on the open unit square of DZZ. -/
theorem lgdDZZ_lt_top_openSquare {μ : Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ openSquare → μ K < ⊤) (hat : ∀ x ∈ openSquare, μ {x} = 0)
    {δ : ℝ} (hδ : 0 < δ) {u v : ℂ} (hu : u ∈ openSquare) (hv : v ∈ openSquare) :
    lgdDZZ μ δ u v < ⊤ :=
  lgdDZZ_lt_top_of_convex isOpen_openSquare' convex_openSquare hfin hat hδ hu hv

end LQGMetric
