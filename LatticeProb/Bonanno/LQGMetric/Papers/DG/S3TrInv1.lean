/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3TrInv1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Det
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.LGDMeas
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-!
# DG's restricted LGD is a measurable function of rational ball masses (P2-DGTRINV, part 1)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, DG:1243 ("the re-centered field
`ĥ^tr(· − v_S + v_𝕊)` agrees in law with `ĥ^tr`. … it therefore follows that
`P[E_S^ε] = P[E_𝕊^ε]`"). To transfer probabilities of LGD events through an equality in law, the
events must be functions of countably many coordinates of the random measure. This file does
the deterministic part, following `DZZ.lgdMinSet_eq_lgdRat` (LGDMeas.lean) with arbitrary
centres:

* `exists_rat_balls`: a cover of a path by `N` open balls can be replaced by `N` balls with
  rational centres and radii, each contained in the corresponding original ball (compactness of
  the path, `IsCompact.elim_directed_cover`);
* `dgLGDRat`: `D^ε(z,w;U)` as a function of the rational ball masses `μ(B(c,q))`;
  **`dgLGD_eq_dgLGDRat`**: `dgLGD μ ε U z w = dgLGDRat (ballMassQ μ) ε U z w`;
* **`measurable_dgLGDRat`**: measurability in the ball masses (product σ-algebra on
  `ℚ × ℚ → ℚ → ℝ≥0∞`).

Own elementary glue (DG use the measurability implicitly); DV entry proposed in the report.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DG

open DZZ

/-- **rational balls**: a cover of a path by `N` open balls `B(x_i, ρ_i)` can be replaced by a
cover by `N` balls with rational centres and radii `B(c_i, q_i) ⊆ B(x_i, ρ_i)`. -/
lemma exists_rat_balls {z w : ℂ} (P : Path z w) {N : ℕ} (x : Fin N → ℂ) (ρ : Fin N → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hcov : ∀ t, ∃ i, P t ∈ Metric.ball (x i) (ρ i)) :
    ∃ (c : Fin N → ℚ × ℚ) (q : Fin N → ℚ), (∀ i, 0 < q i ∧
      Metric.ball (ratPt (c i)) (q i) ⊆ Metric.ball (x i) (ρ i)) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (q i) := by
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr0 : ∀ n, 0 < r n := fun n => by
    have : 1 / ((n : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith
    simp only [hr]; linarith
  have hr1 : ∀ n, r n < 1 := fun n => by
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    simp only [hr]; linarith
  set U : ℕ → Set ℂ := fun n => ⋃ i, Metric.ball (x i) (ρ i * r n) with hU
  obtain ⟨n, hn⟩ := (isCompact_range P.continuous).elim_directed_cover U
    (fun n => isOpen_iUnion fun i => Metric.isOpen_ball) (by
      rintro _ ⟨t, rfl⟩
      obtain ⟨i, hi⟩ := hcov t
      rw [Metric.mem_ball] at hi
      have hpos : 0 < 1 - dist (P t) (x i) / ρ i := by
        rw [sub_pos, div_lt_one (hρ i)]; exact hi
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨i, Metric.mem_ball.2 ?_⟩⟩
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 : dist (P t) (x i) / ρ i < r n := by simp only [hr]; linarith
      rwa [div_lt_iff₀ (hρ i), mul_comm] at h3)
    (by
      intro a b
      refine ⟨max a b, ?_, ?_⟩ <;>
      · refine iUnion_mono fun i => Metric.ball_subset_ball ?_
        exact mul_le_mul_of_nonneg_left (shrinkFac_mono (by omega)) (hρ i).le)
  -- the slack `η_i = ρ_i (1 − r_n) / 2`
  have hη : ∀ i, 0 < ρ i * (1 - r n) / 2 := fun i => by
    have := hr1 n; have := hρ i; positivity
  have hc : ∀ i, ∃ c : ℚ × ℚ, dist (ratPt c) (x i) < ρ i * (1 - r n) / 2 := fun i =>
    exists_ratPt_dist_lt (x i) (hη i)
  choose c hc using hc
  have hq : ∀ i, ∃ q : ℚ, ρ i * r n + dist (ratPt (c i)) (x i) < q ∧
      (q : ℝ) < ρ i - dist (ratPt (c i)) (x i) := fun i =>
    exists_rat_btwn (by nlinarith [hc i, hρ i, hr1 n])
  choose q hq1 hq2 using hq
  refine ⟨c, q, fun i => ⟨?_, fun y hy => ?_⟩, fun t => ?_⟩
  · have : (0 : ℝ) < q i := lt_of_le_of_lt (by
      have := mul_pos (hρ i) (hr0 n); have := dist_nonneg (x := ratPt (c i)) (y := x i)
      linarith) (hq1 i)
    exact_mod_cast this
  · rw [Metric.mem_ball] at hy ⊢
    have := dist_triangle y (ratPt (c i)) (x i)
    linarith [hq2 i]
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hn ⟨t, rfl⟩)
    refine ⟨i, ?_⟩
    rw [Metric.mem_ball] at hi ⊢
    have := dist_triangle (P t) (x i) (ratPt (c i))
    rw [dist_comm (x i)] at this
    linarith [hq1 i]

/-- `N` rational balls are admissible for `D^ε(z,w;U)` with the mass function `m` -/
def dgRatAdm (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U : Set ℂ) (z w : ℂ) (N : ℕ) : Prop :=
  ∃ (c : Fin N → ℚ × ℚ) (q : Fin N → ℚ),
    (∃ P : Path z w, ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (q i)) ∧
    ∀ i, (0 < q i ∧ Metric.ball (ratPt (c i)) (q i) ⊆ closure U) ∧
      m (c i) (q i) ≤ ENNReal.ofReal ε

/-- DG's `D^ε(z,w;U)` as a function of the rational ball masses `m c q = μ(B(c,q))` -/
def dgLGDRat (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U : Set ℂ) (z w : ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : dgRatAdm m ε U z w N), (N : ℕ∞)

/-- **`D^ε(z,w;U)` is a function of the rational ball masses** -/
theorem dgLGD_eq_dgLGDRat (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    dgLGD μ ε U z w = dgLGDRat (ballMassQ μ) ε U z w := by
  unfold dgLGD dgLGDRat
  refine le_antisymm ?_ ?_
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨c, q, ⟨P, hP⟩, hm⟩ := hN
    refine iInf₂_le N ⟨fun i => ratPt (c i), fun i => q i, P, fun i => ⟨?_, (hm i).1.2, (hm i).2⟩,
      hP⟩
    show (0 : ℝ) < q i
    exact_mod_cast (hm i).1.1
  · refine le_iInf₂ fun N hN => ?_
    obtain ⟨x, ρ, P, h1, h2⟩ := hN
    obtain ⟨c, q, hq, hcov⟩ := exists_rat_balls P x ρ (fun i => (h1 i).1) h2
    refine iInf₂_le N ⟨c, q, ⟨P, hcov⟩, fun i => ⟨⟨(hq i).1, (hq i).2.trans (h1 i).2.1⟩, ?_⟩⟩
    exact (measure_mono (hq i).2).trans (h1 i).2.2

/-- sublevel sets of `dgLGDRat` -/
lemma dgLGDRat_le_iff (m : ℚ × ℚ → ℚ → ℝ≥0∞) (ε : ℝ) (U : Set ℂ) (z w : ℂ) (K : ℕ) :
    dgLGDRat m ε U z w ≤ K ↔ ∃ N, dgRatAdm m ε U z w N ∧ N ≤ K := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ((K + 1 : ℕ) : ℕ∞) ≤ dgLGDRat m ε U z w :=
      le_iInf₂ fun N hN => by exact_mod_cast hne N hN
    have := this.trans h
    norm_cast at this
    omega
  · rintro ⟨N, hN, hNK⟩
    exact (iInf₂_le N hN).trans (by exact_mod_cast hNK)

/-- **measurability of `dgLGDRat`** in the ball masses -/
theorem measurable_dgLGDRat {α : Type*} [MeasurableSpace α] {m : α → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hm : ∀ c q, Measurable fun a => m a c q) (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    Measurable fun a => dgLGDRat (m a) ε U z w := by
  refine measurable_enat_of_le fun K => ?_
  simp_rw [dgLGDRat_le_iff, dgRatAdm]
  refine measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.and
    (Measurable.exists fun c => Measurable.exists fun q => Measurable.and measurable_const
      (Measurable.forall fun i => Measurable.and measurable_const
        (measurableSet_setOfPred.1 (measurableSet_le (hm _ _) measurable_const))))
    measurable_const)

/-- the identity `ℚ × ℚ → ℚ → ℝ≥0∞` with the product σ-algebra: `D^ε(z,w;U)` of the rational
ball masses is measurable -/
theorem measurable_dgLGDRat_id (ε : ℝ) (U : Set ℂ) (z w : ℂ) :
    Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => dgLGDRat m ε U z w :=
  measurable_dgLGDRat (fun c q => (measurable_pi_apply q).comp (measurable_pi_apply c)) ε U z w

/-- the event `E_S^ε` (`goodSq`, DG:1240) as a measurable set of rational ball masses -/
def goodSqRat (ε s : ℝ) (b : ℂ) (M : ℝ) (x : ℤ × ℤ) : Set (ℚ × ℚ → ℚ → ℝ≥0∞) :=
  {m | ∀ u ∈ sqMids s b x, ∀ v ∈ sqMids s b x,
    (dgLGDRat m ε (sqOne s b x) u v : ℝ≥0∞) ≤ ENNReal.ofReal M}

lemma goodSq_iff_rat (μ : Measure ℂ) (ε s : ℝ) (b : ℂ) (M : ℝ) (x : ℤ × ℤ) :
    goodSq μ ε s b M x ↔ ballMassQ μ ∈ goodSqRat ε s b M x := by
  simp only [goodSq, goodSqRat, mem_ofPred_eq, dgLGD_eq_dgLGDRat]

lemma measurableSet_goodSqRat (ε s : ℝ) (b : ℂ) (M : ℝ) (x : ℤ × ℤ) :
    MeasurableSet (goodSqRat ε s b M x) := by
  have hfin : (sqMids s b x).Finite := by
    simp only [sqMids]; exact (((finite_singleton _).insert _).insert _).insert _
  have e : goodSqRat ε s b M x = ⋂ u ∈ sqMids s b x, ⋂ v ∈ sqMids s b x,
      {m | (dgLGDRat m ε (sqOne s b x) u v : ℝ≥0∞) ≤ ENNReal.ofReal M} := by
    ext m; simp [goodSqRat]
  rw [e]
  refine MeasurableSet.biInter hfin.countable fun u _ =>
    MeasurableSet.biInter hfin.countable fun v _ => ?_
  exact measurableSet_le (measurable_from_top.comp (measurable_dgLGDRat_id ε _ u v))
    measurable_const

end DG
end LQGMetric
