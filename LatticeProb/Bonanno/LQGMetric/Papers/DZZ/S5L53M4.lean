/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53M4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Q1

/-!
# DZZ Lemma 5.3, part 1, node 4 in mass-map form, for any chain family (P2-DZZ53M)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522; DEC-131 §2–§3, §9
(the proxies are mass maps `M b : Ω → ℚ × ℚ → ℚ → ℝ≥0∞`, e.g. `proxyMass`, S5L53K1, and the far
relation is `l53FarQ`, S5L53Q1).

* `l53WBadQ`, **`l53WBadQ_le`**, **`l53_wclause_of_not_badQ`**: `l53WBad`, `l53WBad_le`,
  `l53_wclause_of_not_bad` (S5L53M2) for a mass map (same proofs, `measurableSet_l53FarQ`,
  `l53FarQ_of_l53Far_ball`).
* `L53WData`: what the cell/box `b ∋ w` of a chain and its interface `Λ` must satisfy at `ω`
  (level `≤ N`, `b = boxAt b.n w`, small, `Λ ⊆ ∂b` with `μH¹(Λ) ≥ ε s_b`, domination by `M b`).
* **`l53_uv_bound`**: for any family of admissible chains: `P(E ∩ {some admissible chain fails
  the u- or v-clause}) ≤ P(Gᶜ) + 2(N+1)(400/ε)p`, if on `E ∩ G` the head and last boxes of
  admissible chains satisfy `L53WData`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The bad event of node 4 for a mass map**. -/
def l53WBadQ (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T : ℝ) (w : ℂ) (Bd : Set ℂ) (a : ℝ≥0∞) : Set Ω :=
  {ω | a ≤ ((μH[1] : Measure ℂ).restrict Bd) {x | l53FarQ M δ T ω w x}}

/-- **The `w`-clause off the bad event, mass-map form** (copy of `l53_wclause_of_not_bad`). -/
theorem l53_wclause_of_not_badQ {μ0 : Ω → Measure ℂ} {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    {δ T ε : ℝ} {u v w : ℂ} (hw : w = u ∨ w = v) {b : DyBox} {Λ : Set ℂ} {ω : Ω} (hε : 0 < ε)
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q)
    (hΛm : MeasurableSet Λ) (hΛ : Λ ⊆ frontier b.closedBox) (hΛfin : μH[1] Λ ≠ ⊤)
    (hΛε : ε * b.side ≤ (μH[1] : Measure ℂ).real Λ) (hwb : w ∈ b.closedBox)
    (hs : 12 * b.side ≤ ‖v - u‖)
    (hdom : ∀ (c : ℚ × ℚ) (q : ℚ), Metric.ball (ratPt c) q ⊆ sqBox b.center (5 * b.side) →
      μ0 ω (Metric.ball (ratPt c) q) ≤ M ω c q)
    (hnb : ω ∉ l53WBadQ M δ T w (frontier b.closedBox) (ENNReal.ofReal (0.01 * ε * b.side))) :
    ∃ A ⊆ Λ, MeasurableSet A ∧
      0.99 * (μH[1] : Measure ℂ).real Λ ≤ (μH[1] : Measure ℂ).real A ∧
      ∀ x ∈ A, lgdLeExp (dzzWall (tildeBox u v) (μ0 ω)) δ T w x := by
  have hFm : MeasurableSet {x | l53FarQ M δ T ω w x} := by
    have hm : Measurable fun x : ℂ => (((ω, w) : Ω × ℂ), x) :=
      (measurable_const : Measurable fun _ : ℂ => ((ω, w) : Ω × ℂ)).prodMk measurable_id
    exact hm (measurableSet_l53FarQ hM δ T)
  set F : Set ℂ := {x | l53FarQ M δ T ω w x} with hF
  have hBm : MeasurableSet (frontier b.closedBox) := isClosed_frontier.measurableSet
  refine ⟨Λ \ (F ∪ {w}), sdiff_subset, hΛm.diff (hFm.union (measurableSet_singleton w)), ?_, ?_⟩
  · have hlt : μH[1] (F ∩ frontier b.closedBox) < ENNReal.ofReal (0.01 * ε * b.side) := by
      have h : ¬ (ENNReal.ofReal (0.01 * ε * b.side) ≤
          ((μH[1] : Measure ℂ).restrict (frontier b.closedBox)) F) := hnb
      have := not_le.1 h
      rwa [Measure.restrict_apply' hBm] at this
    have hsub : Λ ⊆ (Λ \ (F ∪ {w}) ∪ F ∩ frontier b.closedBox) ∪ {w} := by
      intro x hx
      by_cases hxF : x ∈ F
      · exact Or.inl (Or.inr ⟨hxF, hΛ hx⟩)
      by_cases hxw : x = w
      · exact Or.inr hxw
      · exact Or.inl (Or.inl ⟨hx, fun h => h.elim hxF hxw⟩)
    have h1 : μH[1] Λ ≤ μH[1] (Λ \ (F ∪ {w})) + ENNReal.ofReal (0.01 * ε * b.side) := by
      refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
      rw [l53_hausdorff_singleton, add_zero]
      exact (measure_union_le _ _).trans (add_le_add le_rfl hlt.le)
    have hA : μH[1] (Λ \ (F ∪ {w})) ≠ ⊤ := ne_top_of_le_ne_top hΛfin (measure_mono sdiff_subset)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA, ENNReal.ofReal_ne_top⟩) h1
    rw [ENNReal.toReal_add hA ENNReal.ofReal_ne_top] at h2
    have hb : 0 < b.side := by unfold DyBox.side; positivity
    have hε0 : 0 ≤ ε * b.side := by positivity
    rw [ENNReal.toReal_ofReal (by nlinarith)] at h2
    simp only [measureReal_def] at hΛε ⊢
    nlinarith
  · rintro x ⟨hxΛ, hxn⟩
    have hxF : ¬ l53FarQ M δ T ω w x := fun h => hxn (Or.inl h)
    have hxw : w ≠ x := fun h => hxn (Or.inr h.symm)
    have hxb : x ∈ b.closedBox := (isClosed_closedBox b).frontier_subset (hΛ hxΛ)
    obtain ⟨h1, h2⟩ := l53_tildeBox_sub_uv hw hwb hxb hxw hs
    have h0 : ¬ l53Far μ0 δ T ω w x := fun h =>
      hxF (l53FarQ_of_l53Far_ball (fun c q hcq => hdom c q (hcq.trans h1)) h)
    exact lgdLeExp_wall_mono (h1.trans h2) (μ0 ω) (not_not.1 h0)

/-- **The data of node 4 at the box `b ∋ w` with interface `Λ`** (at `ω`). -/
def L53WData (μ0 : Ω → Measure ℂ) (M : DyBox → Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (u v : ℂ) (ε : ℝ)
    (N : ℕ) (ω : Ω) (b : DyBox) (Λ : Set ℂ) (w : ℂ) : Prop :=
  b.n ≤ N ∧ boxAt b.n w = b ∧ w ∈ b.closedBox ∧ 12 * b.side ≤ ‖v - u‖ ∧ MeasurableSet Λ ∧
    Λ ⊆ frontier b.closedBox ∧ μH[1] Λ ≠ ⊤ ∧ ε * b.side ≤ (μH[1] : Measure ℂ).real Λ ∧
    ∀ (c : ℚ × ℚ) (r : ℚ), Metric.ball (ratPt c) r ⊆ sqBox b.center (5 * b.side) →
      μ0 ω (Metric.ball (ratPt c) r) ≤ M b ω c r

end DZZ
end LQGMetric
