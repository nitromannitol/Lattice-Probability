/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.DcSet at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.JordanBdy
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFDefs

/-!
# The metric `d^U` on `U ∪ ∂U` for `U = ℂ ∖ 𝓑^•_s` (GM S4.5, GM (4.38) = CONF (2.18))

GM `uniqueness-final.tex` l. 2052–2058: for `U` with `ℂ ∖ U` compact and connected,
`d^U(z, w) = inf {diam X : X ⊆ U connected, z, w ∈ Cl′(X)}`, "Then `d^U` is a metric on
`U ∪ ∂U` which is bounded below by the Euclidean metric". Here `Cl′` is the Euclidean closure
(DV-B11; `Blueprint.dU`), and `U = ℂ ∖ 𝓑^•_s(z; D)` whose boundary is a Jordan curve (J1).

* `gm_edist_le_dU`, `gm_dU_comm` (any `U`);
* `gm_dU_self` (`d^U(x, x) = 0` on `U ∪ ∂U`), `gm_dU_triangle` (triangle inequality through any
  `w ∈ U ∪ ∂U`), `gm_dU_eq_zero_iff`: so `d^U` is a metric on `U ∪ ∂U`. The boundary cases use
  the conformal map of J2 (`gm_filledBall_bdy_connect`), hence node J1b (`FilledBallBdyLC`).

GM's proofs are one sentence ("Then `d^U` is a metric …"); the arguments here are own
elementary ones (DV entry proposed in the report).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Topology Filter
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

theorem dc_dU_le {U X : Set ℂ} {x y : ℂ} (hXU : X ⊆ U) (hXc : IsConnected X)
    (hx : x ∈ closure X) (hy : y ∈ closure X) : dU U x y ≤ Metric.ediam X :=
  iInf_le_of_le X (iInf_le_of_le hXU (iInf_le_of_le hXc (iInf_le_of_le hx (iInf_le _ hy))))

variable {D : ContMetric} {z : ℂ} {s : ℝ}

/-- A small connected set of `U` meeting two connected subsets of `U` whose closures contain
`w ∈ U ∪ ∂U`. -/
theorem dc_join (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s))
    (hlc : FilledBallBdyLC D z s) {w : ℂ}
    (hw : w ∈ (filledBall D z s)ᶜ ∪ frontier (filledBall D z s)) {X₁ X₂ : Set ℂ}
    (h₁ : X₁ ⊆ (filledBall D z s)ᶜ) (h₂ : X₂ ⊆ (filledBall D z s)ᶜ) (hw₁ : w ∈ closure X₁)
    (hw₂ : w ∈ closure X₂) {η : ℝ} (hη : 0 < η) :
    ∃ X₃ ⊆ (filledBall D z s)ᶜ, IsPreconnected X₃ ∧ (X₁ ∩ X₃).Nonempty ∧ (X₃ ∩ X₂).Nonempty ∧
      Metric.ediam X₃ ≤ ENNReal.ofReal η := by
  rcases hw with hw | hw
  · obtain ⟨r₀, hr₀, hr₀U⟩ := Metric.isOpen_iff.1 (jb_isClosed_filledBall hbd).isOpen_compl w hw
    set r := min r₀ (η / 2) with hr
    have hrpos : 0 < r := lt_min hr₀ (half_pos hη)
    obtain ⟨a, ha1, ha⟩ := Metric.mem_closure_iff.1 hw₁ r hrpos
    obtain ⟨b, hb2, hb⟩ := Metric.mem_closure_iff.1 hw₂ r hrpos
    refine ⟨ball w r, (ball_subset_ball (min_le_left _ _)).trans hr₀U, isPreconnected_ball,
      ⟨a, ha1, mem_ball.2 (by rwa [dist_comm])⟩, ⟨b, mem_ball.2 (by rwa [dist_comm]), hb2⟩, ?_⟩
    refine Metric.ediam_le fun u hu v hv => ?_
    rw [edist_dist]
    refine ENNReal.ofReal_le_ofReal ?_
    have hu' := mem_ball.1 hu
    have hv' := mem_ball.1 hv
    calc dist u v ≤ dist u w + dist v w := dist_triangle_right _ _ _
      _ ≤ η := by linarith [min_le_right r₀ (η / 2)]
  · obtain ⟨δ, hδ, hX⟩ := gm_filledBall_bdy_connect hs hL hbd hlc hw hη
    obtain ⟨a, ha1, ha⟩ := Metric.mem_closure_iff.1 hw₁ δ hδ
    obtain ⟨b, hb2, hb⟩ := Metric.mem_closure_iff.1 hw₂ δ hδ
    obtain ⟨X₃, hX₃U, hX₃c, haX, hbX, -, hX₃d⟩ :=
      hX a (h₁ ha1) b (h₂ hb2) (by rwa [dist_comm]) (by rwa [dist_comm])
    exact ⟨X₃, hX₃U, hX₃c, ⟨a, ha1, haX⟩, ⟨b, hbX, hb2⟩, hX₃d⟩

/-- **GM S4.5**: the triangle inequality for `d^U` through `w ∈ U ∪ ∂U`. -/
theorem gm_dU_triangle (hs : 0 < s) (hL : D.IsLength) (hbd : Bornology.IsBounded (ballM D z s))
    (hlc : FilledBallBdyLC D z s) (x y : ℂ) {w : ℂ}
    (hw : w ∈ (filledBall D z s)ᶜ ∪ frontier (filledBall D z s)) :
    dU (filledBall D z s)ᶜ x y ≤ dU (filledBall D z s)ᶜ x w + dU (filledBall D z s)ᶜ w y := by
  set U := (filledBall D z s)ᶜ with hU
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hfin => ?_
  set e : ℝ≥0∞ := ENNReal.ofReal ((ε : ℝ) / 3) with he
  have hepos : 0 < e := ENNReal.ofReal_pos.2 (by positivity)
  have h1 : dU U x w < dU U x w + e :=
    ENNReal.lt_add_right (ne_top_of_le_ne_top hfin.ne (le_self_add)) hepos.ne'
  have h2 : dU U w y < dU U w y + e :=
    ENNReal.lt_add_right (ne_top_of_le_ne_top hfin.ne (le_add_self)) hepos.ne'
  simp only [hU, dU, iInf_lt_iff] at h1 h2
  obtain ⟨X₁, hX₁U, hX₁c, hx₁, hw₁, hd₁⟩ := h1
  obtain ⟨X₂, hX₂U, hX₂c, hw₂, hy₂, hd₂⟩ := h2
  obtain ⟨X₃, hX₃U, hX₃c, h13, h32, hd₃⟩ :=
    dc_join hs hL hbd hlc hw hX₁U hX₂U hw₁ hw₂ (η := (ε : ℝ) / 3) (by positivity)
  have hc13 : IsPreconnected (X₁ ∪ X₃) := IsPreconnected.union' h13 hX₁c.2 hX₃c
  have h132 : ((X₁ ∪ X₃) ∩ X₂).Nonempty := by
    obtain ⟨p, hp3, hp2⟩ := h32
    exact ⟨p, Or.inr hp3, hp2⟩
  have hc : IsConnected (X₁ ∪ X₃ ∪ X₂) :=
    ⟨hX₁c.1.mono (subset_union_left.trans subset_union_left),
      IsPreconnected.union' h132 hc13 hX₂c.2⟩
  have hsub : X₁ ∪ X₃ ∪ X₂ ⊆ U := union_subset (union_subset hX₁U hX₃U) hX₂U
  have hdiam : Metric.ediam (X₁ ∪ X₃ ∪ X₂) ≤ Metric.ediam X₁ + Metric.ediam X₃ +
      Metric.ediam X₂ :=
    (Metric.ediam_union_le h132).trans (by gcongr; exact Metric.ediam_union_le h13)
  have h3e : e + e + e = (ε : ℝ≥0∞) := by
    rw [he, ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_coe_nnreal]
    congr 1
    ring
  calc dU U x y ≤ Metric.ediam (X₁ ∪ X₃ ∪ X₂) :=
        dc_dU_le hsub hc (closure_mono (subset_union_left.trans subset_union_left) hx₁)
          (closure_mono subset_union_right hy₂)
    _ ≤ Metric.ediam X₁ + Metric.ediam X₃ + Metric.ediam X₂ := hdiam
    _ ≤ (dU U x w + e) + e + (dU U w y + e) := by
        gcongr
        · exact hd₁.le
        · exact hd₂.le
    _ = dU U x w + dU U w y + (e + e + e) := by ring
    _ = dU U x w + dU U w y + ε := by rw [h3e]

end LQGMetric.GM
