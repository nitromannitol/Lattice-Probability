import LatticeProb.LQG.WeylChainLower
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Rerouting paths around a small disc

Let `E` be a Euclidean length metric on `ℂ`, let `U ⊆ ℂ` and `0 ≤ ρ < r`. A path in `U` between two points outside the
closed disc of radius `r` about `0` which enters the closed disc of radius `ρ` hits the circle `|x| = r` a first and a
last time. Replacing the part of the path between these two times by a path in a set `A ⊆ U \ B̄_ρ(0)` joining the two
hitting points gives

`E(z, w; U \ B̄_ρ(0)) ≤ E(z, w; U) + δ`

whenever any two points of the circle `|x| = r` are at `E(·, ·; A)`-distance at most `δ`.

This is the deterministic step in the proof that the internal metric of a length metric with a logarithmic singularity
at `0` is the limit of its internal metrics on the complements of small discs about `0`, once the internal diameters of
the dyadic-type shells about `0` tend to zero.

## Main statements

* `exists_first_last_norm_eq`: first and last hitting times of the circle `|x| = r` by a curve on `[0, 1]`.
* `IsEuclideanLengthMetric.internalMetric_diff_closedBall_le_add`: the rerouting bound above.
* `IsEuclideanLengthMetric.internalMetric_eq_iInf_diff_closedBall`: if arbitrarily small circles about `0` have
  arbitrarily small internal diameters in thin annuli, then `E(z, w; U) = inf_n E(z, w; U \ B̄_{ρ_n}(0))` for every
  open `U`, `z, w ≠ 0` and `ρ_n → 0`.
-/

namespace LatticeProb.LQG

open Set Metric Filter
open scoped ENNReal unitInterval Topology

/-- First and last hitting times of a circle. If a continuous `p : ℝ → ℂ` satisfies `r < |p 0|`, `r < |p 1|` and
`|p t₀| ≤ r` for some `t₀ ∈ [0, 1]`, there are `0 ≤ s ≤ t ≤ 1` with `|p s| = |p t| = r` and `r < |p u|` for
`u ∈ [0, s) ∪ (t, 1]`. -/
theorem exists_first_last_norm_eq {p : ℝ → ℂ} (hp : Continuous p) {r : ℝ} (h0 : r < ‖p 0‖) (h1 : r < ‖p 1‖)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hle : ‖p t₀‖ ≤ r) :
    ∃ s t, 0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧ ‖p s‖ = r ∧ ‖p t‖ = r ∧
      (∀ u ∈ Ico 0 s, r < ‖p u‖) ∧ ∀ u ∈ Ioc t 1, r < ‖p u‖ := by
  have hcont : Continuous fun u => ‖p u‖ := continuous_norm.comp hp
  set K : Set ℝ := Icc 0 1 ∩ {u | ‖p u‖ ≤ r} with hK
  have hKc : IsClosed K := isClosed_Icc.inter (isClosed_le hcont continuous_const)
  have hKne : K.Nonempty := ⟨t₀, ht₀, hle⟩
  have hKb : BddBelow K := ⟨0, fun u hu => hu.1.1⟩
  have hKa : BddAbove K := ⟨1, fun u hu => hu.1.2⟩
  have hsK : sInf K ∈ K := hKc.csInf_mem hKne hKb
  have htK : sSup K ∈ K := hKc.csSup_mem hKne hKa
  have hbef : ∀ u ∈ Ico 0 (sInf K), r < ‖p u‖ := by
    intro u hu
    by_contra hnot
    have huK : u ∈ K := ⟨⟨hu.1, hu.2.le.trans hsK.1.2⟩, not_lt.mp hnot⟩
    exact absurd (csInf_le hKb huK) (not_le.mpr hu.2)
  have haft : ∀ u ∈ Ioc (sSup K) 1, r < ‖p u‖ := by
    intro u hu
    by_contra hnot
    have huK : u ∈ K := ⟨⟨htK.1.1.trans hu.1.le, hu.2⟩, not_lt.mp hnot⟩
    exact absurd (le_csSup hKa huK) (not_le.mpr hu.1)
  refine ⟨sInf K, sSup K, hsK.1.1, csInf_le hKb htK, htK.1.2, ?_, ?_, hbef, haft⟩
  · obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc' hsK.1.1 hcont.continuousOn ⟨hsK.2, h0.le⟩
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [← h]; exact hu'
    · exact ((hbef u ⟨hu.1, h⟩).ne' hu').elim
  · obtain ⟨u, hu, hu'⟩ := intermediate_value_Icc htK.1.2 hcont.continuousOn ⟨htK.2, h1.le⟩
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [h]; exact hu'
    · exact ((haft u ⟨h, hu.2⟩).ne' hu').elim

/-- **Rerouting around a small disc.** Let `E` be a Euclidean length metric, `ρ < r`, and `A ⊆ U \ B̄_ρ(0)` a set in
which any two points of the circle `|x| = r` are at internal distance at most `δ`. Then for `|z|, |w| > r`,
`E(z, w; U \ B̄_ρ(0)) ≤ E(z, w; U) + δ`: a path in `U` from `z` to `w` entering `B̄_ρ(0)` is replaced, between its
first and last hitting times of the circle `|x| = r`, by a path in `A`. -/
theorem IsEuclideanLengthMetric.internalMetric_diff_closedBall_le_add {E : ℂ → ℂ → ℝ}
    (hE : IsEuclideanLengthMetric E) {U A : Set ℂ} {ρ r : ℝ} {δ : ℝ≥0∞} (hρr : ρ < r)
    (hA : A ⊆ U \ closedBall 0 ρ)
    (hδ : ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r, internalMetric E A a b ≤ δ)
    {z w : ℂ} (hz : r < ‖z‖) (hw : r < ‖w‖) :
    internalMetric E (U \ closedBall 0 ρ) z w ≤ internalMetric E U z w + δ := by
  conv_rhs => rw [internalMetric]
  simp only [ENNReal.iInf_add]
  refine le_iInf₂ fun P hP => ?_
  by_cases hfar : ∀ t, ρ < ‖P t‖
  · refine le_trans ?_ le_self_add
    unfold internalMetric
    exact iInf₂_le P fun t => ⟨hP t, fun h => (not_le.mpr (hfar t)) (mem_closedBall_zero_iff.mp h)⟩
  simp only [not_forall, not_lt] at hfar
  obtain ⟨t₀, ht₀⟩ := hfar
  obtain ⟨s, t, hs0, hst, ht1, hps, hpt, hbef, haft⟩ := exists_first_last_norm_eq P.continuous_extend
    (by rw [Path.extend_zero]; exact hz) (by rw [Path.extend_one]; exact hw) t₀.2
    (by rw [Path.extend_extends']; exact ht₀.trans hρr.le)
  have hmem : ∀ u ∈ Icc (0 : ℝ) 1, r ≤ ‖P.extend u‖ → P.extend u ∈ U \ closedBall 0 ρ := by
    intro u hu hr
    refine ⟨?_, fun h => ?_⟩
    · rw [Path.extend_apply P hu]; exact hP _
    · have := mem_closedBall_zero_iff.mp h
      linarith
  have h1 : internalMetric E (U \ closedBall 0 ρ) z (P.extend s) ≤ curveLength E P.extend 0 s := by
    have key := internalMetric_le_curveLength_of_image_subset hE P hs0
      (W := U \ closedBall 0 ρ) (by
        rintro _ ⟨u, hu, rfl⟩
        refine hmem u ⟨hu.1, hu.2.trans (hst.trans ht1)⟩ ?_
        rcases eq_or_lt_of_le hu.2 with h | h
        · rw [h, hps]
        · exact (hbef u ⟨hu.1, h⟩).le)
    rwa [Path.extend_zero] at key
  have h3 : internalMetric E (U \ closedBall 0 ρ) (P.extend t) w ≤ curveLength E P.extend t 1 := by
    have key := internalMetric_le_curveLength_of_image_subset hE P ht1
      (W := U \ closedBall 0 ρ) (by
        rintro _ ⟨u, hu, rfl⟩
        refine hmem u ⟨(hs0.trans hst).trans hu.1, hu.2⟩ ?_
        rcases eq_or_lt_of_le hu.1 with h | h
        · rw [← h, hpt]
        · exact (haft u ⟨h, hu.2⟩).le)
    rwa [Path.extend_one] at key
  have h2 : internalMetric E (U \ closedBall 0 ρ) (P.extend s) (P.extend t) ≤ δ :=
    (internalMetric_anti E hA _ _).trans
      (hδ _ (mem_sphere_zero_iff_norm.mpr hps) _ (mem_sphere_zero_iff_norm.mpr hpt))
  have hlen : curveLength E P.extend 0 s + curveLength E P.extend s t + curveLength E P.extend t 1 =
      pathLength E P := by
    rw [hE.curveLength_add P.extend hs0 hst, hE.curveLength_add P.extend (hs0.trans hst) ht1]
    rfl
  calc internalMetric E (U \ closedBall 0 ρ) z w
      ≤ internalMetric E (U \ closedBall 0 ρ) z (P.extend s) +
          internalMetric E (U \ closedBall 0 ρ) (P.extend s) (P.extend t) +
          internalMetric E (U \ closedBall 0 ρ) (P.extend t) w :=
        (hE.internalMetric_triangle _ z (P.extend t) w).trans
          (add_le_add (hE.internalMetric_triangle _ z (P.extend s) (P.extend t)) le_rfl)
    _ ≤ curveLength E P.extend 0 s + δ + curveLength E P.extend t 1 := add_le_add (add_le_add h1 h2) h3
    _ ≤ curveLength E P.extend 0 s + curveLength E P.extend s t + curveLength E P.extend t 1 + δ := by
        rw [add_right_comm _ δ]
        exact add_le_add (add_le_add le_self_add le_rfl) le_rfl
    _ = pathLength E P + δ := by rw [hlen]

/-- **The internal metric as a limit over punctured domains.** Let `E` be a Euclidean length metric such that for
every `ε > 0` and `R > 0` there are radii `0 < ρ' < r < R` and a set `A ⊆ B_R(0) \ B̄_{ρ'}(0)` in which any two points
of the circle `|x| = r` are at internal distance at most `ε`. Then for every open `U`, every sequence `ρ_n → 0` and
all `z, w ≠ 0`, `E(z, w; U) = inf_n E(z, w; U \ B̄_{ρ_n}(0))`. A path avoiding `0` avoids a disc about `0` by
compactness; a path through `0` is rerouted around a small circle. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_iInf_diff_closedBall {E : ℂ → ℂ → ℝ}
    (hE : IsEuclideanLengthMetric E) {U : Set ℂ} (hU : IsOpen U) {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop (𝓝 0))
    (hshell : ∀ ε : ℝ≥0∞, 0 < ε → ∀ R : ℝ, 0 < R → ∃ r ρ' : ℝ, 0 < ρ' ∧ ρ' < r ∧ r < R ∧
      ∃ A ⊆ ball (0 : ℂ) R \ closedBall 0 ρ',
        ∀ a ∈ sphere (0 : ℂ) r, ∀ b ∈ sphere (0 : ℂ) r, internalMetric E A a b ≤ ε)
    {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    internalMetric E U z w = ⨅ n, internalMetric E (U \ closedBall 0 (ρ n)) z w := by
  refine le_antisymm (le_iInf fun n => internalMetric_anti E sdiff_subset z w) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  conv_rhs => rw [internalMetric]
  simp only [ENNReal.iInf_add]
  refine le_iInf₂ fun P hP => ?_
  by_cases h0 : ∀ t, P t ≠ 0
  · obtain ⟨t₁, -, ht₁⟩ := isCompact_univ.exists_isMinOn univ_nonempty
      (continuous_norm.comp P.continuous).continuousOn
    have hη : 0 < ‖P t₁‖ := norm_pos_iff.mpr (h0 t₁)
    obtain ⟨n, hn⟩ := (hρ.eventually (gt_mem_nhds hη)).exists
    refine (iInf_le _ n).trans (le_trans ?_ le_self_add)
    unfold internalMetric
    refine iInf₂_le P fun t => ⟨hP t, fun h => ?_⟩
    have h1 := mem_closedBall_zero_iff.mp h
    have h2 : ‖P t₁‖ ≤ ‖P t‖ := isMinOn_iff.mp ht₁ t (mem_univ _)
    linarith
  · simp only [not_forall, not_not] at h0
    obtain ⟨t₀, ht₀⟩ := h0
    have h0U : (0 : ℂ) ∈ U := by rw [← ht₀]; exact hP t₀
    obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.mp hU 0 h0U
    have hR'pos : 0 < min R (min ‖z‖ ‖w‖) :=
      lt_min hR (lt_min (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw))
    obtain ⟨r, ρ', hρ'0, hρ'r, hrR, A, hAsub, hAε⟩ := hshell ε (ENNReal.coe_pos.mpr hε) _ hR'pos
    obtain ⟨n, hn⟩ := (hρ.eventually (gt_mem_nhds hρ'0)).exists
    have hA : A ⊆ U \ closedBall 0 (ρ n) := fun x hx => by
      obtain ⟨hx1, hx2⟩ := hAsub hx
      exact ⟨hRU (ball_subset_ball (min_le_left _ _) hx1),
        fun h => hx2 (closedBall_subset_closedBall hn.le h)⟩
    have key := hE.internalMetric_diff_closedBall_le_add (hn.trans hρ'r) hA hAε
      (lt_of_lt_of_le hrR ((min_le_right _ _).trans (min_le_left _ _)))
      (lt_of_lt_of_le hrR ((min_le_right _ _).trans (min_le_right _ _)))
    refine (iInf_le _ n).trans (key.trans (add_le_add ?_ le_rfl))
    unfold internalMetric
    exact iInf₂_le P hP

end LatticeProb.LQG
