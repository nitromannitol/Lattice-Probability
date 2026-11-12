/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.SetupStab at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.SetupArc
import LatticeProb.Bonanno.LQGMetric.Metric.Geodesic

/-!
# GM §4.1: the candidate pairs `𝒵_k`, the events `Stab_{k,r}(z)`, GM.S4.2 and the pathwise part
# of GM Lemma 4.6

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, §4.1, l. 1680–1716.

* `candSet` — GM (4.10) (l. 1682–1686): `z ∈ (λ₁ε^{1+ν}𝕣/4)ℤ² ∖ 𝓑^•_{t_k}`, `r ∈ {r_j^ε}`,
  `dist(z, ∂𝓑^•_{t_k}) ∈ [λ₄ε𝕣, 2λ₄ε𝕣]`.
* `IsAvoidGeod` — GM's `D_h(·,·;ℂ∖cl B_r(z))`-geodesic (l. 1695–1696): "a path from `𝕫` to `x`
  in `ℂ ∖ B_r(z)` which has minimal `D_h`-length among all such paths and which does not hit
  `∂B_r(z)` except at `x`".
* `stabCond` — GM (4.11) (l. 1692): "each `D_h(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to a point of
  `∂B_r(z)` hits `∂𝓑^•_{t_k}` in the same arc of `𝓘_k`". Reading: there is one `x₀ ∈ Conf_k` such
  that every such geodesic meets `∂𝓑^•_{t_k}` only inside `arcOf x₀` (the event `Stab_{k,r}(z)` is
  `{(z,r) ∈ 𝒵_k} ∩ stabCond`).
* `gm_S4_2` — GM.S4.2 (l. 1697–1698): a `D`-geodesic from `𝕫 ∉ cl B_r(z)` which enters `B_r(z)`,
  stopped when it first hits `cl B_r(z)`, is a `D(·,·;ℂ∖cl B_r(z))`-geodesic to a point of
  `∂B_r(z)`. (GM say "stopped at the first time when it enters `B_r(z)`"; the first hitting time of
  the closed ball is the one for which "does not hit `∂B_r(z)` except at `x`" holds.)
* `gm_L4_6_arc` — the pathwise step of GM Lemma 4.6's proof (l. 1709–1712): on
  `stabCond ∩ {P ∩ B_r(z) ≠ ∅}`, with `cl B_r(z)` disjoint from `𝓑^•_{t_k}`, the arc of `𝓘_k`
  containing `P(t_k)` is the arc `arcOf x₀` of `stabCond`, and `x₀ = P(s_k)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- GM (4.10): the candidate pairs `(z, r)` for the filled ball `K = 𝓑^•_{t_k}` and the radii
`Rads = {r_1^ε, …}` -/
def candSet (K : Set ℂ) (lam1 lam4 ε ν 𝕣 : ℝ) (Rads : Set ℝ) : Set (ℂ × ℝ) :=
  {p | p.1 ∈ gridPts (lam1 * ε ^ (1 + ν) * 𝕣 / 4) ∧ p.1 ∉ K ∧ p.2 ∈ Rads ∧
    infDist p.1 (frontier K) ∈ Icc (lam4 * ε * 𝕣) (2 * lam4 * ε * 𝕣)}

/-- `Q : [0,T] → ℂ` is a `D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `x ∈ ∂B_r(z)` in GM's sense
(l. 1695–1696) -/
def IsAvoidGeod (D : ContMetric) (𝕫 z : ℂ) (r : ℝ) (x : ℂ) (Q : ℝ → ℂ) (T : ℝ) : Prop :=
  0 ≤ T ∧ ContinuousOn Q (Icc 0 T) ∧ Q 0 = 𝕫 ∧ Q T = x ∧ x ∈ sphere z r ∧
    (∀ u ∈ Ico 0 T, Q u ∉ closedBall z r) ∧
    ∀ (Q' : ℝ → ℂ) (a b : ℝ), a ≤ b → ContinuousOn Q' (Icc a b) → Q' a = 𝕫 → Q' b = x →
      MapsTo Q' (Icc a b) (ball z r)ᶜ → D.len Q 0 T ≤ D.len Q' a b

/-- GM (4.11): every `D(·,·;ℂ∖cl B_r(z))`-geodesic from `𝕫` to `∂B_r(z)` hits `∂𝓑^•_t` inside one
arc `arcOf x₀`, `x₀ ∈ Conf(s,t)` -/
def stabCond (D : ContMetric) (𝕫 : ℂ) (s t : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  ∃ x₀ ∈ confPts D 𝕫 s t, ∀ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod D 𝕫 z r x Q T →
    Q '' Icc 0 T ∩ frontier (filledBall D 𝕫 t) ⊆ arcOf D 𝕫 t x₀

section Det
variable {D : ContMetric} {𝕫 w z : ℂ} {r : ℝ} {P : ℝ → ℂ} {L : ℝ}

/-- the `D`-length of a unit-speed geodesic on `[0, T]` is `T` -/
theorem gm_len_geodL (hP : IsGeodesicL D P L 𝕫 w) {T : ℝ} (hT : T ∈ Icc 0 L) :
    D.len P 0 T = ENNReal.ofReal T := by
  have h := MetricGeometry.isGeodesicCurve_of_edist_eq (X := D.Space) (P := D.pt ∘ P) hP.1
    (fun s hs t ht => by
      simp only [Function.comp_apply, edist_dist]
      show ENNReal.ofReal (D.1 (P s, P t)) = ENNReal.ofReal (dist s t)
      rw [hP.2.2.2 s hs t ht, Real.dist_eq, abs_sub_comm])
  have := MetricGeometry.curveLength_of_hasUnitSpeedOn h.2 ⟨le_rfl, hP.1⟩ hT
  rw [sub_zero] at this
  exact this

/-- **GM.S4.2** (l. 1697–1698) -/
theorem gm_S4_2 (hP : IsGeodesicL D P L 𝕫 w) (h𝕫 : 𝕫 ∉ closedBall z r)
    (hent : ∃ u ∈ Icc 0 L, P u ∈ ball z r) :
    ∃ T ∈ Icc 0 L, IsAvoidGeod D 𝕫 z r (P T) P T := by
  have hc := gm_geodL_continuousOn hP
  set S : Set ℝ := Icc 0 L ∩ P ⁻¹' closedBall z r
  have hSc : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  obtain ⟨u₀, hu₀, hu₀b⟩ := hent
  have hSne : S.Nonempty := ⟨u₀, hu₀, ball_subset_closedBall hu₀b⟩
  have hSb : BddBelow S := ⟨0, fun u hu => hu.1.1⟩
  set T := sInf S
  have hTS : T ∈ S := hSc.csInf_mem hSne hSb
  have hT0 : 0 < T := by
    rcases eq_or_lt_of_le hTS.1.1 with h0 | h0
    · exfalso
      have : P 0 ∈ closedBall z r := by rw [h0]; exact hTS.2
      rw [hP.2.1] at this
      exact h𝕫 this
    · exact h0
  have hbefore : ∀ u ∈ Ico 0 T, P u ∉ closedBall z r := by
    intro u hu hub
    have : T ≤ u := csInf_le hSb ⟨⟨hu.1, hu.2.le.trans hTS.1.2⟩, hub⟩
    exact absurd hu.2 (not_lt.mpr this)
  have hsph : P T ∈ sphere z r := by
    have hle : dist (P T) z ≤ r := hTS.2
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq
    · exfalso
      obtain ⟨δ, hδ, hδε⟩ := Metric.continuousWithinAt_iff.mp (hc T hTS.1)
        (r - dist (P T) z) (by linarith)
      set u := max (T - δ / 2) (T / 2)
      have hu1 : u < T := max_lt (by linarith) (by linarith)
      have hu0 : 0 ≤ u := le_max_of_le_right (by linarith)
      have hdu : dist u T < δ := by
        rw [Real.dist_eq, abs_of_neg (by linarith)]
        have : T - δ / 2 ≤ u := le_max_left _ _
        linarith
      have := hδε ⟨hu0, hu1.le.trans hTS.1.2⟩ hdu
      apply hbefore u ⟨hu0, hu1⟩
      show dist (P u) z ≤ r
      linarith [dist_triangle (P u) (P T) z]
  refine ⟨T, hTS.1, hT0.le, hc.mono (Icc_subset_Icc le_rfl hTS.1.2), hP.2.1, rfl, hsph,
    hbefore, ?_⟩
  intro Q' a b hab _ hQa hQb _
  rw [gm_len_geodL hP hTS.1]
  have h1 := MetricGeometry.edist_le_curveLength (D.pt ∘ Q') hab
  simp only [Function.comp_apply, edist_dist] at h1
  have h2 : D.1 (𝕫, P T) = T := gm_geodL_dist hP hTS.1
  refine le_trans (le_of_eq ?_) h1
  show ENNReal.ofReal T = ENNReal.ofReal (D.1 (Q' a, Q' b))
  rw [hQa, hQb, h2]

/-- **GM Lemma 4.6, pathwise step** (l. 1709–1712): if `P` (the unique geodesic from `𝕫` to
`𝕨 ∉ 𝓑^•_t`) enters `B_r(z)`, `cl B_r(z)` is disjoint from `𝓑^•_t` and `stabCond` holds with
witness `x₀`, then `P(t) ∈ arcOf x₀` and `x₀ = P(s)`. -/
theorem gm_L4_6_arc (hU : UniqueGeod D 𝕫 w) (hP : IsGeodesicL D P L 𝕫 w) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (hw : w ∉ filledBall D 𝕫 t)
    (hleft : ∀ y ∈ frontier (filledBall D 𝕫 t), ∃ Q, IsLeftmostGeod D 𝕫 t y Q)
    (hdisj : (confPts D 𝕫 s t).PairwiseDisjoint (arcOf D 𝕫 t))
    (hball : Disjoint (closedBall z r) (filledBall D 𝕫 t))
    (hent : ∃ u ∈ Icc 0 L, P u ∈ ball z r) {x₀ : ℂ} (hx₀ : x₀ ∈ confPts D 𝕫 s t)
    (hstab : ∀ (x : ℂ) (Q : ℝ → ℂ) (T : ℝ), IsAvoidGeod D 𝕫 z r x Q T →
      Q '' Icc 0 T ∩ frontier (filledBall D 𝕫 t) ⊆ arcOf D 𝕫 t x₀) :
    P t ∈ arcOf D 𝕫 t x₀ ∧ x₀ = P s := by
  have ht : 0 < t := hs.trans hst
  have hz : 𝕫 ∈ filledBall D 𝕫 t := by
    refine Or.inl (subset_closure ?_)
    show D.1 (𝕫, 𝕫) < t
    rw [D.2.self_eq_zero]
    exact ht
  have h𝕫 : 𝕫 ∉ closedBall z r := fun h' => hball.ne_of_mem h' hz rfl
  obtain ⟨T, hT, hav⟩ := gm_S4_2 hP h𝕫 hent
  have htT : t < T := by
    by_contra hle
    replace hle := not_lt.mp hle
    have hPT : P T ∈ filledBall D 𝕫 t := by
      rcases eq_or_lt_of_le hT.1 with h0 | h0
      · rw [← h0, hP.2.1]; exact hz
      · exact Or.inl (gm_closure_ballM_mono D 𝕫 hle (gm_geod_mem_closure_ballM hP h0 hT.2))
    exact hball.ne_of_mem (sphere_subset_closedBall hav.2.2.2.2.1) hPT rfl
  have htL := gm_lt_length_of_not_mem hP ht hw
  have hfr : P t ∈ frontier (filledBall D 𝕫 t) := gm_geod_mem_frontier hP ht htL hw
  have harc : P t ∈ arcOf D 𝕫 t x₀ :=
    hstab (P T) P T hav ⟨⟨t, ⟨ht.le, htT.le⟩, rfl⟩, hfr⟩
  exact ⟨harc, (gm_L4_5_arc hU hP hs hst hw hleft hdisj).2.2 x₀ hx₀ harc⟩

end Det

end LQGMetric.GM
