/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedShortcut at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.LQGMetric.Metric.CurveLength

/-!
# GM §3.3: the shortcut inequality (3.16) and the telescoping bound (3.17)
(task P2-M2F, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Proposition 3.6, Steps 2–3 (l. 1440–1488).

* `exists_hit_of_disconnects`: a path `P|_{[c,d]}` from `E` to `F` hits every set disconnecting
  `E` from `F`.
* `gm_S3_8` (**GM.S3.8**, l. 1467–1477): if a `D`-geodesic `P` starts and ends outside `B_r(w)`,
  is in `cl B_{αr}(w)` at time `a`, and runs from `∂B_{αr}(w)` at time `s ≥ a` to `∂B_r(w)` at
  time `t`, and `G` is a path disconnecting the boundaries of `𝔸_{αr,r}(w)` with `D`-length
  `≤ A D(∂B_{αr}(w), ∂B_r(w))`, then `s − a ≤ A (t − s)`. (GM: "The geodesic `P` must hit this
  path at least once before time `t_{j−1}` and at least once after time `s_j`.")
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- a path `P|_{[c,d]}` from `E` to `F` meets every set `X` disconnecting `E` from `F` -/
theorem exists_hit_of_disconnects {P : ℝ → ℂ} {c d : ℝ} (hcd : c ≤ d)
    (hP : ContinuousOn P (Icc c d)) {X E F : Set ℂ} (hX : Disconnects X E F) (hc : P c ∈ E)
    (hd : P d ∈ F) : ∃ τ ∈ Icc c d, P τ ∈ X := by
  have hmap : ∀ u : unitInterval, c + (u : ℝ) * (d - c) ∈ Icc c d := fun u =>
    ⟨by nlinarith [u.2.1], by nlinarith [u.2.2]⟩
  have hcont : Continuous fun u : unitInterval => P (c + (u : ℝ) * (d - c)) :=
    hP.comp_continuous (by fun_prop) hmap
  let γ : Path (P c) (P d) :=
    { toFun := fun u => P (c + (u : ℝ) * (d - c))
      continuous_toFun := hcont
      source' := by simp
      target' := by simp }
  obtain ⟨x, ⟨u, rfl⟩, hx⟩ := hX _ _ γ hc hd
  exact ⟨_, hmap u, hx⟩

/-- `D(x, y) ≤ len(G; D)` for `x, y` on `G([a', b'])` -/
lemma ofReal_dist_le_len (D : ContMetric) {G : ℝ → ℂ} {a' b' u v : ℝ} (hu : u ∈ Icc a' b')
    (hv : v ∈ Icc a' b') : ENNReal.ofReal (D.1 (G u, G v)) ≤ D.len G a' b' := by
  have := eVariationOn.edist_le (D.pt ∘ G) hu hv
  rw [edist_dist] at this
  exact this

/-- **GM.S3.8** (shortcut inequality, l. 1467–1477) -/
theorem gm_S3_8 (D : ContMetric) {P : ℝ → ℂ} {L : ℝ} (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {w : ℂ} {α r A : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    {a' b' : ℝ} {G : ℝ → ℂ}
    (hGd : Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r))
    (hGl : D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    {a s t : ℝ} (ha0 : 0 ≤ a) (has : a ≤ s) (hst : s ≤ t) (htL : t ≤ L)
    (h0 : P 0 ∉ ball w r) (hPa : P a ∈ closedBall w (α * r)) (hPs : P s ∈ sphere w (α * r))
    (hPt : P t ∈ sphere w r) (hLr : P L ∉ ball w r) : s - a ≤ A * (t - s) := by
  have hr : 0 ≤ r := by
    have := mem_sphere.1 hPt; rw [← this]; exact dist_nonneg
  have hαr : α * r ≤ r := by nlinarith
  have hX := Disconnects.closedBall_compl_ball hαr hGd
  obtain ⟨τ₁, hτ₁, ⟨u₁, hu₁, e₁⟩⟩ := exists_hit_of_disconnects (c := 0) (d := a) ha0
    (hP.mono (Icc_subset_Icc le_rfl (by linarith))) hX.symm h0 hPa
  obtain ⟨τ₂, hτ₂, ⟨u₂, hu₂, e₂⟩⟩ := exists_hit_of_disconnects (c := s) (d := L)
    (hst.trans htL) (hP.mono (Icc_subset_Icc (by linarith) le_rfl)) hX
    (sphere_subset_closedBall hPs) hLr
  have hd := ofReal_dist_le_len D (G := G) hu₁ hu₂
  rw [e₁, e₂, hgeo τ₁ ⟨hτ₁.1, by linarith [hτ₁.2]⟩ τ₂ ⟨by linarith [hτ₂.1], hτ₂.2⟩,
    abs_of_nonneg (by linarith [hτ₁.2, hτ₂.1])] at hd
  have hsd : setDist D (sphere w (α * r)) (sphere w r) ≤ ENNReal.ofReal (t - s) := by
    have := MetricGeometry.setEDist_le_edist (X := D.Space) (mem_image_of_mem D.pt hPs)
      (mem_image_of_mem D.pt hPt)
    rw [edist_dist] at this
    have e : dist (D.pt (P s)) (D.pt (P t)) = t - s := by
      show D.1 (P s, P t) = t - s
      rw [hgeo s ⟨by linarith, by linarith⟩ t ⟨by linarith, htL⟩, abs_of_nonneg (by linarith)]
    rw [e] at this
    exact this
  have h3 : ENNReal.ofReal (τ₂ - τ₁) ≤ ENNReal.ofReal (A * (t - s)) := by
    rw [ENNReal.ofReal_mul hA]
    exact hd.trans (hGl.trans (by gcongr))
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by nlinarith)).1 h3
  linarith [hτ₁.2, hτ₂.1]

end LQGMetric.GM
