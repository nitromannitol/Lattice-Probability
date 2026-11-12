/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32X at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8

/-!
# Decision D97: the walled measure and the first-exit comparison for `lgdDZZ` (P2-DEC97)

The frozen `lgdDZZ` (Statement/Dimension.lean, DZZ arXiv:1807.00422 `LBM_LGDarXiv.tex`
l. 121–124) lets the path and the balls leave `𝕍`. DZZ's proofs (P3.2, l. 1159–1206) use
balls inside `𝕍`. DZZ themselves introduce the confined distance `D^A_{γ,δ}` (l. 2268: balls
"*contained in `A`*"). Here:

* `dzzWall K μ = μ + ∞ · Leb|_{Kᶜ}`. For closed `K`, an open ball has finite `dzzWall K μ`-mass
  only if it lies in `K`, where its mass is its `μ`-mass (`dzzWall_ball_of_subset`,
  `dzzWall_ball_of_not_subset`). So `lgdDZZ (dzzWall K μ)` is DZZ's `D^K` with the mass `μ`, and
  the existing `lgdDZZ`-nodes (all generic in `μ`) apply to it unchanged.
* **`lgdMinSet_dzzWall_le_of_exit`**: the first-exit argument of DZZ l. 2340–2350
  (eq-geodesic-range): if every ball meeting `closure U` and leaving `K` is heavy, then the frozen
  `D(u, v)` for `v ∉ U` is at least `min_{x ∈ ∂U} D^K(u, x)`.
* **`lgd_sandwich_dzzWall`**: the two-sided comparison between the frozen `lgdDZZ μ` and
  `lgdDZZ (dzzWall dzzV ν)` (`ν`, e.g., the Wick-normalised chaos), with the mass comparisons
  as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

/-- `μ + ∞ · Leb|_{Kᶜ}`: balls leaving the closed set `K` get infinite mass. -/
def dzzWall (K : Set ℂ) (μ : Measure ℂ) : Measure ℂ :=
  μ + (⊤ : ℝ≥0∞) • volume.restrict Kᶜ

lemma le_dzzWall (K : Set ℂ) (μ : Measure ℂ) : μ ≤ dzzWall K μ :=
  Measure.le_add_right le_rfl

lemma dzzWall_ball_of_subset {K : Set ℂ} (μ : Measure ℂ) {x : ℂ} {r : ℝ}
    (h : Metric.ball x r ⊆ K) : dzzWall K μ (Metric.ball x r) = μ (Metric.ball x r) := by
  have h0 : Metric.ball x r ∩ Kᶜ = ∅ := by
    ext z; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
      not_not]; exact fun hz => h hz
  simp [dzzWall, Measure.restrict_apply Metric.isOpen_ball.measurableSet, h0]

lemma dzzWall_ball_of_not_subset {K : Set ℂ} (hK : IsClosed K) (μ : Measure ℂ) {x : ℂ}
    {r : ℝ} (h : ¬ Metric.ball x r ⊆ K) : dzzWall K μ (Metric.ball x r) = ⊤ := by
  have hne : (Metric.ball x r ∩ Kᶜ).Nonempty := by
    obtain ⟨z, hz, hzK⟩ := not_subset.mp h
    exact ⟨z, hz, hzK⟩
  have hpos : 0 < volume (Metric.ball x r ∩ Kᶜ) :=
    (Metric.isOpen_ball.inter hK.isOpen_compl).measure_pos volume hne
  simp [dzzWall, Measure.restrict_apply Metric.isOpen_ball.measurableSet,
    ENNReal.top_mul hpos.ne']

/-- More wall, more balls. -/
lemma dzzWall_anti {K K' : Set ℂ} (h : K ⊆ K') (μ : Measure ℂ) :
    dzzWall K' μ ≤ dzzWall K μ := by
  refine Measure.le_iff'.2 fun s => ?_
  simp only [dzzWall, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  gcongr

/-- A mass comparison on the balls inside `K` passes to the walled measures. -/
lemma dzzWall_ball_le {K : Set ℂ} (hK : IsClosed K) {μ ν : Measure ℂ} {C : ℝ≥0∞} (hC : C ≠ 0)
    (h : ∀ (x : ℚ × ℚ) (r : ℝ), Metric.ball (ratPt x) r ⊆ K →
      μ (Metric.ball (ratPt x) r) ≤ C * ν (Metric.ball (ratPt x) r))
    (x : ℚ × ℚ) (r : ℝ) :
    dzzWall K μ (Metric.ball (ratPt x) r) ≤ C * dzzWall K ν (Metric.ball (ratPt x) r) := by
  by_cases hs : Metric.ball (ratPt x) r ⊆ K
  · rw [dzzWall_ball_of_subset _ hs, dzzWall_ball_of_subset _ hs]; exact h x r hs
  · rw [dzzWall_ball_of_not_subset hK μ hs, dzzWall_ball_of_not_subset hK ν hs, ENNReal.mul_top hC]

/-- **First exit** (DZZ l. 2340–2350, (eq-geodesic-range)): if `u ∈ U` (open), `v ∉ U`, and
every rational ball of `μ`-mass `≤ δ²` that meets `closure U` lies in `K`, then
`min_{x ∈ ∂U} D^K_δ(u, x) ≤ D_δ(u, v)`. -/
theorem lgdMinSet_dzzWall_le_of_exit (μ : Measure ℂ) (δ : ℝ) {U K : Set ℂ} (hU : IsOpen U)
    {u v : ℂ} (hu : u ∈ U) (hv : v ∉ U)
    (hheavy : ∀ (c : ℚ × ℚ) (ρ : ℝ), (Metric.ball (ratPt c) ρ ∩ closure U).Nonempty →
      μ (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) → Metric.ball (ratPt c) ρ ⊆ K) :
    lgdMinSet (dzzWall K μ) δ {u} (frontier U) ≤ lgdDZZ μ δ u v := by
  unfold lgdDZZ
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  -- the first exit time `s₀` of `P.extend` from `U`
  set T : Set ℝ := Icc 0 1 ∩ (P.extend ⁻¹' Uᶜ) with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hU.isClosed_compl.preimage P.continuous_extend)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hv⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have hs₀0 : 0 ≤ s₀ := hs₀T.1.1
  have hs₀1 : s₀ ≤ 1 := csInf_le hTb h1T
  have hbefore : ∀ s, 0 ≤ s → s < s₀ → P.extend s ∈ U := by
    intro s hs hss
    by_contra hsU
    exact absurd (csInf_le hTb ⟨⟨hs, hss.le.trans hs₀1⟩, hsU⟩) (not_le.mpr hss)
  have hpos : 0 < s₀ := by
    refine lt_of_le_of_ne hs₀0 fun h => ?_
    have := hs₀T.2
    rw [← h] at this
    simp only [mem_preimage, mem_compl_iff, Path.extend_zero] at this
    exact this hu
  have hcl : P.extend s₀ ∈ closure U := by
    have ht : Tendsto P.extend (𝓝[<] s₀) (𝓝 (P.extend s₀)) :=
      (P.continuous_extend.tendsto s₀).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hpos] with s hs
    exact hbefore s hs.1.le hs.2
  have hfr : P.extend s₀ ∈ frontier U := by
    rw [hU.frontier_eq]; exact ⟨hcl, hs₀T.2⟩
  -- the truncated path from `u` to `x = P.extend s₀`, inside `closure U`
  set Q : Path u (P.extend s₀) := (P.truncateOfLE hs₀0).cast (by simp) rfl with hQ
  have hQval : ∀ s, ∃ r ∈ Icc (0 : ℝ) s₀, Q s = P.extend r := by
    intro s
    refine ⟨min (max (s : ℝ) 0) s₀, ⟨le_min (le_max_right _ _) hs₀0, min_le_right _ _⟩, ?_⟩
    rfl
  have hQcl : ∀ s, Q s ∈ closure U := by
    intro s
    obtain ⟨r, hr, hQr⟩ := hQval s
    rw [hQr]
    rcases hr.2.lt_or_eq with h | h
    · exact subset_closure (hbefore r hr.1 h)
    · rw [h]; exact hcl
  have hQcov : ∀ s, ∃ i, Q s ∈ Metric.ball (ratPt (c i)) (ρ i) := by
    intro s
    obtain ⟨r, hr, hQr⟩ := hQval s
    obtain ⟨i, hi⟩ := h2 ⟨r, hr.1, hr.2.trans hs₀1⟩
    refine ⟨i, ?_⟩
    rw [hQr, Path.extend_apply P ⟨hr.1, hr.2.trans hs₀1⟩]
    exact hi
  -- keep the balls that meet `Q`; replace the others by the ball containing `u`
  classical
  obtain ⟨i₀, hi₀⟩ := hQcov 0
  set I : Set (Fin N) := {i | ∃ s, Q s ∈ Metric.ball (ratPt (c i)) (ρ i)} with hI
  set j : Fin N → Fin N := fun i => if i ∈ I then i else i₀ with hj
  have hjI : ∀ i, j i ∈ I := by
    intro i
    by_cases h : i ∈ I
    · have e : j i = i := by simp [hj, h]
      rw [e]; exact h
    · have e : j i = i₀ := by simp [hj, h]
      rw [e]; exact ⟨0, hi₀⟩
  have hsub : ∀ i, Metric.ball (ratPt (c (j i))) (ρ (j i)) ⊆ K := by
    intro i
    obtain ⟨s, hs⟩ := hjI i
    exact hheavy _ _ ⟨Q s, hs, hQcl s⟩ (h1 (j i)).2
  have hD : lgdDZZ (dzzWall K μ) δ u (P.extend s₀) ≤ N := by
    refine iInf₂_le N ⟨fun i => c (j i), fun i => ρ (j i), Q, fun i => ⟨(h1 (j i)).1, ?_⟩, ?_⟩
    · rw [dzzWall_ball_of_subset _ (hsub i)]; exact (h1 (j i)).2
    · intro s
      obtain ⟨i, hi⟩ := hQcov s
      have hiI : i ∈ I := ⟨s, hi⟩
      refine ⟨i, ?_⟩
      have e : j i = i := by simp [hj, hiI]
      show Q s ∈ Metric.ball (ratPt (c (j i))) (ρ (j i))
      rw [e]; exact hi
  have hm : lgdMinSet (dzzWall K μ) δ {u} (frontier U) ≤
      lgdDZZ (dzzWall K μ) δ u (P.extend s₀) := by
    unfold lgdMinSet
    exact (iInf₂_le u (mem_singleton u)).trans (iInf₂_le (P.extend s₀) hfr)
  exact hm.trans hD

/-- **Sandwich** of the frozen `D_δ(μ)` between walled distances of `ν`: if
`μ(B) ≤ e^a ν(B)` for the balls inside `𝕍` and `ν(B) ≤ e^b μ(B)` for the balls inside `K ⊆ 𝕍`,
and the balls of mass `≤ δ²` meeting `closure U` lie in `K`, then for `u ∈ U`, `v ∉ U`
`min_{x ∈ ∂U} D^𝕍_{δe^{b/2}}(ν)(u, x) ≤ D_δ(μ)(u, v) ≤ D^𝕍_{δe^{−a/2}}(ν)(u, v)`. -/
theorem lgd_sandwich_dzzWall {μ ν : Measure ℂ} {a b δ : ℝ} {U K : Set ℂ} (hU : IsOpen U)
    (hK : IsClosed K) (hKV : K ⊆ dzzV)
    (hup : ∀ (x : ℚ × ℚ) (r : ℝ), Metric.ball (ratPt x) r ⊆ dzzV →
      μ (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp a) * ν (Metric.ball (ratPt x) r))
    (hlow : ∀ (x : ℚ × ℚ) (r : ℝ), Metric.ball (ratPt x) r ⊆ K →
      ν (Metric.ball (ratPt x) r) ≤ ENNReal.ofReal (Real.exp b) * μ (Metric.ball (ratPt x) r))
    {u v : ℂ} (hu : u ∈ U) (hv : v ∉ U)
    (hheavy : ∀ (c : ℚ × ℚ) (ρ : ℝ), (Metric.ball (ratPt c) ρ ∩ closure U).Nonempty →
      μ (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) → Metric.ball (ratPt c) ρ ⊆ K) :
    lgdMinSet (dzzWall dzzV ν) (δ * Real.exp (b / 2)) {u} (frontier U) ≤ lgdDZZ μ δ u v ∧
      lgdDZZ μ δ u v ≤ lgdDZZ (dzzWall dzzV ν) (δ * Real.exp (-a / 2)) u v := by
  have hexp : ∀ c : ℝ, ENNReal.ofReal (Real.exp c) ≠ 0 := fun c =>
    (ENNReal.ofReal_pos.mpr (Real.exp_pos c)).ne'
  constructor
  · refine le_trans ?_ (lgdMinSet_dzzWall_le_of_exit μ δ hU hu hv hheavy)
    refine iInf₂_mono fun x _ => iInf₂_mono fun y _ => ?_
    have h1 := lgdDZZ_mono_measure (dzzWall_anti hKV ν) (δ * Real.exp (b / 2)) x y
    have h2 := lgdDZZ_le_of_ball_le (dzzWall_ball_le hK (hexp b) hlow) (δ * Real.exp (b / 2)) x y
    rw [neg_div, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h2
    exact h1.trans h2
  · exact (lgdDZZ_mono_measure (le_dzzWall dzzV μ) δ u v).trans
      (lgdDZZ_le_of_ball_le (dzzWall_ball_le isClosed_dzzV (hexp a) hup) δ u v)

end DZZ
end LQGMetric
