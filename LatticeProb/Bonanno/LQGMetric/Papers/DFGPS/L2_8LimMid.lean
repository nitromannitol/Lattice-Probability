/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8LimMid at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8ProofCont
import LatticeProb.Bonanno.LQGMetric.LFPP.PathOps

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.8, third conjunct: midpoints of internal LFPP metrics and of their limits

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex` T:860–866, T:888–889) uses
Lemma 2.7 (`lem-bbi` = BBI Exercise 2.4.19, via BBI Corollary 2.4.17 / Theorem 2.4.16(2)):
uniform limits of length metrics on a compact space are length metrics. The proof of BBI goes
through midpoints (BBI Lemma 2.4.10, Theorem 2.4.16). Here:

* `exists_half_lfppLen`, `lfppDOn_approxMid`: the internal LFPP metric `D_φ(·,·;S)` (continuous
  `φ`, convex bounded `S`) has `ε`-midpoints in `S` (BBI Lemma 2.4.10 for this length structure:
  cut a near-optimal path at half its length; intermediate value theorem for `t ↦ ∫₀ᵗ`);
* `exists_mid_of_tendsto`: midpoints pass to uniform limits of continuous functions on a compact
  metric space (compactness, as in BBI Theorem 2.4.16 / Corollary 2.4.17);
* `midSet`, `isClosed_midSet`, `symmSet`, `isClosed_symmSet`: the closed sets of
  `C(X × X, ℝ)` used with the portmanteau theorem in `L2_8Lim.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open LFPP

/-- **Cutting a path at half its LFPP length** (intermediate value theorem). -/
theorem exists_half_lfppLen {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {P : ℝ → ℂ} {x y : ℂ}
    (hP : IsPiecewiseC1Path P x y) (hfin : lfppLen ξ φ P ≠ ⊤) :
    ∃ t ∈ Icc (0 : ℝ) 1,
      ∫⁻ u in Icc 0 t, lenDens ξ φ P u = ENNReal.ofReal ((lfppLen ξ φ P).toReal / 2) ∧
      ∫⁻ u in Icc t 1, lenDens ξ φ P u = ENNReal.ofReal ((lfppLen ξ φ P).toReal / 2) := by
  set g : ℝ → ℝ := fun u => Real.exp (ξ * φ (P u)) * ‖deriv P u‖ with hg
  have hg0 : ∀ u, 0 ≤ g u := fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  have hmeas : AEStronglyMeasurable g (volume.restrict (Icc (0 : ℝ) 1)) := by
    have h1 : ContinuousOn (fun u => Real.exp (ξ * φ (P u))) (Icc (0 : ℝ) 1) :=
      Real.continuous_exp.comp_continuousOn
        ((continuous_const.mul hφ).comp_continuousOn hP.continuousOn)
    exact (h1.aestronglyMeasurable measurableSet_Icc).mul
      (measurable_deriv P).norm.aestronglyMeasurable
  have hlen : lfppLen ξ φ P = ∫⁻ u in Icc (0 : ℝ) 1, ENNReal.ofReal (g u) := rfl
  have hint : IntegrableOn g (Icc (0 : ℝ) 1) :=
    ⟨hmeas, (hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)).2
      (by rw [← hlen]; exact lt_top_iff_ne_top.2 hfin)⟩
  have hsub : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      ∫⁻ u in Icc a b, lenDens ξ φ P u = ENNReal.ofReal (∫ u in a..b, g u) := by
    intro a b ha hab hb
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
      ofReal_integral_eq_lintegral_ofReal (hint.mono_set (Icc_subset_Icc ha hb))
        (ae_of_all _ fun u => hg0 u)]
    rfl
  have hii : ∀ t ∈ Icc (0 : ℝ) 1, IntervalIntegrable g volume 0 t := fun t ht =>
    (hint.mono_set (by rw [uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)).intervalIntegrable
  set G : ℝ → ℝ := fun t => ∫ u in (0 : ℝ)..t, g u with hG
  have hGc : ContinuousOn G (Icc 0 1) := by
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := 1)
      (μ := volume) (f := g) (by rw [uIcc_of_le zero_le_one]; exact hint)
    rwa [uIcc_of_le zero_le_one] at this
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have hG1nn : 0 ≤ G 1 := intervalIntegral.integral_nonneg zero_le_one fun u _ => hg0 u
  have hG1 : (lfppLen ξ φ P).toReal = G 1 := by
    rw [lfppLen_eq, hsub 0 1 le_rfl zero_le_one le_rfl, ENNReal.toReal_ofReal hG1nn]
  obtain ⟨t, ht, hGt⟩ := intermediate_value_Icc zero_le_one hGc
    (show G 1 / 2 ∈ Icc (G 0) (G 1) from ⟨by rw [hG0]; positivity, by linarith⟩)
  refine ⟨t, ht, ?_, ?_⟩
  · rw [hsub 0 t le_rfl ht.1 ht.2, hG1]
    exact congrArg ENNReal.ofReal hGt
  · rw [hsub t 1 ht.1 ht.2 le_rfl, hG1]
    congr 1
    rw [← intervalIntegral.integral_interval_sub_left (hii 1 ⟨zero_le_one, le_rfl⟩) (hii t ht)]
    change G 1 - G t = G 1 / 2
    rw [hGt]; ring

/-- **`ε`-midpoints of the internal LFPP metric** (BBI Lemma 2.4.10 for `D_φ(·,·;S)`). -/
theorem lfppDOn_approxMid {ξ : ℝ} {φ : ℂ → ℝ} (hφ : Continuous φ) {S : Set ℂ}
    (hS : Convex ℝ S) {R : ℝ} (hSR : S ⊆ closedBall (0 : ℂ) R) {x y : ℂ} (hx : x ∈ S)
    (hy : y ∈ S) {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ S, (lfppDOn ξ φ S x z).toReal ≤ (lfppDOn ξ φ S x y).toReal / 2 + ε ∧
      (lfppDOn ξ φ S z y).toReal ≤ (lfppDOn ξ φ S x y).toReal / 2 + ε := by
  obtain ⟨B, -, hB⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hφ hS hSR
  have hfin : lfppDOn ξ φ S x y ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB x hx y hy)
  have hlt : lfppDOn ξ φ S x y < lfppDOn ξ φ S x y + ENNReal.ofReal (2 * ε) :=
    ENNReal.lt_add_right hfin (by simp; positivity)
  obtain ⟨Q, hQ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨P, hP, hPS⟩ := Q
  simp only at hQ
  have hLfin : lfppLen ξ φ P ≠ ⊤ := ne_top_of_lt hQ
  set L := (lfppLen ξ φ P).toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hLlt : L < (lfppDOn ξ φ S x y).toReal + 2 * ε := by
    have := (ENNReal.toReal_lt_toReal hLfin
      (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩)).2 hQ
    rwa [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at this
  obtain ⟨t, ht, h1, h2⟩ := exists_half_lfppLen hφ hP hLfin
  have hzS : P t ∈ S := hPS t ht
  have b1 : lfppDOn ξ φ S x (P t) ≤ ENNReal.ofReal (L / 2) := by
    rcases ht.1.eq_or_lt with h0 | h0
    · rw [← h0, hP.source, lfppDOn_self hS hx]; exact zero_le
    · have hpp := isPiecewiseC1Path_subPath hP le_rfl h0 ht.2
      rw [hP.source] at hpp
      refine (lfppDOn_le hpp fun u hu => hPS _ ⟨by nlinarith [hu.1, hu.2, ht.1, ht.2],
        by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩).trans (le_of_eq ?_)
      rw [lfppLen_subPath P h0, h1]
  have b2 : lfppDOn ξ φ S (P t) y ≤ ENNReal.ofReal (L / 2) := by
    rcases ht.2.eq_or_lt with h0 | h0
    · rw [h0, hP.target, lfppDOn_self hS hy]; exact zero_le
    · have hpp := isPiecewiseC1Path_subPath hP ht.1 h0 le_rfl
      rw [hP.target] at hpp
      refine (lfppDOn_le hpp fun u hu => hPS _ ⟨by nlinarith [hu.1, hu.2, ht.1, ht.2],
        by nlinarith [hu.1, hu.2, ht.1, ht.2]⟩).trans (le_of_eq ?_)
      rw [lfppLen_subPath P h0, h2]
  refine ⟨P t, hzS, ?_, ?_⟩
  · exact (ENNReal.toReal_le_of_le_ofReal (by positivity) b1).trans (by linarith)
  · exact (ENNReal.toReal_le_of_le_ofReal (by positivity) b2).trans (by linarith)

/-- **Midpoints pass to uniform limits** on a compact metric space: if `dₙ → d` in
`C(X × X, ℝ)`, `εₙ → 0` and `zₙ` is an `εₙ`-midpoint of `x, y` for `dₙ`, then `x, y` have an
exact `d`-midpoint (compactness, as in BBI Theorem 2.4.16 / Corollary 2.4.17). -/
theorem exists_mid_of_tendsto {X : Type*} [MetricSpace X] [CompactSpace X]
    {dn : ℕ → C(X × X, ℝ)} {d : C(X × X, ℝ)} (hd : Tendsto dn atTop (𝓝 d)) {εn : ℕ → ℝ}
    (hε : Tendsto εn atTop (𝓝 0)) (x y : X) (z : ℕ → X)
    (hz : ∀ n, dn n (x, z n) ≤ dn n (x, y) / 2 + εn n ∧ dn n (z n, y) ≤ dn n (x, y) / 2 + εn n) :
    ∃ w, d (x, w) ≤ d (x, y) / 2 ∧ d (w, y) ≤ d (x, y) / 2 := by
  obtain ⟨w, -, ψ, hψ, hlim⟩ := isCompact_univ.tendsto_subseq (fun n => mem_univ (z n))
  have hdψ : Tendsto (fun n => dn (ψ n)) atTop (𝓝 d) := hd.comp hψ.tendsto_atTop
  have hεψ : Tendsto (fun n => εn (ψ n)) atTop (𝓝 0) := hε.comp hψ.tendsto_atTop
  have hev : ∀ p : ℕ → X × X, ∀ q : X × X, Tendsto p atTop (𝓝 q) →
      Tendsto (fun n => dn (ψ n) (p n)) atTop (𝓝 (d q)) := fun p q hp =>
    (continuous_eval.tendsto (d, q)).comp (hdψ.prodMk_nhds hp)
  have hxy := hev (fun _ => (x, y)) (x, y) tendsto_const_nhds
  have hrhs : Tendsto (fun n => dn (ψ n) (x, y) / 2 + εn (ψ n)) atTop (𝓝 (d (x, y) / 2)) := by
    simpa using (hxy.div_const 2).add hεψ
  refine ⟨w, le_of_tendsto_of_tendsto' (hev (fun n => (x, z (ψ n))) (x, w)
      (tendsto_const_nhds.prodMk_nhds hlim)) hrhs fun n => (hz (ψ n)).1,
    le_of_tendsto_of_tendsto' (hev (fun n => (z (ψ n), y)) (w, y)
      (hlim.prodMk_nhds tendsto_const_nhds)) hrhs fun n => (hz (ψ n)).2⟩

/-- the continuous functions on `X × X` with exact midpoints -/
def midSet (X : Type*) [TopologicalSpace X] : Set C(X × X, ℝ) :=
  {d | ∀ x y, ∃ z, d (x, z) ≤ d (x, y) / 2 ∧ d (z, y) ≤ d (x, y) / 2}

theorem isClosed_midSet (X : Type*) [MetricSpace X] [CompactSpace X] :
    IsClosed (midSet X) := by
  refine isClosed_of_closure_subset fun d hd x y => ?_
  obtain ⟨dn, hdn, hlim⟩ := mem_closure_iff_seq_limit.1 hd
  choose z hz using fun n => hdn n x y
  exact exists_mid_of_tendsto hlim tendsto_const_nhds x y z fun n => by
    simpa using hz n

/-- approximate midpoints give exact ones (continuous `d`, compact metric `X`) -/
theorem mem_midSet_of_approx {X : Type*} [MetricSpace X] [CompactSpace X] (d : C(X × X, ℝ))
    (h : ∀ x y, ∀ ε : ℝ, 0 < ε → ∃ z, d (x, z) ≤ d (x, y) / 2 + ε ∧ d (z, y) ≤ d (x, y) / 2 + ε) :
    d ∈ midSet X := by
  intro x y
  choose z hz using fun n : ℕ => h x y (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
  exact exists_mid_of_tendsto tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat x y z hz

/-- the symmetric continuous functions on `X × X` -/
def symmSet (X : Type*) [TopologicalSpace X] : Set C(X × X, ℝ) :=
  {d | ∀ x y, d (x, y) = d (y, x)}

theorem isClosed_symmSet (X : Type*) [TopologicalSpace X] : IsClosed (symmSet X) := by
  have e : symmSet X = ⋂ x, ⋂ y, {d : C(X × X, ℝ) | d (x, y) = d (y, x)} := by
    ext d; simp only [symmSet, mem_iInter, mem_ofPred_eq]
  rw [e]
  exact isClosed_iInter fun x => isClosed_iInter fun y =>
    isClosed_eq (continuous_eval_const _) (continuous_eval_const _)

end LQGMetric.DFGPS
