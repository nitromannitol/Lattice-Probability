/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.HeatMollifyUnif at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyKolm

/-!
# A.s. locally uniform convergence and continuity of `h*_ε` (task P2-FHEAT, part 2b)

GM (1.2) (`uniqueness-final.tex` l. 170–177, footnote l. 212); FOUNDATIONS §3 obligation:
for `IsWholePlaneGFF h P` (any additive constant) and for `IsGFFPlusBddCont h P`, for fixed
`ε ≠ 0`, a.s. the truncated pairings `z ↦ ⟨h, p_{ε²/2}(z,·) χ_n⟩` converge locally uniformly
to `heatMollify ε (h ω)`, which is therefore continuous.

Deterministic part (`tendstoLocallyUniformly_heatMollify_of_bound`): the Weierstrass M-test
(mathlib `tendstoUniformlyOn_tsum_nat_eventually`) on each ball applied to the telescoping
increments `⟨g, heatDiff s z n⟩`, continuity of `z ↦ heatTrunc s z n` in `𝓓(ℂ)` (P2-FMEAS:
`continuous_heatTrunc`) and `TendstoLocallyUniformly.continuous`. Probabilistic input:
`IsWholePlaneGFF.ae_eventually_gaussDiffProc_le` (Kolmogorov + Borel–Cantelli). Own argument
along the route of FOUNDATIONS §3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric

namespace LQGMetric

/-- **Deterministic M-test.** -/
theorem tendstoLocallyUniformly_heatMollify_of_bound (g : DistC) (ε : ℝ)
    (hb : ∀ R : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ n in atTop,
      ∀ z ∈ closedBall (0 : ℂ) R, |g (heatDiff (ε ^ 2 / 2) z n)| ≤ u n) :
    TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => g (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε g) atTop ∧ Continuous (heatMollify ε g) := by
  set s := ε ^ 2 / 2
  set F : ℕ → ℂ → ℝ := fun N z => g (heatTrunc s z N)
  set G : ℂ → ℝ := fun z => F 0 z + ∑' n, g (heatDiff s z n)
  have hF : ∀ N z, F N z = F 0 z + ∑ n ∈ Finset.range N, g (heatDiff s z n) := by
    intro N z
    have : ∀ n, g (heatDiff s z n) = F (n + 1) z - F n z := fun n => by
      simp only [heatDiff, map_sub, F]
    simp_rw [this, Finset.sum_range_sub (fun n => F n z)]
    ring
  have hU : ∀ R : ℕ, TendstoUniformlyOn F G atTop (closedBall (0 : ℂ) R) := by
    intro R
    obtain ⟨u, hu, hev⟩ := hb R
    have hT := tendstoUniformlyOn_tsum_nat_eventually hu
      (f := fun n z => g (heatDiff s z n)) (s := closedBall (0 : ℂ) R)
      (by filter_upwards [hev] with n hn z hz; simpa [Real.norm_eq_abs] using hn z hz)
    rw [Metric.tendstoUniformlyOn_iff] at hT ⊢
    intro δ hδ
    filter_upwards [hT δ hδ] with N hN z hz
    simp only [G, hF N z, dist_add_left]
    exact hN z hz
  have hLU : TendstoLocallyUniformly F G atTop := by
    intro u hu x
    obtain ⟨R, hR⟩ := exists_nat_gt ‖x‖
    exact ⟨closedBall (0 : ℂ) R, closedBall_mem_nhds_of_mem (by simpa using hR), hU R u hu⟩
  have hGeq : heatMollify ε g = G := by
    funext z
    obtain ⟨R, hR⟩ := exists_nat_gt ‖z‖
    exact ((hU R).tendsto_at (by simpa using hR.le)).limUnder_eq
  rw [hGeq]
  refine ⟨hLU, hLU.continuous (Frequently.of_forall fun N => ?_)⟩
  exact g.continuous.comp (continuous_heatTrunc s N)

lemma abs_integral_heatDiff_le (s : ℝ) (hs : 0 < s) (R : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) (n : ℕ)
    (f : ℂ → ℝ) (M : ℝ) (hM : ∀ w, |f w| ≤ M) :
    |∫ w, heatDiff s z n w * f w| ≤
      (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + R) * Real.exp (-(n : ℝ)) * M *
        (Real.pi * ((n : ℝ) + 3) ^ 2) := by
  refine abs_integral_le_of_bound (by positivity) (fun w => ?_) (fun w hw => ?_)
  · rw [abs_mul]
    exact mul_le_mul (abs_heatTrunc_succ_sub_le s hs z R hz n w) (hM w) (abs_nonneg _)
      (by positivity)
  · have : heatDiff s z n w = 0 := heatTrunc_succ_sub_eq_zero' s z n w hw.le
    rw [this, zero_mul]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma summable_exp_neg_half : Summable fun n : ℕ => Real.exp (-(n : ℝ) / 2) :=
  (Real.summable_pow_mul_exp_neg_nat_mul 0 (by norm_num : (0 : ℝ) < 1 / 2)).congr fun n => by
    simp only [pow_zero, one_mul]; congr 1; ring

/-- a.s. bounds on the GFF increments, uniformly on balls -/
theorem IsWholePlaneGFF.ae_bound_heatDiff (hh : IsWholePlaneGFF h P) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ᶠ n in atTop,
      ∀ z ∈ closedBall (0 : ℂ) R, |h ω (heatDiff s z n)| ≤ u n := by
  filter_upwards [hh.ae_eventually_gaussDiffProc_le s hs] with ω hω R
  set K0 : ℝ := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + R)
  refine ⟨fun n => 9 * Real.exp (-(n : ℝ) / 2) + K0 * Real.exp (-(n : ℝ)) * 1 *
    (Real.pi * ((n : ℝ) + 3) ^ 2) * |h ω refTest|, ?_, ?_⟩
  · refine (summable_exp_neg_half.mul_left 9).add ?_
    exact (((summable_shift_pow_mul_exp 2).mul_left (K0 * Real.pi)).mul_right
      |h ω refTest|).congr fun n => by ring
  · filter_upwards [hω R] with n hn z hz
    have hzR : ‖z‖ ≤ R := by simpa using hz
    obtain ⟨q, hq, rfl⟩ := exists_mem_boxD hzR
    rw [pair_eq_meanZeroPart (h ω)]
    refine (abs_add_le _ _).trans (add_le_add (hn q hq) ?_)
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have := abs_integral_heatDiff_le s hs R (cplxOf q) hzR n (fun _ => 1) 1 (by simp)
    simp only [mul_one] at this ⊢
    exact this

/-- **A.s. locally uniform convergence and continuity of `h*_ε` for the whole-plane GFF.** -/
theorem IsWholePlaneGFF.ae_tendstoLocallyUniformly_heatMollify (hh : IsWholePlaneGFF h P)
    (ε : ℝ) (hε : ε ≠ 0) :
    ∀ᵐ ω ∂P, TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => h ω (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε (h ω)) atTop ∧ Continuous (heatMollify ε (h ω)) := by
  filter_upwards [hh.ae_bound_heatDiff (ε ^ 2 / 2) (by positivity)] with ω hω
  exact tendstoLocallyUniformly_heatMollify_of_bound (h ω) ε hω

/-- **A.s. locally uniform convergence and continuity of `h*_ε` for a whole-plane GFF plus a
bounded continuous function** (GM l. 211–212). -/
theorem IsGFFPlusBddCont.ae_tendstoLocallyUniformly_heatMollify (hh : IsGFFPlusBddCont h P)
    (ε : ℝ) (hε : ε ≠ 0) :
    ∀ᵐ ω ∂P, TendstoLocallyUniformly (fun (n : ℕ) (z : ℂ) => h ω (heatTrunc (ε ^ 2 / 2) z n))
      (heatMollify ε (h ω)) atTop ∧ Continuous (heatMollify ε (h ω)) := by
  obtain ⟨_, f, _, hfb, hg⟩ := hh
  set s := ε ^ 2 / 2
  have hs : 0 < s := by positivity
  filter_upwards [hg.ae_bound_heatDiff s hs] with ω hω
  obtain ⟨M, hM⟩ := hfb ω
  refine tendstoLocallyUniformly_heatMollify_of_bound (h ω) ε fun R => ?_
  obtain ⟨u, hu, hev⟩ := hω R
  set K0 : ℝ := (2 * Real.pi * s)⁻¹ * Real.exp (s / 2 + R)
  refine ⟨fun n => u n + K0 * Real.exp (-(n : ℝ)) * M * (Real.pi * ((n : ℝ) + 3) ^ 2),
    hu.add ?_, ?_⟩
  · exact ((summable_shift_pow_mul_exp 2).mul_left (K0 * M * Real.pi)).congr fun n => by ring
  · filter_upwards [hev] with n hn z hz
    have hzR : ‖z‖ ≤ R := by simpa using hz
    have e : h ω (heatDiff s z n) = (h ω - ofCont (f ω)) (heatDiff s z n) +
        ofCont (f ω) (heatDiff s z n) := by
      simp only [ContinuousLinearMap.sub_apply, sub_add_cancel]
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add (hn z hz) ?_)
    rw [ofCont_apply_heat]
    exact abs_integral_heatDiff_le s hs R z hzR n (f ω) M hM

end LQGMetric
