/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_1PolarCont at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Polar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.1: continuity of the polar integral in `(ε, z)`

DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`) T:722–723: "From this representation
and the continuity of the circle average process, we infer that `(z, ε) ↦ ĝ*_ε(z)` a.s. admits a
continuous modification." Here: the polar integral
`(ε, z) ↦ (2/ε²) ∫_0^∞ r F(r, z) (1 − ψ_ε(r)) e^{−r²/ε²} dr` is continuous on `(0, ∞) × ℂ`
whenever `F` is continuous on `(0, ∞) × ℂ` and obeys the Lemma 2.2 bound
`|F(r, z)| ≤ C max{A log(1/r), log r, 1}` on every ball (`continuousOn_polarDiffInt`; dominated
convergence, mathlib `continuousAt_of_dominated`, with the Gaussian dominating function
`(A + r² + r) e^{−r²/b²}`).
-/

noncomputable section

open MeasureTheory Set Filter Topology Metric

namespace LQGMetric.DFGPS

open LFPP

/-- the polar integral `(2/ε²) ∫_0^∞ r F(r, z) (1 − ψ_ε(r)) e^{−r²/ε²} dr`, with `ψ_ε` written
through its profile `locProf (log ε)` (so that it is defined for every `ε`) -/
def polarDiffInt (F : ℝ → ℂ → ℝ) (p : ℝ × ℂ) : ℝ :=
  2 / p.1 ^ 2 * ∫ r in Ioi 0, r * F r p.2 * (1 - locProf (Real.log p.1) (r : ℂ)) *
    Real.exp (-r ^ 2 / p.1 ^ 2)

lemma locBump_congr {ε ε' : ℝ} (e : ε = ε') (hε : 0 < ε) (hε' : 0 < ε') (y : ℂ) :
    locBump ε hε y = locBump ε' hε' y := by subst e; rfl

lemma locBump_eq_locProf {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    locBump ε hε y = locProf (Real.log ε) y := by
  rw [← locBump_exp, locBump_congr (Real.exp_log hε).symm hε]

lemma locProf_mem_Icc (u : ℝ) (y : ℂ) : locProf u y ∈ Icc (0 : ℝ) 1 := by
  rw [← locBump_exp]
  exact ⟨locBump_nonneg _ _ _, locBump_le_one _ _ _⟩

lemma polarDiffInt_eq (F : ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    polarDiffInt F (ε, z) = 2 / ε ^ 2 * ∫ r in Ioi 0, r * F r z * (1 - locBump ε hε (r : ℂ)) *
      Real.exp (-r ^ 2 / ε ^ 2) := by
  simp only [polarDiffInt, locBump_eq_locProf hε]

lemma integrableOn_gaussW (A : ℝ) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => (A + r ^ 2 + r) * Real.exp (-c * r ^ 2)) (Ioi 0) := by
  have h0 := (integrable_exp_neg_mul_sq hc).integrableOn (s := Ioi (0 : ℝ))
  have h1 := (integrable_mul_exp_neg_mul_sq hc).integrableOn (s := Ioi (0 : ℝ))
  have h2 : IntegrableOn (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-c * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hc (by norm_num)
  simp_rw [Real.rpow_two] at h2
  have := ((h0.const_mul A).add h2).add h1
  refine IntegrableOn.congr_fun this (fun r _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

/-- **Continuity of the polar integral** (DFGPS T:722–723). -/
theorem continuousOn_polarDiffInt {F : ℝ → ℂ → ℝ}
    (hF : ContinuousOn (fun p : ℝ × ℂ => F p.1 p.2) (Ioi 0 ×ˢ univ))
    (hb : ∀ R : ℝ, ∃ A C : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) R,
      |F r z| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1) :
    ContinuousOn (polarDiffInt F) (Ioi 0 ×ˢ univ) := by
  have hS : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := isOpen_Ioi.prod isOpen_univ
  refine continuousOn_of_forall_continuousAt fun p0 hp0 => ?_
  obtain ⟨ε0, z0⟩ := p0
  have hε0 : 0 < ε0 := (mem_prod.1 hp0).1
  obtain ⟨A, C, hA, hC⟩ := hb (‖z0‖ + 1)
  set b := 2 * ε0
  have hb0 : 0 < b := by positivity
  -- the neighbourhood
  have hN : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), ε0 / 2 < p.1 ∧ p.1 < b ∧ p.2 ∈ ball (0 : ℂ) (‖z0‖ + 1) := by
    have h1 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), ε0 / 2 < p.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds (by linarith))
    have h2 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.1 < b :=
      continuous_fst.continuousAt.eventually (gt_mem_nhds (by simp only [b]; linarith))
    have h3 : ∀ᶠ p : ℝ × ℂ in 𝓝 (ε0, z0), p.2 ∈ ball (0 : ℂ) (‖z0‖ + 1) :=
      continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds (by simp))
    filter_upwards [h1, h2, h3] with p a1 a2 a3 using ⟨a1, a2, a3⟩
  set G : ℝ × ℂ → ℝ → ℝ := fun p r => r * F r p.2 * (1 - locProf (Real.log p.1) (r : ℂ)) *
    Real.exp (-r ^ 2 / p.1 ^ 2)
  have hFr : ∀ z : ℂ, ContinuousOn (fun r => F r z) (Ioi 0) := fun z =>
    hF.comp (continuous_id.prodMk continuous_const).continuousOn fun r hr => ⟨hr, mem_univ _⟩
  have hprof : Continuous fun q : ℝ × ℂ => locProf q.1 q.2 := contDiff_locProf.continuous
  have hInt : ContinuousAt (fun p : ℝ × ℂ => ∫ r in Ioi 0, G p r) (ε0, z0) := by
    refine continuousAt_of_dominated (bound := fun r => |C| * ((A + r ^ 2 + r) *
      Real.exp (-(1 / b ^ 2) * r ^ 2))) ?_ ?_ ?_ ?_
    · filter_upwards [hN] with p hp
      have hp1 : 0 < p.1 := by linarith [hp.1]
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ((continuousOn_id.mul (hFr p.2)).mul (continuousOn_const.sub
        (hprof.comp_continuousOn (continuousOn_const.prodMk
          (Complex.continuous_ofReal.continuousOn))))).mul ?_
      exact (Real.continuous_exp.comp ((continuous_pow 2).neg.div_const _)).continuousOn
    · filter_upwards [hN] with p hp
      have hp1 : 0 < p.1 := by linarith [hp.1]
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      have hI := locProf_mem_Icc (Real.log p.1) (r : ℂ)
      have hFb : |F r p.2| ≤ |C| * (A / r + r + 1) := by
        have hm := max_log_le hA hr
        have hm1 : (1 : ℝ) ≤ max (max (A * Real.log (1 / r))
            (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := le_max_right _ _
        calc |F r p.2| ≤ C * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := hC r hr p.2 hp.2.2
          _ ≤ |C| * max (max (A * Real.log (1 / r))
              (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
          _ ≤ |C| * (A / r + r + 1) := mul_le_mul_of_nonneg_left hm (abs_nonneg C)
      have he : Real.exp (-r ^ 2 / p.1 ^ 2) ≤ Real.exp (-(1 / b ^ 2) * r ^ 2) := by
        refine Real.exp_le_exp.2 ?_
        have hpb : p.1 ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ hp1.le hp.2.1.le 2
        rw [neg_div, neg_mul, neg_le_neg_iff, one_div, inv_mul_eq_div]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpb
      simp only [G, Real.norm_eq_abs, abs_mul, abs_of_pos hr,
        abs_of_nonneg (by linarith [hI.2] : (0 : ℝ) ≤ 1 - locProf (Real.log p.1) (r : ℂ)),
        abs_of_pos (Real.exp_pos _)]
      calc r * |F r p.2| * (1 - locProf (Real.log p.1) (r : ℂ)) * Real.exp (-r ^ 2 / p.1 ^ 2)
          ≤ r * (|C| * (A / r + r + 1)) * 1 * Real.exp (-(1 / b ^ 2) * r ^ 2) := by
            gcongr
            all_goals linarith [hI.1, hI.2]
        _ = |C| * ((A + r ^ 2 + r) * Real.exp (-(1 / b ^ 2) * r ^ 2)) := by
            field_simp
    · exact ((integrableOn_gaussW A (by positivity)).const_mul _)
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr : 0 < r := hr
      have hm : ((r, z0) : ℝ × ℂ) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := ⟨hr, mem_univ _⟩
      have hH : ContinuousAt (fun p : ℝ × ℂ => F r p.2) (ε0, z0) := by
        have h2 : ContinuousAt (fun p : ℝ × ℂ => ((r, p.2) : ℝ × ℂ)) (ε0, z0) :=
          continuousAt_const.prodMk continuous_snd.continuousAt
        exact ContinuousAt.comp (g := fun q : ℝ × ℂ => F q.1 q.2)
          (f := fun p : ℝ × ℂ => ((r, p.2) : ℝ × ℂ)) (hF.continuousAt (hS.mem_nhds hm)) h2
      have hL : ContinuousAt (fun p : ℝ × ℂ => locProf (Real.log p.1) (r : ℂ)) (ε0, z0) := by
        have h1 : ContinuousAt (fun p : ℝ × ℂ => (Real.log p.1, (r : ℂ))) (ε0, z0) :=
          (continuous_fst.continuousAt.log hε0.ne').prodMk continuousAt_const
        exact hprof.continuousAt.comp h1
      have hE : ContinuousAt (fun p : ℝ × ℂ => Real.exp (-r ^ 2 / p.1 ^ 2)) (ε0, z0) :=
        Real.continuous_exp.continuousAt.comp (continuousAt_const.div
          (continuous_fst.continuousAt.pow 2) (by simpa using hε0.ne'))
      exact ((continuousAt_const.mul hH).mul (continuousAt_const.sub hL)).mul hE
  exact (continuousAt_const.div (continuous_fst.continuousAt.pow 2)
    (by simpa using hε0.ne')).mul hInt

/-- **Polar formula for `g*_ε(z) − ĝ*_ε(z)` at a fixed `(ε, z)`** (DFGPS T:715–722: `ψ_ε(z − ·)`
and `p_{ε²/2}(z, ·)` are radial about `z`, so both mollifications are integrals of the circle
averages about `z` against their radial profiles). Open node. -/
def Lem2_1PolarPoint.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ),
    IsWholePlaneGFF g P → IsCircleAvgVersion g P H →
    ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ z : ℂ, ∀ᵐ ω ∂P,
      heatMollify ε (g ω) z - locMollify ε hε (g ω) z =
        2 / ε ^ 2 * ∫ r in Ioi 0, r * H r z ω * (1 - locBump ε hε (r : ℂ)) *
          Real.exp (-r ^ 2 / ε ^ 2)

/-- **`g*_ε(z)` exists and is continuous jointly in `(ε, z)`**, a.s. for the whole-plane GFF
(the paper treats `(ε, z) ↦ g*_ε(z)` as a continuous process, GM (1.2)/DFGPS T:690). Open node:
`Field/HeatMollifyUnif` gives this for each fixed `ε` only. -/
def Lem2_1HeatJoint.{u} : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → DistC), IsWholePlaneGFF g P →
    ∀ᵐ ω ∂P, (∀ ε : ℝ, 0 < ε → ∀ z : ℂ,
        ∃ L, Tendsto (fun n : ℕ => g ω (heatTrunc (ε ^ 2 / 2) z n)) atTop (𝓝 L)) ∧
      ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (g ω) p.2) (Ioi 0 ×ˢ univ)

/-- the left side `g*_ε(z) − ĝ*_ε(z)` as a function of `p = (ε, z)` -/
def polarDiffLhs (g : DistC) (p : ℝ × ℂ) : ℝ :=
  heatMollify p.1 g p.2 - if hp : 0 < p.1 then locMollify p.1 hp g p.2 else 0

/-- **From the pointwise polar formula to the simultaneous one**: both sides are a.s. continuous
in `(ε, z)` (`Lem2_1HeatJoint`, `lem2_1_cont`, `continuousOn_polarDiffInt` with `lem2_2`), and agree
a.s. on a countable dense set. -/
theorem lem2_1PolarDiff_of.{u} (HPt : Lem2_1PolarPoint.{u}) (HJ : Lem2_1HeatJoint.{u}) :
    Lem2_1PolarDiff.{u} := by
  intro Ω _ P g H hg hH
  set S : Set (ℝ × ℂ) := Ioi 0 ×ˢ univ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have hD : ∀ᵐ ω ∂P, ∀ q ∈ D, polarDiffLhs (g ω) q.1 = polarDiffInt (fun r z => H r z ω) q.1 := by
    refine (ae_ball_iff hDc).2 fun q _ => ?_
    obtain ⟨⟨ε, z⟩, hq⟩ := q
    have hε : 0 < ε := (mem_prod.1 hq).1
    filter_upwards [HPt P g H hg hH ε hε z] with ω hω
    simp only [polarDiffLhs, dif_pos hε, polarDiffInt_eq _ hε]
    exact hω
  have hA : ∀ n : ℕ, ∃ A : ℝ, 0 < A ∧ ∀ ζ : ℝ, 0 < ζ → ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ r : ℝ, 0 < r →
      ∀ z ∈ ball (0 : ℂ) n,
        |H r z ω| ≤ C * max (max (A * Real.log (1 / r)) (Real.log r ^ (1 / 2 + ζ))) 1 :=
    fun n => lem2_2 hg hH n
  choose A hA0 hAb using hA
  have hB : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) n,
      |H r z ω| ≤ C * max (max (A n * Real.log (1 / r))
        (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 :=
    ae_all_iff.2 fun n => hAb n (1 / 2) (by norm_num)
  filter_upwards [hD, hB, HJ P g hg] with ω hωD hωB hωJ ε hε z
  refine ⟨hωJ.1 ε hε z, ?_⟩
  have hb : ∀ R : ℝ, ∃ A C : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) R,
      |H r z ω| ≤ C * max (max (A * Real.log (1 / r))
        (Real.log r ^ (1 / 2 + 1 / 2 : ℝ))) 1 := by
    intro R
    obtain ⟨C, hC⟩ := hωB ⌈R⌉₊
    exact ⟨A ⌈R⌉₊, C, (hA0 _).le, fun r hr z hz =>
      hC r hr z (ball_subset_ball (Nat.le_ceil R) hz)⟩
  have hR : ContinuousOn (polarDiffInt fun r z => H r z ω) S :=
    continuousOn_polarDiffInt (hH.cont ω) hb
  have hL : ContinuousOn (polarDiffLhs (g ω)) S := hωJ.2.sub (lem2_1_cont (g ω))
  have heq : (S.restrict (polarDiffLhs (g ω))) = S.restrict (polarDiffInt fun r z => H r z ω) :=
    Continuous.ext_on hDd (continuousOn_iff_continuous_restrict.1 hL)
      (continuousOn_iff_continuous_restrict.1 hR) fun q hq => hωD q hq
  have e := congrFun heq ⟨(ε, z), ⟨hε, mem_univ _⟩⟩
  have e' : polarDiffLhs (g ω) (ε, z) = polarDiffInt (fun r z => H r z ω) (ε, z) := e
  rw [polarDiffInt_eq _ hε] at e'
  simpa only [polarDiffLhs, dif_pos hε] using e'

end LQGMetric.DFGPS
