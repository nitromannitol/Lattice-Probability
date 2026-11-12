/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea6C at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6B
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgKolm
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgGP

/-!
For a whole-plane GFF `X` (LM `IsWholePlaneGFF`), a radius `δ > 0` and the inner process

  `wpU X δ k t = h_{2^{-k}}(t) − h_δ(0)` (LM `CircleAvg.cInc`),

the hypotheses `TwoRadiusC.TRLHypC` of QZ's planar two-radius lemma hold at every level `k` with
`B̄(t, 2^{-k}) ⊆ B̄(0, δ)` for `t ∈ S`, with `K = 0` (`levelHyp_wpU`). The inputs are LM's
Gaussian process of circle-average increments (`CircleAvg.isGaussianProcess_incProc`,
`CircleAvg.map_cInc`, `CircleAvg.covariance_cInc`; Duplantier–Sheffield arXiv:0808.1560 §3.1) and
the explicit covariances: with `circLog w s x = log max(s, |w − x|)` (LM `circLog_eq_log_max`),

* `circCov_eq_of_inside`: `∂B(z,r) ⊆ B̄(w,s)` gives `circCov z r w s = log s`;
* `circCov_eq_of_outside`: `∂B(z,r) ∩ B(w,s) = ∅` gives `circCov z r w s = log max(r, |z − w|)`

(the mean value property of `log|·|`, through LM's `circLog`). This is the whole-plane analogue of
QZ `AreaP3b.trlHypC_inner` (free-boundary GFF on `ℍ`); for the whole plane all reflected terms
vanish, so the constant is `K = 0`. The independence of disjoint-scale increments is
Duplantier–Sheffield Prop. 3.3. The covariance computations are an own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea6

open QuantumZipper TwoRadiusC LQGMetric LQGMetric.CircleAvg

/-! ### Circle covariances -/

lemma circCov_eq_of_inside {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : ∀ x ∈ sphere z r, ‖w - x‖ ≤ s) : circCov z r w s = Real.log s := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [abs_of_pos hr] at hx
  rw [circLog_eq_log_max hs, max_eq_left (h x hx)]

lemma circCov_eq_of_outside {z w : ℂ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : ∀ x ∈ sphere z r, s ≤ ‖w - x‖) : circCov z r w s = Real.log (max r ‖z - w‖) := by
  rw [circCov, ← circLog_eq_log_max hr z w]
  show Real.circleAverage (circLog w s) z r =
    Real.circleAverage (fun a => Real.log ‖a - w‖) z r
  refine Real.circleAverage_congr_sphere fun x hx => ?_
  rw [abs_of_pos hr] at hx
  rw [circLog_eq_log_max hs, max_eq_right (h x hx), norm_sub_rev]

lemma circCov_same {t : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    circCov t a t b = Real.log (max b a) := by
  refine Real.circleAverage_const_on_circle fun x hx => ?_
  rw [abs_of_pos ha, mem_sphere_iff_norm] at hx
  rw [circLog_eq_log_max hb, norm_sub_rev, hx]

/-! ### Independence from vanishing covariances -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Field}

/-- jointly Gaussian circle-average increments with vanishing cross covariances are independent
(as QZ `GaussTK.indepFun_fcPair`, for LM's increment process) -/
theorem indepFun_incProc (hX : IsWholePlaneGFF X P) {S T : Type*} (f : S → IncIdx)
    (g : T → IncIdx)
    (h : ∀ s t, incCov (f s).1.2 (f s).1.1 (f s).2.2 (f s).2.1
      (g t).1.2 (g t).1.1 (g t).2.2 (g t).2.1 = 0) :
    IndepFun (fun ω s => incProc X (f s) ω) (fun ω t => incProc X (g t) ω) P := by
  have hG := (isGaussianProcess_incProc hX).comp_right (Sum.elim f g)
  have hG' : IsGaussianProcess (Sum.elim (fun s => incProc X (f s))
      (fun t => incProc X (g t))) P := by
    have e : Sum.elim (fun s => incProc X (f s)) (fun t => incProc X (g t)) =
        incProc X ∘ Sum.elim f g := by
      funext i; cases i <;> rfl
    rw [e]; exact hG
  exact hG'.indepFun_of_covariance_eq_zero
    (fun s => (measurable_cInc hX _ _ _ _).aemeasurable)
    (fun t => (measurable_cInc hX _ _ _ _).aemeasurable) fun s t => by
      rw [show incProc X (f s) = cInc X (f s).1.1 (f s).1.2 (f s).2.1 (f s).2.2 from rfl,
        show incProc X (g t) = cInc X (g t).1.1 (g t).1.2 (g t).2.1 (g t).2.2 from rfl,
        covariance_cInc hX (f s).1.1.2 (f s).2.1.2 (g t).1.1.2 (g t).2.1.2]
      exact h s t

/-! ### The inner process of the whole-plane GFF -/

/-- the inner process `U_k(t) = h_{2^{-k}}(t) − h_δ(0)` -/
def wpU (X : Ω → Field) (δ : ℝ) (k : ℕ) (t : ℂ) (ω : Ω) : ℝ := cInc X (radius k) t δ 0 ω

theorem measurable_wpU (hX : IsWholePlaneGFF X P) (δ : ℝ) (k : ℕ) :
    Measurable (fun p : ℂ × Ω => wpU X δ k p.1 p.2) := by
  have h1 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) (radius k) p.1 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, radius k, p.1))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst))
  have h2 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) δ 0 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, δ, (0 : ℂ)))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_const))
  exact h1.sub h2

omit [MeasurableSpace Ω] in
lemma wpU_succ_sub (δ : ℝ) (k : ℕ) (t : ℂ) :
    (fun ω => wpU X δ (k + 1) t ω - wpU X δ k t ω) = cInc X (radius (k + 1)) t (radius k) t := by
  funext ω; simp only [wpU, cInc]; ring

/-- **the two-radius hypotheses for the whole-plane GFF** at level `k` (`K = 0`) -/
theorem levelHyp_wpU [IsProbabilityMeasure P] (hX : IsWholePlaneGFF X P) {δ : ℝ} {S : Set ℂ}
    {k : ℕ} (hSk : ∀ t ∈ S, ‖t‖ + radius k ≤ δ) (hk : radius k ≤ δ) :
    ConeArea6.LevelHyp P S δ 0 (wpU X δ) k := by
  have hr := QuantumZipper.radius_pos k
  have hδ : 0 < δ := hr.trans_le hk
  have hr' : radius (k + 1) = radius k / 2 := AreaExist.aradius_succ k
  have hr1 : 0 < radius (k + 1) := QuantumZipper.radius_pos (k + 1)
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  -- covariance facts
  have hin : ∀ t ∈ S, ∀ a, 0 < a → a ≤ radius k → circCov t a 0 δ = Real.log δ := by
    intro t ht a ha har
    refine circCov_eq_of_inside ha hδ fun x hx => ?_
    rw [mem_sphere_iff_norm] at hx
    have := norm_sub_norm_le x t
    have h2 := hSk t ht
    rw [zero_sub, norm_neg]
    linarith
  have hout0 : ∀ t ∈ S, ∀ a, 0 < a → a ≤ radius k → circCov 0 δ t a = Real.log δ := by
    intro t ht a ha har
    rw [circCov_eq_of_outside hδ ha fun x hx => ?_]
    · rw [zero_sub, norm_neg, max_eq_left (by linarith [hSk t ht, norm_nonneg t])]
    · rw [mem_sphere_iff_norm, sub_zero] at hx
      have := norm_sub_norm_le x t
      rw [norm_sub_rev] at this
      linarith [hSk t ht]
  have hfar : ∀ t u : ℂ, 2 * radius k ≤ ‖t - u‖ → ∀ a b, 0 < a → a ≤ radius k → 0 < b →
      b ≤ radius k → circCov t a u b = Real.log ‖t - u‖ := by
    intro t u htu a b ha har hb hbr
    rw [circCov_eq_of_outside ha hb fun x hx => ?_, max_eq_right (by linarith)]
    rw [mem_sphere_iff_norm, norm_sub_rev] at hx
    have := norm_sub_norm_le (t - u) (t - x)
    rw [show t - u - (t - x) = x - u by ring, norm_sub_rev x u] at this
    linarith
  have hsame : ∀ t : ℂ, circCov t (radius (k + 1)) t (radius k) = Real.log (radius k) := by
    intro t; rw [circCov_same hr1 hr, max_eq_left (by rw [hr']; linarith)]
  have hsame' : ∀ t : ℂ, circCov t (radius k) t (radius (k + 1)) = Real.log (radius k) := by
    intro t; rw [circCov_same hr hr1, max_eq_right (by rw [hr']; linarith)]
  have hr1k : radius (k + 1) ≤ radius k := by rw [hr']; linarith
  -- the increments as LM processes
  let iU : ℂ → IncIdx := fun t => ((⟨radius k, hr⟩, t), (⟨δ, hδ⟩, 0))
  let iΔ : ℂ → IncIdx := fun t => ((⟨radius (k + 1), hr1⟩, t), (⟨radius k, hr⟩, t))
  have eU : ∀ t, wpU X δ k t = incProc X (iU t) := fun t => rfl
  have eΔ : ∀ t, (fun ω => wpU X δ (k + 1) t ω - wpU X δ k t ω) = incProc X (iΔ t) :=
    fun t => wpU_succ_sub δ k t
  have cΔU : ∀ t ∈ S, ∀ u ∈ S, (t = u ∨ 2 * radius k ≤ ‖t - u‖) →
      incCov t (radius (k + 1)) t (radius k) u (radius k) 0 δ = 0 := by
    intro t ht u hu htu
    simp only [incCov]
    rw [hin t ht _ hr1 hr1k, hin t ht _ hr le_rfl]
    rcases htu with rfl | htu
    · rw [hsame, circCov_same hr hr, max_self]; ring
    · rw [hfar t u htu _ _ hr1 hr1k hr le_rfl, hfar t u htu _ _ hr le_rfl hr le_rfl]; ring
  have cΔΔ : ∀ t u : ℂ, 2 * radius k ≤ ‖t - u‖ →
      incCov t (radius (k + 1)) t (radius k) u (radius (k + 1)) u (radius k) = 0 := by
    intro t u htu
    simp only [incCov]
    rw [hfar t u htu _ _ hr1 hr1k hr1 hr1k, hfar t u htu _ _ hr1 hr1k hr le_rfl,
      hfar t u htu _ _ hr le_rfl hr1 hr1k, hfar t u htu _ _ hr le_rfl hr le_rfl]
    ring
  refine ⟨hk, fun t => (incCov t (radius k) 0 δ t (radius k) 0 δ).toNNReal,
    { measU := measurable_wpU hX δ k
      measΔ := (measurable_wpU hX δ (k + 1)).sub (measurable_wpU hX δ k)
      measL := measurable_const
      measw := measurable_const
      lawU := fun t _ => ⟨(measurable_cInc hX _ _ _ _).aemeasurable, (map_cInc hX hr hδ t 0).1⟩
      lawΔ := fun t _ => ?_
      varU := fun t ht => ?_
      varΔ := fun t _ => (Real.coe_toNNReal _ hlog2).le
      indep := fun t ht => ?_
      decor := fun t ht u hu htu => ?_ }⟩
  · rw [eΔ t]
    refine ⟨(measurable_cInc hX _ _ _ _).aemeasurable, ?_⟩
    rw [show incProc X (iΔ t) = cInc X (radius (k + 1)) t (radius k) t from rfl,
      (map_cInc hX hr1 hr t t).1]
    congr 2
    simp only [incCov]
    rw [hsame, hsame', circCov_same hr1 hr1, circCov_same hr hr, max_self, max_self, hr',
      Real.log_div hr.ne' two_ne_zero]
    ring
  · have hL0 : 0 ≤ Real.log (δ / radius k) :=
      Real.log_nonneg (by rw [le_div_iff₀ hr]; linarith)
    rw [Real.coe_toNNReal']
    refine max_le ?_ (by linarith)
    simp only [incCov]
    rw [circCov_same hr hr, max_self, hin t ht _ hr le_rfl, hout0 t ht _ hr le_rfl,
      circCov_same hδ hδ, max_self, Real.log_div hδ.ne' hr.ne']
    linarith
  · have hI := indepFun_incProc hX (fun _ : Unit => iΔ t) (fun _ : Unit => iU t)
      (fun _ _ => cΔU t ht t ht (Or.inl rfl))
    have h2 := hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
    rw [eΔ t, eU t]
    exact h2
  · have hI := indepFun_incProc hX (fun _ : Unit => iΔ t) ![iU t, iU u, iΔ u]
      (fun _ i => by
        fin_cases i
        · exact cΔU t ht t ht (Or.inl rfl)
        · exact cΔU t ht u hu (Or.inr htu)
        · exact cΔΔ t u htu)
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    have h2 := hI.comp (measurable_pi_apply ()) hφ
    have e : (fun ω => (wpU X δ k t ω, wpU X δ k u ω, wpU X δ (k + 1) u ω - wpU X δ k u ω)) =
        (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) ∘
          fun ω i => incProc X (![iU t, iU u, iΔ u] i) ω := by
      funext ω
      exact Prod.ext (congrFun (eU t) ω) (Prod.ext (congrFun (eU u) ω) (congrFun (eΔ u) ω))
    rw [eΔ t, e]
    exact h2

end ConeArea6
end MatedCRTHarmonic.MoTPort
