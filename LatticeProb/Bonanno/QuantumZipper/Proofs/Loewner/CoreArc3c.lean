/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc3c at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3b

/-!
# CORE_ARC, part 3c: no jumps (the analytic core of left continuity of `arcTime`)

Plan node "No jump (left continuity)" of `blueprint/CORE_ARC_PLAN.md`.

## Main result

* `no_jump`: let `A` be continuous with `A 0 = 0`, `0 < s`, `closedBall p R ⊆ ℍ` disjoint from
  every `K_{s'}`, `s' ∈ [0,s)`, with `p` an accumulation point of `K_s` and a point
  `q ∈ ball p R \ K_s`. Then `False`.

## Proof

`g := 0` on `K_s` and `g := f_s` off `K_s`. Along `σ n = s - s/(n+2) ↑ s`, `f_{σ n} → g`
pointwise on the closed disc (`tendsto_fwdMap_nhdsLT_of_mem`, `tendsto_fwdMap_nhdsLT_of_notMem`),
and `‖f_{σ n}‖ ≤ C` there (UB, `norm_fwdMap_sub_le_uniform`). Each `f_{σ n}` is holomorphic on
the closed disc, so it is given by its Cauchy integral; dominated convergence passes this to
`g`, so `g` equals the Cauchy integral of `g` on the open disc and is analytic there
(`hasFPowerSeriesOn_cauchy_integral`). It vanishes on `K_s`, which accumulates at `p`, so it
vanishes on the disc (identity theorem), but `g q = f_s q ∈ ℍ`.

## Sources

Route of `blueprint/CORE_ARC_PLAN.md`, the project's own: no published proof of this direction
(Loewner hulls of an arc are its initial subarcs, with continuous parametrisation) in this
form was found (see `handoff/CORE-2.md`). The analytic tools are standard mathlib results (Cauchy
integral formula, power series of Cauchy integrals, dominated convergence, identity theorem).
Own elementary proof of the assembly (a Vitali-type limit argument).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory Complex
open scoped Real NNReal ENNReal

namespace QuantumZipper

namespace CoreArc

variable {A : ℝ → ℝ}

/-- **No jump.** A closed disc in `ℍ` that is disjoint from every `K_{s'}`, `s' < s`, cannot
meet `K_s` in a set accumulating at its centre while also containing a point off `K_s`. -/
theorem no_jump (hA : Continuous A) (hA0 : A 0 = 0) {s R : ℝ} {p q : ℂ} (hs : 0 < s)
    (hR : 0 < R) (hB : closedBall p R ⊆ H)
    (hdisj : ∀ s' ∈ Ico (0 : ℝ) s, ∀ z ∈ closedBall p R, z ∉ fwdHull A s')
    (hacc : ∃ᶠ z in 𝓝[≠] p, z ∈ fwdHull A s) (hq : q ∈ ball p R)
    (hqK : q ∉ fwdHull A s) : False := by
  classical
  set g : ℂ → ℂ := fun z => if z ∈ fwdHull A s then 0 else fwdMap A s z with hg
  set σ : ℕ → ℝ := fun n => s - s / ((n : ℝ) + 2) with hσ
  have hσ_mem : ∀ n, σ n ∈ Ioo (0 : ℝ) s := by
    intro n
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    have h3 : s / ((n : ℝ) + 2) < s := div_lt_self hs (by linarith [n.cast_nonneg (α := ℝ)])
    have h4 : 0 < s / ((n : ℝ) + 2) := div_pos hs h2
    exact ⟨by simp only [hσ]; linarith, by simp only [hσ]; linarith⟩
  have hσt : Tendsto σ atTop (𝓝[<] s) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hσ_mem n).2⟩
    have h := (tendsto_const_div_atTop_nhds_zero_nat s).comp (tendsto_add_atTop_nat 2)
    have h' : Tendsto (fun n : ℕ => s / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine h.congr fun n => ?_
      simp
    simpa [hσ] using (tendsto_const_nhds (x := s)).sub h'
  have hlim : ∀ z ∈ closedBall p R,
      Tendsto (fun n => fwdMap A (σ n) z) atTop (𝓝 (g z)) := by
    intro z hz
    by_cases hzK : z ∈ fwdHull A s
    · simp only [hg, hzK, ↓reduceIte]
      exact (tendsto_fwdMap_nhdsLT_of_mem hA hs hzK fun s' hs' => hdisj s' hs' z hz).comp hσt
    · simp only [hg, hzK, ↓reduceIte]
      exact (tendsto_fwdMap_nhdsLT_of_notMem hA hs ⟨hB hz, hzK⟩).comp hσt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.continuousOn (s := Icc 0 s))
  set C := ‖p‖ + R + (24 * M + 8 * Real.sqrt s) with hC
  have hbound : ∀ n, ∀ z ∈ closedBall p R, ‖fwdMap A (σ n) z‖ ≤ C := by
    intro n z hz
    have hn := hσ_mem n
    have h1 := norm_fwdMap_sub_le_uniform hA hA0 hn.1
      (fun t ht => (Real.norm_eq_abs _).symm.trans_le (hM t ⟨ht.1, ht.2.trans hn.2.le⟩))
      ⟨hB hz, hdisj _ ⟨hn.1.le, hn.2⟩ z hz⟩
    have h2 : Real.sqrt (σ n) ≤ Real.sqrt s := Real.sqrt_le_sqrt hn.2.le
    have h3 : ‖z - p‖ ≤ R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hz
    have h4 := norm_le_insert' z p
    have h5 := norm_le_insert' (fwdMap A (σ n) z) z
    linarith
  have hgbound : ∀ z ∈ closedBall p R, ‖g z‖ ≤ C := fun z hz =>
    le_of_tendsto' (hlim z hz).norm fun n => hbound n z hz
  have hdiff : ∀ n, DifferentiableOn ℂ (fwdMap A (σ n)) (closedBall p R) := fun n =>
    (FwdHolo.differentiableOn_fwdMap hA (hσ_mem n).1.le).mono fun z hz =>
      ⟨hB hz, hdisj _ ⟨(hσ_mem n).1.le, (hσ_mem n).2⟩ z hz⟩
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hcirc : ∀ θ, circleMap p R θ ∈ closedBall p R := circleMap_mem_closedBall p hR0
  have hgC : CircleIntegrable g p R := by
    rw [circleIntegrable_def, intervalIntegrable_iff, uIoc_of_le Real.two_pi_pos.le]
    refine IntegrableOn.of_bound measure_Ioc_lt_top ?_ C (ae_of_all _ fun θ => hgbound _ (hcirc θ))
    exact aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n θ => fwdMap A (σ n) (circleMap p R θ))
      (fun n => ((hdiff n).continuousOn.comp_continuous (continuous_circleMap p R)
        hcirc).aestronglyMeasurable)
      (ae_of_all _ fun θ => hlim _ (hcirc θ))
  have hcauchy : ∀ w ∈ ball p R,
      g w = (2 * π * I : ℂ)⁻¹ • ∮ z in C(p, R), (z - w)⁻¹ • g z := by
    intro w hw
    have hn : ∀ n, (∮ z in C(p, R), (z - w)⁻¹ • fwdMap A (σ n) z) =
        (2 * π * I : ℂ) • fwdMap A (σ n) w :=
      fun n => (hdiff n).circleIntegral_sub_inv_smul hw
    have hT1 : Tendsto (fun n => ∮ z in C(p, R), (z - w)⁻¹ • fwdMap A (σ n) z) atTop
        (𝓝 ((2 * π * I : ℂ) • g w)) := by
      simp_rw [hn]
      exact (hlim w (ball_subset_closedBall hw)).const_smul _
    have hpos : 0 < R - dist w p := sub_pos.2 (mem_ball.1 hw)
    have hsph : ∀ θ, R - dist w p ≤ ‖circleMap p R θ - w‖ := by
      intro θ
      have h1 : dist (circleMap p R θ) p = R := by
        have := circleMap_mem_sphere p hR0 θ
        rwa [mem_sphere] at this
      have h2 := dist_triangle (circleMap p R θ) w p
      rw [← dist_eq_norm]
      linarith
    have hT2 : Tendsto (fun n => ∮ z in C(p, R), (z - w)⁻¹ • fwdMap A (σ n) z) atTop
        (𝓝 (∮ z in C(p, R), (z - w)⁻¹ • g z)) := by
      simp only [circleIntegral]
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun _ => R * ((R - dist w p)⁻¹ * C)) (Eventually.of_forall fun n => ?_)
        (Eventually.of_forall fun n => ae_of_all _ fun θ _ => ?_) intervalIntegrable_const
        (ae_of_all _ fun θ _ => ((hlim _ (hcirc θ)).const_smul _).const_smul _)
      · have hci : CircleIntegrable (fun z => (z - w)⁻¹ • fwdMap A (σ n) z) p R := by
          refine ContinuousOn.circleIntegrable hR0 ?_
          refine ((continuousOn_id.sub continuousOn_const).inv₀ fun z hz => ?_).smul
            ((hdiff n).continuousOn.mono sphere_subset_closedBall)
          intro h0
          have hzw : z = w := sub_eq_zero.1 h0
          rw [hzw, mem_sphere] at hz
          linarith [mem_ball.1 hw]
        exact ((circleIntegrable_iff R).1 hci).aestronglyMeasurable_restrict_uIoc
      · rw [norm_smul, norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I,
          mul_one, abs_of_nonneg hR0, norm_inv]
        have hinv : ‖circleMap p R θ - w‖⁻¹ ≤ (R - dist w p)⁻¹ := inv_anti₀ hpos (hsph θ)
        have hf := hbound n _ (hcirc θ)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul hinv hf (norm_nonneg _) (inv_nonneg.2 hpos.le)) hR0
    have heq := tendsto_nhds_unique hT1 hT2
    rw [← heq, smul_smul, inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  have hRn : (R.toNNReal : ℝ) = R := Real.coe_toNNReal R hR0
  have hgC' : CircleIntegrable g p (R.toNNReal : ℝ) := by rwa [hRn]
  have hps := hasFPowerSeriesOn_cauchy_integral hgC' (Real.toNNReal_pos.2 hR)
  rw [hRn] at hps
  have hanal : AnalyticOnNhd ℂ g (ball p R) := by
    intro w hw
    have hw' : w ∈ Metric.eball p (R.toNNReal : ℝ≥0∞) := by rwa [Metric.eball_coe, hRn]
    exact (hps.analyticAt_of_mem hw').congr
      (Filter.eventually_of_mem (isOpen_ball.mem_nhds hw) fun y hy => (hcauchy y hy).symm)
  have hzero := hanal.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball p R).isPreconnected (mem_ball_self hR)
    (hacc.mono fun z hz => by simp [hg, hz])
  have hgq : g q = 0 := hzero hq
  simp only [hg, hqK, ↓reduceIte] at hgq
  have hqH := FwdHolo.mapsTo_fwdMap hA hs.le ⟨hB (ball_subset_closedBall hq), hqK⟩
  rw [hgq] at hqH
  simp [H] at hqH

end CoreArc

end QuantumZipper
