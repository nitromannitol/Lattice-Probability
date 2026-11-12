/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.WeylLower at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Length
import LatticeProb.Bonanno.LQGMetric.Metric.WeylCont

/-!
# LFPP Weyl identity, first half: `e^{ξψ}·D^φ ≤ D^{φ+ψ}`

Task P2-LFPP, item 3 (DFGPS.S5, `lqg-metric-estimates-final.tex`; Weyl scaling GM (1.6),
`uniqueness-final.tex` l. 300–302). For continuous `φ` and `ψ`, the Weyl scaling of the LFPP
metric `D^φ` by `e^{ξψ}` is at most the LFPP metric with density `e^{ξ(φ+ψ)}`: on a fine
partition of a piecewise C¹ path, `(e^{ξψ}·D^φ)(P(t_i), P(t_{i+1})) ≤ e^{ξψ(P(t_i)) + ω}
len(P|[t_i,t_{i+1}]; D^φ)` (`weylScaleOn_le_of_le`, internal metrics) and
`len(P|[s,t]; D^φ) ≤ ∫_s^t e^{ξφ(P)}|P'|` (`len_le_lfppLen`). Own elementary argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

open MetricGeometry

variable {ξ : ℝ} {φ : ℂ → ℝ}

/-- chain form of a triangle inequality -/
theorem le_sum_of_triangle (d : ℂ → ℂ → ℝ≥0∞) (hself : ∀ x, d x x = 0)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) (v : ℕ → ℂ) (N : ℕ) :
    d (v 0) (v N) ≤ ∑ i ∈ Finset.range N, d (v i) (v (i + 1)) := by
  induction N with
  | zero => simp [hself]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    exact (htri _ (v N) _).trans (add_le_add ih le_rfl)

theorem lenDens_add (ξ : ℝ) (φ ψ : ℂ → ℝ) (P : ℝ → ℂ) (s : ℝ) :
    lenDens ξ (fun x => φ x + ψ x) P s =
      ENNReal.ofReal (Real.exp (ξ * ψ (P s))) * lenDens ξ φ P s := by
  unfold lenDens
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_add, Real.exp_add]
  ring_nf

/-- Weyl cost of a sub-path on which `ξ ψ ≤ b`. -/
theorem weylScale_le_piece (hφ : Continuous φ) (ψ : C(ℂ, ℝ)) {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) {b : ℝ}
    (hb : ∀ τ ∈ Icc s t, ξ * ψ (P τ) ≤ b) :
    weylScale ξ ψ (lfppContMetric ξ φ hφ) (P s) (P t) ≤
      ENNReal.ofReal (Real.exp b) * ∫⁻ τ in Icc s t, lenDens ξ φ P τ := by
  set D := lfppContMetric ξ φ hφ
  set U : Set ℂ := {x | ξ * ψ x ≤ b}
  calc weylScale ξ ψ D (P s) (P t) ≤ weylScaleOn ξ ψ D U (P s) (P t) := weylScale_le_weylScaleOn
    _ ≤ ENNReal.ofReal (Real.exp b) * D.internal U (P s) (P t) :=
        weylScaleOn_le_of_le fun x hx => hx
    _ ≤ ENNReal.ofReal (Real.exp b) * D.len P s t := by
        gcongr
        exact internalEDist_le_curveLength (P := D.pt ∘ P) hst
          ((ContMetric.continuous_pt D).comp_continuousOn
            (hP.continuousOn.mono (Icc_subset_Icc hs ht)))
          fun τ hτ => ⟨P τ, hb τ hτ, rfl⟩
    _ ≤ ENNReal.ofReal (Real.exp b) * ∫⁻ τ in Icc s t, lenDens ξ φ P τ := by
        gcongr
        exact len_le_lfppLen hφ hP hs ht

/-- **`e^{ξψ}·D^φ ≤ D^{φ+ψ}`.** -/
theorem weylScale_le_lfppD (hφ : Continuous φ) (ψ : C(ℂ, ℝ)) (z w : ℂ) :
    weylScale ξ ψ (lfppContMetric ξ φ hφ) z w ≤ lfppD ξ (fun x => φ x + ψ x) z w := by
  refine le_iInf fun P => ?_
  obtain ⟨P, hP, -⟩ := P
  show _ ≤ lfppLen ξ (fun x => φ x + ψ x) P
  set L := lfppLen ξ (fun x => φ x + ψ x) P
  set D := lfppContMetric ξ φ hφ
  -- the bound `≤ e^{2ω} L` for every `ω > 0`
  have key : ∀ ω : ℝ, 0 < ω → weylScale ξ ψ D z w ≤ ENNReal.ofReal (Real.exp (2 * ω)) * L := by
    intro ω hω
    have hgc : ContinuousOn (fun s => ξ * ψ (P s)) (Icc 0 1) :=
      (continuous_const.mul ψ.continuous).comp_continuousOn hP.continuousOn
    obtain ⟨τ, hτ, hτg⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous hgc) ω hω
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hτ
    set t : ℕ → ℝ := fun i => i / ((N : ℝ) + 1)
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have ht_mono : Monotone t := fun i j hij => by simp only [t]; gcongr
    have ht_mem : ∀ i, i ≤ N + 1 → t i ∈ Icc (0 : ℝ) 1 := fun i hi => by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one hN1]; exact_mod_cast hi
    have ht0 : t 0 = 0 := by simp [t]
    have ht1 : t (N + 1) = 1 := by simp only [t]; push_cast; exact div_self hN1.ne'
    have ht_step : ∀ i, t (i + 1) - t i = 1 / ((N : ℝ) + 1) := fun i => by
      simp only [t]; push_cast; ring
    have hchain := le_sum_of_triangle (weylScale ξ ψ D) weylScale_self weylScale_triangle
      (fun i => P (t i)) (N + 1)
    simp only [ht0, ht1, hP.source, hP.target] at hchain
    refine hchain.trans ?_
    have hpiece : ∀ i, i ≤ N → weylScale ξ ψ D (P (t i)) (P (t (i + 1))) ≤
        ∫⁻ s in Ioc (t i) (t (i + 1)),
          ENNReal.ofReal (Real.exp (2 * ω)) * lenDens ξ (fun x => φ x + ψ x) P s := by
      intro i hi
      have hti := ht_mem i (by omega)
      have hti1 := ht_mem (i + 1) (by omega)
      have hclose : ∀ s ∈ Icc (t i) (t (i + 1)), |ξ * ψ (P s) - ξ * ψ (P (t i))| < ω := by
        intro s hs
        have := hτg s ⟨hti.1.trans hs.1, hs.2.trans hti1.2⟩ _ hti (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
          linarith [hs.2, ht_step i])
        rwa [Real.dist_eq] at this
      refine (weylScale_le_piece hφ ψ hP hti.1 (ht_mono (Nat.le_succ i)) hti1.2
        (b := ξ * ψ (P (t i)) + ω) fun s hs => by
          linarith [(abs_lt.1 (hclose s hs)).2]).trans ?_
      rw [setLIntegral_congr Ioc_ae_eq_Icc, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
      rw [lenDens_add, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)) le_rfl
      linarith [(abs_lt.1 (hclose s hs)).1]
    refine (Finset.sum_le_sum fun i hi =>
      hpiece i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))).trans ?_
    rw [sum_setLIntegral_Ioc _ t ht_mono, ht0, ht1,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_right (lintegral_mono_set Ioc_subset_Icc_self) _
  have hT : Tendsto (fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω)) * L) (𝓝[>] 0) (𝓝 L) := by
    have hc : Continuous fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω)) :=
      ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have h1 : Tendsto (fun ω : ℝ => ENNReal.ofReal (Real.exp (2 * ω))) (𝓝[>] 0) (𝓝 1) := by
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero)
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ω hω => key ω hω)

end LFPP
end LQGMetric
