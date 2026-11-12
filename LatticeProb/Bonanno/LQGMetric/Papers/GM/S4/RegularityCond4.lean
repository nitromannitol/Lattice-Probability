/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.Regularity
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail

/-!
# GM Lemma 4.11: condition 4 (comparison of circle averages) of `ℰ_𝕣`

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11 (`lem-reg-event-prob`),
l. 1986: "By the continuity of the circle average process and the scale invariance of the law of
`h`, modulo additive constant, after possibly further shrinking `a` we can arrange that
condition 4 (comparison of circle averages) holds with probability at least `1 − (1−p)/6`."

GM give no further detail. We follow the argument of the proof of DFGPS Lemma 2.3
(Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380, T:757–768; in Lean
`DFGPS.blk_tail`, `Papers/DFGPS/L2_3Tail.lean`): for a jointly continuous version `H` of the
circle-average process (D60), the field `x ↦ H_𝕣(𝕣x) − H_𝕣(0)`, `|x| ≤ ρ`, is a continuous
centered Gaussian field whose variances and increment variances are bounded independently of `𝕣`
(scale invariance, `IsCircleAvgVersion.variance_sub`, `integral_sq_sub`), so the chaining bound
for `E sup` (`SupTail.integral_iSup_family_le`) and the Borell–TIS inequality (Adler–Taylor,
*Random Fields and Geometry*, Thm 2.1.1; `SupTail.tail_iSup_abs_le`) give a Gaussian tail of
`sup_{z ∈ 𝕣V} |h_𝕣(z) − h_𝕣(0)|` uniform in `𝕣` (as in DFGPS, the uniformity is checked on the
covariance bounds rather than through the law of `h`; DEVIATIONS: DEV-DFGPS-2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the index set `cl B_ρ(0)` of the rescaled circle-average field -/
abbrev C4Idx (ρ : ℝ) : Type := ↥(Metric.closedBall (0 : ℂ) ρ)

instance (ρ : ℝ) : CompactSpace (C4Idx ρ) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- the field `x ↦ H_𝕣(𝕣x) − H_𝕣(0)` -/
def c4Fld {Ω' : Type*} (H : ℝ → ℂ → Ω' → ℝ) (𝕣 ρ : ℝ) (t : C4Idx ρ) (ω : Ω') : ℝ :=
  H 𝕣 ((𝕣 : ℂ) * t.1) ω - H 𝕣 0 ω

/-- the coordinates `(Re x, Im x)` -/
def c4Par {ρ : ℝ} (t : C4Idx ρ) : Fin 2 → ℝ := ![t.1.re, t.1.im]

theorem c4_norm_le {ρ : ℝ} (t t' : C4Idx ρ) : ‖t.1 - t'.1‖ ≤ 2 * ‖c4Par t - c4Par t'‖ := by
  unfold c4Par
  have n0 := norm_le_pi_norm (![t.1.re, t.1.im] - ![t'.1.re, t'.1.im]) 0
  have n1 := norm_le_pi_norm (![t.1.re, t.1.im] - ![t'.1.re, t'.1.im]) 1
  simp only [Pi.sub_apply, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one] at n0 n1
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  linarith

theorem c4Par_diam {ρ : ℝ} (hρ : 0 ≤ ρ) (t t' : C4Idx ρ) : ‖c4Par t - c4Par t'‖ ≤ 2 * ρ := by
  have hz : ‖t.1‖ ≤ ρ := mem_closedBall_zero_iff.1 t.2
  have hz' : ‖t'.1‖ ≤ ρ := mem_closedBall_zero_iff.1 t'.2
  have a1 := Complex.abs_re_le_norm t.1; have a2 := Complex.abs_re_le_norm t'.1
  have a3 := Complex.abs_im_le_norm t.1; have a4 := Complex.abs_im_le_norm t'.1
  have b1 := abs_le.1 a1; have b2 := abs_le.1 a2; have b3 := abs_le.1 a3; have b4 := abs_le.1 a4
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i <;> simp only [c4Par, Pi.sub_apply, Real.norm_eq_abs, abs_le] <;>
    simp <;> constructor <;> linarith

/-- the uniform bound for `E sup` of the rescaled circle-average field -/
def c4M (ρ : ℝ) : ℝ := 20 * Real.sqrt 5 * 2 * Real.sqrt ((2 + 1) * (2 * ρ))

section Field
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ}

/-- **Gaussian tail of `sup_{|x| ≤ ρ} |H_𝕣(𝕣x) − H_𝕣(0)|`, uniformly in `𝕣`** (the argument of
DFGPS Lemma 2.3, T:757–768, at the scale `𝕣`). -/
theorem gm_c4_tail (hh : IsWholePlaneGFF h P) (hH : DFGPS.IsCircleAvgVersion h P H) {ρ : ℝ}
    (hρ : 0 < ρ) {𝕣 : ℝ} (h𝕣 : 0 < 𝕣) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | c4M ρ + u ≤ ⨆ t : C4Idx ρ, |c4Fld H 𝕣 ρ t ω|} ≤
      2 * Real.exp (-u ^ 2 / (2 * Real.sqrt (2 * ρ) ^ 2)) := by
  have : Nonempty (C4Idx ρ) := ⟨⟨0, Metric.mem_closedBall_self hρ.le⟩⟩
  set f : C4Idx ρ → CircleAvg.IncIdx := fun t =>
    ((⟨𝕣, h𝕣⟩, (𝕣 : ℂ) * t.1), (⟨𝕣, h𝕣⟩, 0)) with hf
  have hG : IsGaussianProcess (fun t : C4Idx ρ => c4Fld H 𝕣 ρ t) P :=
    hH.isGaussianProcess hh f
  have h0 : ∀ t : C4Idx ρ, ∫ ω, c4Fld H 𝕣 ρ t ω ∂P = 0 := fun t =>
    hH.integral_sub hh h𝕣 h𝕣 _ _
  have hc : ∀ ω, Continuous fun t : C4Idx ρ => c4Fld H 𝕣 ρ t ω := by
    intro ω
    have hg : Continuous fun t : C4Idx ρ => (𝕣, (𝕣 : ℂ) * t.1) :=
      continuous_const.prodMk (continuous_const.mul continuous_subtype_val)
    exact ((hH.cont ω).comp_continuous hg fun _ => ⟨h𝕣, mem_univ _⟩).sub continuous_const
  have hvar : ∀ t : C4Idx ρ, Var[c4Fld H 𝕣 ρ t; P] ≤ Real.sqrt (2 * ρ) ^ 2 := by
    intro t
    rw [Real.sq_sqrt (by positivity)]
    refine (hH.variance_sub hh h𝕣 h𝕣 _ _).trans ?_
    have hz : ‖t.1‖ ≤ ρ := mem_closedBall_zero_iff.1 t.2
    rw [sub_self, abs_zero, zero_add, min_self, sub_zero, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h𝕣, mul_div_cancel_left₀ _ h𝕣.ne']
    linarith
  have hincr : ∀ t t' : C4Idx ρ, ∫ ω, (c4Fld H 𝕣 ρ t ω - c4Fld H 𝕣 ρ t' ω) ^ 2 ∂P ≤
      2 ^ 2 * ‖c4Par t - c4Par t'‖ := by
    intro t t'
    have e : (fun ω => (c4Fld H 𝕣 ρ t ω - c4Fld H 𝕣 ρ t' ω) ^ 2) =
        fun ω => (H 𝕣 ((𝕣 : ℂ) * t.1) ω - H 𝕣 ((𝕣 : ℂ) * t'.1) ω) ^ 2 := by
      funext ω; simp only [c4Fld]; ring
    rw [e]
    refine (hH.integral_sq_sub hh h𝕣 h𝕣 _ _).trans ?_
    rw [sub_self, abs_zero, zero_add, min_self, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos h𝕣, mul_div_cancel_left₀ _ h𝕣.ne']
    have := c4_norm_le t t'
    linarith
  have hesup : ∀ s : ℝ, (s = 1 ∨ s = -1) →
      Integrable (fun ω => ⨆ t : C4Idx ρ, s * c4Fld H 𝕣 ρ t ω) P ∧
        ∫ ω, (⨆ t : C4Idx ρ, s * c4Fld H 𝕣 ρ t ω) ∂P ≤ c4M ρ := by
    intro s hs
    have hGs : IsGaussianProcess (fun (t : C4Idx ρ) ω => s * c4Fld H 𝕣 ρ t ω) P := by
      simpa using hG.smul (fun _ => s)
    refine SupTail.integrable_iSup_of_continuous hGs (fun ω => continuous_const.mul (hc ω))
      fun n t => ?_
    refine SupTail.integral_iSup_family_le hGs (fun t => by
        rw [integral_const_mul, h0, mul_zero]) (Nat.succ_pos n) t
      (c4Par (ρ := ρ)) (by norm_num) (fun i j => c4Par_diam hρ.le _ _) fun i j => ?_
    have e : (fun ω => (s * c4Fld H 𝕣 ρ (t i) ω - s * c4Fld H 𝕣 ρ (t j) ω) ^ 2) =
        fun ω => (c4Fld H 𝕣 ρ (t i) ω - c4Fld H 𝕣 ρ (t j) ω) ^ 2 := by
      funext ω
      rcases hs with rfl | rfl <;> ring
    rw [e]
    exact hincr _ _
  obtain ⟨i1, e1⟩ := hesup 1 (Or.inl rfl)
  obtain ⟨i2, e2⟩ := hesup (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at i1 e1 i2 e2
  exact SupTail.tail_iSup_abs_le hG h0 hc i1 i2 e1 e2 hvar hu

/-- `2 e^{−y} ≤ 2/y` for `y > 0` -/
theorem gm_two_exp_neg_le {y : ℝ} (hy : 0 < y) : 2 * Real.exp (-y) ≤ 2 / y := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [le_div_iff₀ hy]
  have := Real.exp_pos (-y)
  nlinarith

/-- **GM Lemma 4.11, condition 4** (l. 1986): with `H` a jointly continuous version of the
circle-average process (D60), condition 4 of `ℰ_𝕣` holds with probability `→ 1` as `a → 0`,
uniformly in `𝕣`. -/
theorem gm_regC4_prob {V : Set ℂ} (hV : Bornology.IsBounded V) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ), IsWholePlaneGFF h P →
      DFGPS.IsCircleAvgVersion h P H → ∀ R : RegPar, R.V = V → RegCondAt P (regC4 H R) q a₀ := by
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  set ρ := max ρ₀ 1 with hρdef
  have hρ : 0 < ρ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hVρ : V ⊆ Metric.closedBall 0 ρ :=
    hρ₀.trans (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
      (le_max_left _ _)))
  have hM0 : 0 ≤ c4M ρ := by unfold c4M; positivity
  intro q hq
  have hq' : 0 < 1 - q := by linarith
  set u₀ : ℝ := 8 * ρ / (1 - q) + 1 with hu₀
  have h8 : 0 ≤ 8 * ρ / (1 - q) := by positivity
  have hu₀1 : 1 ≤ u₀ := by rw [hu₀]; linarith
  refine ⟨(c4M ρ + u₀)⁻¹, by positivity, ?_⟩
  intro Ω _ P _ h H hh hH R hRV
  subst hRV
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have hainv : c4M ρ + u₀ ≤ a⁻¹ := by
    rw [le_inv_comm₀ (by positivity) ha0]; exact ha
  set u : ℝ := a⁻¹ - c4M ρ with hudef
  have hu1 : u₀ ≤ u := by rw [hudef]; linarith
  have hu0 : 0 < u := by linarith
  have hsub : (regC4 H R 𝕣 a)ᶜ ⊆
      {ω | c4M ρ + u ≤ ⨆ t : C4Idx ρ, |c4Fld H 𝕣 ρ t ω|} := by
    intro ω hω
    simp only [regC4, mem_compl_iff, mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨_, ⟨x, hx, rfl⟩, hlt⟩ := hω
    simp only [mem_ofPred_eq]
    have hbdd : BddAbove (range fun t : C4Idx ρ => |c4Fld H 𝕣 ρ t ω|) := by
      have hc : Continuous fun t : C4Idx ρ => |c4Fld H 𝕣 ρ t ω| := by
        have hg : Continuous fun t : C4Idx ρ => (𝕣, (𝕣 : ℂ) * t.1) :=
          continuous_const.prodMk (continuous_const.mul continuous_subtype_val)
        exact (((hH.cont ω).comp_continuous hg fun _ => ⟨h𝕣, mem_univ _⟩).sub
          continuous_const).abs
      exact (isCompact_range hc).bddAbove
    have := le_ciSup hbdd ⟨x, hVρ hx⟩
    simp only [c4Fld] at this ⊢
    rw [hudef]; linarith
  have htail := gm_c4_tail hh hH hρ h𝕣 hu0.le
  rw [Real.sq_sqrt (by positivity)] at htail
  have hy : 0 < u ^ 2 / (2 * (2 * ρ)) := by positivity
  have h2 := gm_two_exp_neg_le hy
  rw [neg_div] at htail
  have hfin : 2 / (u ^ 2 / (2 * (2 * ρ))) ≤ 1 - q := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    have hu2 : u₀ ≤ u ^ 2 := by nlinarith
    have : 8 * ρ / (1 - q) ≤ u₀ := by rw [hu₀]; linarith
    rw [div_le_iff₀ hq'] at this
    nlinarith
  calc P (regC4 H R 𝕣 a)ᶜ ≤ P {ω | c4M ρ + u ≤ ⨆ t : C4Idx ρ, |c4Fld H 𝕣 ρ t ω|} :=
        measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | c4M ρ + u ≤ ⨆ t : C4Idx ρ, |c4Fld H 𝕣 ρ t ω|}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (1 - q) := ENNReal.ofReal_le_ofReal (by linarith)

end Field

end LQGMetric.GM
