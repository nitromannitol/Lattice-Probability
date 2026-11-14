/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RLogLen at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.J2EfronStein
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RTransfer

 










set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneA3R_logLen_add_sub_le {ξ : ℝ} {f s : ℂ → ℝ} (hf : Continuous f)
    (hs : Continuous s) {M : ℝ} (hM : ∀ x ∈ (rectAB 1 1).toSet, |s x| ≤ M) :
    |L23.logLen ξ (fun x => f x + s x) - L23.logLen ξ f| ≤ |ξ| * M := by
  have hfs : Continuous fun x => f x + s x := hf.add hs
  have h1 : rectLen ξ (fun x => f x + s x) (rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * rectLen ξ f (rectAB 1 1) :=
    crossLenIn_le_of_abs_sub_le fun x hx => by
      simpa only [add_sub_cancel_left] using hM x hx
  have h2 : rectLen ξ f (rectAB 1 1) ≤
      ENNReal.ofReal (Real.exp (|ξ| * M)) * rectLen ξ (fun x => f x + s x) (rectAB 1 1) :=
    crossLenIn_le_of_abs_sub_le fun x hx => by
      rw [show f x - (f x + s x) = -s x by ring, abs_neg]; exact hM x hx
  have hpos : ∀ g : ℂ → ℝ, Continuous g → 0 < (rectLen ξ g (rectAB 1 1)).toReal := fun g hg =>
    ENNReal.toReal_pos (rectLen_pos (ξ := ξ) (rectAB 1 1)
      (by simp [rectAB, MarkedRect.crossWidth]) hg).ne'
      (rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) hg)
  have hfin : ∀ g : ℂ → ℝ, Continuous g → rectLen ξ g (rectAB 1 1) ≠ ⊤ := fun g hg =>
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) hg
  have hr1 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin f hf)) h1
  have hr2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin _ hfs)) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hr1 hr2
  have l1 := Real.log_le_log (hpos _ hfs) hr1
  have l2 := Real.log_le_log (hpos _ hf) hr2
  rw [Real.log_mul (Real.exp_pos _).ne' (hpos _ hf).ne', Real.log_exp] at l1
  rw [Real.log_mul (Real.exp_pos _).ne' (hpos _ hfs).ne', Real.log_exp] at l2
  unfold L23.logLen
  rw [abs_le]
  constructor <;> linarith

theorem laneA3R_integrable_logLen_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) (K : ℕ)
    {s : ℂ → ℝ} (hs : Continuous s) :
    Integrable (fun ω' => L23.logLen ξ (fun x => psiMN Q W P 0 K x ω' + s x)) P := by
  haveI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  obtain ⟨M, hM⟩ := ((rectAB 1 1).isCompact_toSet.image_of_continuousOn
    (continuous_abs.comp hs).continuousOn).isBounded.bddAbove
  have hM' : ∀ x ∈ (rectAB 1 1).toSet, |s x| ≤ M := fun x hx => hM ⟨x, hx, rfl⟩
  have hint0 : Integrable (L24.logLenPsi ξ Q W P K) P :=
    ((L24.psi_memLp_variance hW Q ξ).choose_spec.2 K).1.integrable one_le_two
  have hmeas : Measurable fun ω' => L23.logLen ξ (fun x => psiMN Q W P 0 K x ω' + s x) := by
    unfold L23.logLen
    refine Real.measurable_log.comp (ENNReal.measurable_toReal.comp ?_)
    exact measurable_crossLenIn (Y := fun x ω' => psiMN Q W P 0 K x ω' + s x)
      (rectAB 1 1).isCompact_toSet (fun ω' => (hψ.cont ω').add hs)
      (fun x => (hψ.meas x).add_const _)
  refine Integrable.mono' (hint0.norm.add (integrable_const (|ξ| * M)))
    hmeas.aestronglyMeasurable (Eventually.of_forall fun ω' => ?_)
  have h := laneA3R_logLen_add_sub_le (ξ := ξ) (hψ.cont ω') hs hM'
  have e : L24.logLenPsi ξ Q W P K ω' = L23.logLen ξ (fun x => psiMN Q W P 0 K x ω') := rfl
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply, Real.norm_eq_abs, e]
  have := abs_sub_abs_le_abs_sub (L23.logLen ξ (fun x => psiMN Q W P 0 K x ω' + s x))
    (L23.logLen ξ (fun x => psiMN Q W P 0 K x ω'))
  linarith

 
theorem laneA3R_fLen_option_eq {ξ : ℝ} {K : ℕ} {y s : ℂ → ℝ} (hy : Continuous y)
    (hs : Continuous s) (v : T20B.nearIdx K → T20B.dyD → ℝ)
    (hv : ∀ c : T20B.dyD, ∑ b, v b c = s c) :
    T20B.fLen ξ (fun o : Option (T20B.nearIdx K) => o.elim (T20B.restrD y) v) =
      L23.logLen ξ (fun x => y x + s x) := by
  apply T20B.fLen_eq (hy.add hs)
  intro c
  rw [Fintype.sum_option]
  simp only [Option.elim, T20B.restrD]
  rw [hv c]
  rfl

theorem laneA3R_ofReal_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hmax : Integrable (fun x => max (f x) 0) μ := hf.pos_part
  calc ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) :=
        ENNReal.ofReal_le_ofReal (integral_mono hf hmax fun x => le_max_left _ _)
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hmax (Eventually.of_forall fun x => le_max_right _ _)
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        congr 1; funext x
        rcases le_total (f x) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

end SupercriticalLQGUniqueness.B2.DG20Conc
