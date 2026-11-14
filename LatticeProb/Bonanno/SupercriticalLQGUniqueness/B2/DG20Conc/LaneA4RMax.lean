/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RMax at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4RRate
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA4BadKernel

 












set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

attribute [local instance] Classical.propDecidable

universe u

 
theorem laneA4R_weight_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    (γ : ℕ → ℕ → Ω → ℝ → ℂ) (n K : ℕ) (b : ℤ × ℤ) (x : Ω) :
    laneA3HitWeight P W hW Q ξ γ n K b x ^ (2 : ℝ) ≤
      ENNReal.ofReal ((lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) x)⁻¹) ^ (2 : ℝ) *
        laneA3Around P W hW Q ξ n K b x ^ (2 : ℝ) := by
  have hψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hLfin : rectLen ξ (fun z => psiMN Q W P 0 n z x) (rectAB 1 1) ≠ ⊤ :=
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) (hψ.cont x)
  have hLpos : 0 < rectLen ξ (fun z => psiMN Q W P 0 n z x) (rectAB 1 1) :=
    rectLen_pos (ξ := ξ) (rectAB 1 1) (by simp [rectAB, MarkedRect.crossWidth]) (hψ.cont x)
  have hLr : 0 < lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) x :=
    ENNReal.toReal_pos hLpos.ne' hLfin
  have hle : laneA3HitWeight P W hW Q ξ γ n K b x ≤
      ENNReal.ofReal ((lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) x)⁻¹) *
        laneA3Around P W hW Q ξ n K b x := by
    have e : laneA3Around P W hW Q ξ n K b x /
        rectLen ξ (fun z => psiMN Q W P 0 n z x) (rectAB 1 1) =
        ENNReal.ofReal ((lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) x)⁻¹) *
          laneA3Around P W hW Q ξ n K b x := by
      rw [ENNReal.ofReal_inv_of_pos hLr, lenObs, ENNReal.ofReal_toReal hLfin, div_eq_mul_inv,
        mul_comm]
    unfold laneA3HitWeight
    by_cases hF : x ∈ laneCEventualHit γ n K (laneBCoarseIndex Q K) b
    · rw [indicator_of_mem hF, e]
    · rw [indicator_of_notMem hF]; exact bot_le
  calc laneA3HitWeight P W hW Q ξ γ n K b x ^ (2 : ℝ)
      ≤ (ENNReal.ofReal ((lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) x)⁻¹) *
          laneA3Around P W hW Q ξ n K b x) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = _ := ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)

 

theorem laneA4_max_condHit_L2_le_of_inputs.{v}
    (hC2 : LaneC2StarAt.{v}) (hInd : LaneFineStarIndepCoarse.{v}) :
  ∀ (Q : PsiParams), Q.ε₀ < 1 / 100 → ∀ (ξ : Ioi (0 : ℝ)) (Qe : ℝ),
  IsLFPPExponent ξ Qe → ∀ p : ℝ, 0 < p → p < 2⁻¹ →
  J1FixedPAt.{v} Q (ξ : ℝ) p → LaneB3Defs.B3FixedPSubaddTails.{v} Q ξ Qe p →
  ∀ C ζ : ℝ, 0 < C → 0 < ζ →
  ∃ K₀ : ℕ,
    ∀ {Ω : Type v} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (n K : ℕ),
      K₀ ≤ K → K ≤ n →
      LambdaN (ξ : ℝ) W P (n - K) (ENNReal.ofReal p) ≤
        Real.exp (C * Real.sqrt (K : ℝ)) →
    ∀ γ : ℕ → ℕ → Ω → ℝ → ℂ,
      (∀ j : ℕ, T20.IsNearGeodSel (ξ : ℝ) Q W P (((j : ℝ) + 1)⁻¹) (γ j)) →
      (∀ j : ℕ, ∀ b : ℤ × ℤ,
        MeasurableSet (laneCHits γ j n K (laneBCoarseIndex Q K) b)) →
      (∫⁻ ω, ((laneSourceIdx Q K).sup (fun b =>
          ∫⁻ x, laneA3HitWeight P W hW Q (ξ : ℝ) γ n K b x
            ∂(condExpKernel P (laneFineStar Q W P K n) ω))) ^ (2 : ℝ) ∂P) ^
          (1 / 2 : ℝ) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (-(hitExponent (ξ : ℝ) Qe - ζ) * (K : ℝ))) := by
  intro Q hε ξ Qe hQe p hp hp2 hJ hB3 C ζ hC hζ
  set ξ' : ℝ := (ξ : ℝ) with hξ'def
  have hξ' : 0 < ξ' := ξ.2
  set ζ₁ := laneA4RSlack ξ' Qe ζ with hζ₁def
  have hζ₁ : 0 < ζ₁ := laneA4RSlack_pos hξ' hζ
  set E₂ : ℝ := (2 : ℝ) ^ 2 * ξ' ^ 2 / 2 - 2 * ξ' * Qe + 1 with hE₂
  set α := hitExponent ξ' Qe with hαdef
  set M := 2 * E₂ + 4 * |α| + 4 * ζ + 8 with hMdef
  obtain ⟨KB, cB₀, cB₁, hcB₀, hcB₁, hB3t⟩ := hB3 ζ₁ C hζ₁ hC
  obtain ⟨C₀, c₀, KJ, hC₀, hc₀, hJr⟩ := j1FixedPAt_roundCut Q ξ' p hJ C hC.le
  obtain ⟨KC, hC2t⟩ := hC2 Q hε ξ Qe hQe p hp hp2 hJ hB3 C 2 1 hC two_pos one_pos
  obtain ⟨KS1, hKS1⟩ := laneA4R_superexp_rate (c := cB₀) (c' := cB₁) (M := M) hcB₀ hcB₁
    Q.ε₀_pos hε
  obtain ⟨KS2, hKS2⟩ := laneA4R_superexp_rate (c := C₀) (c' := c₀) (M := M) hC₀ hc₀
    Q.ε₀_pos hε
  obtain ⟨KF, hKF1, hKF⟩ := laneA4R_final_rate (ξ := ξ') (Q := Qe) (ζ := ζ) (E := E₂) hξ' hζ
  refine ⟨max 8 (max (max KB KJ) (max KC (max KS1 (max KS2 KF)))), ?_⟩
  intro Ω _ _ P _ W hW n K hK hKn hH γ hγ hhits
  have hK8 : 8 ≤ K := (le_max_left _ _).trans hK
  have hKB : KB ≤ K := by omega
  have hKJ : KJ ≤ K := by omega
  have hKC : KC ≤ K := by omega
  have hKS1' : KS1 ≤ K := by omega
  have hKS2' : KS2 ≤ K := by omega
  have hKF' : KF ≤ K := by omega
  have hε1 : Q.ε₀ ≤ 1 := by linarith
  set I := laneSourceIdx Q K with hIdef
  have hm := laneFineStar_le hW Q hKn
  set κ := condExpKernel P (laneFineStar Q W P K n) with hκ
  
  by_cases hI : I.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hI
    simp only [hI, Finset.sup_empty, ENNReal.bot_eq_zero]
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2), lintegral_zero,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact bot_le
  set E := laneA4RGood Q ξ' Qe ζ₁ P W hW n K with hEdef
  have hEm : MeasurableSet E := laneA4RGood_measurableSet Q ξ' Qe ζ₁ P W hW n K
  have hEsub : E ⊆ laneA4Regular Q ξ' Qe ζ₁ P W hW n K := laneA4RGood_subset Q ξ' Qe ζ₁ P W hW n K
  set Y : ℤ × ℤ → Ω → ℝ≥0∞ := fun b => laneA3HitWeight P W hW Q ξ' γ n K b with hYdef
  have hYae : ∀ b, AEMeasurable (Y b) P := fun b =>
    laneA3HitWeight_aemeasurable P W hW Q ξ' γ n K b (fun j => hhits j b)
  set Yh : ℤ × ℤ → Ω → ℝ≥0∞ := fun b => (hYae b).mk (Y b)
  have hYhm : ∀ b, Measurable (Yh b) := fun b => (hYae b).measurable_mk
  have hYeq : ∀ b, Y b =ᵐ[P] Yh b := fun b => (hYae b).ae_eq_mk
  set F : ℤ × ℤ → Set Ω := fun b => laneCEventualHit γ n K (laneBCoarseIndex Q K) b
  set β := Qe + (ζ₁ + 2 * (K : ℝ) ^ (-(1 / 3 : ℝ))) / ξ' with hβ
  set τ := (2 : ℝ) ^ ((K : ℝ) ^ (2 / 3 : ℝ)) with hτ
  set gr : ℝ := τ ^ 2 * (2 : ℝ) ^ ((ζ₁ - ξ' * Qe) * K) *
    Real.exp ((ξ' * min ξ' β - (min ξ' β) ^ 2 / 2) * ((K : ℝ) * Real.log 2)) with hgr
  have hgr0 : 0 ≤ gr := by positivity
  set g : ℝ≥0∞ := ENNReal.ofReal gr with hg
  
  have hgood : ∀ᵐ ω ∂P, ∀ b ∈ I, ∫⁻ x, (F b ∩ E).indicator (Y b) x ∂(κ ω) ≤ g := by
    apply (Filter.eventually_all_finset I).2
    intro b hb
    have h := laneA4R_good_conditional_gaussian_le_of_indep P W hW hm K b ξ' β
      (laneA4R_indep_point_fineStar hInd P W hW Q hKn b) (F b) E (Y b)
      (ENNReal.ofReal (τ ^ 2 * (2 : ℝ) ^ ((ζ₁ - ξ' * Qe) * K)))
      (fun ω hω => laneA4_hit_truncation_source Q hε1 ξ' Qe ζ₁ hξ' P W hW n K hK8 hKn γ hγ b hb
        ⟨hω.1, hEsub hω.2⟩)
      (fun ω hω => laneA4R_weight_le_of_regular hW Q ξ' Qe ζ₁ γ n K b hb ω (hEsub hω))
    filter_upwards [h] with ω hω
    refine hω.trans (le_of_eq ?_)
    rw [hg, hgr]
    exact (ENNReal.ofReal_mul (by positivity)).symm
  
  have hsplit : ∀ b ω, ∫⁻ x, Y b x ∂(κ ω) =
      ∫⁻ x, (F b ∩ E).indicator (Y b) x ∂(κ ω) + ∫⁻ x, Eᶜ.indicator (Y b) x ∂(κ ω) := by
    intro b ω
    rw [← lintegral_add_compl (Y b) hEm, ← lintegral_indicator hEm, ← lintegral_indicator hEm.compl]
    congr 2
    funext x
    by_cases hxE : x ∈ E
    · by_cases hxF : x ∈ F b
      · rw [indicator_of_mem hxE, indicator_of_mem (show x ∈ F b ∩ E from ⟨hxF, hxE⟩)]
      · rw [indicator_of_mem hxE, indicator_of_notMem (fun h => hxF h.1)]
        simp only [Y, laneA3HitWeight]
        exact indicator_of_notMem hxF _
    · rw [indicator_of_notMem hxE, indicator_of_notMem (fun h => hxE h.2)]
  have hbadeq : ∀ᵐ ω ∂P, ∀ b ∈ I,
      ∫⁻ x, Eᶜ.indicator (Y b) x ∂(κ ω) = ∫⁻ x, Eᶜ.indicator (Yh b) x ∂(κ ω) := by
    apply (Filter.eventually_all_finset I).2
    intro b _
    have hI1 : Eᶜ.indicator (Y b) =ᵐ[P] Eᶜ.indicator (Yh b) :=
      (hYeq b).mono fun x hx => by
        show Eᶜ.indicator (Y b) x = Eᶜ.indicator (Yh b) x
        by_cases h : x ∈ Eᶜ
        · rw [indicator_of_mem h, indicator_of_mem h, hx]
        · rw [indicator_of_notMem h, indicator_of_notMem h]
    filter_upwards [laneC_conditional_lintegral_mono_ae P hm hI1.le,
      laneC_conditional_lintegral_mono_ae P hm hI1.symm.le] with ω h1 h2
    exact le_antisymm h1 h2
  set Bsup : Ω → ℝ≥0∞ := fun ω => I.sup' hI (fun b => ∫⁻ x, Eᶜ.indicator (Yh b) x ∂(κ ω))
  have hpoint : ∀ᵐ ω ∂P, (I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω))) ^ (2 : ℝ) ≤
      2 * (g ^ (2 : ℝ) + Bsup ω ^ (2 : ℝ)) := by
    filter_upwards [hgood, hbadeq] with ω hg' hb'
    have hle : I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω)) ≤ g + Bsup ω := by
      apply Finset.sup_le
      intro b hb
      rw [hsplit b ω, hb' b hb]
      exact add_le_add (hg' b hb) (Finset.le_sup' (fun b => ∫⁻ x, Eᶜ.indicator (Yh b) x ∂(κ ω)) hb)
    calc (I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω))) ^ (2 : ℝ) ≤ (g + Bsup ω) ^ (2 : ℝ) :=
          ENNReal.rpow_le_rpow hle (by norm_num)
      _ ≤ 2 ^ ((2 : ℝ) - 1) * (g ^ (2 : ℝ) + Bsup ω ^ (2 : ℝ)) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ (by norm_num)
      _ = 2 * (g ^ (2 : ℝ) + Bsup ω ^ (2 : ℝ)) := by norm_num
  
  set δ : ℝ≥0∞ := 4 * ENNReal.ofReal ((2 : ℝ) ^ (-(M * K))) with hδ
  have hτrange : (2 : ℝ) ^ ((K : ℝ) ^ ((1 / 2 : ℝ) + 3 * Q.ε₀)) < τ := by
    have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
    rw [hτ, Real.rpow_lt_rpow_left_iff (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt hK1 (by linarith)
  have hBad : ∀ i : Fin 4, P (laneA4RBad Q ξ' Qe ζ₁ P W hW n K i) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(M * K))) := by
    obtain ⟨hB3lo, hB3hi⟩ := hB3t P W hW n K hKB hKn hH τ hτrange
    obtain ⟨hJlo, hJhi⟩ := hJr P W hW K n hKJ hKn hH τ hτrange
    obtain ⟨hS1a, hS1b⟩ := hKS1 K hKS1'
    obtain ⟨hS2a, hS2b⟩ := hKS2 K hKS2'
    intro i
    fin_cases i
    · exact hB3hi.trans (ENNReal.ofReal_le_ofReal hS1a)
    · exact hB3lo.trans (ENNReal.ofReal_le_ofReal hS1a)
    · exact hJlo.trans (ENNReal.ofReal_le_ofReal hS2b)
    · refine hJhi.trans (ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) hS2a))
      congr 2
      ring
  have hPE : P Eᶜ ≤ δ := by
    calc P Eᶜ ≤ ∑ i : Fin 4, P (laneA4RBad Q ξ' Qe ζ₁ P W hW n K i) :=
          laneA4RGood_compl_le Q ξ' Qe ζ₁ P W hW n K
      _ ≤ ∑ _i : Fin 4, ENNReal.ofReal ((2 : ℝ) ^ (-(M * K))) := Finset.sum_le_sum fun i _ => hBad i
      _ = δ := by simp [hδ]
  set H : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (E₂ * K)) ^ (2 : ℝ) with hHdef
  have hsecond : (∫⁻ ω, (I.sup' hI (fun b =>
      ∫⁻ x, Yh b x ^ (2 : ℝ) ∂(condExpKernel P (laneFineStar Q W P K n) ω))) ^ (2 : ℝ) ∂P) ≤ H := by
    have hC2K := hC2t P W hW n K hKC hKn hH
    have hpt : ∀ᵐ ω ∂P, I.sup' hI (fun b => ∫⁻ x, Yh b x ^ (2 : ℝ) ∂(κ ω)) ≤
        I.sup (fun b => laneCNormalizedAroundProductStar P W hW Q ξ' 2 n K b ω) := by
      have hb : ∀ b ∈ I, ∀ᵐ ω ∂P, ∫⁻ x, Yh b x ^ (2 : ℝ) ∂(κ ω) ≤
          laneCNormalizedAroundProductStar P W hW Q ξ' 2 n K b ω := by
        intro b _
        have hsq : (fun x => Yh b x ^ (2 : ℝ)) ≤ᵐ[P] (fun x =>
            ENNReal.ofReal ((lenObs ξ' (psiMN Q W P 0 n) (rectAB 1 1) x)⁻¹) ^ (2 : ℝ) *
              laneA3Around P W hW Q ξ' n K b x ^ (2 : ℝ)) := by
          filter_upwards [hYeq b] with x hx
          rw [← hx]
          exact laneA4R_weight_sq_le hW Q ξ' γ n K b x
        filter_upwards [laneC_conditional_lintegral_mono_ae P hm hsq] with ω hω
        exact hω
      filter_upwards [(Filter.eventually_all_finset I).2 hb] with ω hω
      rw [Finset.sup'_eq_sup]
      exact Finset.sup_mono_fun hω
    have hint : (∫⁻ ω, (I.sup (fun b =>
        laneCNormalizedAroundProductStar P W hW Q ξ' 2 n K b ω)) ^ (2 : ℝ) ∂P) ≤ H := by
      have h2 := ENNReal.rpow_le_rpow hC2K (by norm_num : (0 : ℝ) ≤ 2)
      rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h2
      exact h2
    calc (∫⁻ ω, (I.sup' hI (fun b =>
          ∫⁻ x, Yh b x ^ (2 : ℝ) ∂(condExpKernel P (laneFineStar Q W P K n) ω))) ^ (2 : ℝ) ∂P)
        ≤ ∫⁻ ω, (I.sup (fun b =>
            laneCNormalizedAroundProductStar P W hW Q ξ' 2 n K b ω)) ^ (2 : ℝ) ∂P :=
          lintegral_mono_ae (hpt.mono fun ω h => ENNReal.rpow_le_rpow h (by norm_num))
      _ ≤ H := hint
  have hbadint := laneA4_bad_kernel_max_square_le P hm I hI E hEm Yh (fun b _ => hYhm b) hPE
    hsecond
  
  have hmain : ∫⁻ ω, (I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω))) ^ (2 : ℝ) ∂P ≤
      2 * (g ^ (2 : ℝ) + δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) := by
    calc ∫⁻ ω, (I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω))) ^ (2 : ℝ) ∂P
        ≤ ∫⁻ ω, 2 * (g ^ (2 : ℝ) + Bsup ω ^ (2 : ℝ)) ∂P := lintegral_mono_ae hpoint
      _ = 2 * (g ^ (2 : ℝ) + ∫⁻ ω, Bsup ω ^ (2 : ℝ) ∂P) := by
          rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left measurable_const,
            lintegral_const, measure_univ, mul_one]
      _ ≤ 2 * (g ^ (2 : ℝ) + δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) := by
          gcongr
  
  have hfin := hKF K hKF'
  simp only at hfin
  have hgsq : g ^ (2 : ℝ) = ENNReal.ofReal (gr ^ 2) := by
    rw [hg, ENNReal.ofReal_rpow_of_nonneg hgr0 (by norm_num), Real.rpow_two]
  have hδh : δ ^ (1 / 2 : ℝ) = ENNReal.ofReal (2 * (2 : ℝ) ^ (-(M * K) / 2)) := by
    have hδr : δ = ENNReal.ofReal (4 * (2 : ℝ) ^ (-(M * K))) := by
      rw [hδ, ENNReal.ofReal_mul (by norm_num)]
      simp
    rw [hδr, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by norm_num)]
    have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h4]
    congr 2
    ring
  have hHh : H ^ (1 / 2 : ℝ) = ENNReal.ofReal ((2 : ℝ) ^ (E₂ * K)) := by
    rw [hHdef, ← ENNReal.rpow_mul]; norm_num
  have hreal : 2 * (gr ^ 2 + 2 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E₂ * K)) ≤
      (2 : ℝ) ^ (-(2 * (α - ζ)) * K) := by
    have := hfin
    nlinarith [this]
  have hinner : g ^ (2 : ℝ) + δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (gr ^ 2 + 2 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E₂ * K)) := by
    rw [hgsq, hδh, hHh, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hL : 2 * (g ^ (2 : ℝ) + δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) =
      ENNReal.ofReal (2 * (gr ^ 2 + 2 * (2 : ℝ) ^ (-(M * K) / 2) * (2 : ℝ) ^ (E₂ * K))) := by
    rw [hinner, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    simp
  have hR : ENNReal.ofReal ((2 : ℝ) ^ (-(α - ζ) * K)) ^ (2 : ℝ) =
      ENNReal.ofReal ((2 : ℝ) ^ (-(2 * (α - ζ)) * K)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul (by norm_num)]
    congr 2
    ring
  have htarget : 2 * (g ^ (2 : ℝ) + δ ^ (1 / 2 : ℝ) * H ^ (1 / 2 : ℝ)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(α - ζ) * K)) ^ (2 : ℝ) := by
    rw [hL, hR]
    exact ENNReal.ofReal_le_ofReal hreal
  calc (∫⁻ ω, (I.sup (fun b => ∫⁻ x, Y b x ∂(κ ω))) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal ((2 : ℝ) ^ (-(α - ζ) * K)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (hmain.trans htarget) (by norm_num)
    _ = ENNReal.ofReal ((2 : ℝ) ^ (-(α - ζ) * K)) := by
        rw [← ENNReal.rpow_mul]; norm_num

end SupercriticalLQGUniqueness.B2.DG20Conc
