/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3REfron at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3RLogLen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneA3Log

 
















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise J2Defs

 
theorem laneA3R_ofReal_log_sub_le {L₀ L₁ H : ℝ≥0∞} (h0 : 0 < L₀) (h0' : L₀ ≠ ⊤) (h1 : 0 < L₁)
    (h1' : L₁ ≠ ⊤) (h : L₁ ≤ L₀ + H) :
    ENNReal.ofReal (Real.log L₁.toReal - Real.log L₀.toReal) ≤ H / L₀ := by
  by_cases hH : H = ⊤
  · rw [hH, ENNReal.top_div_of_ne_top h0']; exact le_top
  have hr : L₁.toReal ≤ L₀.toReal + H.toReal := by
    rw [← ENNReal.toReal_add h0' hH]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h0', hH⟩) h
  have hpos0 : 0 < L₀.toReal := ENNReal.toReal_pos h0.ne' h0'
  have hpos1 : 0 < L₁.toReal := ENNReal.toReal_pos h1.ne' h1'
  calc ENNReal.ofReal (Real.log L₁.toReal - Real.log L₀.toReal)
      ≤ ENNReal.ofReal (H.toReal / L₀.toReal) :=
        ENNReal.ofReal_le_ofReal (laneA3_log_resampling_le hpos0 hpos1 hr)
    _ = H / L₀ := by
        rw [ENNReal.ofReal_div_of_pos hpos0, ENNReal.ofReal_toReal hH, ENNReal.ofReal_toReal h0']

theorem laneA3R_rectLen_pos_ne_top {ξ : ℝ} {g : ℂ → ℝ} (hg : Continuous g) :
    0 < rectLen ξ g (rectAB 1 1) ∧ rectLen ξ g (rectAB 1 1) ≠ ⊤ :=
  ⟨rectLen_pos (ξ := ξ) (rectAB 1 1) (by simp [rectAB, MarkedRect.crossWidth]) hg,
    rectLen_ne_top (ξ := ξ) _ (by simp [rectAB]) (by simp [rectAB]) hg⟩

theorem laneA3R_sum_update_apply {ι α : Type*} [Fintype ι] [DecidableEq ι] (v : ι → α → ℝ)
    (b : ι) (w : α → ℝ) (x : α) :
    ∑ c, Function.update v b w c x = ∑ c, v c x - v b x + w x := by
  have h : ∀ c, Function.update v b w c x = v c x + (if c = b then w x - v b x else 0) := by
    intro c
    by_cases hc : c = b
    · subst hc; simp
    · simp [hc]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

 
theorem laneA3R_fLen_update_eq {ξ : ℝ} {K : ℕ} {y : ℂ → ℝ} (hy : Continuous y)
    {B : T20B.nearIdx K → ℂ → ℝ} (hB : ∀ c, Continuous (B c)) (b : T20B.nearIdx K)
    {g : ℂ → ℝ} (hg : Continuous g) :
    T20B.fLen ξ (fun o : Option (T20B.nearIdx K) => o.elim (T20B.restrD y)
        (Function.update (fun c => T20B.restrD (B c)) b (T20B.restrD g))) =
      L23.logLen ξ (fun x => y x + (∑ c, B c x - B b x + g x)) :=
  laneA3R_fLen_option_eq hy
    (((continuous_finsetSum _ fun c _ => hB c).sub (hB b)).add hg) _
    fun c => by rw [laneA3R_sum_update_apply]; rfl

 
theorem laneA3R_fLen_blocks_eq {ξ : ℝ} {K : ℕ} {y : ℂ → ℝ} (hy : Continuous y)
    {B : T20B.nearIdx K → ℂ → ℝ} (hB : ∀ c, Continuous (B c)) :
    T20B.fLen ξ (fun o : Option (T20B.nearIdx K) => o.elim (T20B.restrD y)
        (fun c => T20B.restrD (B c))) =
      L23.logLen ξ (fun x => y x + ∑ c, B c x) :=
  laneA3R_fLen_option_eq hy (continuous_finsetSum _ fun c _ => hB c) _ fun _ => rfl

 
theorem laneA3R_efron_pathwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hQ : PsiSmall Q) (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (hC1 : ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2)
          (rectAB 1 1) ≤
        rectLen ξ (fun x => psiMN Q W P 0 n x z.1) (rectAB 1 1) +
        (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator
          (laneA3Around P W hW Q ξ n K b) z.1) :
    ∀ᵐ z ∂(P.prod P), ∀ b : T20B.nearIdx K,
      ENNReal.ofReal (T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1))
            (Function.update (fineBlocks Q W P K n z.1) b (fineBlocks Q W P K n z.2 b))) -
        T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1)) (fineBlocks Q W P K n z.1))) ≤
        laneA3HitWeight P W hW Q ξ γ n K b.1 z.1 := by
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have h0n := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
  have hB := fun b => T20B.blkKn_spec hW Q hKn b
  have hfst : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᵐ z ∂(P.prod P), p z.1 := fun h =>
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving.ae h
  filter_upwards [hC1, hfst (T20B.sum_blkKn_ae hW Q hQ hKn),
    hfst (T20B.psiMN_add_ae hW Q hKn)] with z hc hsum hadd b
  have hy : Continuous fun x => psiMN Q W P 0 K x z.1 := h0K.cont z.1
  have hBf : ∀ c : T20B.nearIdx K, Continuous fun x => T20B.blkKn Q W P K n c.1 x z.1 :=
    fun c => (hB c.1).1 z.1
  have hg : Continuous fun x => T20B.blkKn Q W P K n b.1 x z.2 := (hB b.1).1 z.2
  have hsum' : ∀ x ∈ (rectAB 1 1).toSet,
      ∑ c : T20B.nearIdx K, T20B.blkKn Q W P K n c.1 x z.1 = psiMN Q W P K n x z.1 := by
    intro x hx
    have hx' : x ∈ L23.sq01 := hx
    rw [Finset.sum_coe_sort (T20B.nearIdx K) (fun c => T20B.blkKn Q W P K n c x z.1),
      hsum x hx']
  have e1 : T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
      o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1))
        (Function.update (fineBlocks Q W P K n z.1) b (fineBlocks Q W P K n z.2 b))) =
      L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2) := by
    rw [show fineBlocks Q W P K n z.1 = fun c => T20B.restrD
        (fun x => T20B.blkKn Q W P K n c.1 x z.1) from rfl,
      show fineBlocks Q W P K n z.2 b = T20B.restrD
        (fun x => T20B.blkKn Q W P K n b.1 x z.2) from rfl,
      laneA3R_fLen_update_eq hy hBf b hg]
    simp only [L23.logLen]
    congr 2
    refine rectLen_congr _ fun x hx => ?_
    rw [hsum' x hx, hadd x]
    ring
  have e0 : T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
      o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1)) (fineBlocks Q W P K n z.1)) =
      L23.logLen ξ (fun x => psiMN Q W P 0 n x z.1) := by
    rw [show fineBlocks Q W P K n z.1 = fun c => T20B.restrD
        (fun x => T20B.blkKn Q W P K n c.1 x z.1) from rfl,
      laneA3R_fLen_blocks_eq hy hBf]
    simp only [L23.logLen]
    congr 2
    refine rectLen_congr _ fun x hx => ?_
    rw [hsum' x hx, hadd x]
    ring
  rw [e1, e0]
  simp only [L23.logLen]
  have hc1 : Continuous fun x => psiMN Q W P 0 n x z.1 -
      T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2 :=
    ((h0n.cont z.1).sub ((hB b.1).1 z.1)).add hg
  obtain ⟨hp0, hf0⟩ := laneA3R_rectLen_pos_ne_top (ξ := ξ) (h0n.cont z.1)
  obtain ⟨hp1, hf1⟩ := laneA3R_rectLen_pos_ne_top (ξ := ξ) hc1
  refine (laneA3R_ofReal_log_sub_le hp0 hf0 hp1 hf1 (hc b.1 b.2)).trans (le_of_eq ?_)
  unfold laneA3HitWeight
  by_cases hz : z.1 ∈ laneCEventualHit γ n K (laneBCoarseIndex Q K) b.1
  · simp [Set.indicator, hz]
  · simp [Set.indicator, hz]

 

theorem laneA3R_efron_clause_i.{u} (hInd : LaneFineStarIndepCoarse.{u})
    {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W) (Q : PsiParams)
    (hQ : PsiSmall Q) (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n) (γ : ℕ → ℕ → Ω → ℝ → ℂ)
    (hC1 : ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
          T20B.blkKn Q W P K n b x z.1 + T20B.blkKn Q W P K n b x z.2)
          (rectAB 1 1) ≤
        rectLen ξ (fun x => psiMN Q W P 0 n x z.1) (rectAB 1 1) +
        (laneCEventualHit γ n K (laneBCoarseIndex Q K) b).indicator
          (laneA3Around P W hW Q ξ n K b) z.1)
    (b : T20B.nearIdx K) {w : (ℂ → ℝ) → ℝ≥0∞} (hw : Measurable w)
    (hwae : laneA3HitWeight P W hW Q ξ γ n K b.1 =ᵐ[P]
      fun ω => w (laneA3RField Q W P n ω)) :
    ∀ᵐ z ∂(P.prod P), ENNReal.ofReal (efronDiff ξ Q W P K n b z) ≤
      ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n z.1) := by
  have h0K := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le K)
  have hB := fun b => T20B.blkKn_spec hW Q hKn b
  have hYcm : Measurable fun ω (x : ℂ) => psiMN Q W P 0 K x ω :=
    measurable_pi_iff.mpr h0K.meas
  have hFkm : Measurable fun ω (x : ℂ) => psiMN Q W P K n x ω :=
    measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW hKn).meas
  have hXm : Measurable (laneA3RStarMap Q W P K n) :=
    hFkm.prodMk (measurable_pi_iff.mpr fun c =>
      measurable_pi_iff.mpr (hB c.1).2.1)
  have hstar : MeasurableSpace.comap (laneA3RStarMap Q W P K n) inferInstance ≤ mΩ :=
    hXm.comap_le
  have hfine : MeasurableSpace.comap (fun ω (x : ℂ) => psiMN Q W P K n x ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ)) ≤ mΩ := hFkm.comap_le
  have hIndStar : IndepFun (laneA3RStarMap Q W P K n)
      (fun ω (x : ℂ) => psiMN Q W P 0 K x ω) P := by
    have h := hInd P W hW Q K n hKn
    have h2 : Indep (MeasurableSpace.comap (fun ω (x : ℂ) => psiMN Q W P 0 K x ω)
        inferInstance) (laneFineStar Q W P K n) P :=
      indep_of_indep_of_le_left h le_sup_right
    rw [laneFineStar_eq_comap] at h2
    exact h2.symm
  have hŴm : Measurable fun ω => w (laneA3RField Q W P n ω) :=
    hw.comp (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)).meas)
  
  have htr := laneA3R_kernel_transfer hInd P W hW Q hKn hw hwae
  rw [laneFineStar_eq_comap] at htr
  have hfineW : ∀ᵐ ω ∂P, ∫⁻ x, laneA3HitWeight P W hW Q ξ γ n K b.1 x
      ∂(J2Inputs.fineKernel Q W P K n ω) =
      ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n ω) := by
    filter_upwards [laneC_conditional_lintegral_mono_ae P hfine hwae.le,
      laneC_conditional_lintegral_mono_ae P hfine hwae.symm.le] with ω h1 h2
    exact le_antisymm h1 h2
  
  have hpath := laneA3R_efron_pathwise hW Q hQ ξ hKn γ hC1
  have hpath1 : ∀ᵐ z ∂(P.prod P), ENNReal.ofReal (T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1))
            (Function.update (fineBlocks Q W P K n z.1) b (fineBlocks Q W P K n z.2 b))) -
        T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x z.1)) (fineBlocks Q W P K n z.1))) ≤
        laneA3HitWeight P W hW Q ξ γ n K b.1 z.1 := by
    filter_upwards [hpath] with z hz using hz b
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := P)).quasiMeasurePreserving.ae hpath1
  have hslice := Measure.ae_ae_of_ae_prod hswap
  
  have key : ∀ ω₂ : Ω, (∀ᵐ ω ∂P, ENNReal.ofReal (T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω))
            (Function.update (fineBlocks Q W P K n ω) b (fineBlocks Q W P K n ω₂ b))) -
        T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω)) (fineBlocks Q W P K n ω))) ≤
        laneA3HitWeight P W hW Q ξ γ n K b.1 ω) →
      ∀ᵐ ω ∂P, ENNReal.ofReal (efronDiff ξ Q W P K n b (ω, ω₂)) ≤
        ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n ω) := by
    intro ω₂ hω₂
    let φ : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) → ℝ≥0∞ := fun q =>
      ENNReal.ofReal (T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD q.2)
            (Function.update (fun c => T20B.restrD (q.1.2 c)) b (fineBlocks Q W P K n ω₂ b))) -
        T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD q.2) (fun c => T20B.restrD (q.1.2 c))))
    have hv : Measurable fun q : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) =>
        fun c => T20B.restrD (q.1.2 c) :=
      measurable_pi_iff.mpr fun c => T20B.measurable_restrD.comp
        ((measurable_pi_apply c).comp (measurable_snd.comp measurable_fst))
    have hupd : Measurable fun q : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) =>
        Function.update (fun c => T20B.restrD (q.1.2 c)) b (fineBlocks Q W P K n ω₂ b) :=
      measurable_update'.comp (hv.prodMk measurable_const)
    have hu₁ : Measurable fun q : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) =>
        fun o : Option (T20B.nearIdx K) => o.elim (T20B.restrD q.2)
          (Function.update (fun c => T20B.restrD (q.1.2 c)) b (fineBlocks Q W P K n ω₂ b)) := by
      refine measurable_pi_iff.mpr fun o => ?_
      rcases o with _ | c
      · exact T20B.measurable_restrD.comp measurable_snd
      · exact (measurable_pi_apply c).comp hupd
    have hu₀ : Measurable fun q : ((ℂ → ℝ) × (T20B.nearIdx K → ℂ → ℝ)) × (ℂ → ℝ) =>
        fun o : Option (T20B.nearIdx K) => o.elim (T20B.restrD q.2)
          (fun c => T20B.restrD (q.1.2 c)) := by
      refine measurable_pi_iff.mpr fun o => ?_
      rcases o with _ | c
      · exact T20B.measurable_restrD.comp measurable_snd
      · exact (measurable_pi_apply c).comp hv
    have hφ : Measurable φ := ENNReal.measurable_ofReal.comp
      (((T20B.measurable_fLen ξ).comp hu₁).sub ((T20B.measurable_fLen ξ).comp hu₀))
    have hfr := laneA3R_kernel_freeze P hXm hYcm hIndStar hφ
    have hmono := laneC_conditional_lintegral_mono_ae P hstar
      (f := fun x => φ (laneA3RStarMap Q W P K n x, fun y => psiMN Q W P 0 K y x))
      (g := laneA3HitWeight P W hW Q ξ γ n K b.1) hω₂
    filter_upwards [hfr, hmono, htr, hfineW] with ω e1 e2 e3 e4
    
    have hBf : ∀ c : T20B.nearIdx K, Continuous fun x => T20B.blkKn Q W P K n c.1 x ω :=
      fun c => (hB c.1).1 ω
    have hg : Continuous fun x => T20B.blkKn Q W P K n b.1 x ω₂ := (hB b.1).1 ω₂
    have hs1 : Continuous fun x => ∑ c : T20B.nearIdx K, T20B.blkKn Q W P K n c.1 x ω -
        T20B.blkKn Q W P K n b.1 x ω + T20B.blkKn Q W P K n b.1 x ω₂ :=
      ((continuous_finsetSum _ fun c _ => hBf c).sub (hBf b)).add hg
    have hs0 : Continuous fun x => ∑ c : T20B.nearIdx K, T20B.blkKn Q W P K n c.1 x ω :=
      continuous_finsetSum _ fun c _ => hBf c
    have hi1 : Integrable (fun ω' => T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
        o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω'))
          (Function.update (fineBlocks Q W P K n ω) b (fineBlocks Q W P K n ω₂ b)))) P := by
      have e : (fun ω' => T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω'))
            (Function.update (fineBlocks Q W P K n ω) b (fineBlocks Q W P K n ω₂ b)))) =
          fun ω' => L23.logLen ξ (fun x => psiMN Q W P 0 K x ω' +
            (∑ c : T20B.nearIdx K, T20B.blkKn Q W P K n c.1 x ω -
              T20B.blkKn Q W P K n b.1 x ω + T20B.blkKn Q W P K n b.1 x ω₂)) :=
        funext fun ω' => laneA3R_fLen_update_eq (h0K.cont ω') hBf b hg
      rw [e]
      exact laneA3R_integrable_logLen_add hW Q ξ K hs1
    have hi0 : Integrable (fun ω' => T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
        o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω')) (fineBlocks Q W P K n ω))) P := by
      have e : (fun ω' => T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω')) (fineBlocks Q W P K n ω))) =
          fun ω' => L23.logLen ξ (fun x => psiMN Q W P 0 K x ω' +
            ∑ c : T20B.nearIdx K, T20B.blkKn Q W P K n c.1 x ω) :=
        funext fun ω' => laneA3R_fLen_blocks_eq (h0K.cont ω') hBf
      rw [e]
      exact laneA3R_integrable_logLen_add hW Q ξ K hs0
    have hED : efronDiff ξ Q W P K n b (ω, ω₂) = ∫ ω', (T20B.fLen ξ
        (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω'))
            (Function.update (fineBlocks Q W P K n ω) b (fineBlocks Q W P K n ω₂ b))) -
        T20B.fLen ξ (fun o : Option (T20B.nearIdx K) =>
          o.elim (T20B.restrD (fun x => psiMN Q W P 0 K x ω')) (fineBlocks Q W P K n ω))) ∂P := by
      unfold efronDiff condLogLen
      rw [integral_sub hi1 hi0]
    have hbound : ENNReal.ofReal (efronDiff ξ Q W P K n b (ω, ω₂)) ≤
        ∫⁻ y, φ (laneA3RStarMap Q W P K n ω, y)
          ∂(P.map fun ω (x : ℂ) => psiMN Q W P 0 K x ω) := by
      rw [lintegral_map (f := fun y => φ (laneA3RStarMap Q W P K n ω, y))
        (hφ.comp measurable_prodMk_left) hYcm, hED]
      exact laneA3R_ofReal_integral_le (hi1.sub hi0)
    calc ENNReal.ofReal (efronDiff ξ Q W P K n b (ω, ω₂))
        ≤ ∫⁻ y, φ (laneA3RStarMap Q W P K n ω, y)
          ∂(P.map fun ω (x : ℂ) => psiMN Q W P 0 K x ω) := hbound
      _ = ∫⁻ x, φ (laneA3RStarMap Q W P K n x, fun y => psiMN Q W P 0 K y x)
          ∂(condExpKernel P (MeasurableSpace.comap (laneA3RStarMap Q W P K n)
            inferInstance) ω) := e1.symm
      _ ≤ ∫⁻ x, laneA3HitWeight P W hW Q ξ γ n K b.1 x
          ∂(condExpKernel P (MeasurableSpace.comap (laneA3RStarMap Q W P K n)
            inferInstance) ω) := e2
      _ = ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n ω) := by
          rw [e3, e4]
  
  have hS : ∀ᵐ ω₂ ∂P, ∀ᵐ ω ∂P, ENNReal.ofReal (efronDiff ξ Q W P K n b (ω, ω₂)) ≤
      ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n ω) := by
    filter_upwards [hslice] with ω₂ h using key ω₂ h
  have hfb : Measurable (fineBlocks Q W P K n) :=
    measurable_pi_iff.2 fun c => measurable_pi_iff.2 fun d => (hB c.1).2.1 d
  have hupd2 : Measurable fun z : Ω × Ω =>
      Function.update (fineBlocks Q W P K n z.1) b (fineBlocks Q W P K n z.2 b) :=
    measurable_update'.comp ((hfb.comp measurable_fst).prodMk
      ((measurable_pi_apply b).comp (hfb.comp measurable_snd)))
  have hEDm : Measurable (efronDiff ξ Q W P K n b) :=
    ((j2_measurable_condLogLen hW Q ξ K).comp hupd2).sub
      ((j2_measurable_condLogLen hW Q ξ K).comp (hfb.comp measurable_fst))
  have hKm : Measurable fun ω =>
      ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n ω) :=
    (Measurable.lintegral_kernel hŴm).mono hfine le_rfl
  have hSm : MeasurableSet {z : Ω × Ω | ENNReal.ofReal (efronDiff ξ Q W P K n b (z.2, z.1)) ≤
      ∫⁻ x, w (laneA3RField Q W P n x) ∂(J2Inputs.fineKernel Q W P K n z.2)} :=
    measurableSet_le (ENNReal.measurable_ofReal.comp (hEDm.comp measurable_swap))
      (hKm.comp measurable_snd)
  have h3 := (Measure.ae_prod_iff_ae_ae hSm).mpr hS
  filter_upwards [(Measure.measurePreserving_swap (μ := P) (ν := P)).quasiMeasurePreserving.ae h3]
    with z hz
  exact hz

end SupercriticalLQGUniqueness.B2.DG20Conc
