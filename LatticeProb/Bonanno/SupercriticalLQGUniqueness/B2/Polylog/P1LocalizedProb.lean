/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedProb at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P1LocalizedApprox
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.HeatVersionPoint
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1PolarJoint

 
























set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP LQGMetric.DFGPS

 
def plMollifyT (q : ℝ) (g : DistC) (p : ℝ × ℂ) : ℝ :=
  if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plMollify q p.1 hp g p.2 else 0

lemma plMollifyT_of_mem (q : ℝ) (g : DistC) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (z : ℂ) :
    plMollifyT q g (ε, z) = plMollify q ε hε g z := by
  simp only [plMollifyT, hε, ↓reduceDIte]

 
def locErr (q : ℝ) (g : DistC) (p : ℝ × ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal |heatMollify p.1 g p.2 - plMollifyT q g p|

 
def locErrSup (q : ℝ) (U : Set ℂ) (η : ℝ) (g : DistC) : ℝ≥0∞ :=
  ⨆ p ∈ Ioc (0 : ℝ) η ×ˢ closure U, locErr q g p

lemma measurable_locErr (q : ℝ) (p : ℝ × ℂ) : Measurable fun g : DistC => locErr q g p := by
  unfold locErr plMollifyT
  have h2 : Measurable fun g : DistC =>
      (if hp : p.1 ∈ Ioo (0 : ℝ) 1 then plMollify q p.1 hp g p.2 else 0) := by
    split_ifs with hp
    · exact measurable_const.mul (measurable_distOn_apply _)
    · exact measurable_const
  exact ENNReal.measurable_ofReal.comp
    (continuous_abs.measurable.comp ((measurable_heatMollify_left _ _).sub h2))

 
lemma ae_continuousOn_locErr.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) (q : ℝ) :
    ∀ᵐ ω ∂P, ContinuousOn (locErr q (g ω)) (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  filter_upwards [lem2_1HeatJoint P g hg] with ω hω
  have h1 : ContinuousOn (fun p : ℝ × ℂ => heatMollify p.1 (g ω) p.2) (Ioo (0 : ℝ) 1 ×ˢ univ) :=
    hω.2.mono (prod_mono (fun _ hε => hε.1) subset_rfl)
  exact ENNReal.continuous_ofReal.comp_continuousOn (h1.sub (plMollify_continuousOn q (g ω))).abs

 

lemma biSup_eq_biSup_of_dense {X : Type*} [TopologicalSpace X] {f : X → ℝ≥0∞} {T D : Set X}
    (hf : ContinuousOn f T) (hDT : D ⊆ T) (hTD : T ⊆ closure D) :
    ⨆ p ∈ T, f p = ⨆ p ∈ D, f p := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (biSup_mono hDT)
  have hc : f p ∈ closure (f '' D) := ((hf p hp).mono hDT).mem_closure_image (hTD hp)
  have hcl : closure (f '' D) ⊆ Iic (⨆ p ∈ D, f p) :=
    closure_minimal (by rintro _ ⟨x, hx, rfl⟩; exact le_iSup₂ (f := fun x _ => f x) x hx)
      isClosed_Iic
  exact hcl hc

 
theorem aemeasurable_locErrSup.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) (q : ℝ) (U : Set ℂ) {η : ℝ} (hη : η < 1) :
    AEMeasurable (fun ω => locErrSup q U η (g ω)) P := by
  set T : Set (ℝ × ℂ) := Ioc (0 : ℝ) η ×ˢ closure U
  have hT : T ⊆ Ioo (0 : ℝ) 1 ×ˢ univ :=
    prod_mono (fun ε hε => ⟨hε.1, lt_of_le_of_lt hε.2 hη⟩) (subset_univ _)
  obtain ⟨D, hDT, hDc, hTD⟩ := (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  have hae : (fun ω => locErrSup q U η (g ω)) =ᵐ[P] fun ω => ⨆ p : D, locErr q (g ω) p := by
    filter_upwards [ae_continuousOn_locErr hg q] with ω hω
    simp only [locErrSup]
    rw [biSup_eq_biSup_of_dense (hω.mono hT) hDT hTD, iSup_subtype']
  have : Countable D := hDc.to_subtype
  refine AEMeasurable.congr ?_ hae.symm
  exact AEMeasurable.iSup fun p => ((measurable_locErr q p).comp hg.measurable).aemeasurable

 
theorem ae_tendsto_locErrSup.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q) {U : Set ℂ}
    (hU : Bornology.IsBounded U) :
    ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η < η₀ →
      locErrSup q U η (g ω) ≤ ENNReal.ofReal δ := by
  filter_upwards [lem_localized_approx_sup hg hq hU] with ω hω δ hδ
  have h1 := hω δ hδ
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨η₀, hη₀, hη⟩ := h1
  refine ⟨min η₀ 1, lt_min hη₀ one_pos, fun η hηlt => iSup₂_le fun p hp => ?_⟩
  have hp1 : p.1 ∈ Ioo (0 : ℝ) 1 := ⟨hp.1.1, lt_of_le_of_lt hp.1.2 (hηlt.trans_le (min_le_right _ _))⟩
  have hd : dist p.1 0 < η₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hp.1.1]
    exact lt_of_le_of_lt hp.1.2 (hηlt.trans_le (min_le_left _ _))
  have := (hη hd hp.1.1 hp1 p.2 hp.2).2
  unfold locErr
  rw [plMollifyT_of_mem q _ hp1]
  exact ENNReal.ofReal_le_ofReal this

 

theorem ae_locErrSup_lt_top.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q) {U : Set ℂ}
    (hU : Bornology.IsBounded U) {η : ℝ} (hη : η < 1) :
    ∀ᵐ ω ∂P, locErrSup q U η (g ω) < ∞ := by
  filter_upwards [ae_tendsto_locErrSup hg hq hU, ae_continuousOn_locErr hg q] with ω hω hc
  obtain ⟨η₀, hη₀, hle⟩ := hω 1 one_pos
  set η₁ := η₀ / 2
  have hη₁ : 0 < η₁ := by positivity
  set K : Set (ℝ × ℂ) := Icc η₁ η ×ˢ closure U
  have hK : IsCompact K := isCompact_Icc.prod hU.isCompact_closure
  have hKS : K ⊆ Ioo (0 : ℝ) 1 ×ˢ univ :=
    prod_mono (fun ε hε => ⟨lt_of_lt_of_le hη₁ hε.1, lt_of_le_of_lt hε.2 hη⟩) (subset_univ _)
  have hcr : ContinuousOn (fun p => (locErr q (g ω) p).toReal) K :=
    ENNReal.continuousOn_toReal.comp (hc.mono hKS) fun p _ => ENNReal.ofReal_ne_top
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcr
  have hsmall : locErrSup q U η₁ (g ω) ≤ ENNReal.ofReal 1 := hle η₁ (by simp only [η₁]; linarith)
  refine lt_of_le_of_lt (iSup₂_le fun p hp => ?_)
    (max_lt (ENNReal.ofReal_lt_top (r := 1)) (ENNReal.ofReal_lt_top (r := B)))
  rcases le_or_gt p.1 η₁ with h | h
  · exact le_max_of_le_left ((le_iSup₂ (f := fun p _ => locErr q (g ω) p) p
      ⟨⟨hp.1.1, h⟩, hp.2⟩).trans hsmall)
  · refine le_max_of_le_right ?_
    have hpK : p ∈ K := ⟨⟨h.le, hp.1.2⟩, hp.2⟩
    have hb := hB p hpK
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
    calc locErr q (g ω) p = ENNReal.ofReal (locErr q (g ω) p).toReal :=
          (ENNReal.ofReal_toReal ENNReal.ofReal_ne_top).symm
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hb

lemma exists_nat_ofReal_ge {x : ℝ≥0∞} (hx : x < ∞) :
    ∃ n : ℕ, x ≤ ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := by
  refine ⟨⌈x.toReal⌉₊, ?_⟩
  calc x = ENNReal.ofReal x.toReal := (ENNReal.ofReal_toReal hx.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by push_cast; linarith [Nat.le_ceil x.toReal])

 
theorem exists_measure_locErrSup_gt_le.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q)
    {U : Set ℂ} (hU : Bornology.IsBounded U) {η : ℝ} (hη : η < 1) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ K : ℝ, 0 < K ∧ P {ω | ENNReal.ofReal K < locErrSup q U η (g ω)} ≤ θ := by
  have hM := aemeasurable_locErrSup hg q U hη
  set s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal (n + 1 : ℕ) < hM.mk _ ω}
  have hs : Antitone s := fun m n hmn ω hω =>
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by exact_mod_cast Nat.succ_le_succ hmn)) hω
  have hsm : ∀ n, NullMeasurableSet (s n) P := fun n =>
    (measurableSet_lt measurable_const hM.measurable_mk).nullMeasurableSet
  have hlim := tendsto_measure_iInter_atTop hsm hs ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n, s n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_locErrSup_lt_top hg hq hU hη, hM.ae_eq_mk] with ω hlt heq hω
    obtain ⟨n, hn⟩ := exists_nat_ofReal_ge hlt
    have h1 : ENNReal.ofReal ((n + 1 : ℕ) : ℝ) < hM.mk _ ω := mem_iInter.1 hω n
    rw [← heq] at h1
    exact absurd (lt_of_lt_of_le h1 hn) (lt_irrefl _)
  rw [hnull] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hθ)).exists
  refine ⟨(n + 1 : ℕ), by positivity, ?_⟩
  calc P {ω | ENNReal.ofReal ((n + 1 : ℕ) : ℝ) < locErrSup q U η (g ω)} = P (s n) := by
        refine measure_congr (hM.ae_eq_mk.mono fun ω hω => ?_)
        simp only [s, mem_ofPred_eq, hω]
    _ ≤ θ := hn.le

 
theorem tendsto_measure_locErrSup_gt.{u} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P) {q : ℝ} (hq : 0 < q)
    {U : Set ℂ} (hU : Bornology.IsBounded U) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun η => P {ω | ENNReal.ofReal δ < locErrSup q U η (g ω)}) (𝓝[>] 0) (𝓝 0) := by
  
  set ηs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hηs1 : ∀ n, ηs n < 1 := fun n => by
    simp only [ηs]; rw [div_lt_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hM : ∀ n, AEMeasurable (fun ω => locErrSup q U (ηs n) (g ω)) P :=
    fun n => aemeasurable_locErrSup hg q U (hηs1 n)
  set s : ℕ → Set Ω := fun n => {ω | ENNReal.ofReal δ < (hM n).mk _ ω}
  have hmono : ∀ {η η' : ℝ}, η ≤ η' → ∀ g', locErrSup q U η g' ≤ locErrSup q U η' g' :=
    fun hle g' => biSup_mono (prod_mono (fun ε hε => ⟨hε.1, hε.2.trans hle⟩) subset_rfl)
  have hηanti : Antitone ηs := fun m n hmn => by
    simp only [ηs]
    have : (m : ℝ) ≤ n := Nat.cast_le.2 hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  
  have hsm : ∀ n, NullMeasurableSet (s n) P := fun n =>
    (measurableSet_lt measurable_const (hM n).measurable_mk).nullMeasurableSet
  set t : ℕ → Set Ω := fun n => ⋂ k ≤ n, s k
  have ht : Antitone t := fun m n hmn => biInter_mono (fun k hk => le_trans hk hmn) fun _ _ => le_rfl
  have htm : ∀ n, NullMeasurableSet (t n) P := fun n =>
    NullMeasurableSet.biInter (to_countable _) fun k _ => hsm k
  have hlim := tendsto_measure_iInter_atTop htm ht ⟨0, measure_ne_top P _⟩
  have hnull : P (⋂ n, t n) = 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ n, locErrSup q U (ηs n) (g ω) = (hM n).mk _ ω :=
      ae_all_iff.2 fun n => (hM n).ae_eq_mk
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_tendsto_locErrSup hg hq hU, hall] with ω h1 h2 hω
    obtain ⟨η₀, hη₀, hle⟩ := h1 (δ / 2) (by positivity)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / η₀)
    have hηn : ηs n < η₀ := by
      simp only [ηs]
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hη₀] at hn
      nlinarith
    have hs' : ENNReal.ofReal δ < (hM n).mk _ ω := mem_iInter₂.1 (mem_iInter.1 hω n) n le_rfl
    rw [← h2 n] at hs'
    have h3 := (hle _ hηn)
    have : ENNReal.ofReal δ < ENNReal.ofReal (δ / 2) := lt_of_lt_of_le hs' h3
    rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)] at this
    linarith
  rw [hnull] at hlim
  
  have hts : ∀ n, P {ω | ENNReal.ofReal δ < locErrSup q U (ηs n) (g ω)} ≤ P (t n) := by
    intro n
    refine measure_mono_ae ?_
    have hall : ∀ᵐ ω ∂P, ∀ k, locErrSup q U (ηs k) (g ω) = (hM k).mk _ ω :=
      ae_all_iff.2 fun k => (hM k).ae_eq_mk
    filter_upwards [hall] with ω hω hmem
    have hmem' : ENNReal.ofReal δ < locErrSup q U (ηs n) (g ω) := hmem
    show ω ∈ t n
    refine mem_iInter₂.2 fun k hk => ?_
    show ENNReal.ofReal δ < (hM k).mk _ ω
    rw [← hω k]
    exact lt_of_lt_of_le hmem' (hmono (hηanti hk) _)
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  obtain ⟨n, hn⟩ := (hlim.eventually (ge_mem_nhds hθ)).exists
  have hpos : 0 < ηs n := by simp only [ηs]; positivity
  filter_upwards [Ioo_mem_nhdsGT hpos] with η hη
  calc P {ω | ENNReal.ofReal δ < locErrSup q U η (g ω)}
      ≤ P {ω | ENNReal.ofReal δ < locErrSup q U (ηs n) (g ω)} :=
        measure_mono fun ω hω => lt_of_lt_of_le hω (hmono hη.2.le _)
    _ ≤ P (t n) := hts n
    _ ≤ θ := hn

 

 
lemma ae_heatSmoothing_err_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) (q : ℝ)
    (U : Set ℂ) {η : ℝ} (X : Ω → C(ℂ, ℝ)) {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (hεη : ε ≤ η)
    (hX : IsHeatSmoothing P h ⟨ε, hε.1⟩ X) :
    ∀ᵐ ω ∂P, ∀ z ∈ closure U,
      ENNReal.ofReal |X ω z - plMollify q ε hε (h ω) z| ≤ locErrSup q U η (h ω) := by
  filter_upwards [DG20Pt.dg20_heat_smoothing_ae_heatMollify P h hh ⟨ε, hε.1⟩ X hX] with ω hω z hz
  rw [hω z]
  have := le_iSup₂ (f := fun p (_ : p ∈ Ioc (0 : ℝ) η ×ˢ closure U) => locErr q (h ω) p) (ε, z)
    ⟨⟨hε.1, hεη⟩, hz⟩
  unfold locErrSup
  simpa only [locErr, plMollifyT_of_mem q _ hε] using this

 


theorem heatSmoothing_localized_tendsto {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P) {q : ℝ}
    (hq : 0 < q) {U : Set ℂ} (hU : Bornology.IsBounded U) {δ : ℝ} (hδ : 0 < δ)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ)) (hX : ∀ ε, IsHeatSmoothing P h ε (X ε)) :
    Tendsto (fun ε => if hε : ε ∈ Ioo (0 : ℝ) 1 then
        P {ω | ∃ z ∈ closure U, δ < |X ⟨ε, hε.1⟩ ω z - plMollify q ε hε (h ω) z|} else 0)
      (𝓝[>] 0) (𝓝 0) := by
  have hlim := tendsto_measure_locErrSup_gt hh.1 hq hU hδ
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_mem_Ioo01] with ε hε
  simp only [hε, ↓reduceDIte]
  refine measure_mono_ae ?_
  filter_upwards [ae_heatSmoothing_err_le hh q U (X ⟨ε, hε.1⟩) hε le_rfl (hX _)] with ω hω hmem
  obtain ⟨z, hz, hδz⟩ := hmem
  exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hδ.le hδz)).2 hδz) (hω z hz)

end SupercriticalLQGUniqueness.B2.Polylog
