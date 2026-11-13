/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SLUMetricAPI at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUSupport
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.LocallyConstant.Basic

 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness

 
theorem lowerSemicontinuous_iff_seq {β γ : Type*} [TopologicalSpace β] [FirstCountableTopology β]
    [CompleteLinearOrder γ] [TopologicalSpace γ] [OrderTopology γ] {f : β → γ} :
    LowerSemicontinuous f ↔
      ∀ (u : ℕ → β) (x : β), Tendsto u atTop (𝓝 x) → f x ≤ liminf (fun n => f (u n)) atTop := by
  constructor
  · intro hf u x hu
    calc f x ≤ liminf f (𝓝 x) := hf.le_liminf x
      _ ≤ liminf f (map u atTop) := liminf_le_liminf_of_le hu
      _ = liminf (fun n => f (u n)) atTop := (liminf_comp f u atTop).symm
  · intro h x y hy
    by_contra hne
    rw [not_eventually] at hne
    obtain ⟨u, hu, hfu⟩ := exists_seq_forall_of_frequently hne
    have h2 : liminf (fun n => f (u n)) atTop ≤ y :=
      liminf_le_of_frequently_le' (Frequently.of_forall fun n => not_lt.1 (hfu n))
    exact absurd ((h u x hu).trans h2) (not_le.2 hy)

 

section Criterion

variable {α : Type*} [TopologicalSpace α]

 
theorem LSCTendsto.comp_strictMono {F : ℕ → α × α → EReal} {f : α × α → EReal}
    (hF : LSCTendsto F f) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    LSCTendsto (fun n => F (φ n)) f := by
  classical
  refine ⟨fun p q hp => ?_, fun q => ?_⟩
  · let p' : ℕ → α × α := fun n => if h : ∃ k, φ k = n then p (Nat.find h) else q
    have hp'φ : ∀ k, p' (φ k) = p k := by
      intro k
      have h : ∃ j, φ j = φ k := ⟨k, rfl⟩
      simp only [p', dite_eq_left h]
      exact congrArg p (hφ.injective (Nat.find_spec h))
    have hp' : Tendsto p' atTop (𝓝 q) := by
      refine tendsto_nhds.2 fun s hs hqs => ?_
      obtain ⟨K, hK⟩ := eventually_atTop.1 (hp (hs.mem_nhds hqs))
      refine eventually_atTop.2 ⟨φ K, fun n hn => ?_⟩
      by_cases h : ∃ k, φ k = n
      · have hk : φ (Nat.find h) = n := Nat.find_spec h
        have hK' : K ≤ Nat.find h := hφ.le_iff_le.1 (hn.trans_eq hk.symm)
        simpa only [p', Set.mem_preimage, dite_eq_left h] using hK _ hK'
      · simpa only [p', Set.mem_preimage, dite_eq_right h] using hqs
    calc f q ≤ liminf (fun n => F n (p' n)) atTop := hF.1 p' q hp'
      _ ≤ liminf (fun n => F n (p' n)) (map φ atTop) :=
          liminf_le_liminf_of_le hφ.tendsto_atTop
      _ = liminf (fun k => F (φ k) (p k)) atTop := by
          rw [← liminf_comp]
          simp only [Function.comp_def, hp'φ]
  · obtain ⟨p, hp, hFp⟩ := hF.2 q
    exact ⟨fun k => p (φ k), hp.comp hφ.tendsto_atTop, hFp.comp hφ.tendsto_atTop⟩

 
end Criterion

 

namespace LSCFun

theorem tendsto_of_lscTendsto {F : ℕ → LSCFun} {f : LSCFun}
    (h : LSCTendsto (fun n => (F n).1) f.1) : Tendsto F atTop (𝓝 f) :=
  tendsto_nhds.2 fun _ hV hfV => hV F f h hfV

 

theorem le_of_forall_tendsto (t : TopologicalSpace (LSCFun))
    (ht : ∀ (F : ℕ → LSCFun) (f : LSCFun), LSCTendsto (fun n => (F n).1) f.1 →
      Tendsto F atTop (@nhds _ t f)) :
    LSCFun.instTopologicalSpace ≤ t := by
  intro V hV F f hF hfV
  exact ht F f hF (@IsOpen.mem_nhds _ t f V hV hfV)

 
instance instSequentialSpace : SequentialSpace (LSCFun) where
  isClosed_of_seq s hs := by
    rw [← isOpen_compl_iff]
    intro F f hF hf
    by_contra hne
    rw [not_eventually] at hne
    simp only [Set.mem_compl_iff, not_not] at hne
    obtain ⟨φ, hφ, hFφ⟩ := extraction_of_frequently_atTop hne
    exact hf (hs hFφ (tendsto_of_lscTendsto (hF.comp_strictMono hφ)))

 

theorem eq_of_sequentialSpace (t : TopologicalSpace (LSCFun))
    (hseq : @SequentialSpace (LSCFun) t)
    (ht : ∀ (F : ℕ → LSCFun) (f : LSCFun),
      Tendsto F atTop (@nhds _ t f) ↔ LSCTendsto (fun n => (F n).1) f.1) :
    t = LSCFun.instTopologicalSpace := by
  refine le_antisymm (fun V hV => ?_) (le_of_forall_tendsto t fun F f h => (ht F f).2 h)
  have hC : IsClosed[t] Vᶜ := hseq.isClosed_of_seq Vᶜ fun F f hF hFf hfV => by
    obtain ⟨n, hn⟩ := (hV F f ((ht F f).1 hFf) hfV).exists
    exact hF n hn
  have h := @IsClosed.isOpen_compl _ t _ hC
  rwa [compl_compl] at h

 

theorem isOpen_setOf_exists_lt {O : Set (ℂ × ℂ)} (hO : IsOpen O) (s : EReal) :
    IsOpen {f : LSCFun | ∃ q ∈ O, f.1 q < s} := by
  rintro F f hF ⟨q, hqO, hq⟩
  obtain ⟨p, hp, hFp⟩ := hF.2 q
  filter_upwards [hp (hO.mem_nhds hqO), hFp (gt_mem_nhds hq)] with n hn1 hn2
  exact ⟨p n, hn1, hn2⟩

 

theorem isOpen_setOf_forall_lt {K : Set (ℂ × ℂ)} (hK : IsCompact K)
    (t : EReal) : IsOpen {f : LSCFun | ∀ q ∈ K, t < f.1 q} := by
  intro F f hF hf
  by_contra hne
  rw [not_eventually] at hne
  simp only [Set.mem_ofPred_eq, not_forall, not_lt] at hne
  obtain ⟨φ, hφ, hFφ⟩ := extraction_of_frequently_atTop hne
  choose q hqK hq using hFφ
  obtain ⟨q₀, hq₀K, ψ, hψ, hqψ⟩ := hK.tendsto_subseq hqK
  have h1 := (hF.comp_strictMono (hφ.comp hψ)).1 (q ∘ ψ) q₀ hqψ
  have h2 : liminf (fun n => (F ((φ ∘ ψ) n)).1 ((q ∘ ψ) n)) atTop ≤ t :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun n => hq (ψ n))
  exact absurd (h1.trans h2) (not_le.2 (hf q₀ hq₀K))

 
theorem lscTendsto_of_tendsto
    {F : ℕ → LSCFun} {f : LSCFun} (h : Tendsto F atTop (𝓝 f)) :
    LSCTendsto (fun n => (F n).1) f.1 := by
  classical
  have hi : ∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
      f.1 q ≤ liminf (fun n => (F n).1 (p n)) atTop := by
    intro p q hp
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨t, ht1, ht2⟩ := exists_between hlt
    obtain ⟨K, hKq, hKsub, hK⟩ := local_compact_nhds (f.2 q t ht2)
    have hV : {g : LSCFun | ∀ q' ∈ K, t < g.1 q'} ∈ 𝓝 f :=
      (isOpen_setOf_forall_lt hK t).mem_nhds fun q' hq' => hKsub hq'
    have hev : ∀ᶠ n in atTop, t ≤ (F n).1 (p n) := by
      filter_upwards [h hV, hp hKq] with n hn1 hn2
      exact (hn1 (p n) hn2).le
    exact absurd (le_liminf_of_le (by isBoundedDefault) hev) (not_le.2 ht1)
  refine ⟨hi, fun q => ?_⟩
  by_cases htop : f.1 q = ⊤
  · refine ⟨fun _ => q, tendsto_const_nhds, ?_⟩
    have h1 := hi (fun _ => q) q tendsto_const_nhds
    rw [htop] at h1 ⊢
    exact tendsto_of_le_liminf_of_limsup_le h1 le_top
  obtain ⟨s, -, hs_mem, hs_lim⟩ := exists_seq_strictAnti_tendsto' (lt_top_iff_ne_top.2 htop)
  obtain ⟨O, hO⟩ := (𝓝 q).exists_antitone_basis
  
  let P : ℕ → ℕ → Prop := fun n k => ∃ x ∈ O k, (F n).1 x < s k
  have hPev : ∀ k, ∀ᶠ n in atTop, P n k := by
    intro k
    have hmem : f ∈ {g : LSCFun | ∃ x ∈ interior (O k), g.1 x < s k} :=
      ⟨q, mem_interior_iff_mem_nhds.2 (hO.mem k), (hs_mem k).1⟩
    filter_upwards [h ((isOpen_setOf_exists_lt isOpen_interior (s k)).mem_nhds hmem)]
      with n ⟨x, hx, hxs⟩
    exact ⟨x, interior_subset hx, hxs⟩
  let ρ : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  have hρ : Tendsto ρ atTop atTop := by
    refine tendsto_atTop.2 fun K => ?_
    filter_upwards [hPev K, eventually_ge_atTop K] with n hn hKn
    exact Nat.le_findGreatest hKn hn
  have hPρ : ∀ᶠ n in atTop, P n (ρ n) := by
    filter_upwards [hPev 0] with n hn
    exact Nat.findGreatest_spec (Nat.zero_le n) hn
  let x : ℕ → ℂ × ℂ := fun n => if h : P n (ρ n) then h.choose else q
  have hxP : ∀ᶠ n in atTop, x n ∈ O (ρ n) ∧ (F n).1 (x n) < s (ρ n) := by
    filter_upwards [hPρ] with n hn
    simp only [x, dite_eq_left hn]
    exact hn.choose_spec
  have hx : Tendsto x atTop (𝓝 q) := by
    refine hO.1.tendsto_right_iff.2 fun K _ => ?_
    filter_upwards [hxP, hρ.eventually_ge_atTop K] with n hn hKn
    exact hO.2 hKn hn.1
  refine ⟨x, hx, tendsto_of_le_liminf_of_limsup_le (hi x q hx) ?_⟩
  calc limsup (fun n => (F n).1 (x n)) atTop ≤ limsup (fun n => s (ρ n)) atTop :=
        limsup_le_limsup (hxP.mono fun n hn => hn.2.le)
    _ = f.1 q := (hs_lim.comp hρ).limsup_eq

 

theorem tendsto_iff_lscTendsto
    {F : ℕ → LSCFun} {f : LSCFun} :
    Tendsto F atTop (𝓝 f) ↔ LSCTendsto (fun n => (F n).1) f.1 :=
  ⟨lscTendsto_of_tendsto, tendsto_of_lscTendsto⟩

end LSCFun

 

namespace LSCMetric

@[ext]
theorem ext {D D' : LSCMetric} (h : ∀ p, D p = D' p) : D = D' :=
  Subtype.ext (funext h)

theorem isInducing_toLSCFun : Topology.IsInducing (toLSCFun : LSCMetric → LSCFun) :=
  ⟨rfl⟩

theorem toLSCFun_apply (D : LSCMetric) (p : ℂ × ℂ) : D.toLSCFun.1 p = ((D p : ℝ≥0∞) : EReal) :=
  rfl

 
theorem lscTendsto_toLSCFun_iff {G : ℕ → LSCMetric} {D : LSCMetric} :
    LSCTendsto (fun n => (G n).toLSCFun.1) D.toLSCFun.1 ↔
      (∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
          D q ≤ liminf (fun n => G n (p n)) atTop) ∧
        ∀ q : ℂ × ℂ, ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
          Tendsto (fun n => G n (p n)) atTop (𝓝 (D q)) := by
  have hlim : ∀ u : ℕ → ℝ≥0∞, ((liminf u atTop : ℝ≥0∞) : EReal) =
      liminf (fun n => ((u n : ℝ≥0∞) : EReal)) atTop := fun u =>
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt u
      continuous_coe_ennreal_ereal.continuousAt
  have htend : ∀ (u : ℕ → ℝ≥0∞) (a : ℝ≥0∞), Tendsto (fun n => ((u n : ℝ≥0∞) : EReal)) atTop
      (𝓝 (a : EReal)) ↔ Tendsto u atTop (𝓝 a) := fun u a =>
    (EReal.isEmbedding_coe_ennreal.tendsto_nhds_iff).symm
  simp only [toLSCFun_apply, ← hlim, EReal.coe_ennreal_le_coe_ennreal_iff, LSCTendsto, htend]

 

theorem tendsto_iff
    {G : ℕ → LSCMetric} {D : LSCMetric} :
    Tendsto G atTop (𝓝 D) ↔
      (∀ (p : ℕ → ℂ × ℂ) (q : ℂ × ℂ), Tendsto p atTop (𝓝 q) →
          D q ≤ liminf (fun n => G n (p n)) atTop) ∧
        ∀ q : ℂ × ℂ, ∃ p : ℕ → ℂ × ℂ, Tendsto p atTop (𝓝 q) ∧
          Tendsto (fun n => G n (p n)) atTop (𝓝 (D q)) := by
  rw [isInducing_toLSCFun.tendsto_nhds_iff, ← lscTendsto_toLSCFun_iff]
  exact LSCFun.tendsto_iff_lscTendsto

 
theorem lowerSemicontinuous_iInf_of_isCompact {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) : LowerSemicontinuous fun D : LSCMetric => ⨅ q ∈ K, D q := by
  intro D t ht
  obtain ⟨s, hts, hs⟩ := exists_between ht
  have hopen : IsOpen {D : LSCMetric | ∀ q ∈ K, s < D q} := by
    have h := (LSCFun.isOpen_setOf_forall_lt hK (s : EReal)).preimage
      isInducing_toLSCFun.continuous
    simpa only [Set.preimage_ofPred_eq, toLSCFun_apply, EReal.coe_ennreal_lt_coe_ennreal_iff]
      using h
  have hD : D ∈ {D : LSCMetric | ∀ q ∈ K, s < D q} := fun q hq =>
    hs.trans_le (iInf₂_le q hq)
  filter_upwards [hopen.mem_nhds hD] with D' hD'
  exact hts.trans_le (le_iInf₂ fun q hq => (hD' q hq).le)

 
end LSCMetric


 

theorem acrossDist_eq_iInf_prod (D : LSCMetric) (A : EuclideanAnnulus) :
    acrossDist D A = ⨅ q ∈ A.innerBoundary ×ˢ A.outerBoundary, D q := by
  refine le_antisymm (le_iInf₂ fun q hq => ?_) (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
  · exact iInf₂_le_of_le q.1 hq.1 (iInf₂_le q.2 hq.2)
  · exact iInf₂_le (x, y) ⟨hx, hy⟩

 

theorem lowerSemicontinuous_acrossDist (A : EuclideanAnnulus) :
    LowerSemicontinuous fun D : LSCMetric => acrossDist D A := by
  simp only [acrossDist_eq_iInf_prod]
  exact LSCMetric.lowerSemicontinuous_iInf_of_isCompact
    ((isCompact_sphere A.center A.innerRadius).prod (isCompact_sphere A.center A.outerRadius))

theorem measurable_acrossDist (A : EuclideanAnnulus) :
    Measurable fun D : LSCMetric => acrossDist D A :=
  (lowerSemicontinuous_acrossDist A).measurable

 

 
theorem len_eq_partitionLengthSup (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = LQGMetric.MetricGeometry.partitionLengthSup (D.pt ∘ P) a b := by
  exact LQGMetric.MetricGeometry.curveLength_eq_partitionLengthSup (D.pt ∘ P) a b

theorem apply_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D (P a, P b) ≤ D.len P a b :=
  eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)

theorem weylScale_const (ξ c : ℝ) (D : LSCMetric) (hD : D.IsLengthSpace) (p : ℂ × ℂ) :
    weylScale ξ (ContinuousMap.const ℂ c) D p = ENNReal.ofReal (Real.exp (ξ * c)) * D p := by
  set K := ENNReal.ofReal (Real.exp (ξ * c)) with hK
  have hint : ∀ (P : ℝ → ℂ) (L : ℝ), ∫⁻ t in Icc 0 L,
      ENNReal.ofReal (Real.exp (ξ * (ContinuousMap.const ℂ c) (P t))) = K * ENNReal.ofReal L := by
    intro P L
    simp only [ContinuousMap.const_apply, lintegral_const, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, hK]
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne (D p) ⊤ with htop | htop
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne']
      exact le_top
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    set δ : ℝ := (ε : ℝ) / Real.exp (ξ * c) with hδ
    have hδpos : 0 < δ := div_pos (by exact_mod_cast hε) (Real.exp_pos _)
    have hKδ : K * ENNReal.ofReal δ = ε := by
      rw [hK, ← ENNReal.ofReal_mul (Real.exp_pos _).le, hδ,
        mul_div_cancel₀ _ (Real.exp_pos _).ne', ENNReal.ofReal_coe_nnreal]
    obtain ⟨P, a, b, hP, ha, hb, hlen⟩ := hD p.1 p.2 (lt_top_iff_ne_top.2 htop) δ hδpos
    have hL : LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨htop, ENNReal.ofReal_ne_top⟩) hlen
    obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ → ℂ, Q = LQGMetric.MetricGeometry.lengthParam (D.pt ∘ P) a b :=
      ⟨_, rfl⟩
    obtain ⟨L, hLdef⟩ :
        ∃ L : ℝ, L = (LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b).toReal := ⟨_, rfl⟩
    have hQc : D.IsCurve Q 0 L := by
      subst hQdef hLdef
      exact ⟨ENNReal.toReal_nonneg,
        (LQGMetric.MetricGeometry.lipschitzOnWith_lengthParam hP.1 hP.2 hL).continuousOn⟩
    have hQu : HasUnitSpeedOn (D.pt ∘ Q) (Icc 0 L) := by
      subst hQdef hLdef
      exact LQGMetric.MetricGeometry.hasUnitSpeedOn_lengthParam hP.1 hP.2 hL
    have hQ0 : Q 0 = p.1 := by
      subst hQdef
      have h0 := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hL
        (left_mem_Icc.2 hP.1)
      rw [variationOnFromTo.self] at h0
      exact h0.trans ha
    have hQL : Q L = p.2 := by
      subst hQdef hLdef
      have h1 := LQGMetric.MetricGeometry.lengthParam_variationOnFromTo hL
        (right_mem_Icc.2 hP.1)
      rw [variationOnFromTo.eq_of_le _ _ hP.1, Set.inter_self] at h1
      exact h1.trans hb
    calc weylScale ξ (ContinuousMap.const ℂ c) D p
        ≤ ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * (ContinuousMap.const ℂ c) (Q t))) :=
          iInf_le_of_le Q <| iInf_le_of_le L <| iInf_le_of_le hQc <| iInf_le_of_le hQu <|
            iInf_le_of_le hQ0 <| iInf_le_of_le hQL le_rfl
      _ = K * D.len P a b := by
          rw [hint, hLdef, ENNReal.ofReal_toReal hL]
          rfl
      _ ≤ K * (D p + ENNReal.ofReal δ) := by
          gcongr
      _ = K * D p + ε := by rw [mul_add, hKδ]
  · refine le_iInf fun P => le_iInf fun L => le_iInf fun hP => le_iInf fun hu =>
      le_iInf fun h0 => le_iInf fun hL => ?_
    rw [hint P L]
    have hlen : D.len P 0 L = ENNReal.ofReal L := by
      have h1 := hu (left_mem_Icc.2 hP.1) (right_mem_Icc.2 hP.1)
      rwa [Set.inter_self, NNReal.coe_one, one_mul, sub_zero] at h1
    gcongr
    calc D p = D (P 0, P L) := by rw [h0, hL]
      _ ≤ D.len P 0 L := apply_le_len D P hP.1
      _ = ENNReal.ofReal L := hlen

theorem toSet_dilate (A : EuclideanAnnulus) (r : ℝ) (hr : 0 < r) :
    (A.dilate r hr).toSet = r • A.toSet := by
  have hr₁ : ∀ B : EuclideanAnnulus, B.innerRadius ≠ 0 := fun B => B.2.1.ne'
  have toSet_eq : ∀ B : EuclideanAnnulus, B.toSet =
      {z | B.innerRadius < dist z B.center ∧ dist z B.center < B.outerRadius} := by
    intro B
    ext z
    simp only [EuclideanAnnulus.toSet, closure_ball _ (hr₁ B), mem_diff, Metric.mem_ball,
      Metric.mem_closedBall, not_le, mem_setOf_eq]
    exact and_comm
  have hd : ∀ w : ℂ, dist (r • w) (r • A.center) = r * dist w A.center := fun w => by
    rw [dist_smul₀, Real.norm_of_nonneg hr.le]
  ext z
  rw [toSet_eq, Set.mem_smul_set, toSet_eq]
  simp only [EuclideanAnnulus.dilate, EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, mem_setOf_eq] at hd ⊢
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨r⁻¹ • z, ⟨?_, ?_⟩, smul_inv_smul₀ hr.ne' z⟩
    · rw [← mul_lt_mul_iff_of_pos_left hr, ← hd, smul_inv_smul₀ hr.ne']
      exact h1
    · rw [← mul_lt_mul_iff_of_pos_left hr, ← hd, smul_inv_smul₀ hr.ne']
      exact h2
  · rintro ⟨w, ⟨h1, h2⟩, rfl⟩
    rw [hd]
    exact ⟨mul_lt_mul_of_pos_left h1 hr, mul_lt_mul_of_pos_left h2 hr⟩

end SupercriticalLQGUniqueness
