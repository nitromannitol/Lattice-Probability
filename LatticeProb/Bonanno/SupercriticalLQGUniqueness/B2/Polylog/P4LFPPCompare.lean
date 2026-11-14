/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Median.LFPPMetric
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_1Ratio
import LatticeProb.Bonanno.LQGMetric.LFPP.ContMetric

 

















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP

 

 

lemma lfppLen_ge_of_exit {ξ : ℝ} {φ : ℂ → ℝ} {P : ℝ → ℂ} {x y : ℂ}
    (hP : IsPiecewiseC1Path P x y) {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 ≤ m)
    (hmE : ∀ u ∈ closedBall x ρ, m ≤ Real.exp (ξ * φ u)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hout : ρ ≤ ‖P t - x‖) : ENNReal.ofReal (m * ρ) ≤ lfppLen ξ φ P := by
  have ht0 : 0 < t := by
    rcases ht.1.lt_or_eq with h | h
    · exact h
    · subst h; rw [hP.source, sub_self, norm_zero] at hout; linarith
  have hsub := isPiecewiseC1Path_subPath hP le_rfl ht0 ht.2
  have h1 := le_lfppLen_of_path (ξ := ξ) (φ := φ) hsub hρ hm (by rw [hP.source]; exact hmE)
  rw [lfppLen_subPath P ht0, hP.source, min_eq_left hout] at h1
  calc ENNReal.ofReal (m * ρ) ≤ ∫⁻ u in Icc 0 t, lenDens ξ φ P u := h1
    _ ≤ ∫⁻ u in Icc 0 1, lenDens ξ φ P u := lintegral_mono_set (Icc_subset_Icc le_rfl ht.2)
    _ = lfppLen ξ φ P := (lfppLen_eq ξ φ P).symm

 

lemma lfppDOn_ball_le_lfppD {ξ : ℝ} {φ : ℂ → ℝ} {x y : ℂ} {ρ m : ℝ} (hρ : 0 < ρ) (hm : 0 ≤ m)
    (hmE : ∀ u ∈ closedBall x ρ, m ≤ Real.exp (ξ * φ u))
    (hd : lfppD ξ φ x y < ENNReal.ofReal (m * ρ)) :
    lfppDOn ξ φ (ball x ρ) x y ≤ lfppD ξ φ x y := by
  have hin : ∀ P : ℝ → ℂ, IsPiecewiseC1Path P x y → lfppLen ξ φ P < ENNReal.ofReal (m * ρ) →
      ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ ball x ρ := by
    intro P hP hlt t ht
    by_contra hc
    rw [mem_ball, not_lt, dist_eq_norm] at hc
    exact absurd (lfppLen_ge_of_exit hP hρ hm hmE ht hc) (not_le.2 hlt)
  have hball : lfppDOn ξ φ (ball x ρ) x y < ENNReal.ofReal (m * ρ) := by
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 hd
    exact lt_of_le_of_lt (iInf_le_of_le ⟨P.1, P.2.1, hin P.1 P.2.1 hP⟩ le_rfl) hP
  refine le_iInf fun P => ?_
  by_cases hlt : lfppLen ξ φ P.1 < ENNReal.ofReal (m * ρ)
  · exact iInf_le_of_le ⟨P.1, P.2.1, hin P.1 P.2.1 hlt⟩ le_rfl
  · exact hball.le.trans (not_lt.1 hlt)

lemma lfppD_le_lfppDOn {ξ : ℝ} {φ : ℂ → ℝ} (S : Set ℂ) (x y : ℂ) :
    lfppD ξ φ x y ≤ lfppDOn ξ φ S x y :=
  le_iInf fun P => iInf_le_of_le ⟨P.1, P.2.1, fun _ _ => mem_univ _⟩ le_rfl

 


lemma exists_lfppD_le_of_abs_sub_le {ξ : ℝ} {φ φ' : ℂ → ℝ} (hφ : Continuous φ) {V T : Set ℂ}
    (hV : IsOpen V) (hT : IsCompact T) (hTV : T ⊆ V) {K : ℝ}
    (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) :
    ∃ η > 0, ∀ x ∈ T, ∀ y : ℂ, ‖y - x‖ < η →
      lfppD ξ φ' x y ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) * lfppD ξ φ x y := by
  obtain ⟨δ, hδ, hδV⟩ := hT.exists_thickening_subset_open hV hTV
  set ρ := δ / 2 with hρdef
  have hρ : 0 < ρ := by positivity
  obtain ⟨B₀, hB₀⟩ := (hT.cthickening (r := ρ)).exists_bound_of_continuousOn hφ.continuousOn
  set B := max B₀ 0
  have hB : ∀ x ∈ cthickening ρ T, |φ x| ≤ B := fun x hx => by
    rw [← Real.norm_eq_abs]; exact (hB₀ x hx).trans (le_max_left _ _)
  set m := Real.exp (-(|ξ| * B))
  set Mx := Real.exp (|ξ| * B)
  have hm0 : 0 < m := Real.exp_pos _
  have hMx : 0 < Mx := Real.exp_pos _
  have hlow : ∀ u ∈ cthickening ρ T, m ≤ Real.exp (ξ * φ u) := fun u hu => Real.exp_le_exp.2 (by
    have h1 := hB u hu
    have h2 : -(|ξ| * |φ u|) ≤ ξ * φ u := by rw [← abs_mul]; exact neg_abs_le _
    have h3 : |ξ| * |φ u| ≤ |ξ| * B := mul_le_mul_of_nonneg_left h1 (abs_nonneg ξ)
    linarith)
  have hup : ∀ u ∈ cthickening ρ T, Real.exp (ξ * φ u) ≤ Mx := fun u hu => Real.exp_le_exp.2 (by
    have h1 := hB u hu
    have h2 : ξ * φ u ≤ |ξ| * |φ u| := by rw [← abs_mul]; exact le_abs_self _
    have h3 : |ξ| * |φ u| ≤ |ξ| * B := mul_le_mul_of_nonneg_left h1 (abs_nonneg ξ)
    linarith)
  set η := min ρ (m * ρ / (2 * Mx))
  have hη : 0 < η := lt_min hρ (by positivity)
  refine ⟨η, hη, fun x hx y hy => ?_⟩
  have hball : closedBall x ρ ⊆ cthickening ρ T := closedBall_subset_cthickening hx ρ
  have hballV : ball x ρ ⊆ V := fun u hu =>
    hδV (mem_thickening_iff.2 ⟨x, hx, by rw [mem_ball] at hu; linarith⟩)
  have hyρ : ‖y - x‖ ≤ ρ := (le_of_lt hy).trans (min_le_left _ _)
  have hseg : lfppD ξ φ x y < ENNReal.ofReal (m * ρ) := by
    have h1 : lfppD ξ φ x y ≤ lfppLen ξ φ (segPath x y) :=
      lfppDOn_le (isPiecewiseC1Path_segPath x y) fun _ _ => mem_univ _
    have h2 := lfppLen_segPath_le (ξ := ξ) (φ := φ) x y (B := Mx) fun u hu =>
      hup u (hball (closedBall_subset_closedBall hyρ hu))
    have h3 : Mx * ‖y - x‖ < m * ρ := by
      have : ‖y - x‖ < m * ρ / (2 * Mx) := lt_of_lt_of_le hy (min_le_right _ _)
      calc Mx * ‖y - x‖ < Mx * (m * ρ / (2 * Mx)) := mul_lt_mul_of_pos_left this hMx
        _ = m * ρ / 2 := by field_simp
        _ < m * ρ := by linarith [mul_pos hm0 hρ]
    exact lt_of_le_of_lt (h1.trans h2) ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 h3)
  calc lfppD ξ φ' x y ≤ lfppDOn ξ φ' (ball x ρ) x y := lfppD_le_lfppDOn _ x y
    _ ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) * lfppDOn ξ φ (ball x ρ) x y :=
        DFGPS.lfppDOn_le_of_abs_sub_le (fun u hu => hK u (hballV hu)) x y
    _ ≤ ENNReal.ofReal (Real.exp (|ξ| * K)) * lfppD ξ φ x y :=
        mul_le_mul_right (lfppDOn_ball_le_lfppD hρ hm0.le (fun u hu => hlow u (hball hu)) hseg) _

 

lemma eVariationOn_le_mul_of_edist_le {E E' : Type*} [PseudoEMetricSpace E]
    [PseudoEMetricSpace E'] {F : ℝ → E} {G : ℝ → E'} {c : ℝ≥0∞} {S : Set ℝ}
    (h : ∀ s ∈ S, ∀ t ∈ S, edist (F s) (F t) ≤ c * edist (G s) (G t)) :
    eVariationOn F S ≤ c * eVariationOn G S := by
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1, edist (F (p.2.1 (i + 1))) (F (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, c * edist (G (p.2.1 (i + 1))) (G (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => h _ (p.2.2.2 _) _ (p.2.2.2 _)
    _ = c * ∑ i ∈ Finset.range p.1, edist (G (p.2.1 (i + 1))) (G (p.2.1 i)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ c * eVariationOn G S := mul_le_mul_right (eVariationOn.sum_le p.2.2.1 p.2.2.2) c

lemma eVariationOn_add_Icc {E : Type*} [PseudoEMetricSpace E] (F : ℝ → E) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    eVariationOn F (Icc a b) + eVariationOn F (Icc b c) = eVariationOn F (Icc a c) := by
  have := eVariationOn.Icc_add_Icc F (s := univ) hab hbc (mem_univ b)
  simpa only [univ_inter] using this

 
lemma eVariationOn_Icc_le_mul_of_local {E E' : Type*} [PseudoEMetricSpace E]
    [PseudoEMetricSpace E'] {F : ℝ → E} {G : ℝ → E'} {c : ℝ≥0∞} {τ : ℝ} (hτ : 0 < τ) {s t : ℝ}
    (h : ∀ u ∈ Icc s t, ∀ v ∈ Icc s t, |u - v| < τ →
      edist (F u) (F v) ≤ c * edist (G u) (G v)) :
    eVariationOn F (Icc s t) ≤ c * eVariationOn G (Icc s t) := by
  have key : ∀ n : ℕ, ∀ a : ℝ, s ≤ a → a ≤ t → t - a ≤ n * (τ / 2) →
      eVariationOn F (Icc a t) ≤ c * eVariationOn G (Icc a t) := by
    intro n
    induction n with
    | zero =>
      intro a _ hat hn
      have : a = t := le_antisymm hat (by simpa using hn)
      subst this
      rw [eVariationOn.subsingleton F (subsingleton_Icc_of_ge le_rfl)]
      exact zero_le
    | succ n ih =>
      intro a hsa hat hn
      set b := min t (a + τ / 2)
      have hab : a ≤ b := le_min hat (by linarith)
      have hbt : b ≤ t := min_le_left _ _
      have hb2 : t - b ≤ n * (τ / 2) := by
        simp only [b]
        rcases le_total t (a + τ / 2) with h1 | h1
        · rw [min_eq_left h1, sub_self]; positivity
        · rw [min_eq_right h1]; push_cast at hn; linarith
      have h1 : eVariationOn F (Icc a b) ≤ c * eVariationOn G (Icc a b) :=
        eVariationOn_le_mul_of_edist_le fun u hu v hv => h u ⟨hsa.trans hu.1, hu.2.trans hbt⟩ v
          ⟨hsa.trans hv.1, hv.2.trans hbt⟩ (by
            rw [abs_lt]
            constructor <;> linarith [hu.1, hu.2, hv.1, hv.2, min_le_right t (a + τ / 2)])
      have h2 := ih b (hsa.trans hab) hbt hb2
      rw [← eVariationOn_add_Icc F hab hbt, ← eVariationOn_add_Icc G hab hbt, mul_add]
      exact add_le_add h1 h2
  rcases le_or_gt s t with hst | hst
  · obtain ⟨n, hn⟩ := exists_nat_ge ((t - s) / (τ / 2))
    exact key n s le_rfl hst (by rwa [div_le_iff₀ (by positivity)] at hn)
  · rw [Icc_eq_empty (not_le.2 hst), eVariationOn.subsingleton F subsingleton_empty]
    exact zero_le

 


theorem lfppMetric_len_le_of_abs_sub_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {V : Set ℂ} (hV : IsOpen V) {K : ℝ} (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) {γ : ℝ → ℂ} {s t : ℝ}
    (hγ : ContinuousOn γ (Icc s t)) (hγV : ∀ u ∈ Icc s t, γ u ∈ V) :
    (Median.lfppMetric ξ a φ').len γ s t ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * (Median.lfppMetric ξ a φ).len γ s t := by
  set T := γ '' Icc s t
  have hT : IsCompact T := isCompact_Icc.image_of_continuousOn hγ
  have hTV : T ⊆ V := by rintro _ ⟨u, hu, rfl⟩; exact hγV u hu
  obtain ⟨η, hη, hloc⟩ := exists_lfppD_le_of_abs_sub_le (ξ := ξ) (φ' := φ') φ.continuous hV hT hTV hK
  obtain ⟨τ, hτ, hτη⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ) η hη
  unfold LSCMetric.len
  refine eVariationOn_Icc_le_mul_of_local hτ fun u hu v hv huv => ?_
  show (Median.lfppMetric ξ a φ') (γ u, γ v) ≤ _ * (Median.lfppMetric ξ a φ) (γ u, γ v)
  rw [Median.lfppMetric_apply, Median.lfppMetric_apply, LscTop.lfppDistance_eq_lfppD,
    LscTop.lfppDistance_eq_lfppD]
  have hd : ‖γ v - γ u‖ < η := by
    have := hτη u hu v hv (by rwa [Real.dist_eq])
    rwa [dist_comm, dist_eq_norm] at this
  have := hloc (γ u) ⟨u, hu, rfl⟩ (γ v) hd
  calc ENNReal.ofReal ((a : ℝ)⁻¹) * lfppD ξ (⇑φ') (γ u) (γ v)
      ≤ ENNReal.ofReal ((a : ℝ)⁻¹) * (ENNReal.ofReal (Real.exp (|ξ| * K)) *
          lfppD ξ (⇑φ) (γ u) (γ v)) := mul_le_mul_right this _
    _ = _ := by ring

 

 

lemma isCurve_iff_of_euclidean (D : LSCMetric) (hc : Continuous fun p : ℂ × ℂ => D p)
    (hsmall : ∀ x : ℂ, ∀ ε > 0, ∃ δ > 0, ∀ y : ℂ, D (x, y) < ENNReal.ofReal δ → ‖x - y‖ < ε)
    {γ : ℝ → ℂ} {s t : ℝ} :
    D.IsCurve γ s t ↔ s ≤ t ∧ ContinuousOn γ (Icc s t) := by
  refine ⟨fun hD => ⟨hD.1, fun u hu => ?_⟩, fun hE => ⟨hE.1, fun u hu => ?_⟩⟩
  · have h1 := tendsto_iff_edist_tendsto_0.1 (hD.2 u hu)
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    obtain ⟨δ, hδ, hsm⟩ := hsmall (γ u) ε hε
    have h2 := h1.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hδ))
    filter_upwards [h2] with v hv
    have hv' : D (γ u, γ v) < ENNReal.ofReal δ := by
      rw [D.isExtMetric.2.2.1]; exact hv
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    exact hsm (γ v) hv'
  · refine tendsto_iff_edist_tendsto_0.2 ?_
    have h1 : Tendsto (fun v => ((γ v, γ u) : ℂ × ℂ)) (𝓝[Icc s t] u) (𝓝 (γ u, γ u)) :=
      (hE.2 u hu).prodMk_nhds tendsto_const_nhds
    have h2 := (hc.tendsto (γ u, γ u)).comp h1
    rw [D.isExtMetric.1] at h2
    exact h2

lemma lfppMetric_continuous (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    Continuous fun p : ℂ × ℂ => Median.lfppMetric ξ a φ p :=
  (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).comp (LscTop.continuous_lfppDistance ξ φ)

lemma lfppMetric_small (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (x : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y : ℂ, Median.lfppMetric ξ a φ (x, y) < ENNReal.ofReal δ → ‖x - y‖ < ε := by
  obtain ⟨δ, hδ, hsm⟩ := lfppDReal_euclidean_of_small (ξ := ξ) φ.continuous x ε hε
  have ha := a.2
  refine ⟨δ / (a : ℝ), div_pos hδ ha, fun y hy => hsm y ?_⟩
  rw [Median.lfppMetric_apply, LscTop.lfppDistance_eq_lfppD] at hy
  have hfin : lfppD ξ (⇑φ) x y ≠ ∞ := lfppD_ne_top φ.continuous x y
  have h1 : lfppD ξ (⇑φ) x y = ENNReal.ofReal (lfppDReal ξ φ (x, y)) :=
    (ENNReal.ofReal_toReal hfin).symm
  rw [h1, ← ENNReal.ofReal_mul (inv_nonneg.2 (le_of_lt ha))] at hy
  have h2 := (ENNReal.ofReal_lt_ofReal_iff (div_pos hδ ha)).1 hy
  have h3 : 0 ≤ lfppDReal ξ φ (x, y) := ENNReal.toReal_nonneg
  rw [lt_div_iff₀ ha] at h2
  calc lfppDReal ξ φ (x, y) = (a : ℝ)⁻¹ * lfppDReal ξ φ (x, y) * a := by
        rw [inv_mul_eq_div, div_mul_cancel₀ _ (ne_of_gt ha)]
    _ < δ := h2

theorem lfppMetric_isCurve_iff (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) {γ : ℝ → ℂ}
    {s t : ℝ} : (Median.lfppMetric ξ a φ).IsCurve γ s t ↔ s ≤ t ∧ ContinuousOn γ (Icc s t) :=
  isCurve_iff_of_euclidean _ (lfppMetric_continuous ξ a φ) (lfppMetric_small ξ a φ)

 

 
theorem compactPathInf_lfppMetric_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {V : Set ℂ} (hV : IsOpen V) {K : ℝ} (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) {S E F : Set ℂ}
    (hSV : S ⊆ V) :
    Uniqueness.Toolkit.CompactPathInfimum.compactPathInf (Median.lfppMetric ξ a φ') S E F ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) *
        Uniqueness.Toolkit.CompactPathInfimum.compactPathInf (Median.lfppMetric ξ a φ) S E F := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by simpa using Real.exp_pos _
  unfold Uniqueness.Toolkit.CompactPathInfimum.compactPathInf
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hPS => le_iInf fun hE => le_iInf fun hF => ?_
  have hP' : (Median.lfppMetric ξ a φ').IsCurve P s t :=
    (lfppMetric_isCurve_iff ξ a φ').2 ((lfppMetric_isCurve_iff ξ a φ).1 hP)
  exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP'
    (iInf_le_of_le hPS (iInf_le_of_le hE (iInf_le_of_le hF
      (lfppMetric_len_le_of_abs_sub_le ξ a hV hK ((lfppMetric_isCurve_iff ξ a φ).1 hP).2
        fun u hu => hSV (hPS u hu))))))))

 
theorem aroundDist_lfppMetric_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {V : Set ℂ} (hV : IsOpen V) {K : ℝ} (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) {A : EuclideanAnnulus}
    (hAV : A.toSet ⊆ V) :
    aroundDist (Median.lfppMetric ξ a φ') A ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * aroundDist (Median.lfppMetric ξ a φ) A := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by simpa using Real.exp_pos _
  unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hPA => le_iInf fun hD => ?_
  have hP' : (Median.lfppMetric ξ a φ').IsCurve P s t :=
    (lfppMetric_isCurve_iff ξ a φ').2 ((lfppMetric_isCurve_iff ξ a φ).1 hP)
  exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP'
    (iInf_le_of_le hPA (iInf_le_of_le hD
      (lfppMetric_len_le_of_abs_sub_le ξ a hV hK ((lfppMetric_isCurve_iff ξ a φ).1 hP).2
        fun u hu => hAV (hPA u hu)))))))

end SupercriticalLQGUniqueness.B2.Polylog
