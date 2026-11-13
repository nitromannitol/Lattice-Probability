/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PathInfimum.PathInf




 




set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal
open LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness
namespace Uniqueness.Toolkit.CountableBase

 


theorem exists_lipschitz_path_range_eq
    {X : Type*} [EMetricSpace X] {x y : X}
    (γ : Path x y) (hL : pathLength γ ≠ ∞) :
    ∃ γ' : Path x y, pathLength γ' = pathLength γ ∧
      Set.range γ' = Set.range γ ∧
      LipschitzWith (pathLength γ).toNNReal γ' := by
  set P : ℝ → X := ⇑γ.extend
  have hPc : ContinuousOn P (Icc 0 1) := γ.continuous_extend.continuousOn
  have hL' : curveLength P 0 1 ≠ ∞ := hL
  set L : ℝ := (curveLength P 0 1).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set Q := lengthParam P 0 1
  have hlip := lipschitzOnWith_lengthParam zero_le_one hPc hL'
  have himg := variationOnFromTo_image_Icc zero_le_one hPc hL'
  have hmaps : ∀ s : unitInterval, L * (s : ℝ) ∈ Icc 0 L := fun s =>
    ⟨mul_nonneg hL0 s.2.1, mul_le_of_le_one_right hL0 s.2.2⟩
  have hQP : ∀ u ∈ Icc 0 L, ∃ t ∈ Icc (0 : ℝ) 1, Q u = P t := by
    intro u hu
    rw [← himg] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    exact ⟨t, ht, lengthParam_variationOnFromTo hL' ht⟩
  have hQ0 : Q 0 = x := by
    have h := lengthParam_variationOnFromTo hL'
      (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.self] at h
    exact h.trans (Path.extend_zero γ)
  have hQ1 : Q L = y := by
    have h := lengthParam_variationOnFromTo hL'
      (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
    rw [variationOnFromTo.eq_of_le _ _ zero_le_one, Set.inter_self] at h
    exact h.trans (Path.extend_one γ)
  have hlipI : LipschitzWith (pathLength γ).toNNReal
      (fun s : unitInterval => Q (L * s)) := by
    intro s t
    have h1 := hlip (hmaps s) (hmaps t)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.coe_one, one_mul, ENNReal.coe_toNNReal hL, edist_dist, edist_dist,
      Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hL0, ENNReal.ofReal_mul hL0,
      Subtype.dist_eq, Real.dist_eq,
      show ENNReal.ofReal L = pathLength γ from ENNReal.ofReal_toReal hL']
  let γ' : Path x y :=
    { toFun := fun s => Q (L * s)
      continuous_toFun := hlipI.continuous
      source' := by simpa using hQ0
      target' := by simpa using hQ1 }
  have hlen : pathLength γ' = pathLength γ := by
    unfold pathLength
    rw [curveLength_congr (Q := Q ∘ fun s => L * s) (fun t ht => by
      simp [γ', Path.extend_apply _ ht])]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
      (fun s _ t _ hst => mul_le_mul_of_nonneg_left hst hL0)]
    simp only [mul_zero, mul_one]
    exact curveLength_lengthParam zero_le_one hPc hL'
  have hrange : Set.range γ' = Set.range γ := by
    apply Set.Subset.antisymm
    · rintro _ ⟨s, rfl⟩
      obtain ⟨t, ht, hts⟩ := hQP _ (hmaps s)
      refine ⟨⟨t, ht⟩, ?_⟩
      change γ ⟨t, ht⟩ = Q (L * s)
      rw [hts]
      exact (Path.extend_apply γ ht).symm
    · rintro _ ⟨s, rfl⟩
      let u : ℝ := variationOnFromTo P (Icc 0 1) 0 s
      have hu : u ∈ Icc 0 L := by
        rw [← himg]
        exact ⟨s, s.2, rfl⟩
      have hscaled : u ∈ (fun z : ℝ => L * z) '' Icc 0 1 := by
        rw [image_mul_left_Icc hL0 zero_le_one, mul_zero, mul_one]
        exact hu
      obtain ⟨v, hv, hvu⟩ := hscaled
      change L * v = u at hvu
      refine ⟨⟨v, hv⟩, ?_⟩
      change Q (L * v) = γ s
      rw [hvu]
      change lengthParam P 0 1
        (variationOnFromTo P (Icc 0 1) 0 s) = γ s
      rw [lengthParam_variationOnFromTo hL' s.2]
      exact Path.extend_apply γ s.2
  exact ⟨γ', hlen, hrange, hlipI⟩


 

theorem exists_path_of_curve_range_eq
    {X : Type*} [PseudoEMetricSpace X] {P : ℝ → X} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    ∃ γ : Path (P a) (P b),
      pathLength γ = curveLength P a b ∧
      Set.range γ = P '' Icc a b := by
  set φ : ℝ → ℝ := fun t => a + t * (b - a)
  have hφmono : Monotone φ := fun s t hst => by
    simp only [φ]
    nlinarith [sub_nonneg.2 hab]
  have hφmaps : ∀ t : unitInterval, φ t ∈ Icc a b := fun t =>
    ⟨by simp only [φ]; nlinarith [t.2.1, sub_nonneg.2 hab],
      by simp only [φ]; nlinarith [t.2.2, sub_nonneg.2 hab]⟩
  have hφimage : φ '' Icc (0 : ℝ) 1 = Icc a b := by
    have hφ' : φ = fun t => (b - a) * t + a := by
      funext t
      simp only [φ, mul_comm, add_comm]
    rw [hφ']
    calc
      (fun t => (b - a) * t + a) '' Icc (0 : ℝ) 1 =
          (fun z => z + a) '' ((fun t => (b - a) * t) '' Icc 0 1) := by
            rw [Set.image_image]
      _ = Icc a b := by
        rw [image_mul_left_Icc (sub_nonneg.2 hab) zero_le_one,
          image_add_const_Icc]
        simp only [mul_zero, mul_one, zero_add, sub_add_cancel]
  let γ : Path (P a) (P b) :=
    { toFun := fun t => P (φ t)
      continuous_toFun := hP.comp_continuous (by fun_prop) hφmaps
      source' := by simp [φ]
      target' := by simp [φ] }
  have hlen : pathLength γ = curveLength P a b := by
    unfold pathLength
    rw [curveLength_congr (Q := P ∘ φ) (fun t ht => by
      simp [γ, Path.extend_apply _ ht])]
    rw [curveLength_comp_of_continuousOn_monotoneOn _ zero_le_one (by fun_prop)
      (hφmono.monotoneOn _)]
    simp [φ]
  have hrange : Set.range γ = P '' Icc a b := by
    calc
      Set.range γ = P '' (φ '' Icc (0 : ℝ) 1) := by
        ext z
        simp only [Set.mem_range, Set.mem_image]
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨φ t, ⟨t, t.2, rfl⟩, rfl⟩
        · rintro ⟨v, ⟨t, ht, rfl⟩, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      _ = P '' Icc a b := by rw [hφimage]
  exact ⟨γ, hlen, hrange⟩


 

theorem exists_lipschitz_reparam_range_eq
    (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ}
    (hP : D.IsCurve P a b) (hfin : D.len P a b ≠ ∞) :
    ∃ γ : Path (D.pt (P a)) (D.pt (P b)),
      pathLength γ = D.len P a b ∧
      Set.range (fun t : unitInterval => (γ t : ℂ)) = P '' Icc a b ∧
      LipschitzWith (D.len P a b).toNNReal γ := by
  obtain ⟨γ, hlen, hrange⟩ :=
    exists_path_of_curve_range_eq hP.1 hP.2
  obtain ⟨γ', hlen', hrange', hlip⟩ :=
    exists_lipschitz_path_range_eq γ (hlen ▸ hfin)
  refine ⟨γ', hlen'.trans hlen, ?_, ?_⟩
  · exact hrange'.trans hrange
  · change LipschitzWith
      (curveLength (D.pt ∘ P) a b).toNNReal γ'
    simpa only [hlen] using hlip


 

theorem compact_path_limit_separator
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D))
    {K E F : Set ℂ} (hK : IsCompact K)
    {P : ℕ → unitInterval → ℂ}
    (htrace : ∀ n t, P n t ∈ K)
    (hsep : ∀ n, Disconnects (Set.range (P n)) E F)
    {M : NNReal} (hLip : ∀ n, LipschitzWith M ((G n).pt ∘ P n))
    {L : ENNReal}
    (hbound : ∀ n, (G n).len
      (fun t => P n (projIcc 0 1 zero_le_one t)) 0 1 ≤ L) :
    ∃ P₀ : C(unitInterval, ℂ),
      D.IsCurve (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ∧
      (∀ t, P₀ t ∈ K) ∧
      Disconnects (Set.range P₀) E F ∧
      D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L := by
  obtain ⟨φ, P₀, hφ, hlim, htrace₀⟩ :=
    Toolkit.CompactPathInfimum.compact_trace_path_subseq hG hK htrace hLip
  have hGφ : Tendsto (fun n => G (φ n)) atTop (nhds D) :=
    hG.comp hφ.tendsto_atTop
  have hDlip : LipschitzWith M (D.pt ∘ P₀) :=
    Toolkit.PathInfimum.lipschitz_limit_of_epi hGφ hlim (fun n => hLip (φ n))
  have hcurve : D.IsCurve
      (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
    refine ⟨zero_le_one, ?_⟩
    exact (hDlip.continuous.comp continuous_projIcc).continuousOn
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => P (φ n) (projIcc 0 1 zero_le_one t))
        atTop (nhds (P₀ (projIcc 0 1 zero_le_one t))) :=
    fun t _ => hlim.tendsto_at (projIcc 0 1 zero_le_one t)
  have hlen := Toolkit.CompactPathInfimum.joint_len_le_liminf hGφ hpoint
  have hlen' : D.len
      (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 ≤ L :=
    hlen.trans (liminf_le_of_frequently_le'
      (Frequently.of_forall fun n => hbound (φ n)))
  have hcont : ∀ n, Continuous (P n) := fun n =>
    Toolkit.CompactPathInfimum.continuous_euclidean_of_metric_on_compact
      (G n) hK (htrace n) (hLip n).continuous
  let Q : ℕ → C(unitInterval, ℂ) := fun n => ⟨P n, hcont n⟩
  have hsep₀ : Disconnects (Set.range P₀) E F :=
    Toolkit.PathInfimum.separator_stable_of_uniform_limit E F
      (P := fun n => Q (φ n)) hlim (fun n => hsep (φ n))
  exact ⟨P₀, hcurve, htrace₀, hsep₀, hlen'⟩


 
def compactSepInf (D : LSCMetric) (K E F : Set ℂ) : ENNReal :=
  ⨅ (P : ℝ → ℂ) (a : ℝ) (b : ℝ) (_ : D.IsCurve P a b)
    (_ : ∀ t ∈ Icc a b, P t ∈ K)
    (_ : Disconnects (P '' Icc a b) E F), D.len P a b

private theorem compactSepInf_le (D : LSCMetric) {K E F : Set ℂ}
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b)
    (hK : ∀ t ∈ Icc a b, P t ∈ K)
    (hsep : Disconnects (P '' Icc a b) E F) :
    compactSepInf D K E F ≤ D.len P a b := by
  exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
    iInf_le_of_le hP <| iInf_le_of_le hK <|
    iInf_le_of_le hsep le_rfl

 
theorem compactSepInf_seq_liminf
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (nhds D))
    {K E F : Set ℂ} (hK : IsCompact K) :
    compactSepInf D K E F ≤
      liminf (fun n => compactSepInf (G n) K E F) atTop := by
  refine le_of_forall_lt fun v hv => ?_
  obtain ⟨w, hvw, hw⟩ := exists_between hv
  have hwfin : w ≠ ∞ := ne_top_of_lt hw
  have htail : ∀ᶠ n in atTop, w ≤ compactSepInf (G n) K E F := by
    by_contra hn
    rw [not_eventually] at hn
    obtain ⟨φ, hφ, hbad⟩ := extraction_of_frequently_atTop hn
    have hbad' : ∀ n, compactSepInf (G (φ n)) K E F < w :=
      fun n => lt_of_not_ge (hbad n)
    have hpaths : ∀ n, ∃ (P : ℝ → ℂ) (a b : ℝ),
        (G (φ n)).IsCurve P a b ∧
        (∀ t ∈ Icc a b, P t ∈ K) ∧
        Disconnects (P '' Icc a b) E F ∧
        (G (φ n)).len P a b < w := by
      intro n
      unfold compactSepInf at hbad'
      obtain ⟨P, a, b, hP, htr, hsep, hcost⟩ :=
        (by simpa only [iInf_lt_iff] using hbad' n)
      exact ⟨P, a, b, hP, htr, hsep, hcost⟩
    choose P a b hP htrace hsep hlen using hpaths
    have hfin : ∀ n, (G (φ n)).len (P n) (a n) (b n) ≠ ∞ :=
      fun n => ne_top_of_lt (hlen n)
    choose γ hγlen hγrange hγlip using fun n =>
      exists_lipschitz_reparam_range_eq (G (φ n)) (P n) (hP n) (hfin n)
    let Q : ℕ → unitInterval → ℂ := fun n t => γ n t
    have hQtrace : ∀ n t, Q n t ∈ K := by
      intro n t
      have hEq : Set.range (Q n) = P n '' Icc (a n) (b n) := hγrange n
      have hmem : Q n t ∈ Set.range (Q n) := Set.mem_range_self t
      rw [hEq] at hmem
      obtain ⟨s, hs, hst⟩ := hmem
      exact hst ▸ htrace n s hs
    have hQsep : ∀ n, Disconnects (Set.range (Q n)) E F := by
      intro n
      have hEq : Set.range (Q n) = P n '' Icc (a n) (b n) := hγrange n
      exact hEq.symm ▸ hsep n
    have hQlip : ∀ n, LipschitzWith w.toNNReal
        ((G (φ n)).pt ∘ Q n) := by
      intro n
      have hmono : ((G (φ n)).len (P n) (a n) (b n)).toNNReal ≤ w.toNNReal :=
        ENNReal.toNNReal_mono hwfin (hlen n).le
      exact (hγlip n).weaken hmono
    have hQbound : ∀ n,
        (G (φ n)).len
          (fun t => Q n (projIcc 0 1 zero_le_one t)) 0 1 ≤ w := by
      intro n
      change pathLength (γ n) ≤ w
      exact (hγlen n).le.trans (hlen n).le
    obtain ⟨P₀, hP₀, hK₀, hsep₀, hlen₀⟩ :=
      compact_path_limit_separator
        (hG.comp hφ.tendsto_atTop) hK hQtrace hQsep hQlip hQbound
    have hInf : compactSepInf D K E F ≤
        D.len (fun t => P₀ (projIcc 0 1 zero_le_one t)) 0 1 := by
      apply compactSepInf_le D _ 0 1 hP₀
      · intro t ht
        rw [projIcc_of_mem zero_le_one ht]
        exact hK₀ ⟨t, ht⟩
      · convert hsep₀ using 1
        ext z
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, by simp only [projIcc_of_mem zero_le_one ht]⟩
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.2, by simp only [projIcc_of_mem zero_le_one t.2]⟩
    exact (not_le_of_gt hw) (hInf.trans hlen₀)
  exact hvw.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) htail)


theorem compactSepInf_lsc {K E F : Set ℂ} (hK : IsCompact K) :
    LowerSemicontinuous (fun D : LSCMetric => compactSepInf D K E F) := by
  apply (lowerSemicontinuous_iff_seq).2
  intro G D hG
  exact compactSepInf_seq_liminf hG hK

theorem compactSepInf_measurable {K E F : Set ℂ} (hK : IsCompact K) :
    Measurable (fun D : LSCMetric => compactSepInf D K E F) :=
  (compactSepInf_lsc hK).measurable


theorem annulus_toSet_open (A : EuclideanAnnulus) : IsOpen A.toSet := by
  unfold EuclideanAnnulus.toSet
  exact Metric.isOpen_ball.sdiff isClosed_closure

theorem annulus_toSet_bounded (A : EuclideanAnnulus) :
    Bornology.IsBounded A.toSet := by
  unfold EuclideanAnnulus.toSet
  exact Metric.isBounded_ball.subset Set.sdiff_subset

 

theorem aroundDist_eq_iInf_compactSepInf
    (D : LSCMetric) (A : EuclideanAnnulus)
    (H : CompactExhaustion A.toSet) :
    aroundDist D A =
      ⨅ n : ℕ, compactSepInf D ((H n).image Subtype.val)
        A.innerBoundary A.outerBoundary := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun n => ?_
    unfold compactSepInf
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hK => le_iInf fun hsep => ?_
    have hA : ∀ t ∈ Icc a b, P t ∈ A.toSet := by
      intro t ht
      obtain ⟨u, -, hu⟩ := hK t ht
      exact hu ▸ u.2
    unfold aroundDist
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <|
      iInf_le_of_le hP <| iInf_le_of_le hA <|
      iInf_le_of_le hsep le_rfl
  · unfold aroundDist
    refine le_iInf fun P => le_iInf fun a => le_iInf fun b =>
      le_iInf fun hP => le_iInf fun hA => le_iInf fun hsep => ?_
    obtain ⟨n, hn⟩ :=
      curve_trace_in_compact_exhaustion D (annulus_toSet_bounded A) H hP hA
    refine (iInf_le
      (fun n : ℕ => compactSepInf D ((H n).image Subtype.val)
        A.innerBoundary A.outerBoundary) n).trans ?_
    exact compactSepInf_le D P a b hP hn hsep

 

theorem aroundBoundedAnnulus_borel (A : EuclideanAnnulus) :
    Measurable (fun D : LSCMetric => aroundDist D A) := by
  letI : LocallyCompactSpace A.toSet :=
    (annulus_toSet_open A).locallyCompactSpace
  let H : CompactExhaustion A.toSet := CompactExhaustion.choice A.toSet
  have hm (n : ℕ) :
      Measurable (fun D : LSCMetric =>
        compactSepInf D ((H n).image Subtype.val)
          A.innerBoundary A.outerBoundary) :=
    compactSepInf_measurable
      ((H.isCompact n).image continuous_subtype_val)
  have hmi : Measurable (fun D : LSCMetric =>
      ⨅ n : ℕ, compactSepInf D ((H n).image Subtype.val)
        A.innerBoundary A.outerBoundary) := Measurable.iInf hm
  convert hmi using 1
  funext D
  exact aroundDist_eq_iInf_compactSepInf D A H


end Uniqueness.Toolkit.CountableBase
end SupercriticalLQGUniqueness
