/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P7Bridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.InputsPLACompare
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Transport
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Objects.AnnulusTails.Finite

 






















set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Polylog

open LQGMetric LQGMetric.LFPP
open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)
open Uniqueness.Objects.CorrectedEvent (acr cann)

 
theorem acrossIn_eq_acr (D : LSCMetric) (z : ℂ) (r₁ r₂ : ℝ) :
    acrossIn D z r₁ r₂ = acr D z r₁ r₂ := by
  have hset : closedAnn z r₁ r₂ = cann z r₁ r₂ := by
    ext w; simp only [closedAnn, cann, mem_ofPred_eq, dist_eq_norm]
  unfold acrossIn compactPathInf acr
  refine iInf_congr fun P => iInf_congr fun a => iInf_congr fun b => iInf_congr fun _ => ?_
  rw [hset]
  apply le_antisymm
  · refine le_iInf fun hK => ?_
    exact iInf_le_of_le (fun t ht => hK ⟨t, ht, rfl⟩) le_rfl
  · refine le_iInf fun hK => ?_
    exact iInf_le_of_le (by rintro _ ⟨t, ht, rfl⟩; exact hK t ht) le_rfl

 
theorem acr_le_internalSetDist (D : LSCMetric) {V : Set ℂ} (hV : Bornology.IsBounded V)
    {v : ℂ} {c d : ℝ} (hcd : c ≤ d) (K₁ K₂ : Set V)
    (h₁ : ∀ x ∈ K₁, dist (x : ℂ) v ≤ c) (h₂ : ∀ y ∈ K₂, d ≤ dist (y : ℂ) v) :
    acr D v c d ≤ D.internalSetDist V K₁ K₂ := by
  unfold LSCMetric.internalSetDist LSCMetric.internal
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => le_iInf fun P => le_iInf fun a =>
    le_iInf fun b => le_iInf fun hP => le_iInf fun hPV => le_iInf fun ha => le_iInf fun hb => ?_
  have hbdd : Bornology.IsBounded (P '' Icc a b) :=
    hV.subset (by rintro _ ⟨t, ht, rfl⟩; exact hPV t ht)
  have hcont := Uniqueness.BiLipschitz.Barrier.continuousOn_of_isBounded D hP hbdd
  refine Uniqueness.Objects.AnnulusTails.acr_le_curve_of_endpoint_order D hP hcont hcd ?_ ?_
  · rw [ha]; exact h₁ x hx
  · rw [hb]; exact h₂ y hy

 
theorem acr_mono (D : LSCMetric) (v : ℂ) {c c' d d' : ℝ} (hc : c ≤ c') (hcd' : c' ≤ d')
    (hd : d' ≤ d) : acr D v c' d' ≤ acr D v c d := by
  conv_rhs => unfold acr
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hPK =>
    le_iInf fun ha => le_iInf fun hb => ?_
  have hbdd : Bornology.IsBounded (P '' Icc a b) :=
    (isBounded_closedBall (x := v) (r := d)).subset fun x hx => by
      rw [mem_closedBall]; exact (hPK hx).2
  have hcont := Uniqueness.BiLipschitz.Barrier.continuousOn_of_isBounded D hP hbdd
  refine Uniqueness.Objects.AnnulusTails.acr_le_curve_of_endpoint_order D hP hcont hcd' ?_ ?_
  · rw [mem_sphere] at ha; rw [ha]; exact hc
  · rw [mem_sphere] at hb; rw [hb]; exact hd

 

 
theorem internal_lfppMetric_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} {V : Set ℂ}
    (hV : IsOpen V) {K : ℝ} (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) (p : V × V) :
    (Median.lfppMetric ξ a φ').internal V p ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * (Median.lfppMetric ξ a φ).internal V p := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by simpa using Real.exp_pos _
  unfold LSCMetric.internal
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP =>
    le_iInf fun hPV => le_iInf fun hs => le_iInf fun ht => ?_
  have hP' : (Median.lfppMetric ξ a φ').IsCurve P s t :=
    (lfppMetric_isCurve_iff ξ a φ').2 ((lfppMetric_isCurve_iff ξ a φ).1 hP)
  exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP'
    (iInf_le_of_le hPV (iInf_le_of_le hs (iInf_le_of_le ht
      (lfppMetric_len_le_of_abs_sub_le ξ a hV hK ((lfppMetric_isCurve_iff ξ a φ).1 hP).2
        hPV)))))))

theorem internalSetDist_lfppMetric_le (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)}
    {V : Set ℂ} (hV : IsOpen V) {K : ℝ} (hK : ∀ x ∈ V, |φ' x - φ x| ≤ K) (K₁ K₂ : Set V) :
    (Median.lfppMetric ξ a φ').internalSetDist V K₁ K₂ ≤
      ENNReal.ofReal (Real.exp (|ξ| * K)) * (Median.lfppMetric ξ a φ).internalSetDist V K₁ K₂ := by
  have h0 : ENNReal.ofReal (Real.exp (|ξ| * K)) ≠ 0 := by simpa using Real.exp_pos _
  unfold LSCMetric.internalSetDist
  simp only [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  exact iInf₂_mono fun x _ => iInf₂_mono fun y _ => internal_lfppMetric_le ξ a hV hK (x, y)

 
theorem internal_lfppMetric_le_crossLenIn (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (U : Set ℂ) {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    (Median.lfppMetric ξ a φ).internal U (⟨z, hz⟩, ⟨w, hw⟩) ≤
      ENNReal.ofReal ((a : ℝ)⁻¹) * DDDF.crossLenIn ξ (⇑φ) U {z} {w} := by
  have h0 : ENNReal.ofReal ((a : ℝ)⁻¹) ≠ 0 := by
    have : (0 : ℝ) < a := a.2
    simpa using this
  rw [DDDF.crossLenIn_eq_biInf]
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun P => ?_
  rw [ENNReal.mul_iInf_of_ne h0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hP => ?_
  obtain ⟨z', hz', w', hw', hPath, hPU⟩ := hP
  rw [mem_singleton_iff] at hz' hw'
  subst hz' hw'
  have hc := Median.lfppMetric_isCurve ξ a φ hPath
  have hlen := Median.lfppMetric_len_le_lfppLen ξ a φ hPath
  have hint := Uniqueness.BiLipschitz.Barrier.internal_le_len' (Median.lfppMetric ξ a φ) hc hPU
  have e1 : (⟨P 0, hPU 0 ⟨le_rfl, zero_le_one⟩⟩ : U) = ⟨z', hz⟩ := Subtype.ext hPath.source
  have e2 : (⟨P 1, hPU 1 ⟨zero_le_one, le_rfl⟩⟩ : U) = ⟨w', hw⟩ := Subtype.ext hPath.target
  rw [e1, e2] at hint
  exact hint.trans hlen

 

 
lemma isPreconnected_real_segment (a b : ℝ) :
    IsPreconnected ((fun x : ℝ => (x : ℂ)) '' Icc a b) :=
  isPreconnected_Icc.image _ Complex.continuous_ofReal.continuousOn

 
theorem exists_real_points_of_disconnects {T : Set ℂ}
    (hT : T ⊆ (annAt 0 1 2 one_pos one_lt_two).toSet)
    (hD : Disconnects T (annAt 0 1 2 one_pos one_lt_two).innerBoundary
      (annAt 0 1 2 one_pos one_lt_two).outerBoundary) :
    (∃ x : ℝ, 1 < x ∧ x < 2 ∧ (x : ℂ) ∈ T) ∧ (∃ x : ℝ, -2 < x ∧ x < -1 ∧ (x : ℂ) ∈ T) := by
  have hin : ∀ y ∈ T, 1 < ‖y‖ ∧ ‖y‖ < 2 := fun y hy => by
    have := hT hy
    rw [annAt_toSet] at this
    simpa only [mem_ofPred_eq, sub_zero] using this
  constructor
  · by_contra hno
    push Not at hno
    refine hD ⟨_, isPreconnected_real_segment 1 2, ?_, ⟨1, ⟨1, ⟨le_rfl, one_le_two⟩, rfl⟩, ?_⟩,
      ⟨2, ⟨2, ⟨one_le_two, le_rfl⟩, rfl⟩, ?_⟩⟩
    · rintro _ ⟨x, hx, rfl⟩ hxT
      have hb := hin _ hxT
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [hx.1])] at hb
      exact hno x hb.1 hb.2 hxT
    · show ((1 : ℝ) : ℂ) ∈ sphere (0 : ℂ) 1
      simp
    · show ((2 : ℝ) : ℂ) ∈ sphere (0 : ℂ) 2
      simp
  · by_contra hno
    push Not at hno
    refine hD ⟨_, isPreconnected_real_segment (-2) (-1), ?_,
      ⟨((-1 : ℝ) : ℂ), ⟨-1, ⟨by norm_num, le_rfl⟩, rfl⟩, ?_⟩,
      ⟨((-2 : ℝ) : ℂ), ⟨-2, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩⟩
    · rintro _ ⟨x, hx, rfl⟩ hxT
      have hb := hin _ hxT
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith [hx.2])] at hb
      exact hno x (by linarith [hb.2]) (by linarith [hb.1]) hxT
    · show ((-1 : ℝ) : ℂ) ∈ sphere (0 : ℂ) 1
      simp
    · show ((-2 : ℝ) : ℂ) ∈ sphere (0 : ℂ) 2
      simp

 

theorem exists_loop_points_of_aroundDist_lt (D : LSCMetric) {U : Set ℂ}
    (hU : (annAt 0 1 2 one_pos one_lt_two).toSet ⊆ U) {Y : ℝ≥0∞}
    (hY : aroundDist D (annAt 0 1 2 one_pos one_lt_two) < Y) :
    ∃ (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U),
      ((1 < z.re ∧ z.re < 2 ∧ z.im = 0 ∧ -2 < w.re ∧ w.re < -1 ∧ w.im = 0) ∨
        (1 < w.re ∧ w.re < 2 ∧ w.im = 0 ∧ -2 < z.re ∧ z.re < -1 ∧ z.im = 0)) ∧
      D.internal U (⟨z, hz⟩, ⟨w, hw⟩) < Y := by
  unfold aroundDist at hY
  obtain ⟨P, hY⟩ := iInf_lt_iff.1 hY
  obtain ⟨a, hY⟩ := iInf_lt_iff.1 hY
  obtain ⟨b, hY⟩ := iInf_lt_iff.1 hY
  obtain ⟨hP, hY⟩ := iInf_lt_iff.1 hY
  obtain ⟨hPA, hY⟩ := iInf_lt_iff.1 hY
  obtain ⟨hPD, hlen⟩ := iInf_lt_iff.1 hY
  have hT : P '' Icc a b ⊆ (annAt 0 1 2 one_pos one_lt_two).toSet := by
    rintro _ ⟨t, ht, rfl⟩; exact hPA t ht
  obtain ⟨⟨x, hx1, hx2, ⟨u, hu, hPu⟩⟩, ⟨y, hy1, hy2, ⟨v, hv, hPv⟩⟩⟩ :=
    exists_real_points_of_disconnects hT hPD
  set s := min u v
  set t := max u v
  have hs : s ∈ Icc a b := ⟨le_min hu.1 hv.1, (min_le_left _ _).trans hu.2⟩
  have ht : t ∈ Icc a b := ⟨hu.1.trans (le_max_left _ _), max_le hu.2 hv.2⟩
  have hst : s ≤ t := min_le_max
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hPst : D.IsCurve P s t := ⟨hst, hP.2.mono hsub⟩
  have hPU : ∀ τ ∈ Icc s t, P τ ∈ U := fun τ hτ => hU (hPA τ (hsub hτ))
  have hint := Uniqueness.BiLipschitz.Barrier.internal_le_len' D hPst hPU
  have hlen' : D.len P s t ≤ D.len P a b :=
    LQGMetric.MetricGeometry.curveLength_mono _ hs.1 ht.2
  refine ⟨P s, P t, hPU s ⟨le_rfl, hst⟩, hPU t ⟨hst, le_rfl⟩, ?_, lt_of_le_of_lt (hint.trans hlen')
    hlen⟩
  rcases le_total u v with huv | huv
  · have es : s = u := min_eq_left huv
    have et : t = v := max_eq_right huv
    left
    rw [es, et, hPu, hPv]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hx1, hx2, trivial, hy1, hy2, trivial⟩
  · have es : s = v := min_eq_right huv
    have et : t = u := max_eq_left huv
    right
    rw [es, et, hPu, hPv]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨hx1, hx2, trivial, hy1, hy2, trivial⟩

end SupercriticalLQGUniqueness.B2.Polylog
