/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510C6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.L510C5

/-!
# GM Lemma 5.10, condition (6): the union bound (task P2-M2M6)

See `L510C5.lean`. `gm_L510Bdy` proves `L510BdyG` (= `L510Bdy` of `L510B.lean` with the range
`0 < γ < 2`) from DFGPS Prop 4.1 (`Blueprint.DFGPSProp4_1`, = GM Lemma 2.10) and
`Blueprint.GMXiQBound` (GM l. 1056), following GM l. 3322.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- `L510Bdy` (condition (6), `L510B.lean`) with the range `0 < γ < 2` -/
def L510BdyG : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c →
  ∀ {ε₀ A q : ℝ}, 0 < ε₀ → 0 < A → 0 < q → ∃ ζ : ℝ, 0 < ζ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
    P {ω | ¬ ∀ V : Set ℂ, IsOpen V → IsConnected V →
      IsSquareTube V (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} →
      ∀ (Q : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn Q (Icc s t) →
        Q '' Icc s t ⊆ Metric.thickening (2 * ζ * r) (frontier V) →
        ε₀ * r / 100 ≤ Metric.diam (Q '' Icc s t) →
        ENNReal.ofReal (100 * A * scaleFac (xiGamma γ) c (h ω) r 0) ≤ (D (h ω)).len Q s t} ≤
      ENNReal.ofReal q

/-- the deterministic part of condition (6): a path of diameter `≥ ε₀r/100` near the frontier of
a tube has a sub-path near one clipped grid line with end points `ε₀r/800` apart -/
lemma l510_bdy_det {ε₀ r ζ : ℝ} (hε₀ : 0 < ε₀) (hr : 0 < r) (hζ0 : 0 < ζ)
    (hζ : ζ ≤ ε₀ / 6400) (hζ1 : ζ ≤ 1 / 2) {F : Finset (ℤ × ℤ)}
    (hF : ∀ m ∈ F, (gridSquare (ε₀ * r) m ∩ closedBall 0 (2 * r)).Nonempty)
    {Q : ℝ → ℂ} {s t : ℝ} (hQc : ContinuousOn Q (Icc s t))
    (hQ : Q '' Icc s t ⊆ thickening (2 * ζ * r) (frontier (tubeOf (ε₀ * r) F)))
    (hdiam : ε₀ * r / 100 ≤ diam (Q '' Icc s t)) :
    ∃ α β : ℝ, s ≤ α ∧ α ≤ β ∧ β ≤ t ∧ ε₀ / 800 * r ≤ ‖Q β - Q α‖ ∧
      ∃ l : Bool × ℤ, |l.2| ≤ ⌈(5 + 3 * ε₀) / ε₀⌉₊ ∧
        Q '' Icc α β ⊆ thickening (4 * ζ * r) (scaleSet r 0 (lineSeg ε₀ (3 + 3 * ε₀) l)) := by
  set a := ε₀ * r with ha
  have ha0 : 0 < a := mul_pos hε₀ hr
  set δ := 2 * ζ * r with hδ
  have hδ0 : 0 < δ := by positivity
  have hreg : ∀ τ ∈ Icc s t, ‖Q τ‖ ≤ (3 + 3 * ε₀) * r := fun τ hτ =>
    l510_region (ζ := δ) hε₀ hr (by rw [hδ]; nlinarith) hF (hQ ⟨τ, hτ, rfl⟩)
  -- two points `a/200` apart
  obtain ⟨τ, hτ, τ', hτ', hpair⟩ : ∃ τ ∈ Icc s t, ∃ τ' ∈ Icc s t, a / 200 ≤ ‖Q τ - Q τ'‖ := by
    by_contra hno
    push Not at hno
    have : diam (Q '' Icc s t) ≤ a / 200 := by
      refine Metric.diam_le_of_forall_dist_le (by positivity) ?_
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [dist_eq_norm]; exact (hno x hx y hy).le
    linarith
  set t1 := min τ τ'
  set t2 := max τ τ'
  have h12 : t1 ≤ t2 := min_le_max
  have hsub : Icc t1 t2 ⊆ Icc s t :=
    Icc_subset_Icc (le_min hτ.1 hτ'.1) (max_le hτ.2 hτ'.2)
  have hd : a / 200 ≤ ‖Q t2 - Q t1‖ := by
    rcases le_total τ τ' with h | h
    · rw [show t1 = τ from min_eq_left h, show t2 = τ' from max_eq_right h, norm_sub_rev]
      exact hpair
    · rw [show t1 = τ' from min_eq_right h, show t2 = τ from max_eq_left h]; exact hpair
  have hS : ∀ τ ∈ Icc t1 t2, ∃ l, Q τ ∈ gStrip a δ l := fun τ hτ =>
    mem_iUnion.1 (l510_thickening_frontier_subset ha0 F (hQ ⟨τ, hsub hτ, rfl⟩))
  obtain ⟨α, β, hα, hαβ, hβ, hdist, l, hl⟩ := l510_subpath ha0 hδ0 (ρ := a / 200)
    (by rw [ha, hδ]; nlinarith) (by rw [ha, hδ]; nlinarith) h12 (hQc.mono hsub) hS hd
  have hαβs : Icc α β ⊆ Icc s t := (Icc_subset_Icc hα hβ).trans hsub
  refine ⟨α, β, (hsub ⟨hα, hαβ.trans hβ⟩).1, hαβ, (hsub ⟨hα.trans hαβ, hβ⟩).2,
    ?_, l, ?_, ?_⟩
  · have : a / 800 ≤ (a / 200 - 8 * δ) / 2 := by rw [ha, hδ]; nlinarith
    rw [ha] at this; linarith
  · -- the line comes close to `B_{(3 + 3ε₀) r}(0)`
    have hz := hl ⟨α, ⟨le_rfl, hαβ⟩, rfl⟩
    have hz' : |crd l.1 (Q α) - l.2 * a| < 2 * δ := hz
    have hc : |crd l.1 (Q α)| ≤ (3 + 3 * ε₀) * r := by
      have := abs_crd_sub_le l.1 (Q α) 0
      have e : crd l.1 (0 : ℂ) = 0 := by cases l.1 <;> simp [crd]
      rw [e, sub_zero, sub_zero] at this
      exact this.trans (hreg α (hαβs ⟨le_rfl, hαβ⟩))
    have hk : |(l.2 : ℝ)| * a < (5 + 3 * ε₀) * r := by
      have h1 : |(l.2 : ℝ) * a| ≤ |crd l.1 (Q α) - l.2 * a| + |crd l.1 (Q α)| := by
        have := abs_sub (crd l.1 (Q α)) (crd l.1 (Q α) - l.2 * a)
        rw [show crd l.1 (Q α) - (crd l.1 (Q α) - l.2 * a) = l.2 * a by ring] at this
        linarith
      rw [abs_mul, abs_of_pos ha0] at h1
      rw [hδ] at hz'
      nlinarith [mul_le_mul_of_nonneg_right hζ1 hr.le]
    have hk' : |(l.2 : ℝ)| < (5 + 3 * ε₀) / ε₀ := by
      rw [lt_div_iff₀ hε₀]
      have h4 := hk
      rw [ha, ← mul_assoc] at h4
      exact lt_of_mul_lt_mul_right h4 hr.le
    have hc' : (5 + 3 * ε₀) / ε₀ ≤ (⌈(5 + 3 * ε₀) / ε₀⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((|l.2| : ℤ) : ℝ) ≤ ((⌈(5 + 3 * ε₀) / ε₀⌉₊ : ℕ) : ℝ) := by
      rw [Int.cast_abs]; linarith
    exact_mod_cast h3
  · rintro _ ⟨x, hx, rfl⟩
    have h2 : (2 : ℝ) * δ = 4 * ζ * r := by rw [hδ]; ring
    exact l510_strip_subset hr (by positivity) l (h2 ▸ hl ⟨x, hx, rfl⟩) (hreg x (hαβs hx))

/-- **GM Lemma 5.10, condition (6)** (l. 3322: GM Lemma 2.10 = DFGPS Prop 4.1 and a union bound
over the grid lines) -/
theorem gm_L510Bdy (h41 : DFGPSProp4_1) (hXi : GMXiQBound) : L510BdyG := by
  intro γ D c hγ hγ2 hD ε₀ A q hε₀ hA hq
  have hξ : 0 < xiGamma γ := xiGamma_pos hγ
  have hκ := hXi γ hγ hγ2
  obtain ⟨pp, hppdef⟩ : ∃ pp : ℝ, pp = -(xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) / 2 :=
    ⟨_, rfl⟩
  have hpp : 0 < pp := by rw [hppdef]; linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = pp + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2 := ⟨_, rfl⟩
  have hE : E < 0 := by rw [hEdef, hppdef]; linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = pp ^ 2 / (4 * xiGamma γ ^ 2) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκdef]; positivity
  have hκe : pp ^ 2 / (2 * xiGamma γ ^ 2) - κ = κ := by rw [hκdef]; field_simp; ring
  set R0 : ℝ := 3 + 3 * ε₀ with hR0
  set K : ℕ := ⌈(5 + 3 * ε₀) / ε₀⌉₊ with hK
  set I : Finset (Bool × ℤ) := Finset.univ ×ˢ Finset.Icc (-(K : ℤ)) K with hI
  have hIne : I.Nonempty :=
    ⟨(true, 0), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩⟩
  have hbb : 0 < ε₀ / 800 := by positivity
  have H41 : ∀ l : Bool × ℤ, ∃ e : ℝ, 0 < e ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWPGFF h P →
      ∀ ε ∈ Ioo (0 : ℝ) e, ∀ 𝕣 : ℝ, 0 < 𝕣 →
      P (h ⁻¹' {g : DistC | ∀ u ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 (lineSeg ε₀ R0 l)),
        ∀ v ∈ thickening (ε * 𝕣) (scaleSet 𝕣 0 (lineSeg ε₀ R0 l)), ε₀ / 800 * 𝕣 ≤ ‖u - v‖ →
        ENNReal.ofReal (ε ^ E * scaleFac (xiGamma γ) c g 𝕣 0) ≤
          (D g).internal (thickening (ε * 𝕣) (scaleSet 𝕣 0 (lineSeg ε₀ R0 l))) u v})ᶜ ≤
        ENNReal.ofReal (ε ^ κ) := by
    intro l
    obtain ⟨e, he, H⟩ := h41 γ hγ hγ2 D c hD _ (isSegmentOrArc_lineSeg ε₀ R0 l) _ hbb pp hpp κ hκ0
    refine ⟨e, he, fun P _ h hh ε hε 𝕣 h𝕣 => ?_⟩
    have := H P h hh ε hε 𝕣 h𝕣
    rw [hκe] at this
    rw [hEdef]; exact this
  choose ef hef HF using H41
  set e1 : ℝ := I.inf' hIne ef with he1def
  have he1 : 0 < e1 := (Finset.lt_inf'_iff hIne).2 fun l _ => hef l
  have he1l : ∀ l ∈ I, e1 ≤ ef l := fun l hl => Finset.inf'_le ef hl
  set n : ℝ := (I.card : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hIne.card_pos
  have hA100 : 0 < 100 * A := by positivity
  have hqn : 0 < q / n := div_pos hq hn0
  set ε : ℝ := min (min (min (e1 / 2) 1) (ε₀ / 1600)) (min ((100 * A) ^ E⁻¹) ((q / n) ^ κ⁻¹))
    with hεdef
  have hε0 : 0 < ε := lt_min (lt_min (lt_min (by linarith) one_pos) (by positivity))
    (lt_min (Real.rpow_pos_of_pos hA100 _) (Real.rpow_pos_of_pos hqn _))
  have hεe1 : ε < e1 := lt_of_le_of_lt
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))) (by linarith)
  have hε1 : ε ≤ 1 := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεε₀ : ε ≤ ε₀ / 1600 := (min_le_left _ _).trans (min_le_right _ _)
  have hεA : 100 * A ≤ ε ^ E := by
    calc 100 * A = ((100 * A) ^ E⁻¹) ^ E := (Real.rpow_inv_rpow hA100.le hE.ne).symm
      _ ≤ ε ^ E := Real.rpow_le_rpow_of_nonpos hε0
          ((min_le_right _ _).trans (min_le_left _ _)) hE.le
  have hεq : ε ^ κ ≤ q / n := by
    calc ε ^ κ ≤ ((q / n) ^ κ⁻¹) ^ κ := Real.rpow_le_rpow hε0.le
          ((min_le_right _ _).trans (min_le_right _ _)) hκ0.le
      _ = q / n := Real.rpow_inv_rpow hqn.le hκ0.ne'
  refine ⟨ε / 4, by positivity, ?_⟩
  intro Ω _ P _ h hh r hr
  -- the normalized field `h − h_1(0)`
  have hm : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with hh'def
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hm, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst hh 0 one_pos] with ω hω
    simp only [h', hω, add_neg_cancel]
  have hT : ∀ᵐ ω ∂P, (∀ x y, (D (h' ω)).1 (x, y) =
      Real.exp (-(xiGamma γ * circleAvg (h ω) 1 0)) * (D (h ω)).1 (x + 0, y + 0)) ∧
      circleAvg (h' ω) r 0 = circleAvg (h ω) r 0 - circleAvg (h ω) 1 0 := by
    filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
      CircleAvg.ae_circleAvg_addConst hh 0 hr] with ω h2 h3
    refine ⟨fun x y => ?_, ?_⟩
    · simp only [h', add_zero]; rw [h2, mul_neg]
    · simp only [h']; rw [h3, sub_eq_add_neg]
  set Th : Bool × ℤ → Set ℂ := fun l => thickening (ε * r) (scaleSet r 0 (lineSeg ε₀ R0 l))
    with hTh
  set G : Bool × ℤ → Set Ω := fun l => h' ⁻¹' {g : DistC | ∀ u ∈ Th l, ∀ v ∈ Th l,
    ε₀ / 800 * r ≤ ‖u - v‖ → ENNReal.ofReal (ε ^ E * scaleFac (xiGamma γ) c g r 0) ≤
      (D g).internal (Th l) u v} with hG
  have hPG : ∀ l ∈ I, P (G l)ᶜ ≤ ENNReal.ofReal (ε ^ κ) := fun l hl =>
    HF l P h' hh' ε ⟨hε0, lt_of_lt_of_le hεe1 (he1l l hl)⟩ r hr
  have hU : P (⋃ l ∈ I, (G l)ᶜ) ≤ ENNReal.ofReal q := by
    calc P (⋃ l ∈ I, (G l)ᶜ) ≤ ∑ l ∈ I, P (G l)ᶜ := measure_biUnion_finset_le I _
      _ ≤ ∑ _l ∈ I, ENNReal.ofReal (ε ^ κ) := Finset.sum_le_sum hPG
      _ = ENNReal.ofReal (n * ε ^ κ) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul hn0.le, hn,
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal q := ENNReal.ofReal_le_ofReal (by
          have := mul_le_mul_of_nonneg_left hεq hn0.le
          rwa [mul_div_cancel₀ _ hn0.ne'] at this)
  refine le_trans (measure_mono_ae ?_) hU
  filter_upwards [hT] with ω ⟨hd1, hd2⟩
  intro hbad
  by_contra hcon
  simp only [mem_iUnion, mem_compl_iff, not_exists, not_not] at hcon
  apply hbad
  rintro V - - ⟨F, hF, rfl⟩ Qp s t - hQc hQsub hdiam
  have hF' : ∀ m ∈ F, (gridSquare (ε₀ * r) m ∩ closedBall 0 (2 * r)).Nonempty := by
    intro m hm
    obtain ⟨x, hx1, hx2⟩ := hF hm
    exact ⟨x, hx1, by rw [mem_closedBall, dist_zero_right]; exact hx2.2⟩
  obtain ⟨α, β, hsα, hαβ, hβt, hdist, l, hlK, hlsub⟩ := l510_bdy_det (ζ := ε / 4) hε₀ hr
    (by positivity) (by linarith) (by linarith) hF' hQc hQsub hdiam
  have e4 : 4 * (ε / 4) * r = ε * r := by ring
  rw [e4] at hlsub
  have hlI : l ∈ I := by
    obtain ⟨k1, k2⟩ := abs_le.1 hlK
    exact Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_Icc.2 ⟨k1, k2⟩⟩
  have hGl : ω ∈ G l := hcon l hlI
  have huTh : Qp α ∈ Th l := hlsub ⟨α, ⟨le_rfl, hαβ⟩, rfl⟩
  have hvTh : Qp β ∈ Th l := hlsub ⟨β, ⟨hαβ, le_rfl⟩, rfl⟩
  have h1 := hGl (Qp α) huTh (Qp β) hvTh (by rw [norm_sub_rev]; exact hdist)
  have key := DFGPS.internal_transl_smul (Real.exp_pos _) 0 hd1 (Th l) (Qp α) (Qp β)
  simp only [sub_zero, image_id'] at key
  rw [key] at h1
  set e := Real.exp (-(xiGamma γ * circleAvg (h ω) 1 0)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hsf : scaleFac (xiGamma γ) c (h' ω) r 0 = scaleFac (xiGamma γ) c (h ω) r 0 * e := by
    simp only [scaleFac, hd2, he, mul_assoc, ← Real.exp_add]
    congr 2; ring
  rw [hsf, show ε ^ E * (scaleFac (xiGamma γ) c (h ω) r 0 * e) =
    e * (ε ^ E * scaleFac (xiGamma γ) c (h ω) r 0) by ring,
    ENNReal.ofReal_mul he0.le] at h1
  have h2 : ENNReal.ofReal (ε ^ E * scaleFac (xiGamma γ) c (h ω) r 0) ≤
      (D (h ω)).internal (Th l) (Qp α) (Qp β) := by
    have h3 := mul_le_mul_right h1 (ENNReal.ofReal e⁻¹)
    rwa [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 he0.le),
      inv_mul_cancel₀ he0.ne', ENNReal.ofReal_one, one_mul, one_mul] at h3
  have hsf0 : 0 ≤ scaleFac (xiGamma γ) c (h ω) r 0 :=
    mul_nonneg (hD.tightness.1 r hr).le (Real.exp_pos _).le
  have hlen : (D (h ω)).internal (Th l) (Qp α) (Qp β) ≤ (D (h ω)).len Qp α β :=
    MetricGeometry.internalEDist_le_curveLength hαβ
      ((ContMetric.continuous_pt _).comp_continuousOn (hQc.mono (Icc_subset_Icc hsα hβt)))
      (fun x hx => ⟨Qp x, hlsub ⟨x, hx, rfl⟩, rfl⟩)
  calc ENNReal.ofReal (100 * A * scaleFac (xiGamma γ) c (h ω) r 0)
      ≤ ENNReal.ofReal (ε ^ E * scaleFac (xiGamma γ) c (h ω) r 0) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hεA hsf0)
    _ ≤ (D (h ω)).internal (Th l) (Qp α) (Qp β) := h2
    _ ≤ (D (h ω)).len Qp α β := hlen
    _ ≤ (D (h ω)).len Qp s t := MetricGeometry.curveLength_mono _ hsα hβt

end LQGMetric.GM
