/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L32 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L34
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightBlueprint
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

/-!
# CONF Lemma 3.2: conditions 1 and 2 of `E_r(z)`

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), `literature/src/1905.00381/confluence-final.tex`, proof of Lemma 3.2
(`lem-clsce-event-pos`, C:1166–1172).

* `confCond1_prob` (C:1167): "the laws of the reciprocals of the scaled distances
  `𝔠_r⁻¹e^{−ξh_r(z)} D_h(∂B_{2r}(z), ∂B_{3r}(z))` are tight", so some `c ∈ (0,1)` makes condition 1
  fail with probability `≤ β`, uniformly in `z, r`. From `GM.Tight.blueprint_GMS2_4a` (i)
  (Axioms IV, V; `K = ∂B_2(0)`, `U = B_3(0)`).
* `confCond2_prob` (C:1168): "Axioms IV and V show that we can find `δ = δ(p, c)` such that
  condition 2 … occurs with probability at least `1 − (1−p)/3`". Own elementary route (the paper
  gives no detail): uniform continuity of the rescaled metric (`blueprint_GMS2_4b`) on the closed
  annulus `K = {5/2 ≤ |x| ≤ 9/2}` bounds `D_h(u,v)` for `u, v` in one `δr`-square, and the crossing
  bound `D_h(rK + z, ∂𝔸_{2r,5r}(z)) ≥ s 𝔠_r e^{ξh_r(z)}` (`blueprint_GMS2_4a` (i)) makes this
  distance an internal distance of `𝔸_{2r,5r}(z)` (`internal_eq_of_lt_infEDist_frontier`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

theorem frontier_scaleSet {r : ℝ} (hr : 0 < r) (z : ℂ) (A : Set ℂ) :
    frontier (scaleSet r z A) = scaleSet r z (frontier A) := by
  have hr' : ((r : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hr.ne')
  let g : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-z)).trans (Homeomorph.mulRight₀ ((r : ℂ))⁻¹ hr')
  have hg : ∀ s, scaleSet r z s = g ⁻¹' s := by
    intro s
    rw [GM.Bilip.scaleSet_eq_preimage hr.ne']
    ext x
    simp [g, div_eq_mul_inv, sub_eq_add_neg]
  rw [hg, hg, g.preimage_frontier]

/-- **condition 1** (C:1167) -/
theorem confCond1_prob {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {β : ℝ} (hβ : 0 < β) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ < 1 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ENNReal.ofReal (c₁ * scaleFac (xiGamma γ) c (h ω) r z) ≤
            setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))}ᶜ ≤ ENNReal.ofReal β := by
  obtain ⟨s, hs, H⟩ := (GM.Tight.blueprint_GMS2_4a γ hγ hγ2 D c hD).1 (ball 0 3) (sphere 0 2)
    isOpen_ball isBounded_ball (isCompact_sphere 0 2)
    (sphere_subset_ball (by norm_num)) (1 - β) (by linarith)
  refine ⟨min s (1 / 2), lt_min hs (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro Ω _ P _ h hh z r hr
  have h1 := H P h hh z r hr
  rw [sub_sub_cancel] at h1
  refine (measure_mono ?_).trans h1
  intro ω hω
  simp only [mem_compl_iff, mem_ofPred_eq] at hω ⊢
  intro hc
  apply hω
  rw [frontier_ball 0 (by norm_num), GM.Bilip.scaleSet_sphere hr, GM.Bilip.scaleSet_sphere hr]
    at hc
  rw [mul_comm 2 r, mul_comm 3 r]
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) hc
  have hsc : 0 ≤ scaleFac (xiGamma γ) c (h ω) r z :=
    (mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)).le
  exact mul_le_mul_of_nonneg_right (min_le_left _ _) hsc

/-- two points of one `ε`-square are within `2ε` -/
theorem norm_sub_le_of_mem_confSq {ε : ℝ} {z : ℂ} {k : ℤ × ℤ} {u v : ℂ}
    (hu : u ∈ confSq ε z k) (hv : v ∈ confSq ε z k) : ‖u - v‖ ≤ 2 * ε := by
  obtain ⟨hu1, hu2, hu3, hu4⟩ := hu
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [Complex.sub_re, Complex.sub_im, two_mul]
  refine add_le_add ?_ ?_ <;> rw [abs_le] <;> constructor <;> nlinarith

/-- the closed annulus `{5/2 ≤ |x| ≤ 9/2}` -/
def ann59 : Set ℂ := {x | 5 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 9 / 2}

theorem isCompact_ann59 : IsCompact ann59 := by
  refine (isCompact_closedBall (0 : ℂ) (9 / 2)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · intro x hx; simpa using hx.2

theorem ann59_subset : ann59 ⊆ (annulus 0 2 5 : Set ℂ) := by
  intro x hx
  show 2 < ‖x - 0‖ ∧ ‖x - 0‖ < 5
  rw [sub_zero]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- **condition 2** (C:1168): for each `c₁ > 0` there is `δ` making condition 2 fail with
probability `≤ β`, uniformly in `z, r`. -/
theorem confCond2_prob {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {c₁ : ℝ} (hc₁ : 0 < c₁) {β : ℝ} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 8 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∀ k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)),
            internalDiam (D (h ω)) (confSq (δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
              ENNReal.ofReal (c₁ / 100 * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤
            ENNReal.ofReal β := by
  have hUb : Bornology.IsBounded (annulus 0 2 5 : Set ℂ) :=
    (isBounded_ball (x := (0 : ℂ)) (r := 5)).subset (fun x hx => by
      rw [mem_ball, dist_eq_norm]; exact (show 2 < ‖x - 0‖ ∧ ‖x - 0‖ < 5 from hx).2)
  obtain ⟨s₁, hs₁, H1⟩ := (GM.Tight.blueprint_GMS2_4a γ hγ hγ2 D c hD).1 (annulus 0 2 5) ann59
    (annulus 0 2 5).isOpen hUb isCompact_ann59 ann59_subset (1 - β / 2) (by linarith)
  set s₂ := min (c₁ / 100) (s₁ / 2) with hs₂
  have hs₂0 : 0 < s₂ := lt_min (by positivity) (by positivity)
  obtain ⟨b, hb, H2⟩ := GM.Tight.blueprint_GMS2_4b γ hγ hγ2 D c hD ann59 isCompact_ann59 s₂
    hs₂0 (1 - β / 2) (by linarith)
  refine ⟨min (b / 2) (1 / 16), lt_min (by positivity) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro Ω _ P _ h hh z r hr
  set δ := min (b / 2) (1 / 16) with hδ
  have hδb : 2 * δ ≤ b := by have := min_le_left (b / 2) (1 / 16); linarith
  have hδ8 : δ ≤ 1 / 8 := (min_le_right _ _).trans (by norm_num)
  have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
  have h1 := H1 P h hh z r hr
  have h2 := H2 P h hh z r hr
  rw [sub_sub_cancel] at h1 h2
  have hfr : frontier (annulus z (2 * r) (5 * r) : Set ℂ) =
      scaleSet r z (frontier (annulus 0 2 5 : Set ℂ)) := by
    rw [← frontier_scaleSet hr, GM.Bilip.scaleSet_annulus hr, mul_comm r 2, mul_comm r 5]
  have hmemK : ∀ u : ℂ, 5 / 2 * r ≤ ‖u - z‖ → ‖u - z‖ ≤ 9 / 2 * r → u ∈ scaleSet r z ann59 := by
    intro u h1 h2
    rw [GM.Bilip.scaleSet_eq_preimage hr.ne']
    show 5 / 2 ≤ ‖(u - z) / r‖ ∧ ‖(u - z) / r‖ ≤ 9 / 2
    rw [GM.Bilip.norm_div_ofReal hr, le_div_iff₀ hr, div_le_iff₀ hr]
    exact ⟨h1, h2⟩
  refine (measure_mono_ae ?_).trans ((measure_union_le _ _).trans ((add_le_add h1 h2).trans ?_))
  · filter_upwards [hD.length P h (GM.Tight.isGFFPlusCont_of_wp hh)] with ω hL hbad
    simp only [mem_compl_iff, mem_ofPred_eq] at hbad
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq]
    by_contra hcon
    push Not at hcon
    obtain ⟨hA1, hA2⟩ := hcon
    apply hbad
    intro k hk
    obtain ⟨w, hwS, hwA⟩ := hk
    have hwA' : 3 * r < ‖w - z‖ ∧ ‖w - z‖ < 4 * r := hwA
    have hsc : 0 < scaleFac (xiGamma γ) c (h ω) r z :=
      mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
    refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
    have huw := norm_sub_le_of_mem_confSq hu hwS
    have huv := norm_sub_le_of_mem_confSq hu hv
    have hu1 : 5 / 2 * r ≤ ‖u - z‖ := by
      have := norm_sub_norm_le (w - z) (w - u)
      rw [norm_sub_rev w u] at this
      have e : w - z - (w - u) = u - z := by ring
      rw [e] at this
      nlinarith
    have hu2 : ‖u - z‖ ≤ 9 / 2 * r := by
      have := norm_sub_le (u - w) (z - w)
      have e : u - w - (z - w) = u - z := by ring
      rw [e, norm_sub_rev z w] at this
      nlinarith
    have huK := hmemK u hu1 hu2
    have hvK : v ∈ scaleSet r z ann59 := by
      have hvw := norm_sub_le_of_mem_confSq hv hwS
      refine hmemK v ?_ ?_
      · have := norm_sub_norm_le (w - z) (w - v)
        rw [norm_sub_rev w v] at this
        have e : w - z - (w - v) = v - z := by ring
        rw [e] at this
        nlinarith
      · have := norm_sub_le (v - w) (z - w)
        have e : v - w - (z - w) = v - z := by ring
        rw [e, norm_sub_rev z w] at this
        nlinarith
    have hDuv : (D (h ω)).1 (u, v) ≤ s₂ * scaleFac (xiGamma γ) c (h ω) r z :=
      hA2 u huK v hvK (huv.trans (by nlinarith))
    have huV : u ∈ (annulus z (2 * r) (5 * r) : Set ℂ) := by
      show 2 * r < ‖u - z‖ ∧ ‖u - z‖ < 5 * r
      exact ⟨by linarith, by linarith⟩
    have hlt : edist ((D (h ω)).pt u) ((D (h ω)).pt v) <
        Metric.infEDist ((D (h ω)).pt u) ((D (h ω)).pt '' frontier (annulus z (2 * r) (5 * r))) := by
      rw [ContMetric.edist_pt]
      refine lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_)
        (le_trans hA1 ?_)
      · calc (D (h ω)).1 (u, v) ≤ s₂ * scaleFac (xiGamma γ) c (h ω) r z := hDuv
          _ ≤ s₁ / 2 * scaleFac (xiGamma γ) c (h ω) r z :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hsc.le
          _ < s₁ * scaleFac (xiGamma γ) c (h ω) r z := by nlinarith
      · rw [hfr, setDist, MetricGeometry.setEDist]
        exact iInf₂_le _ (mem_image_of_mem _ huK)
    have hint := (ContMetric.internal_eq_of_lt_infEDist_frontier hL (annulus z (2 * r) (5 * r)).isOpen huV
      hlt).2
    rw [hint, ContMetric.edist_pt]
    refine ENNReal.ofReal_le_ofReal (hDuv.trans ?_)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hsc.le
  · rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- CONF C:1169–1172 (condition 3, the harmonic part): "Since `𝔥^U` is continuous away from `∂U`,
for any fixed choice of `U ∈ 𝒰_1(0;δ)`, a.s. `sup_{u∈U_{δ/4}} |𝔥^U(u)| < ∞`. By combining this
with the translation and scale invariance of the law of `h`, modulo additive constant, we find that
there exists `A > 0` (depending on `δ`) such that with probability at least `1 − (1−p)/3`,
condition 3 … holds simultaneously for every `U ∈ 𝒰_r(z;δ)`." (open) -/
def CONFHarmBound : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ β : ℝ, 0 < β → ∃ A : ℝ, 0 < A ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
        P {ω | ∀ T : Finset (ℤ × ℤ),
          (∀ k ∈ T, k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) →
          ∀ u ∈ innerPart (confU r δ z T) (δ * r / 4),
            |harmPart P h (confU r δ z T) ω u - circleAvg (h ω) r z| ≤ A}ᶜ ≤ ENNReal.ofReal β

/-- **CONF Lemma 3.2** (C:1163–1172) from the harmonic-part bound (C:1169–1172); conditions 1 and
2 are `confCond1_prob`, `confCond2_prob`, each failing with probability `≤ (1−p)/3`. -/
theorem confLem3_2_of {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) (HB : CONFHarmBound) : CONFLem3_2 γ D c := by
  intro p₀ hp₀ hp₀1
  set β := (1 - p₀) / 3 with hβdef
  have hβ : 0 < β := by rw [hβdef]; linarith
  obtain ⟨c₁, hc₁, hc₁1, H1⟩ := confCond1_prob hγ hγ2 hD hβ
  obtain ⟨δ, hδ, hδ8, H2⟩ := confCond2_prob hγ hγ2 hD hc₁ hβ
  have hδ1 : δ < 1 := hδ8.trans (by norm_num)
  obtain ⟨A, hA, H3⟩ := HB δ hδ hδ1 β hβ
  refine ⟨⟨c₁, δ, A, 1⟩, ⟨hc₁, hc₁1, hδ, hδ1, hA, one_pos⟩, hδ8, ?_⟩
  intro Ω _ P _ h hh z r hr
  set E := confE (xiGamma γ) c D P h ⟨c₁, δ, A, 1⟩ r z with hE
  have hsub : Eᶜ ⊆ ({ω | ENNReal.ofReal (c₁ * scaleFac (xiGamma γ) c (h ω) r z) ≤
        setDist (D (h ω)) (sphere z (2 * r)) (sphere z (3 * r))}ᶜ ∪
      {ω | ∀ k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)),
        internalDiam (D (h ω)) (confSq (δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
          ENNReal.ofReal (c₁ / 100 * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ) ∪
      {ω | ∀ T : Finset (ℤ × ℤ),
          (∀ k ∈ T, k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) →
          ∀ u ∈ innerPart (confU r δ z T) (δ * r / 4),
            |harmPart P h (confU r δ z T) ω u - circleAvg (h ω) r z| ≤ A}ᶜ := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hω
    rw [hE, confE, mem_iInter₂]
    intro T hT
    exact ⟨h1, h2, h3 T hT⟩
  have hc : P Eᶜ ≤ ENNReal.ofReal (1 - p₀) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    refine (add_le_add ((measure_union_le _ _).trans (add_le_add (H1 P h hh z r hr)
      (H2 P h hh z r hr))) (H3 P h hh z r hr)).trans ?_
    rw [← ENNReal.ofReal_add hβ.le hβ.le, ← ENNReal.ofReal_add (by positivity) hβ.le]
    exact ENNReal.ofReal_le_ofReal (by rw [hβdef]; linarith)
  have h1 : (1 : ℝ≥0∞) ≤ P E + P Eᶜ := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono (union_compl_self E).symm.le).trans (measure_union_le _ _)
  have h2 : ENNReal.ofReal p₀ + P Eᶜ ≤ P E + P Eᶜ := by
    refine le_trans ?_ h1
    refine (add_le_add le_rfl hc).trans ?_
    rw [← ENNReal.ofReal_add hp₀.le (by linarith)]
    simp
  exact ENNReal.le_of_add_le_add_right (measure_ne_top P _) h2

end LQGMetric.CONF
