/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.L510A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventStmts
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusLong

/-!
# GM Lemma 5.10: the tightness conditions (4), (7), (8) of `E_r` (task P2-M2M5, D83 packet P6)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.10 (`lem-geo-event-prob`, l. 3307–3335). The conditions of `E_r` that follow from
Axiom V (tightness across scales) alone, each with failure probability `≤ q` uniformly in the
whole-plane GFF and in `r > 0`:

* `gm_L510_setDist`: the lower bound `Δ 𝔠_r e^{ξh_r(0)} ≤ D_h(∂B_{2r}(0), ∂B_{3r}(0))` of
  condition (4) (GM l. 3308: "By tightness across scales we can choose `Δ` …"), from
  `Tight.gm_S2_4a` (GM.S2.4a);
* `gm_L510_near`: for every `t > 0` there is `β > 0` such that `D_h(u, v; 𝔸_{r,4r}(0)) ≤ t 𝔠_r
  e^{ξh_r(0)}` for all `u, v ∈ cl 𝔸_{5r/2,3r}(0)` with `|u − v| ≤ βr`. This gives the internal
  bound of condition (4) ("… and then `δ`", l. 3308) and condition (8) (l. 3326: "`θ` small
  enough") — as in DEC-83 §4 P6: a short `D_h`-path from `u` to `v` cannot reach `∂𝔸_{r,4r}(0)`
  (lower bound GM.S2.4a between `cl 𝔸_{5/2,3}` and `∂B_1 ∪ ∂B_4`, modulus GM.S2.4b, Axiom I);
* `gm_L510_across`: condition (7) (l. 3324: "Since `D_h` induces the Euclidean topology, we can
  find `a` …"), from `Tight.gm_S2_4a_sep` (the internal metric dominates `D_h`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma l510_edist_eq (D : ContMetric) (u v : ℂ) :
    edist (D.pt u) (D.pt v) = ENNReal.ofReal (D.1 (u, v)) := edist_dist _ _

lemma l510_mem_annulus_iff {w : ℂ} {r₁ r₂ : ℝ} :
    w ∈ (annulus 0 r₁ r₂ : Set ℂ) ↔ r₁ < ‖w‖ ∧ ‖w‖ < r₂ := by
  show r₁ < ‖w - 0‖ ∧ ‖w - 0‖ < r₂ ↔ _
  rw [sub_zero]

lemma l510_sf (ξ : ℝ) (c : ℝ → ℝ) (g : DistC) (r t : ℝ) :
    t * scaleFac ξ c g r 0 = t * c r * Real.exp (ξ * circleAvg g r 0) := by
  unfold scaleFac; ring

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **Condition (7) of `E_r`** (GM l. 3324) -/
theorem gm_L510_across (hD : IsWeakLQGMetric γ D c) {ζ q : ℝ} (hζ : 0 < ζ) (hq : 0 < q) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∀ z₁ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ),
        ∀ z₂ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ), ζ * r ≤ ‖z₁ - z₂‖ →
          ENNReal.ofReal (a * scaleFac (xiGamma γ) c (h ω) r 0) ≤
            (D (h ω)).internal (annulus 0 (r / 4) (4 * r)) z₁ z₂} ≤ ENNReal.ofReal q := by
  obtain ⟨s, hs, H⟩ := Tight.gm_S2_4a_sep hD (isCompact_closedBall (0 : ℂ) 4) hζ
    (ENNReal.ofReal_pos.2 hq)
  refine ⟨min s (1 / 2), ⟨lt_min hs (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    fun P _ h hh r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr 0).le⟩
  intro hall
  apply hω
  intro z₁ hz₁ z₂ hz₂ hzz
  rw [l510_mem_annulus_iff] at hz₁ hz₂
  have hm : ∀ z : ℂ, ‖z‖ < 4 * r → (z - 0) / (r : ℂ) ∈ closedBall (0 : ℂ) 4 := fun z hz => by
    rw [mem_closedBall_zero_iff, norm_unscale r hr, sub_zero, div_le_iff₀ hr]; linarith
  have hsep : ζ ≤ ‖(z₁ - 0) / (r : ℂ) - (z₂ - 0) / (r : ℂ)‖ := by
    rw [← sub_div, show z₁ - 0 - (z₂ - 0) = (z₁ - z₂) - 0 by ring, norm_unscale r hr, sub_zero,
      le_div_iff₀ hr]
    exact hzz
  have := hall _ (hm z₁ hz₁.2) _ (hm z₂ hz₂.2) hsep
  rw [unscale r hr, unscale r hr] at this
  have hsf : 0 < scaleFac (xiGamma γ) c (h ω) r 0 :=
    mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
  calc ENNReal.ofReal (min s (1 / 2) * scaleFac (xiGamma γ) c (h ω) r 0)
      ≤ ENNReal.ofReal ((D (h ω)).1 (z₁, z₂)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsf.le) ?_
        rw [l510_sf]; exact this.le
    _ = edist ((D (h ω)).pt z₁) ((D (h ω)).pt z₂) := (l510_edist_eq _ _ _).symm
    _ ≤ (D (h ω)).internal (annulus 0 (r / 4) (4 * r)) z₁ z₂ :=
        MetricGeometry.edist_le_internalEDist _ _ _

/-- **Condition (4), lower bound** (GM l. 3308) -/
theorem gm_L510_setDist (hD : IsWeakLQGMetric γ D c) {q : ℝ} (hq : 0 < q) :
    ∃ Δ ∈ Ioo (0 : ℝ) 1, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ENNReal.ofReal (Δ * scaleFac (xiGamma γ) c (h ω) r 0) ≤
        setDist (D (h ω)) (sphere 0 (2 * r)) (sphere 0 (3 * r))} ≤ ENNReal.ofReal q := by
  have hdisj : Disjoint (sphere (0 : ℂ) 2) (sphere (0 : ℂ) 3) := by
    rw [Set.disjoint_left]
    intro w h1 h2
    rw [mem_sphere_zero_iff_norm] at h1 h2
    linarith
  obtain ⟨s, hs, H⟩ := Tight.gm_S2_4a hD (isCompact_sphere (0 : ℂ) 2) (isCompact_sphere (0 : ℂ) 3)
    hdisj (ENNReal.ofReal_pos.2 hq)
  refine ⟨min s (1 / 2), ⟨lt_min hs (by norm_num), (min_le_right _ _).trans_lt (by norm_num)⟩,
    fun P _ h hh r hr => (measure_mono fun ω hω => ?_).trans (H P h hh r hr 0).le⟩
  intro hall
  apply hω
  have hsf : 0 < scaleFac (xiGamma γ) c (h ω) r 0 :=
    mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
  refine MetricGeometry.le_setEDist.2 ?_
  rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
  rw [mem_sphere_zero_iff_norm] at hu hv
  have hm : ∀ z : ℂ, ∀ k : ℝ, ‖z‖ = k * r → (z - 0) / (r : ℂ) ∈ sphere (0 : ℂ) k :=
    fun z k hz => by
      rw [mem_sphere_zero_iff_norm, norm_unscale r hr, sub_zero, hz]; field_simp
  have := hall _ (hm u 2 hu) _ (hm v 3 hv)
  rw [unscale r hr, unscale r hr] at this
  rw [l510_edist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  refine le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hsf.le) ?_
  rw [l510_sf]; exact this.le

/-- **The modulus of `D_h(·,·; 𝔸_{r,4r}(0))` near `∂B_{3r}(0)`**: for every `t > 0` there is
`β > 0` such that w.h.p., uniformly in `r`, `D_h(u, v; 𝔸_{r,4r}(0)) ≤ t 𝔠_r e^{ξh_r(0)}` for
`u, v ∈ cl 𝔸_{5r/2,3r}(0)` with `|u − v| ≤ βr` (conditions (4) and (8), GM l. 3308, 3326). -/
theorem gm_L510_near (hD : IsWeakLQGMetric γ D c) {t q : ℝ} (ht : 0 < t) (hq : 0 < q) :
    ∃ β : ℝ, 0 < β ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      P {ω | ¬ ∀ u v : ℂ, 5 / 2 * r ≤ ‖u‖ → ‖u‖ ≤ 3 * r → 5 / 2 * r ≤ ‖v‖ → ‖v‖ ≤ 3 * r →
        ‖u - v‖ ≤ β * r → (D (h ω)).internal (annulus 0 r (4 * r)) u v ≤
          ENNReal.ofReal (t * scaleFac (xiGamma γ) c (h ω) r 0)} ≤ ENNReal.ofReal q := by
  set K₁ : Set ℂ := {w | 5 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 3} with hK₁
  have hK₁c : IsCompact K₁ := (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm
      continuous_const)) fun w hw => by simpa using hw.2
  set K₂ : Set ℂ := sphere 0 1 ∪ sphere 0 4 with hK₂
  have hK₂c : IsCompact K₂ := (isCompact_sphere _ _).union (isCompact_sphere _ _)
  have hdisj : Disjoint K₁ K₂ := by
    rw [Set.disjoint_left]
    rintro w ⟨h1, h2⟩ (h | h) <;> rw [mem_sphere_zero_iff_norm] at h <;> linarith
  have hq2 : (0 : ℝ≥0∞) < ENNReal.ofReal (q / 2) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨s, hs, HA⟩ := Tight.gm_S2_4a hD hK₁c hK₂c hdisj hq2
  obtain ⟨β, hβ, HB⟩ := Tight.gm_S2_4b hD hK₁c (lt_min hs ht) hq2
  refine ⟨β, hβ, fun P _ h hh r hr => ?_⟩
  have hlenae := hD.length P h (Tight.isGFFPlusCont_of_wp hh)
  set Abad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₂, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0) <
        (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0)} with hAbad
  set Bbad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁, ‖u - v‖ ≤ β →
        (D (h ω)).1 ((r : ℂ) * u + 0, (r : ℂ) * v + 0) <
          min s t * c r * Real.exp (xiGamma γ * circleAvg (h ω) r 0)} with hBbad
  have hm : ∀ z : ℂ, 5 / 2 * r ≤ ‖z‖ → ‖z‖ ≤ 3 * r → (z - 0) / (r : ℂ) ∈ K₁ := fun z h1 h2 => by
    refine ⟨?_, ?_⟩ <;> rw [norm_unscale r hr, sub_zero]
    · rw [le_div_iff₀ hr]; linarith
    · rw [div_le_iff₀ hr]; linarith
  calc _ ≤ P (Abad ∪ Bbad) := by
        refine measure_mono_ae ?_
        filter_upwards [hlenae] with ω hlen hbad
        by_contra hcon
        simp only [mem_union, mem_ofPred_eq, not_or, not_not, hAbad, hBbad] at hcon
        obtain ⟨h1, h2⟩ := hcon
        apply hbad
        intro u v hu1 hu2 hv1 hv2 huv
        have hsf : 0 < scaleFac (xiGamma γ) c (h ω) r 0 :=
          mul_pos (hD.tightness.1 r hr) (Real.exp_pos _)
        have huv' : ‖(u - 0) / (r : ℂ) - (v - 0) / (r : ℂ)‖ ≤ β := by
          rw [← sub_div, show u - 0 - (v - 0) = (u - v) - 0 by ring, norm_unscale r hr, sub_zero,
            div_le_iff₀ hr]
          exact huv
        have hB := h2 _ (hm u hu1 hu2) _ (hm v hv1 hv2) huv'
        rw [unscale r hr, unscale r hr, ← l510_sf] at hB
        have hu : u ∈ (annulus 0 r (4 * r) : Set ℂ) := by
          rw [l510_mem_annulus_iff]; constructor <;> linarith
        have hlt : edist ((D (h ω)).pt u) ((D (h ω)).pt v) <
            Metric.infEDist ((D (h ω)).pt u) ((D (h ω)).pt '' frontier (annulus 0 r (4 * r))) := by
          refine lt_of_lt_of_le (b := ENNReal.ofReal (s * scaleFac (xiGamma γ) c (h ω) r 0)) ?_
            (Metric.le_infEDist.2 ?_)
          · rw [l510_edist_eq]
            refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (hB.trans_le ?_)
            exact mul_le_mul_of_nonneg_right (min_le_left _ _) hsf.le
          · rintro _ ⟨w, hw, rfl⟩
            rw [l510_edist_eq]
            refine ENNReal.ofReal_le_ofReal ?_
            have hw' : (w - 0) / (r : ℂ) ∈ K₂ := by
              rcases frontier_annulus_norm hw with e | e
              · left; rw [mem_sphere_zero_iff_norm, norm_unscale r hr, e]; field_simp
              · right; rw [mem_sphere_zero_iff_norm, norm_unscale r hr, e]; field_simp
            have := h1 _ (hm u hu1 hu2) _ hw'
            rw [unscale r hr, unscale r hr, ← l510_sf] at this
            exact this.le
        rw [(ContMetric.internal_eq_of_lt_infEDist_frontier hlen (annulus 0 r (4 * r)).isOpen hu
          hlt).2, l510_edist_eq]
        refine ENNReal.ofReal_le_ofReal (hB.le.trans ?_)
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) hsf.le
    _ ≤ P Abad + P Bbad := measure_union_le _ _
    _ ≤ ENNReal.ofReal (q / 2) + ENNReal.ofReal (q / 2) :=
        add_le_add (HA P h hh r hr 0).le (HB P h hh r hr 0).le
    _ = ENNReal.ofReal q := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

end LQGMetric.GM
