/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.ThinAnnulusClosed at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulus

/-!
# GM Lemma 2.11 for the closed annulus (task P2-M2E, decision D42)

`gm_L2_11_closed`: GM Lemma 2.11 (`lem-attained-long`, `uniqueness-final.tex` l. 1062–1072) with
`u, v ∈ cl 𝔸_{αr,r}(z)` and the internal metric of `cl 𝔸_{αr,r}(z)`. Same proof as
`LQGMetric.GM.gm_L2_11` (GM l. 1067–1071, DFGPS Prop 4.1 = GM Lemma 2.10 with `L = ∂𝔻`), on the
thickening of radius `2(1−α)r` of `∂B_r(z)`, which contains `cl 𝔸_{αr,r}(z)`. Used for condition 2
of `𝖤_r(z)` (GM l. 1328, proof of Lemma 3.8, l. 1384–1389), whose points lie on `∂𝔸_{αr,r}(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

lemma mem_closure_annulus {z w : ℂ} {r₁ r₂ : ℝ} (hw : w ∈ closure (annulus z r₁ r₂ : Set ℂ)) :
    r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂ := by
  have hc : IsClosed {w : ℂ | r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂} :=
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).inter
      (isClosed_le (continuous_id.sub continuous_const).norm continuous_const)
  have hsub : (annulus z r₁ r₂ : Set ℂ) ⊆ {w : ℂ | r₁ ≤ ‖w - z‖ ∧ ‖w - z‖ ≤ r₂} := by
    intro x hx
    have hx' : r₁ < ‖x - z‖ ∧ ‖x - z‖ < r₂ := hx
    exact ⟨hx'.1.le, hx'.2.le⟩
  exact closure_minimal hsub hc hw

/-- `cl A_{α r, r}(z) − z ⊂ B_{2(1−α) r}(r ∂𝔻)` -/
lemma sub_mem_thickening_of_mem_closure {α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : 0 < r)
    {z w : ℂ} (hw : w ∈ closure (annulus z (α * r) r : Set ℂ)) :
    w - z ∈ Metric.thickening ((2 * (1 - α)) * r) (scaleSet r 0 (Metric.sphere (0 : ℂ) 1)) := by
  have hw' := mem_closure_annulus hw
  have hn : 0 < ‖w - z‖ := lt_of_lt_of_le (by positivity) hw'.1
  have hn' : ((‖w - z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Metric.mem_thickening_iff]
  refine ⟨(r : ℂ) * ((w - z) / (‖w - z‖ : ℂ)) + 0, ⟨(w - z) / (‖w - z‖ : ℂ), ?_, rfl⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_of_nonneg hn.le,
      div_self hn.ne']
  · have e1 : w - z - ((r : ℂ) * ((w - z) / (‖w - z‖ : ℂ)) + 0) =
        (((‖w - z‖ - r) / ‖w - z‖ : ℝ) : ℂ) * (w - z) := by
      push_cast; field_simp; ring
    rw [dist_eq_norm, e1, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos hn, abs_of_nonpos (by linarith : ‖w - z‖ - r ≤ 0), div_mul_cancel₀ _ hn.ne']
    nlinarith

/-- `P(Eᶜ) ≤ P(Aᶜ) + P(Bᶜ)` when `A ∩ B ∩ {G} ⊆ E` and `G` holds a.s. (no measurability) -/
lemma compl_le_of_ae_inter {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A B E : Set Ω} {G : Ω → Prop} (hG : ∀ᵐ ω ∂P, G ω) {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1)
    (hsub : ∀ ω, ω ∈ A → ω ∈ B → G ω → ω ∈ E) (hAB : P Aᶜ + P Bᶜ ≤ ENNReal.ofReal (1 - p)) :
    P Eᶜ ≤ ENNReal.ofReal (1 - p) := by
  have hG' : P {ω | ¬ G ω} = 0 := ae_iff.1 hG
  have hcov : Eᶜ ⊆ Aᶜ ∪ Bᶜ ∪ {ω | ¬ G ω} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hc
    exact hω (hsub ω hc.1.1 hc.1.2 hc.2)
  calc P Eᶜ ≤ P (Aᶜ ∪ Bᶜ ∪ {ω | ¬ G ω}) := measure_mono hcov
    _ ≤ P Aᶜ + P Bᶜ + P {ω | ¬ G ω} := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ = P Aᶜ + P Bᶜ := by rw [hG', add_zero]
    _ ≤ _ := hAB

/-- **GM Lemma 2.11, closed annulus** (decision D42) -/
def L2_11c : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ {s S p : ℝ}, 0 < s → s < S → 0 < p → p < 1 →
  ∃ α₀ : ℝ, 1 / 2 < α₀ ∧ α₀ < 1 ∧ ∀ α ∈ Ico α₀ 1, ∀ (z : ℂ) (r : ℝ), 0 < r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → P {ω | ∀ u ∈ closure (annulus z (α * r) r : Set ℂ),
      ∀ v ∈ closure (annulus z (α * r) r : Set ℂ),
        s * scaleFac (xiGamma γ) c (h ω) r z ≤ (D (h ω)).1 (u, v) →
          ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z) ≤
            (D (h ω)).internal (closure (annulus z (α * r) r : Set ℂ)) u v}ᶜ ≤
      ENNReal.ofReal (1 - p)

/-- **GM Lemma 2.11 for `cl 𝔸_{αr,r}(z)`** (D42), GM's proof (l. 1067–1071) on the thickening of
radius `2(1−α)r`. -/
theorem gm_L2_11_closed (h41 : DFGPSProp4_1) (hXi : GMXiQBound) : L2_11c := by
  intro γ D c hγ hγ2 hD s S p hs hsS hp hp1
  have hξ : 0 < xiGamma γ := xiGamma_pos hγ
  have hS : 0 < S := hs.trans hsS
  have hκ := hXi γ hγ hγ2
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = -(xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) / 2 := ⟨_, rfl⟩
  have hq : 0 < q := by rw [hqdef]; linarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = q + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2 := ⟨_, rfl⟩
  have hE : E < 0 := by rw [hEdef, hqdef]; linarith
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : ℝ, ζ = q ^ 2 / (4 * xiGamma γ ^ 2) := ⟨_, rfl⟩
  have hζ : 0 < ζ := by rw [hζdef]; positivity
  have hζe : q ^ 2 / (2 * xiGamma γ ^ 2) - ζ = ζ := by rw [hζdef]; field_simp; ring
  have hp' : 0 < (1 - p) / 2 := by linarith
  obtain ⟨b, hb, hbP⟩ := Tight.gm_S2_4b hD (isCompact_closedBall (0 : ℂ) 1) hs
    (ε := ENNReal.ofReal ((1 - p) / 2)) (ENNReal.ofReal_pos.2 hp')
  by_cases hex : ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀)
      (_ : IsProbabilityMeasure P₀) (h₀ : Ω₀ → DistC), IsWholePlaneGFF h₀ P₀
  swap
  · exact ⟨3 / 4, by norm_num, by norm_num, fun α _ z r _ Ω _ P _ h hh =>
      (hex ⟨Ω, _, P, inferInstance, h, hh⟩).elim⟩
  obtain ⟨Ω₀, _, P₀, _, h₀, hh₀⟩ := hex
  have hN := measurable_circleAvg_left 1 0
  have hh₀n : IsWholePlaneGFF (fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0)) P₀ :=
    hh₀.addConst (hN.comp hh₀.measurable).neg
  set μ : Measure DistC := P₀.map fun ω => addConst (h₀ ω) (-circleAvg (h₀ ω) 1 0) with hμdef
  have : IsProbabilityMeasure μ := inferInstance
  have hμ : IsNormalizedWPGFF (fun g : DistC => g) μ := by
    refine ⟨isWholePlaneGFF_map_id hh₀n, ?_⟩
    rw [hμdef, ae_map_iff hh₀n.measurable.aemeasurable (measurableSet_eq_fun hN measurable_const)]
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh₀] with ω hω
    rw [hω]; ring
  obtain ⟨ε₀, hε₀, H⟩ := h41.perSpace γ hγ hγ2 D c hD (Metric.sphere 0 1)
    (Or.inr (Or.inr ⟨0, 1, one_pos, rfl⟩)) b hb q hq μ (fun g => g) hμ ζ hζ
  obtain ⟨ε₁, hε₁def⟩ : ∃ ε₁ : ℝ, ε₁ = min (min (ε₀ / 2) (1 / 4))
      (min (S ^ E⁻¹) (((1 - p) / 2) ^ ζ⁻¹)) := ⟨_, rfl⟩
  have hε₁ : 0 < ε₁ := by
    rw [hε₁def]
    exact lt_min (lt_min (by linarith) (by norm_num))
      (lt_min (Real.rpow_pos_of_pos hS _) (Real.rpow_pos_of_pos hp' _))
  have hε₁a : ε₁ ≤ ε₀ / 2 := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hε₁b : ε₁ ≤ 1 / 4 := by rw [hε₁def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hε₁c : ε₁ ≤ S ^ E⁻¹ := by rw [hε₁def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hε₁d : ε₁ ≤ ((1 - p) / 2) ^ ζ⁻¹ := by
    rw [hε₁def]; exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨1 - ε₁ / 2, by linarith, by linarith, ?_⟩
  intro α hα z r hr Ω _ P _ h hh
  have hε : 0 < 2 * (1 - α) := by linarith [hα.2]
  have hεε₁ : 2 * (1 - α) ≤ ε₁ := by linarith [hα.1]
  have hα1 : α < 1 := hα.2
  have hα0 : 0 < α := by linarith [hα.1]
  have hSe : S ≤ (2 * (1 - α)) ^ E := by
    calc S = (S ^ E⁻¹) ^ E := (Real.rpow_inv_rpow hS.le hE.ne).symm
      _ ≤ (2 * (1 - α)) ^ E := Real.rpow_le_rpow_of_nonpos hε (hεε₁.trans hε₁c) hE.le
  have hζb : (2 * (1 - α)) ^ ζ ≤ (1 - p) / 2 := by
    calc (2 * (1 - α)) ^ ζ ≤ (((1 - p) / 2) ^ ζ⁻¹) ^ ζ :=
          Real.rpow_le_rpow hε.le (hεε₁.trans hε₁d) hζ.le
      _ = (1 - p) / 2 := Real.rpow_inv_rpow hp'.le hζ.ne'
  have hz : IsWholePlaneGFF (fun ω => affineComp 1 z (h ω)) P := hh.affineComp one_pos z
  set h' : Ω → DistC := fun ω => addConst (affineComp 1 z (h ω))
    (-circleAvg (affineComp 1 z (h ω)) 1 0) with hh'def
  have hh' : IsWholePlaneGFF h' P := hz.addConst (hN.comp hz.measurable).neg
  have hmap : P.map h' = μ := Tight.map_normalize_eq hz hh₀
  have HB := H (2 * (1 - α)) ⟨hε, by linarith⟩ r hr
  set T := Metric.thickening ((2 * (1 - α)) * r) (scaleSet r 0 (Metric.sphere (0 : ℂ) 1)) with hTdef
  have hcr : 0 < c r := hD.tightness.1 r hr
  refine compl_le_of_ae_inter P (A := {ω | ∀ u ∈ Metric.closedBall (0 : ℂ) 1,
      ∀ v ∈ Metric.closedBall (0 : ℂ) 1, ‖u - v‖ ≤ b →
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)})
    (B := h' ⁻¹' {g : DistC | ∀ u ∈ T, ∀ v ∈ T, b * r ≤ ‖u - v‖ →
      ENNReal.ofReal ((2 * (1 - α)) ^ (q + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) *
          scaleFac (xiGamma γ) c g r 0) ≤ (D g).internal T u v})
    (G := fun ω => (∀ u v : ℂ, (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z)) ∧
      (∀ (a : ℝ) (u v : ℂ), (D (addConst (affineComp 1 z (h ω)) a)).1 (u, v) =
        Real.exp (xiGamma γ * a) * (D (affineComp 1 z (h ω))).1 (u, v)) ∧
      (∀ a, circleAvg (addConst (affineComp 1 z (h ω)) a) r 0 =
        circleAvg (affineComp 1 z (h ω)) r 0 + a))
    ?_ hp.le hp1.le ?_ ?_
  · filter_upwards [hD.translation P h (Tight.isGFFPlusCont_of_wp hh) z,
      hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hz),
      CircleAvg.ae_circleAvg_addConst hz 0 hr] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ω hA hB ⟨h1, h2, h3⟩ u hu v hv hDuv
    set l := Real.exp (xiGamma γ * -circleAvg (h ω) 1 z) with hldef
    have hl : 0 < l := Real.exp_pos _
    have hD' : ∀ x y, (D (h' ω)).1 (x, y) = l * (D (h ω)).1 (x + z, y + z) := by
      intro x y
      rw [hh'def]
      simp only
      rw [h2, h1, Tight.circleAvg_affineComp_one]
    have hsf : scaleFac (xiGamma γ) c (h' ω) r 0 = l * scaleFac (xiGamma γ) c (h ω) r z := by
      unfold scaleFac
      rw [hh'def]
      simp only
      rw [h3, Tight.circleAvg_affineComp_one, Tight.circleAvg_affineComp_one, hldef, mul_add,
        Real.exp_add]
      ring
    have hsf0 : 0 < scaleFac (xiGamma γ) c (h ω) r z := mul_pos hcr (Real.exp_pos _)
    have hfar : b * r ≤ ‖(u - z) - (v - z)‖ := by
      by_contra hlt
      push Not at hlt
      have hu' : (u - z) / (r : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
        have hu2 : ‖u - z‖ ≤ r := (mem_closure_annulus hu).2
        rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
          div_le_one hr]
        exact hu2
      have hv' : (v - z) / (r : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
        have hv2 : ‖v - z‖ ≤ r := (mem_closure_annulus hv).2
        rw [mem_closedBall_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le,
          div_le_one hr]
        exact hv2
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hb' : ‖(u - z) / (r : ℂ) - (v - z) / (r : ℂ)‖ ≤ b := by
        rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le, div_le_iff₀ hr]
        linarith
      have := hA _ hu' _ hv' hb'
      rw [mul_div_cancel₀ _ hr', mul_div_cancel₀ _ hr', sub_add_cancel, sub_add_cancel] at this
      have hsc : s * scaleFac (xiGamma γ) c (h ω) r z =
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) := by
        unfold scaleFac; ring
      linarith
    have hint := hB (u - z) (sub_mem_thickening_of_mem_closure hα0 hα1 hr hu) (v - z)
      (sub_mem_thickening_of_mem_closure hα0 hα1 hr hv) hfar
    have htr := internal_translate_eq hl z hD' T (u - z) (v - z)
    rw [sub_add_cancel, sub_add_cancel] at htr
    have hsubT : closure (annulus z (α * r) r : Set ℂ) ⊆ (· + z) '' T := fun w hw =>
      ⟨w - z, sub_mem_thickening_of_mem_closure hα0 hα1 hr hw, sub_add_cancel w z⟩
    have hanti : (D (h ω)).internal ((· + z) '' T) u v ≤
        (D (h ω)).internal (closure (annulus z (α * r) r : Set ℂ)) u v :=
      internalEDist_anti (Set.image_mono hsubT) _ _
    rw [← hEdef, hsf] at hint
    calc ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)
        ≤ ENNReal.ofReal (l⁻¹ * ((2 * (1 - α)) ^ E * (l * scaleFac (xiGamma γ) c (h ω) r z))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [show l⁻¹ * ((2 * (1 - α)) ^ E * (l * scaleFac (xiGamma γ) c (h ω) r z)) =
            (2 * (1 - α)) ^ E * scaleFac (xiGamma γ) c (h ω) r z by field_simp]
          exact mul_le_mul_of_nonneg_right hSe hsf0.le
      _ = ENNReal.ofReal l⁻¹ *
          ENNReal.ofReal ((2 * (1 - α)) ^ E * (l * scaleFac (xiGamma γ) c (h ω) r z)) :=
          ENNReal.ofReal_mul (inv_nonneg.2 hl.le)
      _ ≤ ENNReal.ofReal l⁻¹ * (D (h' ω)).internal T (u - z) (v - z) := by gcongr
      _ = (D (h ω)).internal ((· + z) '' T) u v := htr.symm
      _ ≤ _ := hanti
  · have hA : P {ω | ¬ ∀ u ∈ Metric.closedBall (0 : ℂ) 1, ∀ v ∈ Metric.closedBall (0 : ℂ) 1,
        ‖u - v‖ ≤ b → (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z) <
          s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z)} ≤
        ENNReal.ofReal ((1 - p) / 2) := (hbP P h hh r hr z).le
    have hB : P (h' ⁻¹' {g : DistC | ∀ u ∈ T, ∀ v ∈ T, b * r ≤ ‖u - v‖ →
        ENNReal.ofReal ((2 * (1 - α)) ^ (q + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) *
          scaleFac (xiGamma γ) c g r 0) ≤ (D g).internal T u v})ᶜ ≤
        ENNReal.ofReal ((1 - p) / 2) := by
      rw [← preimage_compl]
      refine (Measure.le_map_apply hh'.measurable.aemeasurable _).trans ?_
      rw [hmap]
      refine HB.trans ?_
      rw [hζe]
      exact ENNReal.ofReal_le_ofReal hζb
    rw [compl_ofPred]
    refine (add_le_add hA hB).trans ?_
    rw [← ENNReal.ofReal_add hp'.le hp'.le]
    exact ENNReal.ofReal_le_ofReal (by linarith)


end LQGMetric.GM
