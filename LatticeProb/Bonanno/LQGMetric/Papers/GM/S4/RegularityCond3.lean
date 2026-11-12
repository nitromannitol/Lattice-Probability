/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.RegularityCond3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityProb
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightLaw
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas

/-!
# GM Lemma 4.11: condition 3 (Hölder continuity) of `ℰ_𝕣`

Source: GM (arXiv:1905.00383v3) `uniqueness-final.tex`, proof of Lemma 4.11 (`lem-reg-event-prob`),
l. 1985: "By Lemma 2.8, after possibly shrinking `a` we can further arrange that condition 3
(Hölder continuity) holds with probability at least `1 − (1−p)/6`." GM Lemma 2.8 (U:1022–1030)
is DFGPS Proposition 3.18 (lower bound, `Blueprint.DFGPSProp3_18`) together with the first display
of DFGPS Lemma 3.20 (upper bound for `D_h(u,v; B_{2|u−v|}(u))`, `Blueprint.DFGPSLem3_20`, with
`u ≠ v`, D55).

* Both cited statements are for a whole-plane GFF normalized so that `h_1(0) = 0`. Condition 3
  is invariant under `h ↦ h + C` (Axiom III, `IsWeakLQGMetric.ae_dist_addConst`, and
  `(h + C)_𝕣(0) = h_𝕣(0) + C`, `CircleAvg.ae_circleAvg_addConst`), so we apply them to
  `h − h_1(0)` (the same transfer as `GM.gm_S4_8`, `SetupGeoBdy.lean`).
* `K := cl B_{ρ+4ℓ}(0)` with `V ⊂ B_ρ(0)` contains `𝕣⁻¹ B_{4ℓ𝕣}(𝕣V)` (`gm_regRegion_subset`), and
  `ε := a`: the failure probability is `≤ C₁a^{p₁} + C₂a^{p₂} → 0` uniformly in `𝕣`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `C a^p ≤ δ` for all small `a` (the rate step of "polynomially high probability") -/
theorem gm_exists_small_rpow {p C ε₀ δ : ℝ} (hp : 0 < p) (hε₀ : 0 < ε₀) (hδ : 0 < δ) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ < ε₀ ∧ ∀ a ∈ Ioc 0 a₀, C * a ^ p ≤ δ := by
  set x : ℝ := δ / (|C| + 1) with hx
  have hx0 : 0 < x := by positivity
  refine ⟨min (ε₀ / 2) (x ^ p⁻¹), lt_min (by linarith) (Real.rpow_pos_of_pos hx0 _),
    lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  rintro a ⟨ha0, ha⟩
  have h1 : a ^ p ≤ x := by
    have := Real.rpow_le_rpow ha0.le (ha.trans (min_le_right _ _)) hp.le
    rwa [Real.rpow_inv_rpow hx0.le hp.ne'] at this
  have hap : 0 ≤ a ^ p := Real.rpow_nonneg ha0.le _
  have h2 : C * a ^ p ≤ |C| * a ^ p := mul_le_mul_of_nonneg_right (le_abs_self C) hap
  have h3 : |C| * x ≤ δ := by
    rw [hx, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg C]
  nlinarith [abs_nonneg C]

/-- `(𝔠_𝕣 e^{ξ h_𝕣(0)})⁻¹ = 𝔠_𝕣⁻¹ e^{−ξ h_𝕣(0)}` -/
theorem gm_scaleFac_inv (ξ : ℝ) (c : ℝ → ℝ) (g : DistC) (r : ℝ) (z : ℂ) :
    (scaleFac ξ c g r z)⁻¹ = (c r)⁻¹ * Real.exp (-ξ * circleAvg g r z) := by
  rw [scaleFac, mul_inv, ← Real.exp_neg, neg_mul]

/-- **GM Lemma 4.11, condition 3** (l. 1985): by GM Lemma 2.8 (= DFGPS Prop 3.18 and Lemma 3.20),
condition 3 of `ℰ_𝕣` holds with probability `→ 1` as `a → 0`, uniformly in `𝕣`. -/
theorem gm_regC3_prob (h318 : DFGPSProp3_18) (h320 : DFGPSLem3_20) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c)
    {χ χ' : ℝ} (hχ : 0 < χ) (hχQ : χ < xiGamma γ * (Q γ - 2)) (hχ' : xiGamma γ * (Q γ + 2) < χ')
    {V : Set ℂ} {ℓ : ℝ} (hV : Bornology.IsBounded V) :
    ∀ q < 1, ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ R : RegPar,
      R.ξ = xiGamma γ → R.c = c → R.χ = χ → R.χ' = χ' → R.V = V → R.ℓ = ℓ →
      RegCondAt P (regC3 D h R) q a₀ := by
  obtain ⟨ρ₀, hρ₀⟩ := hV.subset_ball (0 : ℂ)
  set K : Set ℂ := Metric.closedBall 0 (ρ₀ + 4 * ℓ) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨p₁, hp₁, C₁, ε₁, hε₁, H1⟩ := h318 γ hγ hγ2 D c hD K hKc χ χ' hχ hχQ hχ'
  obtain ⟨⟨p₂, hp₂, C₂, ε₂, hε₂, H2⟩, -⟩ := h320 γ hγ hγ2 D c hD K hKc χ hχ hχQ
  intro q hq
  have hq' : 0 < (1 - q) / 2 := by linarith
  obtain ⟨b₁, hb₁, hb₁ε, hB1⟩ := gm_exists_small_rpow (C := C₁) hp₁ hε₁ hq'
  obtain ⟨b₂, hb₂, hb₂ε, hB2⟩ := gm_exists_small_rpow (C := C₂) hp₂ hε₂ hq'
  refine ⟨min b₁ b₂, lt_min hb₁ hb₂, ?_⟩
  intro Ω _ P _ h hh R hξ hc hRχ hRχ' hRV hRℓ
  subst hRχ hRχ' hRV hRℓ
  -- the normalized field `h − h_1(0)`
  have hN : Measurable fun ω => -circleAvg (h ω) 1 0 :=
    ((measurable_circleAvg_left 1 0).comp hh.measurable).neg
  set h' : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) 1 0) with hh'def
  have hh' : IsNormalizedWPGFF h' P := by
    refine ⟨hh.addConst hN, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hh] with ω hω
    simp only [h', hω, add_neg_cancel]
  rintro a ⟨ha0, ha⟩ 𝕣 h𝕣
  have ha1 : a ≤ b₁ := ha.trans (min_le_left _ _)
  have ha2 : a ≤ b₂ := ha.trans (min_le_right _ _)
  set E1 := h' ⁻¹' {g : DistC | ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ a * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ R.χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0) * (D g).1 (u, v) ∧
          (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0) * (D g).1 (u, v) ≤
            ‖(u - v) / 𝕣‖ ^ R.χ} with hE1
  set E2 := h' ⁻¹' {g : DistC | ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, u ≠ v →
          ‖u - v‖ ≤ a * 𝕣 →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)) *
              (D g).internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
            ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ R.χ)} with hE2
  have hP1 : P E1ᶜ ≤ ENNReal.ofReal (C₁ * a ^ p₁) :=
    H1 P h' hh' a ⟨ha0, lt_of_le_of_lt ha1 hb₁ε⟩ 𝕣 h𝕣
  have hP2 : P E2ᶜ ≤ ENNReal.ofReal (C₂ * a ^ p₂) :=
    H2 P h' hh' a ⟨ha0, lt_of_le_of_lt ha2 hb₂ε⟩ 𝕣 h𝕣
  -- a.s. inclusion `C₃ᶜ ⊆ E1ᶜ ∪ E2ᶜ`
  have hsub : (regC3 D h R 𝕣 a)ᶜ ≤ᵐ[P] (E1ᶜ ∪ E2ᶜ : Set Ω) := by
    filter_upwards [hD.ae_dist_addConst (Tight.isGFFPlusCont_of_wp hh),
      CircleAvg.ae_circleAvg_addConst hh 0 h𝕣] with ω hA hC
    intro hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨g1, g2⟩ := hcon
    apply hω
    set A := circleAvg (h ω) 1 0
    have hdist : ∀ u v, (D (h' ω)).1 (u, v) = Real.exp (-(xiGamma γ * A)) * (D (h ω)).1 (u, v) :=
      fun u v => (hA (-A) u v).trans (by rw [mul_neg])
    have hcirc : circleAvg (h' ω) 𝕣 0 = circleAvg (h ω) 𝕣 0 + -A := hC _
    have hkey : (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h' ω) 𝕣 0) *
        Real.exp (-(xiGamma γ * A)) = (scaleFac R.ξ R.c (h ω) 𝕣 0)⁻¹ := by
      rw [gm_scaleFac_inv, hξ, hc, hcirc, mul_assoc, ← Real.exp_add]
      congr 2; ring
    have hint : ∀ V u v, (D (h' ω)).internal V u v =
        ENNReal.ofReal (Real.exp (-(xiGamma γ * A))) * (D (h ω)).internal V u v :=
      fun V u v => internal_of_scale (Real.exp_pos _) hdist V u v
    simp only [regC3, mem_ofPred_eq]
    intro z hz w hw hzw
    have hz' := gm_regRegion_subset h𝕣 hρ₀ hz
    have hw' := gm_regRegion_subset h𝕣 hρ₀ hw
    refine ⟨?_, fun hne => ?_⟩
    · have := (g1 z hz' w hw' hzw).1
      rwa [hdist, ← mul_assoc, hkey] at this
    · have := g2 z hz' w hw' hne hzw
      rwa [hint, ← mul_assoc, ← ENNReal.ofReal_mul' (Real.exp_pos _).le, hkey] at this
  calc P (regC3 D h R 𝕣 a)ᶜ ≤ P (E1ᶜ ∪ E2ᶜ) := measure_mono_ae hsub
    _ ≤ P E1ᶜ + P E2ᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (C₁ * a ^ p₁) + ENNReal.ofReal (C₂ * a ^ p₂) := add_le_add hP1 hP2
    _ ≤ ENNReal.ofReal ((1 - q) / 2) + ENNReal.ofReal ((1 - q) / 2) :=
        add_le_add (ENNReal.ofReal_le_ofReal (hB1 a ⟨ha0, ha1⟩))
          (ENNReal.ofReal_le_ofReal (hB2 a ⟨ha0, ha2⟩))
    _ = ENNReal.ofReal (1 - q) := by
        rw [← ENNReal.ofReal_add hq'.le hq'.le]; congr 1; ring

end LQGMetric.GM
