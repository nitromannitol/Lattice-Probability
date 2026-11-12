/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusLong at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulus
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DefsLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.ThinAnnulusClosed
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip

/-!
# GM Lemma 3.8, per-scale step: condition 2 of `𝖤_r(z)` (task P2-M2E, decision D42)

GM = Gwynne–Miller, arXiv:1905.00383v3, `uniqueness-final.tex`, proof of Lemma 3.8, l. 1384–1389:
"By tightness across scales (Axiom V), we can find `S > s > 0` … such that … with probability at
least `1 − (1 − p̃)/4`, `D_h(∂B_r(z), ∂𝔸_{r/2,2r}(z)) ≥ s 𝔠_r e^{ξh_r(z)}` and
`sup_{u,v ∈ 𝔸_{3r/4,r}(z)} D_h(u,v; 𝔸_{r/2,2r}(z)) ≤ S 𝔠_r e^{ξh_r(z)}`, and the same is true with
`D̃_h` in place of `D_h`. … Lemma 2.11 … gives an `α_* ∈ [3/4,1)` such that … condition 2 … holds
with probability at least `1 − (1 − p̃)/3`."

Followed with these details (DEVIATIONS GA-6d, D42):
* the crossing bound is for `u` in the closed annulus `{3r/4 ≤ |u − z| ≤ r}` (GM's `u` lies on
  `∂B_{αr}(z)`, not on `∂B_r(z)`) — `Tight.gm_S2_4a`; the internal diameter is `Tight.gm_S2_4c`;
* the `D̃_h` case reduces to the `D_h` case through GM Prop 2.2 (`P2_2`, bi-Lipschitz constant
  `C`): `D_h(u,v) ≥ C⁻¹ D̃_h(u,v) > C⁻¹ D̃_h(u, ∂𝔸) ≥ C⁻² s 𝔞`;
* Lemma 2.11 is used for the closed annulus (`L2_11c`, `gm_L2_11_closed`), since `u, v` lie on
  `∂𝔸_{αr,r}(z)` and the paths in `cl 𝔸_{αr,r}(z)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- deterministic core of condition 2 -/
lemma mem_gaLong_of {D D' : DistC → ContMetric} {g : DistC} {α r C s S σ : ℝ} {z : ℂ}
    (hα : 3 / 4 ≤ α) (hα1 : α < 1) (hC : 1 ≤ C) (hs : 0 < s) (hS : 0 < S) (hσ : 0 < σ)
    (hbi : ∀ x y, (D' g).1 (x, y) ≤ C * (D g).1 (x, y) ∧ (D g).1 (x, y) ≤ C * (D' g).1 (x, y))
    (hlow : ∀ u : ℂ, 3 / 4 * r ≤ ‖u - z‖ → ‖u - z‖ ≤ r →
      ∀ v ∈ frontier (annulus z (r / 2) (2 * r) : Set ℂ), s * σ < (D g).1 (u, v))
    (hdiam : ∀ u v : ℂ, 3 / 4 * r ≤ ‖u - z‖ → ‖u - z‖ ≤ r → 3 / 4 * r ≤ ‖v - z‖ → ‖v - z‖ ≤ r →
      (D g).internal (annulus z (r / 2) (2 * r)) u v ≤ ENNReal.ofReal (S * σ))
    (hthin : ∀ u ∈ closure (annulus z (α * r) r : Set ℂ), ∀ v ∈ closure (annulus z (α * r) r : Set ℂ),
      s / C ^ 2 * σ ≤ (D g).1 (u, v) →
        ENNReal.ofReal ((S + s) * σ) ≤ (D g).internal (closure (annulus z (α * r) r : Set ℂ)) u v)
    (hr : 0 < r) : g ∈ gaLong D D' α r z := by
  intro u hu v hv hcase a b P hab hP hPa hPb hPA
  rw [mem_sphere_iff_norm] at hu hv
  have hC0 : 0 < C := by linarith
  have hu1 : 3 / 4 * r ≤ ‖u - z‖ := by rw [hu]; nlinarith
  have hu2 : ‖u - z‖ ≤ r := by rw [hu]; nlinarith
  have hv1 : 3 / 4 * r ≤ ‖v - z‖ := by rw [hv]; nlinarith
  have hsC : s / C ^ 2 * σ ≤ s * σ := by
    have : s / C ^ 2 ≤ s := div_le_self hs.le (by nlinarith)
    exact mul_le_mul_of_nonneg_right this hσ.le
  have key : s / C ^ 2 * σ ≤ (D g).1 (u, v) := by
    rcases hcase with h1 | h2
    · have hle : ENNReal.ofReal (s * σ) ≤
          setDist (D g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) := by
        unfold setDist
        refine le_setEDist.2 ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [mem_singleton_iff] at hx
        subst hx
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal (hlow x hu1 hu2 y hy).le
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 (hle.trans_lt h1)
      linarith
    · have hle : ENNReal.ofReal (s / C * σ) ≤
          setDist (D' g) {u} (frontier (annulus z (r / 2) (2 * r) : Set ℂ)) := by
        unfold setDist
        refine le_setEDist.2 ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [mem_singleton_iff] at hx
        subst hx
        rw [edist_dist]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := hlow x hu1 hu2 y hy
        have h2 := (hbi x y).2
        show s / C * σ ≤ (D' g).1 (x, y)
        rw [div_mul_eq_mul_div, div_le_iff₀ hC0]
        nlinarith
      have h3 := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 (hle.trans_lt h2)
      have h4 := (hbi u v).1
      have : s / C ^ 2 * σ = (s / C * σ) / C := by field_simp
      rw [this, div_le_iff₀ hC0]
      linarith [mul_comm C ((D g).1 (u, v))]
  have hcu : u ∈ closure (annulus z (α * r) r : Set ℂ) := hPa ▸ hPA ⟨a, left_mem_Icc.2 hab, rfl⟩
  have hcv : v ∈ closure (annulus z (α * r) r : Set ℂ) := hPb ▸ hPA ⟨b, right_mem_Icc.2 hab, rfl⟩
  have hlen : (D g).internal (closure (annulus z (α * r) r : Set ℂ)) u v ≤ (D g).len P a b := by
    have := internalEDist_le_curveLength (X := (D g).Space) hab
      ((ContMetric.continuous_pt (D g)).comp_continuousOn hP)
      (Y := (D g).pt '' closure (annulus z (α * r) r : Set ℂ))
      (fun t ht => ⟨P t, hPA ⟨t, ht, rfl⟩, rfl⟩)
    simpa [ContMetric.internal, ContMetric.len, hPa, hPb] using this
  calc (D g).internal (annulus z (r / 2) (2 * r)) u v ≤ ENNReal.ofReal (S * σ) :=
        hdiam u v hu1 hu2 hv1 hv.le
    _ < ENNReal.ofReal ((S + s) * σ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
    _ ≤ _ := hthin u hcu v hcv key
    _ ≤ _ := hlen

lemma unscale (r : ℝ) (hr : 0 < r) (z u : ℂ) : (r : ℂ) * ((u - z) / (r : ℂ)) + z = u := by
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp; ring

lemma norm_unscale (r : ℝ) (hr : 0 < r) (z u : ℂ) : ‖(u - z) / (r : ℂ)‖ = ‖u - z‖ / r :=
  Bilip.norm_div_ofReal hr _

lemma frontier_annulus_norm {z v : ℂ} {r₁ r₂ : ℝ}
    (hv : v ∈ frontier (annulus z r₁ r₂ : Set ℂ)) : ‖v - z‖ = r₁ ∨ ‖v - z‖ = r₂ := by
  rw [(annulus z r₁ r₂).isOpen.frontier_eq] at hv
  obtain ⟨h1, h2⟩ := mem_closure_annulus hv.1
  have h3 : ¬ (r₁ < ‖v - z‖ ∧ ‖v - z‖ < r₂) := hv.2
  by_contra hc
  push Not at hc
  exact h3 ⟨lt_of_le_of_ne h1 (Ne.symm hc.1), lt_of_le_of_ne h2 hc.2⟩

/-- **GM l. 1384–1389** (proof of Lemma 3.8): there is `α_* ∈ [3/4, 1)` such that for
`α ∈ [α_*, 1)`, every whole-plane GFF, `r > 0` and `z`, condition 2 of `𝖤_r(z)` fails with
probability `≤ ε`. -/
theorem gm_gaLong_prob (h22 : P2_2) (h211 : L2_11c) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} (hPS : PairSetting γ D D' c) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ α₀ : ℝ, 3 / 4 ≤ α₀ ∧ α₀ < 1 ∧ ∀ α ∈ Ico α₀ 1,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P (h ⁻¹' gaLong D D' α r z)ᶜ ≤ ENNReal.ofReal ε := by
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := hPS
  obtain ⟨C₀, hC₀, hbil⟩ := h22 ⟨hγ0, hγ2, hD, hD'⟩
  set C : ℝ := max C₀ 1 with hCdef
  have hC1 : 1 ≤ C := le_max_right _ _
  set K₁ : Set ℂ := {w | 3 / 4 ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hK₁
  have hK₁c : IsCompact K₁ := (isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm
      continuous_const)) fun w hw => by simpa using hw.2
  set K₂ : Set ℂ := sphere 0 (1 / 2) ∪ sphere 0 2 with hK₂
  have hK₂c : IsCompact K₂ := (isCompact_sphere _ _).union (isCompact_sphere _ _)
  have hdisj : Disjoint K₁ K₂ := by
    rw [Set.disjoint_left]
    rintro w ⟨h1, h2⟩ (h | h) <;> rw [mem_sphere_zero_iff_norm] at h <;> linarith
  have hε3 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 3) := ENNReal.ofReal_pos.2 (by linarith)
  obtain ⟨s, hs, HA⟩ := Tight.gm_S2_4a hD hK₁c hK₂c hdisj hε3
  have hUc : IsConnected (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) :=
    ⟨⟨1, show (1 / 2 : ℝ) < ‖(1 : ℂ) - 0‖ ∧ ‖(1 : ℂ) - 0‖ < 2 by norm_num⟩,
      Bilip.isPreconnected_annulus_zero (by norm_num)⟩
  have hKU : K₁ ⊆ (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) := fun w hw =>
    show (1 / 2 : ℝ) < ‖w - 0‖ ∧ ‖w - 0‖ < 2 by rw [sub_zero]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
  obtain ⟨S, hS, HC⟩ := Tight.gm_S2_4c hD (annulus 0 (1 / 2) 2).isOpen hUc
    (Bilip.isBounded_annulus_zero _ _) hK₁c hKU hε3
  have hsC : 0 < s / C ^ 2 := by positivity
  have hsS : s / C ^ 2 < S + s := by
    have : s / C ^ 2 ≤ s := div_le_self hs.le (by nlinarith)
    linarith
  obtain ⟨α₁, hα₁, hα₁', HT⟩ := h211 hγ0 hγ2 hD hsC hsS (p := 1 - ε / 3) (by linarith)
    (by linarith)
  refine ⟨max α₁ (3 / 4), le_max_right _ _, max_lt hα₁' (by norm_num), ?_⟩
  intro α hα Ω _ P _ h hh r hr z
  have hαα₁ : α ∈ Ico α₁ 1 := ⟨(le_max_left _ _).trans hα.1, hα.2⟩
  have hα34 : 3 / 4 ≤ α := (le_max_right _ _).trans hα.1
  have hT := HT α hαα₁ z r hr P h hh
  have hA := (HA P h hh r hr z).le
  have hB := (HC P h hh r hr z).le
  have hbi := hbil P h hh
  set Abad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₂, s * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) <
        (D (h ω)).1 ((r : ℂ) * u + z, (r : ℂ) * v + z)} with hAbad
  set Bbad := {ω | ¬ ∀ u ∈ K₁, ∀ v ∈ K₁,
        (D (h ω)).internal ((fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ))
          ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
          ENNReal.ofReal (S * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z))} with hBbad
  set Tgood := {ω | ∀ u ∈ closure (annulus z (α * r) r : Set ℂ),
      ∀ v ∈ closure (annulus z (α * r) r : Set ℂ),
        s / C ^ 2 * scaleFac (xiGamma γ) c (h ω) r z ≤ (D (h ω)).1 (u, v) →
          ENNReal.ofReal ((S + s) * scaleFac (xiGamma γ) c (h ω) r z) ≤
            (D (h ω)).internal (closure (annulus z (α * r) r : Set ℂ)) u v} with hTgood
  have hsub : (h ⁻¹' gaLong D D' α r z)ᶜ ⊆ Abad ∪ Bbad ∪ Tgoodᶜ ∪
      {ω | ¬ ∀ u v : ℂ, C₀⁻¹ * (D (h ω)).1 (u, v) ≤ (D' (h ω)).1 (u, v) ∧
        (D' (h ω)).1 (u, v) ≤ C₀ * (D (h ω)).1 (u, v)} := by
    intro ω hω
    by_contra hc
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, hAbad, hBbad,
      hTgood] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    have hcr : 0 < c r := hD.tightness.1 r hr
    have hσ : 0 < scaleFac (xiGamma γ) c (h ω) r z := mul_pos hcr (Real.exp_pos _)
    have hsf : ∀ t : ℝ, t * scaleFac (xiGamma γ) c (h ω) r z =
        t * c r * Real.exp (xiGamma γ * circleAvg (h ω) r z) := fun t => by
      unfold scaleFac; ring
    refine hω (mem_gaLong_of hα34 hα.2 hC1 hs hS hσ ?_ ?_ ?_ h3 hr)
    · intro x y
      obtain ⟨e1, e2⟩ := h4 x y
      have hD0 := Tight.cmetric_nonneg (D (h ω)).2 (x, y)
      have hC₀C : C₀ ≤ C := le_max_left _ _
      refine ⟨e2.trans (mul_le_mul_of_nonneg_right hC₀C hD0), ?_⟩
      have : (D (h ω)).1 (x, y) ≤ C₀ * (D' (h ω)).1 (x, y) := by
        have := mul_le_mul_of_nonneg_left e1 hC₀.le
        rwa [← mul_assoc, mul_inv_cancel₀ hC₀.ne', one_mul] at this
      exact this.trans (mul_le_mul_of_nonneg_right hC₀C (Tight.cmetric_nonneg (D' (h ω)).2 _))
    · intro u hu1 hu2 v hv
      have hu' : (u - z) / (r : ℂ) ∈ K₁ := by
        refine ⟨?_, ?_⟩ <;> rw [norm_unscale r hr] <;>
          [rw [le_div_iff₀ hr]; rw [div_le_one hr]] <;> linarith
      have hv' : (v - z) / (r : ℂ) ∈ K₂ := by
        rcases frontier_annulus_norm hv with e | e
        · left; rw [mem_sphere_zero_iff_norm, norm_unscale r hr, e]; field_simp
        · right; rw [mem_sphere_zero_iff_norm, norm_unscale r hr, e]; field_simp
      have := h1 _ hu' _ hv'
      rw [unscale r hr, unscale r hr] at this
      rw [hsf]; exact this
    · intro u v hu1 hu2 hv1 hv2
      have hu' : (u - z) / (r : ℂ) ∈ K₁ := by
        refine ⟨?_, ?_⟩ <;> rw [norm_unscale r hr] <;>
          [rw [le_div_iff₀ hr]; rw [div_le_one hr]] <;> linarith
      have hv' : (v - z) / (r : ℂ) ∈ K₁ := by
        refine ⟨?_, ?_⟩ <;> rw [norm_unscale r hr] <;>
          [rw [le_div_iff₀ hr]; rw [div_le_one hr]] <;> linarith
      have := h2 _ hu' _ hv'
      rw [unscale r hr, unscale r hr] at this
      have himg : (fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) =
          (annulus z (r / 2) (2 * r) : Set ℂ) := by
        rw [show ((fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ)) =
          scaleSet r z (annulus 0 (1 / 2) 2) from rfl, Bilip.scaleSet_annulus hr,
          show r * (1 / 2) = r / 2 by ring, mul_comm r 2]
      rw [himg] at this
      rw [hsf]; exact this
  have hnull : P {ω | ¬ ∀ u v : ℂ, C₀⁻¹ * (D (h ω)).1 (u, v) ≤ (D' (h ω)).1 (u, v) ∧
      (D' (h ω)).1 (u, v) ≤ C₀ * (D (h ω)).1 (u, v)} = 0 := ae_iff.1 hbi
  calc P (h ⁻¹' gaLong D D' α r z)ᶜ ≤ P (Abad ∪ Bbad ∪ Tgoodᶜ ∪ _) := measure_mono hsub
    _ ≤ P Abad + P Bbad + P Tgoodᶜ + 0 := by
        rw [← hnull]
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 3) + ENNReal.ofReal (ε / 3) + ENNReal.ofReal (1 - (1 - ε / 3)) + 0 := by
        gcongr
    _ = ENNReal.ofReal ε := by
        rw [add_zero, show 1 - (1 - ε / 3) = ε / 3 by ring, ← ENNReal.ofReal_add (by linarith)
          (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring

end LQGMetric.GM
