/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes58 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes58Geom
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes56
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58T5

/-!
# GM Lemma 5.8 from its deterministic geometry (task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8 (l. 3063–3126), the probabilistic part:

* Step 1 (l. 3066–3080): `n_*` from GM Lemma 2.7 with `s = 1/3`, `p = p₁`, `q = 1 − δ(1−p)/100`
  (`gm_L2_7_scaled` at scale `R = 3ρr`, i.e. GM's `h(·/(3ρr))`); `ρ = δ/(500 n_*)`; the events
  `F_{ρr}(z)` have probability `≥ p₁` (Lemma 5.6) and are determined by `h|_{B_{3ρr}(z)}` modulo
  constants (Lemma 5.7, square tubes: `aeEventIn_tubeEvent_addConst`); union bound over the arcs
  (`#A · δ ≤ 100`) gives probability `≥ 1 − (1−p) = p` for (5.23);
* (5.24) `ε₀ = ε₁ρ`, `b = b₁ρ` (l. 3080);
* Step 3 (l. 3093–3126): on (5.23), conditions 1–3 for `U_r^{x,y}` from those of `F_{ρr}(z_k)`:
  condition 1 since `B_{2ρr}(z_k) ⊂ B_{4ρr}(u)` (a `D̃_h`-geodesic from `u` to `∂B_{4ρr}(u)` crosses
  `∂B_{2ρr}(z_k)`, `setDist_sphere_le_of_geod`) and `V_{ρr}(z_k) ⊂ U_r^{x,y}`; conditions 2, 3 from
  `L58Geom` ((5.25)) and monotonicity of internal metrics.
* Decision D83 (c) (P2-M2M4): the tubes also satisfy the local attachment (T5) at `x`, `y`
  (`L58Geom`, `Geom58T5`).
* Decision D92: `U` is deterministic (chosen before the probability space), since the tubes `V_z`
  of Lemma 5.6 are.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- **GM Lemma 5.8** from `L58Geom`, Lemma 5.6, Lemma 5.7 for square tubes (`DFGPSLem3_8`), and
Lemma 2.7 -/
theorem gm_L5_8_of_geom (hgeom : L58Geom) (h56 : L5_6) (h38 : DFGPSLem3_8)
    (hL : L2_7) : L5_8 := by
  intro γ D D' c cs Cs hPS hRat hcs hcsC α p₀ hα3 hα1 hp0 hp1 hEnd c₁ c₂ η hc1 hc12 hc2 hη
    p δ hp hδ
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  obtain ⟨b₁, p₁, ε₁, hb₁, hp₁, hε₁, H56⟩ :=
    h56 hPS hRat hcs hcsC hα3 hα1 hp0 hp1 hEnd hc1 hc12 hc2 hη
  set q : ℝ := 1 - δ * (1 - p) / 100 with hq
  have hq0 : 0 < q := by nlinarith [hp.1, hp.2, hδ.1, hδ.2]
  have hq1 : q < 1 := by
    have : 0 < δ * (1 - p) / 100 := by have := hp.2; have := hδ.1; positivity
    linarith
  obtain ⟨n₀, Hn⟩ := gm_L2_7_scaled hL (s := 1 / 3) (p := p₁) (q := q) (by norm_num) hp₁.1
    (by linarith [hp₁.2]) hq0 hq1
  set n : ℕ := max n₀ 1 with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_max_right n₀ 1
  have hnn : n₀ ≤ n := le_max_left _ _
  set ρ : ℝ := δ / (500 * n) with hρ
  have hρ0 : 0 < ρ := by have := hδ.1; positivity
  have hρ1 : ρ < 1 / 100 := by
    rw [hρ, div_lt_iff₀ (by positivity)]; nlinarith [hδ.2]
  refine ⟨b₁ * ρ, ρ, ε₁ * ρ, ⟨by nlinarith [hb₁.1], by nlinarith [hb₁.2, hb₁.1]⟩, ⟨hρ0, hρ1⟩,
    ⟨by nlinarith [hε₁.1], by nlinarith [hε₁.2]⟩, ?_⟩
  intro r hρr
  have hρr0 : 0 < ρ * r := hρr.1
  have hr : 0 < r := pos_of_mul_pos_right hρr0 hρ0.le
  have hε₁' : ε₁ < 1 / 100 := by linarith [hε₁.2, hb₁.2]
  obtain ⟨Z, A, hAcard, hA, hZr, hZsep, hU⟩ :=
    hgeom δ hδ n (by omega) ε₁ ⟨hε₁.1, hε₁'⟩ r hr
  -- the tubes `V_{ρr}(z)` of Lemma 5.6
  have hV : ∀ z : ℂ, ∃ V : Set ℂ, TubeProps ε₁ (ρ * r) z V ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsWholePlaneGFF h P →
        ENNReal.ofReal p₁ ≤ P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ (ρ * r) z V) := fun z => by
    obtain ⟨V, h1, h2, h3, h4, h5, h6, h7⟩ := H56 z (ρ * r) hρr
    exact ⟨V, ⟨h1, h2, h3, h4, h5, h6⟩, h7⟩
  choose V hVp hVP using hV
  obtain ⟨U, hUprop, hUlink⟩ := hU V (fun z _ => hVp z)
  refine ⟨U, hUprop, ?_⟩
  intro Ω _ P _ h hh
  -- Step 1: each arc contains a point where `F_{ρr}(z)` occurs, with probability `≥ q`
  set B : Finset ℂ → Set Ω := fun a => ⋃ z ∈ a, h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ (ρ * r) z (V z)
  have hdet : ∀ z : ℂ, ∀ a' : Ω → ℝ, Measurable a' →
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (a' ω)) (ballO z (3 * (ρ * r))))
        (h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ (ρ * r) z (V z)) := fun z a' ha' => by
    obtain ⟨-, -, hVb, hVsq, -, -⟩ := hVp z
    refine aeEventIn_tubeEvent_addConst h38 hPS hRat hcs hcsC.le c₁ η b₁ ε₁ (ρ * r) z (V z)
      (ε₁ * (ρ * r)) (closedBall z (2 * (ρ * r))) hρr0 hVsq (hVb.trans (ball_subset_ball ?_)) P h hh a' ha'
    nlinarith [hε₁.1]
  have hnull : ∀ z : ℂ, NullMeasurableSet (h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ (ρ * r) z (V z)) P :=
    fun z => by
      obtain ⟨F, hF, hEF⟩ := hdet z (fun _ => 0) measurable_const
      have hm : Measurable fun ω => addConst (h ω) ((fun _ => (0 : ℝ)) ω) :=
        (hh.addConst measurable_const).measurable
      have hF' : MeasurableSet F := ((measurable_restrictTo _).comp hm).comap_le _ hF
      exact hF'.nullMeasurableSet.congr hEF.symm
  have hB : ∀ a ∈ A, ENNReal.ofReal q ≤ P (B a) := fun a ha => by
    refine Hn P h hh (3 * (ρ * r)) (by positivity) a (hnn.trans (hA a ha).2) (fun z hz w hw hzw => ?_)
      _ (fun z _ => hdet z) (fun z _ => hVP z P h hh)
    have := hZsep z ((hA a ha).1 hz) w ((hA a ha).1 hw) hzw
    calc 2 * (1 + 1 / 3) * (3 * (ρ * r)) = 8 * (ρ * r) := by ring
      _ ≤ _ := this
  have hBc : ∀ a ∈ A, P (B a)ᶜ ≤ ENNReal.ofReal (δ * (1 - p) / 100) := fun a ha => by
    have hBn : NullMeasurableSet (B a) P := NullMeasurableSet.biUnion (a.countable_toSet) fun z _ => hnull z
    rw [prob_compl_eq_one_sub₀ hBn]
    calc 1 - P (B a) ≤ 1 - ENNReal.ofReal q := tsub_le_tsub_left (hB a ha) _
      _ = ENNReal.ofReal (δ * (1 - p) / 100) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0.le, hq]; congr 1; ring
  set G : Set Ω := ⋂ a ∈ A, B a with hG
  have hGc : P Gᶜ ≤ ENNReal.ofReal (1 - p) := by
    rw [hG, compl_iInter₂]
    calc P (⋃ a ∈ A, (B a)ᶜ) ≤ ∑ a ∈ A, P (B a)ᶜ := measure_biUnion_finset_le _ _
      _ ≤ ∑ _a ∈ A, ENNReal.ofReal (δ * (1 - p) / 100) := Finset.sum_le_sum hBc
      _ = ENNReal.ofReal (A.card * (δ * (1 - p) / 100)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (1 - p) := ENNReal.ofReal_le_ofReal (by
        have h1 : 0 ≤ 1 - p := by linarith [hp.2]
        nlinarith)
  have hGp : ENNReal.ofReal p ≤ P G := by
    have h1 : (1 : ℝ≥0∞) ≤ P G + P Gᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self G).ge).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp.1.le (by linarith [hp.2])]; simp
    have h3 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) ≤ P G + ENNReal.ofReal (1 - p) := by
      rw [h2]; exact h1.trans (add_le_add le_rfl hGc)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h3
  -- Step 3: on `G` (and a.s.), the event of Lemma 5.8 occurs
  have hlen := ae_mem_lenSet h38 hγ0 hγ2 hD' P h hh
  have hsub : G ≤ᵐ[P] h ⁻¹' linkEvent D D' cs Cs c₁ η δ ρ (b₁ * ρ) (ε₁ * ρ) r U := by
    filter_upwards [hlen] with ω hl hω
    have hex := hex_of_mem hl
    intro x hx y hy hxy
    obtain ⟨a, ha, hgood⟩ := hUlink x hx y hy hxy
    have hωa : ω ∈ B a := mem_iInter₂.1 hω a ha
    simp only [B, mem_iUnion, mem_preimage] at hωa
    obtain ⟨z, hz, u, hu, v, hv, hb, hrat, hset, hsetv, hUq, hs1, hs2, hi1, hi2⟩ := hωa
    obtain ⟨hVU, hcomp⟩ := hgood z hz
    have hcb : closedBall z (ρ * r) ⊆ ball z (3 / 2 * (ρ * r)) :=
      closedBall_subset_ball (by linarith)
    have hNz : V z ∩ ball z (3 / 2 * (ρ * r)) ∈ 𝓝 u :=
      ((hVp z).1.inter isOpen_ball).mem_nhds ⟨hu.1, hcb hu.2⟩
    have hNz' : V z ∩ ball z (3 / 2 * (ρ * r)) ∈ 𝓝 v :=
      ((hVp z).1.inter isOpen_ball).mem_nhds ⟨hv.1, hcb hv.2⟩
    obtain ⟨hOu, -, -⟩ := hcomp u ⟨hu.1, hcb hu.2⟩
    obtain ⟨hOv, -, -⟩ := hcomp v ⟨hv.1, hcb hv.2⟩
    have hsu : SepDiscNear (U x y) (20 * (ε₁ * ρ) * r) u x y (ε₁ * ρ * r) :=
      (hs1.and hNz).mono fun u' hu' => (hcomp u' hu'.2).2.1 hu'.1
    have hsv : SepDiscNear (U x y) (20 * (ε₁ * ρ) * r) v y x (ε₁ * ρ * r) :=
      (hs2.and hNz').mono fun v' hv' => (hcomp v' hv'.2).2.2 hv'.1
    have hzr : ‖z‖ = r := hZr z ((hA a ha).1 hz)
    have hann : ∀ w ∈ closedBall z (ρ * r),
        w ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) := fun w hw => by
      have hwz : ‖w - z‖ ≤ ρ * r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      have e1 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
        calc ‖z‖ = ‖w - (w - z)‖ := by ring_nf
          _ ≤ ‖w‖ + ‖w - z‖ := norm_sub_le _ _
      have e2 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      show (1 - 4 * ρ) * r < ‖w - 0‖ ∧ ‖w - 0‖ < (1 + 4 * ρ) * r
      rw [sub_zero]
      constructor <;> nlinarith
    refine ⟨u, ⟨hann u hu.2, hVU hu.1⟩, v, ⟨hann v hv.2, hVU hv.1⟩, ?_, hrat, ?_, ?_,
      uniqueGeodIn_mono hUq (inter_subset_left.trans hVU), hsu, hsv, ?_, ?_⟩
    · calc b₁ * ρ * r = b₁ * (ρ * r) := by ring
        _ ≤ _ := hb
    · refine hset.trans (mul_le_mul_right (le_setDist_singleton fun w hw => ?_) _)
      have huz : ‖u - z‖ ≤ ρ * r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hu.2
      refine setDist_sphere_le_of_geod hex (by nlinarith) ?_
      have hwu : ‖w - u‖ = 4 * ρ * r := by rw [← dist_eq_norm]; exact mem_sphere.1 hw
      have : ‖w - u‖ ≤ ‖w - z‖ + ‖u - z‖ := by
        calc ‖w - u‖ = ‖(w - z) - (u - z)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖u - z‖ := norm_sub_le _ _
      nlinarith
    · refine hsetv.trans (mul_le_mul_right (le_setDist_singleton fun w hw => ?_) _)
      have hvz : ‖v - z‖ ≤ ρ * r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hv.2
      refine setDist_sphere_le_of_geod hex (by nlinarith) ?_
      have hwv : ‖w - v‖ = 4 * ρ * r := by rw [← dist_eq_norm]; exact mem_sphere.1 hw
      have : ‖w - v‖ ≤ ‖w - z‖ + ‖v - z‖ := by
        calc ‖w - v‖ = ‖(w - z) - (v - z)‖ := by ring_nf
          _ ≤ ‖w - z‖ + ‖v - z‖ := norm_sub_le _ _
      nlinarith
    · intro w hw
      rw [hOu] at hw
      exact (MetricGeometry.internalEDist_anti (image_mono hVU) _ _).trans (hi1 w hw)
    · intro w hw
      rw [hOv] at hw
      exact (MetricGeometry.internalEDist_anti (image_mono hVU) _ _).trans (hi2 w hw)
  exact hGp.trans (measure_mono_ae hsub)

/-- **GM Lemma 5.8**, from Lemmas 5.6, 2.7 and DFGPS Lemma 3.8 -/
theorem gm_L5_8 (h56 : L5_6) (h38 : DFGPSLem3_8) (hL : L2_7) : L5_8 :=
  gm_L5_8_of_geom l58Geom h56 h38 hL

end LQGMetric.GM
