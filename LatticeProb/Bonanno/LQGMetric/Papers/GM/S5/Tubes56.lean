/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes56 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.SepMeas56
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event4Law
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedP36Det

/-!
# GM Lemma 5.6 from its deterministic geometry (task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.6 (l. 2959–2995), the probabilistic part, step by step:

* "Let `α` be as in Lemma 5.5 and set `b₁ := 1 − α`" (l. 2960): `b₁ ≤ 1 − α` from `L56GeomN`;
* "with probability at least `p₀/9`, the event of Lemma 5.5 occurs and also (5.17)" (l. 2969–2974):
  `EndpointProp` (probability `≥ p₀/8`) and `gm_L56_sqDiam` (failure `≤ p₀/72`), and a.s. `D̃_h` is a
  length metric (Axiom I);
* "The number of subsets of `𝓢_{ε₁r}(B_{2r}(z))` is bounded above by a deterministic constant
  depending only on `ε₁`. Consequently, we can choose `p₁` … and a deterministic `𝒦_r(z)` …"
  (l. 2975–2979): the pigeonhole `exists_fiber_ge` over the subsets of the box `sqBox`
  (`2^{L²}` subsets, `L = boxLen`); the random choice of `(u, v)` and of `𝒦` uses `Classical.choose`
  (no measurability is needed: `exists_fiber_ge` holds for outer measure);
* conditions 1–3 (l. 2980–2994): condition 1 from Lemma 5.5 (with `D̃_h(u, ∂B_{2r}(z)) ≥
  D̃_h(𝔸_{αr,r}(z), ∂B_{2r}(z))` since `u ∈ cl 𝔸`), conditions 2 and 3 from `L56GeomN` (the corrected `L56Geom`, D69) with (5.17).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- `D(A, B) ≤ D({u}, B)` for `u ∈ cl A` -/
lemma setDist_le_singleton_of_mem_closure (d : ContMetric) {A B : Set ℂ} {u : ℂ}
    (hu : u ∈ closure A) : setDist d A B ≤ setDist d {u} B := by
  unfold setDist
  rw [← setEDist_closure (d.pt '' A)]
  refine setEDist_anti ?_ subset_closure
  rw [image_singleton, singleton_subset_iff]
  exact image_closure_subset_closure_image d.continuous_pt ⟨u, hu, rfl⟩

/-- the probability of the good event of the proof: Lemma 5.5's event, (5.17), and `D̃_h` length -/
lemma prob_good_ge {γ : ℝ} {D' : DistC → ContMetric} {c : ℝ → ℝ} (hD' : IsWeakLQGMetric γ D' c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) {p₀ : ℝ} (hp₀ : 0 < p₀) (A B : Set DistC)
    (hA : ENNReal.ofReal (p₀ / 8) ≤ P (h ⁻¹' A)) (hB : P (h ⁻¹' B)ᶜ ≤ ENNReal.ofReal (p₀ / 72)) :
    ENNReal.ofReal (p₀ / 9) ≤
      P (h ⁻¹' A ∩ (h ⁻¹' B ∩ {ω | (D' (h ω)).IsLength})) := by
  have hL : P {ω | (D' (h ω)).IsLength}ᶜ = 0 :=
    ae_iff.1 (hD'.length P h (Tight.isGFFPlusCont_of_wp hh))
  have h1 : P (h ⁻¹' A) ≤ P (h ⁻¹' A ∩ (h ⁻¹' B ∩ {ω | (D' (h ω)).IsLength})) +
      ENNReal.ofReal (p₀ / 72) := by
    calc P (h ⁻¹' A) ≤ P (h ⁻¹' A ∩ (h ⁻¹' B ∩ {ω | (D' (h ω)).IsLength}) ∪
          ((h ⁻¹' B)ᶜ ∪ {ω | (D' (h ω)).IsLength}ᶜ)) := by
          refine measure_mono fun ω hω => ?_
          by_cases h2 : ω ∈ h ⁻¹' B ∩ {ω | (D' (h ω)).IsLength}
          · exact Or.inl ⟨hω, h2⟩
          · right; rw [mem_inter_iff, not_and_or] at h2
            exact h2.imp id id
      _ ≤ P (h ⁻¹' A ∩ (h ⁻¹' B ∩ {ω | (D' (h ω)).IsLength})) +
          (P (h ⁻¹' B)ᶜ + P {ω | (D' (h ω)).IsLength}ᶜ) :=
          (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
      _ ≤ _ := by rw [hL, add_zero]; exact add_le_add le_rfl hB
  have e : ENNReal.ofReal (p₀ / 8) = ENNReal.ofReal (p₀ / 9) + ENNReal.ofReal (p₀ / 72) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  rw [e] at hA
  exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 (hA.trans h1)

/-- **GM Lemma 5.6** from its deterministic geometry `L56GeomN` (GM l. 2959–2995), with GM Lemma
2.8 in the form of DFGPS Lemma 3.20 (`Blueprint.DFGPSLem3_20`) -/
theorem gm_L5_6_of_geom (hgeom : L56GeomN) (h320 : DFGPSLem3_20) (h38 : DFGPSLem3_8) : L5_6 := by
  intro γ D D' c cs Cs hPS hRat hcs hcsC α p₀ hα3 hα1 hp0 hp1 hEnd c₁ c₂ η hc1 hc12 hc2 hη
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  set χ := xiGamma γ * (Q γ - 2) / 2 with hχ
  have hχ0 : 0 < χ := by have := xiQ_pos hγ0 hγ2; positivity
  have hχQ : χ < xiGamma γ * (Q γ - 2) := by have := xiQ_pos hγ0 hγ2; linarith
  obtain ⟨b₁, κ, ε', hb₁, hb₁α, hκ, hε', hG⟩ := hgeom α hα3 hα1 χ hχ0
  obtain ⟨hη0, -, -, -⟩ := hη
  obtain ⟨ε₁, ⟨hε₁0, hε₁lt⟩, Hd⟩ := gm_L56_sqDiam h320 hγ0 hγ2 hD' hχ0 hχQ (b := b₁)
    (θ := η / κ) (q := p₀ / 72) (ε₀ := min ε' (b₁ / 100)) hb₁.1 (div_pos hη0 hκ) (by positivity)
    (lt_min hε' (by linarith [hb₁.1]))
  have hε₁' : ε₁ < ε' := hε₁lt.trans_le (min_le_left _ _)
  have hε₁b : ε₁ < b₁ / 100 := hε₁lt.trans_le (min_le_right _ _)
  set L : ℕ := ⌈6 / ε₁⌉₊ + 1 with hL
  have hL2 : 2 ≤ L := by
    have : 0 < ⌈6 / ε₁⌉₊ := Nat.ceil_pos.2 (by positivity)
    omega
  have hM : (16 : ℝ) ≤ 2 ^ (L * L) := by
    have : 4 ≤ L * L := by nlinarith
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (L * L) := pow_le_pow_right₀ (by norm_num) this
  refine ⟨b₁, p₀ / 9 / 2 ^ (L * L), ε₁, hb₁, ⟨by positivity, ?_⟩, ⟨hε₁0, hε₁b⟩, ?_⟩
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith
  intro z r hr
  have hr0 : 0 < r := hr.1
  -- the pigeonhole for one whole-plane GFF (GM l. 2975–2979)
  have hsp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∃ V : Set ℂ, (IsOpen V ∧ IsConnected V ∧
        V ⊆ ball z ((2 + 2 * ε₁) * r) ∧ IsSquareTube V (ε₁ * r) (closedBall z (2 * r)) ∧
        z - 2 * r ∈ V ∧ z + 2 * r ∈ V) ∧
      ENNReal.ofReal (p₀ / 9 / 2 ^ (L * L)) ≤ P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ r z V) := by
    intro Ω _ P _ h hh
    obtain ⟨H, hH, hPE⟩ := hEnd c₁ r hr z P h hh
    have hPD := Hd P h hh r hr0 z
    set G := h ⁻¹' endpointEvent D D' cs Cs α c₁ r z H ∩
      (h ⁻¹' sqDiamEvent D' χ b₁ (η / κ) ε₁ r z ∩ {ω | (D' (h ω)).IsLength}) with hGdef
    have hPG := prob_good_ge hD' P h hh hp0 _ _ hPE hPD
    -- the deterministic properties of the square set
    let Qd : Finset (ℤ × ℤ) → Prop := fun F =>
      (↑F : Set (ℤ × ℤ)) ⊆ squareSet (ε₁ * r) (closedBall z (2 * r)) ∧
      IsConnected (tubeOf (ε₁ * r) F) ∧
      tubeOf (ε₁ * r) F ⊆ ball z ((2 + 2 * ε₁) * r) ∧ z - 2 * r ∈ tubeOf (ε₁ * r) F ∧
      z + 2 * r ∈ tubeOf (ε₁ * r) F
    have hHB : closure H ⊆ closedBall z r := by
      obtain ⟨e, -, rfl⟩ := hH
      refine (closure_mono inter_subset_left).trans
        ((closure_annulus_subset_closedAnnulus z _ _).trans fun w hw => ?_)
      rw [mem_closedBall, dist_eq_norm]; exact hw.2
    have key : ∀ ω ∈ G, ∃ F, Qd F ∧
        h ω ∈ tubeEvent D D' cs Cs c₁ η b₁ ε₁ r z (tubeOf (ε₁ * r) F) := by
      rintro ω ⟨⟨u, hu, v, hv, hrat, ⟨⟨γ', hγ', huniq⟩, hin⟩, hset⟩, hsq, hlen⟩
      have hTH : range γ' ⊆ closure H := hin γ' hγ'
      have hTc : IsConnected (range γ') := isConnected_range γ'.continuous
      have huT : u ∈ range γ' := ⟨0, hγ'.1⟩
      have hvT : v ∈ range γ' := ⟨1, hγ'.2.1⟩
      obtain ⟨F, hF, hFc, hFb, hFm, hFp, hTV, hs1, hs2, h3⟩ :=
        hG ε₁ ⟨hε₁0, hε₁'⟩ z r hr0 H hH u hu v hv _ hTH hTc huT hvT
      refine ⟨F, ⟨hF, hFc, hFb, hFm, hFp⟩, ?_⟩
      have hu' : ‖u - z‖ = α * r := by rw [← dist_eq_norm]; exact mem_sphere.1 hu
      have hv' : ‖v - z‖ = r := by rw [← dist_eq_norm]; exact mem_sphere.1 hv
      have huv : b₁ * r ≤ ‖u - v‖ := by
        have : ‖v - z‖ ≤ ‖u - v‖ + ‖u - z‖ := by
          rw [norm_sub_rev u v, ← sub_add_sub_cancel v u z]; exact norm_add_le _ _
        nlinarith
      have huB : u ∈ closedBall z r := by
        rw [mem_closedBall, dist_eq_norm, hu']; nlinarith
      have hvB : v ∈ closedBall z r := by rw [mem_closedBall, dist_eq_norm, hv']
      have hd0 : 0 ≤ (D' (h ω)).1 (u, v) := tubes_cm_nonneg _ _ _
      obtain ⟨h3u, h3v⟩ := h3 (D' (h ω)) hlen (η / κ * (D' (h ω)).1 (u, v)) (by positivity)
        (hsq u huB v hvB huv)
      have hk : κ * (η / κ * (D' (h ω)).1 (u, v)) = η * (D' (h ω)).1 (u, v) := by
        field_simp
      refine ⟨u, ⟨hTV huT, huB⟩, v, ⟨hTV hvT, hvB⟩, huv, hrat, ?_, ?_, ⟨⟨γ', hγ', huniq⟩, ?_⟩, hs1,
        hs2, fun w hw => (h3u w hw).trans_eq (by rw [hk]),
        fun w hw => (h3v w hw).trans_eq (by rw [hk])⟩
      · refine hset.trans (mul_le_mul_right (setDist_le_singleton_of_mem_closure _ ?_) _)
        exact mem_closure_annulus_of (by nlinarith) (by nlinarith) hu'.ge (by rw [hu']; nlinarith)
      · refine hset.trans (mul_le_mul_right (setDist_le_singleton_of_mem_closure _ ?_) _)
        exact mem_closure_annulus_of (by nlinarith) (by nlinarith) (by rw [hv']; nlinarith) hv'.le
      · intro η' hη'
        rw [huniq η' hη']
        exact fun w hw => ⟨hTV hw, hHB (hTH hw)⟩
    -- pigeonhole over the subsets of the index box
    classical
    set box := sqBox (ε₁ * r) (3 * r) z with hbox
    have hboxQ : ∀ F, Qd F → F ∈ box.powerset := fun F hF => Finset.mem_powerset.2
      (Finset.coe_subset.1 (hF.1.trans (squareSet_closedBall_subset_box (mul_pos hε₁0 hr0) hr0 _)))
    let X : Ω → box.powerset := fun ω => if hω : ω ∈ G then
        ⟨(key ω hω).choose, hboxQ _ (key ω hω).choose_spec.1⟩ else ⟨∅, Finset.empty_mem_powerset _⟩
    have : Nonempty box.powerset := ⟨⟨∅, Finset.empty_mem_powerset _⟩⟩
    obtain ⟨i, hi⟩ := exists_fiber_ge P G X hPG
    have hcard : (Fintype.card box.powerset : ℝ≥0∞) = 2 ^ (L * L) := by
      rw [Fintype.card_coe, Finset.card_powerset, card_sqBox, boxLen_eq3 hε₁0 hr0]
      push_cast; rfl
    rw [hcard] at hi
    have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (p₀ / 9) / 2 ^ (L * L) :=
      ENNReal.div_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' (ENNReal.pow_ne_top (by simp))
    have hne : (G ∩ X ⁻¹' {i}).Nonempty := by
      by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, measure_empty] at hi
      exact absurd (hpos.trans_le hi) (lt_irrefl _)
    have hXi : ∀ ω ∈ G ∩ X ⁻¹' {i}, ∃ hω : ω ∈ G, i.1 = (key ω hω).choose := by
      rintro ω ⟨hω, hX⟩
      refine ⟨hω, ?_⟩
      rw [mem_preimage, mem_singleton_iff] at hX
      rw [← hX]
      simp only [X, dif_pos hω]
    obtain ⟨ω₀, hω₀⟩ := hne
    obtain ⟨hω₀G, hi₀⟩ := hXi ω₀ hω₀
    have hQi : Qd i.1 := by rw [hi₀]; exact (key ω₀ hω₀G).choose_spec.1
    have hsub : G ∩ X ⁻¹' {i} ⊆
        h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ r z (tubeOf (ε₁ * r) i.1) := by
      intro ω hω
      obtain ⟨hωG, hiω⟩ := hXi ω hω
      rw [mem_preimage, hiω]
      exact (key ω hωG).choose_spec.2
    refine ⟨tubeOf (ε₁ * r) i.1, ⟨isOpen_interior, hQi.2.1, hQi.2.2.1, ⟨i.1, hQi.1, rfl⟩,
      hQi.2.2.2.1, hQi.2.2.2.2⟩, ?_⟩
    calc ENNReal.ofReal (p₀ / 9 / 2 ^ (L * L)) = ENNReal.ofReal (p₀ / 9) / 2 ^ (L * L) := by
          rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_ofNat]
      _ ≤ P (G ∩ X ⁻¹' {i}) := hi
      _ ≤ _ := measure_mono hsub

  -- `V` is deterministic: `P[h ∈ F_r(z)]` does not depend on the GFF (`prob_tubeEvent_eq`)
  by_cases hex : ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (h : Ω → DistC), IsWholePlaneGFF h P
  · obtain ⟨Ω₀, _, P₀, _, h₀, hh₀⟩ := hex
    obtain ⟨V, ⟨h1, h2, h3, h4, h5, h6⟩, hP⟩ := hsp P₀ h₀ hh₀
    refine ⟨V, h1, h2, h3, h4, h5, h6, fun P _ h hh => ?_⟩
    rwa [prob_tubeEvent_eq h38 hPS cs Cs c₁ η b₁ ε₁ r z h1 P h hh P₀ h₀ hh₀]
  · -- no whole-plane GFF: any tube of `L56GeomN` (here along the segment `[z + αr, z + r]`)
    set H0 : Set ℂ := (annulus z (α * r) r : Set ℂ) ∩
      {w | 0 < ((w - z) * (starRingEnd ℂ) 1).re} with hH0
    have hH0' : IsHalfAnnulus H0 z (α * r) r := ⟨1, norm_one, rfl⟩
    have hαr : 0 < α * r := by nlinarith
    have hαr1 : α * r < r := by nlinarith
    set T0 : Set ℂ := (fun t : ℝ => z + (t : ℂ)) '' Icc (α * r) r with hT0
    have hnt : ∀ t : ℝ, 0 ≤ t → ‖z + (t : ℂ) - z‖ = t := fun t ht => by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht]
    have hTH : T0 ⊆ closure H0 := by
      rintro _ ⟨t, ⟨ht1, ht2⟩, rfl⟩
      have ht0 : 0 < t := hαr.trans_le ht1
      rw [hH0, inter_comm]
      refine (isOpen_lt continuous_const (Complex.continuous_re.comp
        ((continuous_id.sub continuous_const).mul continuous_const))).inter_closure
        ⟨?_, mem_closure_annulus_of hαr hαr1 ?_ ?_⟩
      · simp [ht0]
      · rw [hnt t ht0.le]; exact ht1
      · rw [hnt t ht0.le]; exact ht2
    have hTc : IsConnected T0 :=
      (isConnected_Icc hαr1.le).image _ (by fun_prop)
    have hu0 : z + ((α * r : ℝ) : ℂ) ∈ sphere z (α * r) := by
      rw [mem_sphere, dist_eq_norm, hnt _ hαr.le]
    have hv0 : z + ((r : ℝ) : ℂ) ∈ sphere z r := by
      rw [mem_sphere, dist_eq_norm, hnt _ hr0.le]
    obtain ⟨F, hF, hFc, hFb, hFm, hFp, -⟩ := hG ε₁ ⟨hε₁0, hε₁'⟩ z r hr0 H0 hH0' _ hu0 _ hv0 T0
      hTH hTc ⟨α * r, ⟨le_rfl, hαr1.le⟩, rfl⟩ ⟨r, ⟨hαr1.le, le_rfl⟩, rfl⟩
    exact ⟨tubeOf (ε₁ * r) F, isOpen_interior, hFc, hFb, ⟨F, hF, rfl⟩, hFm, hFp,
      fun P _ h hh => absurd ⟨_, _, P, inferInstance, h, hh⟩ hex⟩

end LQGMetric.GM
