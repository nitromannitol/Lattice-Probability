/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreFin
import LatticeProb.Bonanno.LQGMetric.Field.ExistGFF
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380 (`lqg-metric-estimates-final.tex`, "T"),
Theorem 1.5 (`thm-metric-scaling`), proof T:1659–1723: for every `ζ > 0` there is `δ₀` with
`δ^{ξQ+ζ} ≤ 𝔠_{δ𝕣}/𝔠_𝕣 ≤ δ^{ξQ-ζ}` for `δ < δ₀`, `𝕣 > 0`.

Step 1 (T:1662–1670): on the canonical space `(DistC, μ, id)`, Proposition 3.1 at every grid point
`z ∈ (𝕣𝕊) ∩ (δ𝕣ℤ²)` (constants uniform in `z`, `prop3_1_centre_box`, `prop3_1_centre_ann`) with
`A = δ^{-ζ'}`, `p = 3/ζ'`, and a union bound over the `≤ δ^{-2}` grid points; Proposition 3.1 at
the centre `0` (the paper's "Axiom V" bounds for `D_h(𝕣∂_L𝕊, 𝕣∂_R𝕊)`, T:1688, T:1716) and
Lemma 3.6 with `η = 1/4`. The good event has probability `> 0`; on it, Steps 2–3
(`scaling_bounds_of_good`) give `δ^{ξQ+3ζ'} ≤ 8 𝔠_{δ𝕣}/𝔠_𝕣` and `𝔠_{δ𝕣}/𝔠_𝕣 ≤ 2δ^{ξQ-3ζ'}`;
with `ζ' = min(ζ,1)/4` and `δ^{ζ/4} ≤ 1/8` this is the claim ("sending `ζ → 0`").
-/

noncomputable section

open MeasureTheory Set Metric Complex Filter Topology
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint

/-- the canonical space of a normalized whole-plane GFF -/
lemma exists_canonical_normGFF :
    ∃ μ : Measure DistC, IsProbabilityMeasure μ ∧ IsNormalizedWPGFF id μ := by
  obtain ⟨Ω, _, P, hP, h, hh⟩ := GFFExist.exists_normalizedWPGFF
  exact ⟨P.map h, (Measure.isProbabilityMeasure_map_iff hh.1.measurable.aemeasurable).2 hP,
    GM.isWholePlaneGFF_id_map hh.1, (ae_map_iff hh.1.measurable.aemeasurable
      (measurableSet_eq_fun (measurable_circleAvg_left 1 0) measurable_const)).2 hh.2⟩

/-- the grid points of `𝕣𝕊` with mesh `δ𝕣` -/
lemma grid_mem_finset {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) {z : ℂ}
    (hz : z ∈ rS r ∩ gridPts (δ * r)) :
    ∃ q ∈ Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋,
      z = ⟨q.1 * (δ * r), q.2 * (δ * r)⟩ := by
  obtain ⟨a, b, rfl⟩ := hz.2
  have hS := (mem_rS_iff hr).1 hz.1
  simp only at hS
  have hs : 0 < δ * r := mul_pos hδ hr
  have key : ∀ m : ℤ, 0 < (m : ℝ) * (δ * r) → (m : ℝ) * (δ * r) < r →
      (1 : ℤ) ≤ m ∧ m ≤ ⌊δ⁻¹⌋ := by
    intro m h1 h2
    have hm : (0 : ℝ) < m := pos_of_mul_pos_left h1 hs.le
    refine ⟨by exact_mod_cast hm, Int.le_floor.2 ?_⟩
    rw [le_inv_comm₀ ?_ hδ] <;> [skip; exact hm]
    have : (m : ℝ) * δ < 1 := by
      have := (mul_lt_mul_iff_of_pos_right hr).1 (by linarith : (m : ℝ) * δ * r < 1 * r)
      exact this
    rw [inv_eq_one_div, le_div_iff₀ hm]
    linarith
  obtain ⟨ha1, ha2⟩ := key a hS.1 hS.2.1
  obtain ⟨hb1, hb2⟩ := key b hS.2.2.1 hS.2.2.2
  exact ⟨(a, b), Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨ha1, ha2⟩, Finset.mem_Icc.2 ⟨hb1, hb2⟩⟩,
    rfl⟩

lemma card_grid_le {δ : ℝ} (hδ : 0 < δ) :
    ((Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋).card : ℝ) * δ ^ 2 ≤ 1 := by
  rw [Finset.card_product, Int.card_Icc, add_sub_cancel_right]
  have h0 : 0 ≤ ⌊δ⁻¹⌋ := Int.floor_nonneg.2 (inv_pos.2 hδ).le
  have h1 : ((⌊δ⁻¹⌋.toNat : ℕ) : ℝ) ≤ δ⁻¹ := by
    rw [show ((⌊δ⁻¹⌋.toNat : ℕ) : ℝ) = ((⌊δ⁻¹⌋.toNat : ℤ) : ℝ) by norm_cast, Int.toNat_of_nonneg h0]
    exact Int.floor_le _
  push_cast
  calc ((⌊δ⁻¹⌋.toNat : ℝ) * (⌊δ⁻¹⌋.toNat : ℝ)) * δ ^ 2
      ≤ (δ⁻¹ * δ⁻¹) * δ ^ 2 := by gcongr
    _ = 1 := by field_simp

/-- the union bound over the grid (abstract form) -/
lemma exists_good_of_union_bound {μ : Measure DistC} [IsProbabilityMeasure μ] {ι : Type}
    (F : Finset ι) (EH EV EA : ι → Set DistC) (E2 E3 B : Set DistC) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (bH : ∀ q, μ (EH q)ᶜ ≤ ENNReal.ofReal x)
    (bV : ∀ q, μ (EV q)ᶜ ≤ ENNReal.ofReal x) (bA : ∀ q, μ (EA q)ᶜ ≤ ENNReal.ofReal x)
    (b2 : μ E2ᶜ ≤ ENNReal.ofReal x) (b3 : μ E3ᶜ ≤ ENNReal.ofReal x) (bB : μ B ≤ ENNReal.ofReal y)
    (hsum : F.card * (3 * x) + x + x + y < 1) :
    ∃ g, (∀ q ∈ F, g ∈ EH q ∧ g ∈ EV q ∧ g ∈ EA q) ∧ g ∈ E2 ∧ g ∈ E3 ∧ g ∉ B := by
  set Good : Set DistC := {g | (∀ q ∈ F, g ∈ EH q ∧ g ∈ EV q ∧ g ∈ EA q) ∧ g ∈ E2 ∧ g ∈ E3 ∧
    g ∉ B} with hGood
  have hsub : Goodᶜ ⊆ (((⋃ q ∈ F, ((EH q)ᶜ ∪ (EV q)ᶜ ∪ (EA q)ᶜ)) ∪ E2ᶜ) ∪ E3ᶜ) ∪ B := by
    intro g hg
    by_contra hcon
    apply hg
    simp only [mem_union, mem_iUnion, mem_compl_iff, not_or, not_exists, not_not] at hcon
    obtain ⟨⟨⟨hq, h2⟩, h3⟩, hB⟩ := hcon
    exact ⟨fun q hqF => ⟨(hq q hqF).1.1, (hq q hqF).1.2, (hq q hqF).2⟩, h2, h3, hB⟩
  have hU : μ (⋃ q ∈ F, ((EH q)ᶜ ∪ (EV q)ᶜ ∪ (EA q)ᶜ)) ≤ ENNReal.ofReal (F.card * (3 * x)) := by
    refine (measure_biUnion_finset_le F _).trans ?_
    rw [show (F.card : ℝ) * (3 * x) = ∑ q ∈ F, 3 * x by
      rw [Finset.sum_const, nsmul_eq_mul], ENNReal.ofReal_sum_of_nonneg
      (fun _ _ => by positivity)]
    refine Finset.sum_le_sum fun q _ => ?_
    refine (measure_union_le _ _).trans ((add_le_add ((measure_union_le _ _).trans
      (add_le_add (bH _) (bV _))) (bA _)).trans_eq ?_)
    rw [← ENNReal.ofReal_add hx hx, ← ENNReal.ofReal_add (by positivity) hx]
    ring_nf
  have hbad : μ Goodᶜ < 1 := by
    refine lt_of_le_of_lt (measure_mono hsub) ?_
    refine lt_of_le_of_lt (measure_union_le _ _) ?_
    refine lt_of_le_of_lt (add_le_add (measure_union_le _ _) bB) ?_
    refine lt_of_le_of_lt (add_le_add (add_le_add (measure_union_le _ _) b3) le_rfl) ?_
    refine lt_of_le_of_lt (add_le_add (add_le_add (add_le_add hU b2) le_rfl) le_rfl) ?_
    rw [← ENNReal.ofReal_add (by positivity) hx, ← ENNReal.ofReal_add (by positivity) hx,
      ← ENNReal.ofReal_add (by positivity) hy, ENNReal.ofReal_lt_one]
    exact hsum
  by_contra hne
  have : Good = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    exact fun g hg => hne ⟨g, hg⟩
  rw [this, compl_empty, measure_univ] at hbad
  exact lt_irrefl _ hbad

lemma arith_bad {card Cm δ : ℝ} (hc : card * δ ^ 2 ≤ 1) (hCm : 0 ≤ Cm) (hδ : 0 < δ)
    (hδ1 : δ < 1) (h5 : 5 * Cm * δ < 1 / 2) :
    card * (3 * (Cm * δ ^ 3)) + Cm * δ ^ 3 + Cm * δ ^ 3 + 1 / 4 < 1 := by
  have h1 : card * (3 * (Cm * δ ^ 3)) ≤ 3 * Cm * δ := by
    have := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 3 * Cm * δ)
    calc card * (3 * (Cm * δ ^ 3)) = 3 * Cm * δ * (card * δ ^ 2) := by ring
      _ ≤ 3 * Cm * δ * 1 := this
      _ = 3 * Cm * δ := mul_one _
  have h3 : δ ^ 3 ≤ δ := by
    have h2 : δ ^ 2 ≤ 1 := pow_le_one₀ hδ.le hδ1.le
    calc δ ^ 3 = δ * δ ^ 2 := by ring
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left h2 hδ.le
      _ = δ := mul_one δ
  have h4 : Cm * δ ^ 3 ≤ Cm * δ := mul_le_mul_of_nonneg_left h3 hCm
  linarith

lemma exp_lower_aux {P W R : ℝ} (hP : 0 < P) (hW : W ≤ 1 / 8) (hL : P ≤ 8 * R) : P * W ≤ R := by
  have := mul_le_mul_of_nonneg_left hW hP.le
  linarith

lemma exp_upper_aux {P W R : ℝ} (hP : 0 < P) (hW : W ≤ 1 / 8) (hU : R ≤ 2 * (P * W)) :
    R ≤ P := by
  have := mul_le_mul_of_nonneg_left hW hP.le
  linarith

/-- **DFGPS Theorem 1.5** from Proposition 3.1 and Lemma 3.6 (T:1659–1723). -/
theorem dfgpsScaling_of_nodes (h31 : Prop3_1) (h36 : Lem3_6) : Blueprint.DFGPSScaling := by
  intro γ hγ0 hγ2 D c hD ζ hζ
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  set ξ := xiGamma γ with hξ
  set ζ' := min ζ 1 / 4 with hζ'_def
  have hm0 : 0 < min ζ 1 := lt_min hζ one_pos
  have hζ'0 : 0 < ζ' := by positivity
  have hζ'1 : ζ' < 1 := by have := min_le_right ζ 1; rw [hζ'_def]; linarith
  have hζ'ζ : 4 * ζ' ≤ ζ := by have := min_le_left ζ 1; rw [hζ'_def]; linarith
  set p := 3 / ζ' with hp_def
  have hp : 0 < p := by positivity
  obtain ⟨CH, AH, hCH⟩ := prop3_1_centre_box h31 hγ0 hγ2 hD (a₁ := -5 / 2) (b₁ := -5 / 2)
    (c₁ := -1 / 4) (d₁ := 1 / 4) (a₂ := 5 / 2) (b₂ := 5 / 2) (c₂ := -1 / 4) (d₂ := 1 / 4)
    (X₀ := -3) (X₁ := 3) (Y₀ := -1 / 2) (Y₁ := 1 / 2) le_rfl (by norm_num) le_rfl (by norm_num)
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num)
    (by norm_num) hμ p hp
  obtain ⟨CV, AV, hCV⟩ := prop3_1_centre_box h31 hγ0 hγ2 hD (a₁ := -1 / 4) (b₁ := 1 / 4)
    (c₁ := -5 / 2) (d₁ := -5 / 2) (a₂ := -1 / 4) (b₂ := 1 / 4) (c₂ := 5 / 2) (d₂ := 5 / 2)
    (X₀ := -1 / 2) (X₁ := 1 / 2) (Y₀ := -3) (Y₁ := 3) (by norm_num) le_rfl (by norm_num) le_rfl
    (Or.inl (by norm_num)) (Or.inl (by norm_num)) (Or.inr (by norm_num)) (by norm_num)
    (by norm_num) hμ p hp
  obtain ⟨C2, A2, hC2⟩ := prop3_1_centre_box h31 hγ0 hγ2 hD (a₁ := 0) (b₁ := 0)
    (c₁ := -1) (d₁ := 2) (a₂ := 1) (b₂ := 1) (c₂ := -1) (d₂ := 2)
    (X₀ := -2) (X₁ := 3) (Y₀ := -2) (Y₁ := 3) le_rfl (by norm_num) le_rfl (by norm_num)
    (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inl (by norm_num)) (by norm_num)
    (by norm_num) hμ p hp
  obtain ⟨C3, A3, hC3⟩ := prop3_1_centre_box h31 hγ0 hγ2 hD (a₁ := 0) (b₁ := 0)
    (c₁ := 3 / 8) (d₁ := 5 / 8) (a₂ := 5 / 4) (b₂ := 5 / 4) (c₂ := 3 / 8) (d₂ := 5 / 8)
    (X₀ := -1 / 8) (X₁ := 11 / 8) (Y₀ := 1 / 4) (Y₁ := 3 / 4) le_rfl (by norm_num) le_rfl
    (by norm_num) (Or.inr (by norm_num)) (Or.inr (by norm_num)) (Or.inl (by norm_num))
    (by norm_num) (by norm_num) hμ p hp
  obtain ⟨CA, AA, hCA⟩ := prop3_1_centre_ann h31 hγ0 hγ2 hD hμ p hp
  obtain ⟨δ₁, hδ₁, h36'⟩ := h36 γ hγ0 hγ2 μ id hμ ζ' ⟨hζ'0, hζ'1⟩ (1 / 4) (by norm_num)
  set Cm := max (max (max CH CV) (max CA C2)) (max C3 0) with hCm
  set A₀ := max (max (max AH AV) (max AA A2)) A3 with hA₀
  have hCm0 : 0 ≤ Cm := le_max_of_le_right (le_max_right _ _)
  -- smallness of `δ`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < 1 / 8 ∧ δ < δ₁ ∧ A₀ < δ ^ (-ζ') ∧ 5 * Cm * δ < 1 / 2 ∧
      δ ^ (ζ / 4) ≤ 1 / 8 := by
    refine ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8)).filter_mono nhdsWithin_le_nhds).and
      (((eventually_lt_nhds hδ₁).filter_mono nhdsWithin_le_nhds).and
      (((tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.2 hζ'0)).eventually_gt_atTop A₀).and
      (Eventually.and ?_ ?_)))
    · have ht : Tendsto (fun δ : ℝ => 5 * Cm * δ) (𝓝 0) (𝓝 0) := by
        have h := (tendsto_id (x := 𝓝 (0 : ℝ))).const_mul (5 * Cm)
        simpa using h
      exact (ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))).filter_mono
        nhdsWithin_le_nhds
    · have ht : Tendsto (fun δ : ℝ => δ ^ (ζ / 4)) (𝓝 0) (𝓝 0) := by
        have := (Real.continuousAt_rpow_const 0 (ζ / 4) (Or.inr (by positivity))).tendsto
        rwa [Real.zero_rpow (by positivity)] at this
      exact (ht.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 8))).filter_mono
        nhdsWithin_le_nhds
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
  refine ⟨δ₀, hδ₀, fun δ hδ r hr => ?_⟩
  obtain ⟨hδ8, hδδ₁, hAδ, hCδ, hζδ⟩ := hball (by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ.1]; exact hδ.2) hδ.1
  have hδ0 := hδ.1
  set A := δ ^ (-ζ') with hA_def
  set s := δ * r with hs_def
  have hs : 0 < s := mul_pos hδ0 hr
  have hAp : A ^ (-p) = δ ^ 3 := by
    rw [hA_def, ← Real.rpow_mul hδ0.le, show -ζ' * -p = ((3 : ℕ) : ℝ) by
      rw [hp_def]; field_simp; norm_num, Real.rpow_natCast]
  have hgt : ∀ A', A' ≤ A₀ → A' < A := fun A' h => h.trans_lt hAδ
  have hCle : ∀ C', C' ≤ Cm → ENNReal.ofReal (C' * A ^ (-p)) ≤ ENNReal.ofReal (Cm * δ ^ 3) :=
    fun C' h => ENNReal.ofReal_le_ofReal (by
      rw [hAp]; exact mul_le_mul_of_nonneg_right h (by positivity))
  -- the events
  let EH : ℂ → Set DistC := fun z => {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g s z) ≤
      setDistIn (D g) (scaleSet s z rectHK₁) (scaleSet s z rectHK₂) (scaleSet s z rectHU) ∧
    setDistIn (D g) (scaleSet s z rectHK₁) (scaleSet s z rectHK₂) (scaleSet s z rectHU) ≤
      ENNReal.ofReal (A * scaleFac ξ c g s z)}
  let EV : ℂ → Set DistC := fun z => {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g s z) ≤
      setDistIn (D g) (scaleSet s z rectVK₁) (scaleSet s z rectVK₂) (scaleSet s z rectVU) ∧
    setDistIn (D g) (scaleSet s z rectVK₁) (scaleSet s z rectVK₂) (scaleSet s z rectVU) ≤
      ENNReal.ofReal (A * scaleFac ξ c g s z)}
  let EA : ℂ → Set DistC := fun z => {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g s z) ≤
      setDistIn (D g) (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s))}
  let E2 : Set DistC := {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g r 0) ≤
      setDistIn (D g) (scaleSet r 0 box2K₁) (scaleSet r 0 box2K₂) (scaleSet r 0 box2U) ∧
    setDistIn (D g) (scaleSet r 0 box2K₁) (scaleSet r 0 box2K₂) (scaleSet r 0 box2U) ≤
      ENNReal.ofReal (A * scaleFac ξ c g r 0)}
  let E3 : Set DistC := {g | ENNReal.ofReal (A⁻¹ * scaleFac ξ c g r 0) ≤
      setDistIn (D g) (scaleSet r 0 box3K₁) (scaleSet r 0 box3K₂) (scaleSet r 0 box3U) ∧
    setDistIn (D g) (scaleSet r 0 box3K₁) (scaleSet r 0 box3K₂) (scaleSet r 0 box3U) ≤
      ENNReal.ofReal (A * scaleFac ξ c g r 0)}
  let B36 : Set DistC := {g | ¬ (δ ^ (-xiGamma γ * Q γ + ζ') *
        Real.exp (xiGamma γ * circleAvg (id g) r 0) ≤
      graphLFPP (xiGamma γ) (δ * r) (fun x => circleAvg (id g) (δ * r) x)
        (leftVerts (δ * r) r) (rightVerts (δ * r) r) (rS r) ∧
    graphLFPP (xiGamma γ) (δ * r) (fun x => circleAvg (id g) (δ * r) x)
        (leftVerts (δ * r) r) (rightVerts (δ * r) r) (rS r) ≤
      δ ^ (-xiGamma γ * Q γ - ζ') * Real.exp (xiGamma γ * circleAvg (id g) r 0))}
  have bH : ∀ z, μ (EH z)ᶜ ≤ ENNReal.ofReal (Cm * δ ^ 3) := fun z =>
    (hCH A (hgt AH (by simp [hA₀])) s hs z).trans (hCle CH (by simp [hCm]))
  have bV : ∀ z, μ (EV z)ᶜ ≤ ENNReal.ofReal (Cm * δ ^ 3) := fun z =>
    (hCV A (hgt AV (by simp [hA₀])) s hs z).trans (hCle CV (by simp [hCm]))
  have bA : ∀ z, μ (EA z)ᶜ ≤ ENNReal.ofReal (Cm * δ ^ 3) := fun z =>
    (hCA A (hgt AA (by simp [hA₀])) s hs z).trans (hCle CA (by simp [hCm]))
  have b2 : μ E2ᶜ ≤ ENNReal.ofReal (Cm * δ ^ 3) :=
    (hC2 A (hgt A2 (by simp [hA₀])) r hr 0).trans (hCle C2 (by simp [hCm]))
  have b3 : μ E3ᶜ ≤ ENNReal.ofReal (Cm * δ ^ 3) :=
    (hC3 A (hgt A3 (by simp [hA₀])) r hr 0).trans (hCle C3 (by simp [hCm]))
  have b36 : μ B36 ≤ ENNReal.ofReal (1 / 4) := h36' δ ⟨hδ0, hδδ₁⟩ r hr
  -- the union bound
  set F := Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋ ×ˢ Finset.Icc (1 : ℤ) ⌊δ⁻¹⌋ with hF
  have hδ1 : δ < 1 := by linarith
  obtain ⟨g, hgG, hg2, hg3, hg36⟩ := exists_good_of_union_bound (μ := μ) F
    (fun q => EH ⟨q.1 * s, q.2 * s⟩) (fun q => EV ⟨q.1 * s, q.2 * s⟩)
    (fun q => EA ⟨q.1 * s, q.2 * s⟩) E2 E3 B36 (by positivity) (by norm_num)
    (fun q => bH _) (fun q => bV _) (fun q => bA _) b2 b3 b36
    (arith_bad (card_grid_le hδ0) hCm0 hδ0 hδ1 hCδ)
  have hG : ∀ z ∈ rS r ∩ gridPts s, g ∈ EH z ∧ g ∈ EV z ∧ g ∈ EA z := by
    intro z hz
    obtain ⟨q, hqF, rfl⟩ := grid_mem_finset hδ0 hr hz
    exact hgG q hqF
  have hcs : 0 < c s := hD.tightness.1 s hs
  have hcr : 0 < c r := hD.tightness.1 r hr
  have h36g := not_not.1 hg36
  obtain ⟨L, U⟩ := scaling_bounds_of_good (D g) (Qv := Q γ) c g hδ0 hδ8 hr hcs hcr
    (fun z hz => (hG z hz).1.2) (fun z hz => (hG z hz).2.1.2) (fun z hz => (hG z hz).2.2)
    hg2.1 hg3.2 h36g
  -- the exponents
  have hw : δ ^ (ζ - 3 * ζ') ≤ 1 / 8 :=
    (Real.rpow_le_rpow_of_exponent_ge hδ0 (by linarith) (by linarith)).trans hζδ
  have hw0 : 0 < δ ^ (ζ - 3 * ζ') := Real.rpow_pos_of_pos hδ0 _
  have hsplit1 : δ ^ (ξ * Q γ + ζ) = δ ^ (ξ * Q γ + 3 * ζ') * δ ^ (ζ - 3 * ζ') := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hsplit2 : δ ^ (ξ * Q γ - 3 * ζ') = δ ^ (ξ * Q γ - ζ) * δ ^ (ζ - 3 * ζ') := by
    rw [← Real.rpow_add hδ0]; ring_nf
  have hp1 : 0 < δ ^ (ξ * Q γ + 3 * ζ') := Real.rpow_pos_of_pos hδ0 _
  have hp2 : 0 < δ ^ (ξ * Q γ - ζ) := Real.rpow_pos_of_pos hδ0 _
  constructor
  · rw [hsplit1]
    exact exp_lower_aux hp1 hw L
  · rw [hsplit2] at U
    exact exp_upper_aux hp2 hw U

end LQGMetric.DFGPS
