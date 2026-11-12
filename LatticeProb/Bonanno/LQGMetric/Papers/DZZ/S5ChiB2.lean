/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiB2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54J1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61P2

/-!
# DZZ Proposition 5.1, lower bound at `μIn` at the walled box, with rates (D129, P-129B)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Prop 5.1, l. 2333–2340:
Lemma 5.4 (`lem-exponent-point-to-boundary`) at the fixed box `𝕍_{ū,1/10}`, `ū = 1/2 + i/2`,
transported by the scaling coupling (`lem-scaling-coupling`, l. 611–624) to `𝕍_{u,2λ}`:
w.h.p. `min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}_δ(u,x) ≥ δ^{−χ+ι}`. Decision D129 (`decisions/DEC-129.md`
§2 (S3)–(S4), §4 P-129B).

* `alphaHighProb_lower_of_conc`: the polynomial-rate form of `hasRate_lower_of_conc` (S5ChiA1),
  same proof: only P3.17's first concentration bound `δ^{cι²}` enters. The polynomial form is
  needed because the scaling coupling evaluates the reference bound at the *larger* scale
  `δ^{1−ι'}`, under which `δ^c` stays a rate but `e^{−(log δ⁻¹)^{0.7}}` does not;
* `alphaHighProb_ref_lower`: the reference bound at `ū`, from `dzzLem54Exp_dzzMuIn_of_walls`
  (S5L54J1) and the walled P3.17 at `sqBox ū (1/10) ∈ dgWalls`;
* **`hasRate_dzzMuIn_lower_box`**: the bound at `(u, λ)` for any `0 < λ ≤ 1/20` with
  `𝕍_{u,2λ} ⊆ 𝕍°`, by `dzzSimCoupleU_of_norm_le` with `a = 20λ`, `b = u − a ū` (template:
  `ptBdry_key`, S6L61P2, and `hasRate_tilde_link`, S5ChiA2), `λ_coupling = ι' log δ⁻¹ + log a`,
  laws transported by `prob_lgdMinSet_wall_eq` (S5L54I1).

**DEVIATIONS DV-D129-1** (rates explicit; DZZ: "with high probability", `λ = √(log δ⁻¹)`),
**DV-D129-3** (any `λ ≤ 1/20` with `𝕍_{u,2λ} ⊆ 𝕍°` instead of DZZ's
`λ = min{ξ/√2, |u−v|/√2, 1/20}`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma alphaHighProb_mono_ev {α : ℝ} {E F : ℝ → Set Ω} (h : AlphaHighProb P α E)
    (hEF : ∀ᶠ δ in 𝓝[>] (0 : ℝ), E δ ⊆ F δ) : AlphaHighProb P α F := by
  obtain ⟨δ₀, hδ₀, hb⟩ := h
  obtain ⟨δ₁, hδ₁, h1⟩ := exists_Ioo_of_eventually_nhdsGT hEF
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun δ hδ => ?_⟩
  exact (measure_mono (compl_subset_compl.2 (h1 δ ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩))).trans
    (hb δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩)

/-- **polynomial-rate form of `hasRate_lower_of_conc`** (S5ChiA1; same proof, via
`hasRate_ge_of_conc'`): `P[min D_δ(A_δ,B_δ) < δ^{−χ+ι}] ≤ δ^α`. -/
theorem alphaHighProb_lower_of_conc {μ : Ω → Measure ℂ} {K : Set ℂ} {ξ χ : ℝ}
    (h317 : DZZProp317In P μ K ξ) {A B : ℝ → Set ℂ} (hAB : IsXiAdmissible ξ A B)
    (hin : ∀ δ ∈ Ioo (0 : ℝ) 1, A δ ⊆ kXi K ξ ∧ B δ ⊆ kXi K ξ)
    (hexp : Tendsto (fun δ => (∫ ω, logMinLGD (μ ω) δ (A δ) (B δ) ∂P) / Real.log δ⁻¹)
      (𝓝[>] 0) (𝓝 χ))
    {ι : ℝ} (hι : 0 < ι) :
    ∃ α : ℝ, 0 < α ∧ AlphaHighProb P α (fun δ => {ω | ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lgdMinSet (μ ω) δ (A δ) (B δ) : ℕ∞) : ℝ≥0∞)}) := by
  obtain ⟨c, hc, h⟩ := h317
  set ι' := min (ι / 2) (1 / 2)
  have hι' : ι' ∈ Ioo (0 : ℝ) 1 := ⟨lt_min (by linarith) (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num)⟩
  refine ⟨c * ι' ^ 2, by have := hι'.1; positivity,
    alphaHighProb_mono_ev ((h A B hAB hin).1 ι' hι') ?_⟩
  filter_upwards [eventually_Ioo_nhdsGT one_pos, hexp (Ioi_mem_nhds (by linarith : χ - ι / 2 < χ))]
    with δ hδ hEδ ω hω
  have hL := log_inv_pos_of_mem hδ
  simp only [conc1Event, mem_ofPred_eq, mem_preimage, mem_Ioi] at hω hEδ ⊢
  rw [lt_div_iff₀ hL] at hEδ
  have h1 : ι' * Real.log δ⁻¹ ≤ ι / 2 * Real.log δ⁻¹ :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le
  have h2 := neg_abs_le (logMinLGD (μ ω) δ (A δ) (B δ) - ∫ ω', logMinLGD (μ ω') δ (A δ) (B δ) ∂P)
  have hX : (χ - ι) * Real.log δ⁻¹ ≤ logMinLGD (μ ω) δ (A δ) (B δ) := by nlinarith
  by_contra hlt
  rw [not_le] at hlt
  have htop : lgdMinSet (μ ω) δ (A δ) (B δ) ≠ ⊤ := by
    intro h; rw [h] at hlt; simp at hlt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have h1 := one_le_lgdMinSet (μ ω) δ (A δ) (B δ)
  rw [← hn] at h1 hlt
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
  rw [show (((n : ℕ∞) : ℝ≥0∞)) = ENNReal.ofReal n by simp,
    ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)] at hlt
  unfold logMinLGD at hX; rw [← hn] at hX
  simp only [ENat.toNat_natCast] at hX
  rw [← exp_mul_log_inv hδ.1] at hlt
  have := Real.log_lt_log (by linarith) hlt
  rw [Real.log_exp] at this
  linarith

variable {W : WNSpace → Ω → ℝ}

/-- **DZZ Lemma 5.4 at `ū = 1/2 + i/2`, lower tail, polynomial rate** (DZZ l. 2336–2338):
`P[min_{x ∈ ∂𝕍_{ū,1/20}} D̄^{ū,1/10}_δ(ū,x) < δ^{−χ+ι}] ≤ δ^α`. -/
theorem alphaHighProb_ref_lower (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {χ : ℝ} (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    {ι : ℝ} (hι : 0 < ι) :
    ∃ α : ℝ, 0 < α ∧ AlphaHighProb P α (fun δ => {ω | ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lgdMinSet (dzzWall (sqBox ptCentre (1 / 10)) (dzzMuIn γ W ω)) δ {ptCentre}
        (frontier (sqBox ptCentre (1 / 20))) : ℕ∞) : ℝ≥0∞)}) := by
  obtain ⟨ξ₂, hξ₂, hw⟩ := hwalls
  set ξ := min (ξ₂ / 2) (1 / 80) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (by norm_num)
  have hξ1 : ξ ≤ 1 / 80 := min_le_right _ _
  have hξlt : ξ < ξ₂ := (min_le_left _ _).trans_lt (by linarith)
  have hw' := hw ξ hξ hξlt
  have h317 := dzzProp317In_sqBox_of_walls hw' ptCentre_mem_dzzVbar
  have h54 := dzzLem54Exp_dzzMuIn_of_walls hW hγ hγ2 hξ hξ1 hL hw' ptCentre ptCentre_mem_dzzVbar
  obtain ⟨δ₁, hδ₁, hδ₁s⟩ := exists_Ioo_of_eventually_nhdsGT
    (eventually_rpow_lt hξ (by norm_num : (0 : ℝ) < 1 / 20))
  set F := frontier (sqBox ptCentre (1 / 20)) with hF
  have hAB := l54_isXiAdmissible (δ₁ := δ₁) hξ (by linarith) ptCentre_mem_dzzVbar (fun _ => F)
    (fun δ hδ hlt => ⟨subset_rfl, Or.inr ⟨isConnected_frontier_sqBox _ (by norm_num),
      (hδ₁s δ ⟨hδ.1, hlt⟩).le.trans (side_le_diam_frontier_sqBox _ (by norm_num))⟩⟩)
  have hin := l54_pair_kXi (ξ := ξ) (δ₁ := δ₁) (by linarith) (u := ptCentre) (fun _ => F)
    (fun _ _ _ => subset_rfl)
  have hexp : Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (sqBox ptCentre (1 / 10))
      (dzzMuIn γ W ω)) δ {ptCentre} (if δ < δ₁ then F else {l54Pt ptCentre}) ∂P) /
        Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
    refine h54.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ
    simp only [hδ.2, ↓reduceIte]
  obtain ⟨α, hα, hP⟩ := alphaHighProb_lower_of_conc
    (μ := fun ω => dzzWall (sqBox ptCentre (1 / 10)) (dzzMuIn γ W ω)) h317 hAB hin hexp hι
  refine ⟨α, hα, alphaHighProb_mono_ev hP ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ₁] with δ hδ ω hω
  simp only [mem_ofPred_eq, hδ.2, ↓reduceIte] at hω ⊢
  exact hω

/-- the coordinate margin of a box `𝕍_{u,2λ} ⊆ 𝕍°` (own elementary geometry) -/
lemma exists_margin_sqBox {u : ℂ} {l : ℝ} (hl : 0 < l) (h : sqBox u (2 * l) ⊆ openSquare) :
    ∃ m : ℝ, 0 < m ∧ m ≤ u.re - l ∧ u.re + l ≤ 1 - m ∧ m ≤ u.im - l ∧ u.im + l ≤ 1 - m := by
  have hm : ∀ s t : ℝ, |s| ≤ l → |t| ≤ l → (⟨u.re + s, u.im + t⟩ : ℂ) ∈ openSquare :=
    fun s t hs ht => h ⟨by show |(u.re + s) - u.re| ≤ 2 * l / 2; rw [add_sub_cancel_left]; linarith,
      by show |(u.im + t) - u.im| ≤ 2 * l / 2; rw [add_sub_cancel_left]; linarith⟩
  have habs : |l| ≤ l := (abs_of_pos hl).le
  have habs' : |-l| ≤ l := by rw [abs_neg]; exact habs
  have h0 : |(0 : ℝ)| ≤ l := by rw [abs_zero]; exact hl.le
  have h1 := (hm (-l) 0 habs' h0).1
  have h2 := (hm l 0 habs h0).2.1
  have h3 := (hm 0 (-l) h0 habs').2.2.1
  have h4 := (hm 0 l h0 habs).2.2.2
  simp only at h1 h2 h3 h4
  refine ⟨min (min (u.re - l) (1 - u.re - l)) (min (u.im - l) (1 - u.im - l)),
    lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith)),
    (min_le_left _ _).trans (min_le_left _ _), ?_, (min_le_right _ _).trans (min_le_left _ _), ?_⟩
  · have := (min_le_left (min (u.re - l) (1 - u.re - l)) (min (u.im - l) (1 - u.im - l))).trans
      (min_le_right (u.re - l) (1 - u.re - l)); linarith
  · have := (min_le_right (min (u.re - l) (1 - u.re - l)) (min (u.im - l) (1 - u.im - l))).trans
      (min_le_right (u.im - l) (1 - u.im - l)); linarith

/-- **DZZ Prop 5.1, lower bound at the walled box, with rate** (DZZ l. 2333–2340; D129 §4
P-129B): for `0 < λ ≤ 1/20` with `𝕍_{u,2λ} ⊆ 𝕍°`,
`P[min_{x ∈ ∂𝕍_{u,λ}} D̄^{u,2λ}_δ(u,x) < δ^{−χ+ι}] ≤ C(δ^c + e^{−(log δ⁻¹)^{0.7}})`, given DZZ L5.3
at `μIn` and the walled P3.17 at `dgWalls`. -/
theorem hasRate_dzzMuIn_lower_box (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {χ : ℝ} (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    {u : ℂ} (hu : u ∈ openSquare) {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1 / 20)
    (hbox : sqBox u (2 * lam) ⊆ openSquare) {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
      ((lgdMinSet (dzzWall (sqBox u (2 * lam)) (dzzMuIn γ W ω)) δ {u}
        (frontier (sqBox u lam)) : ℕ∞) : ℝ≥0∞)}) := by
  haveI := hW.isProbabilityMeasure
  -- the wall parameter `ξ` and the two boxes inside `𝕍^ξ`
  obtain ⟨m, hm, hm1, hm2, hm3, hm4⟩ := exists_margin_sqBox hlam hbox
  set ξ := min m (1 / 100) with hξdef
  have hξ : 0 < ξ := lt_min hm (by norm_num)
  have hξm : ξ ≤ m := min_le_left _ _
  have hξ1 : ξ ≤ 1 / 100 := min_le_right _ _
  set K := sqBox ptCentre (1 / 10) with hKdef
  have hKξ : K ⊆ dzzVXi ξ := fun z hz =>
    mem_dzzVXi_of_near (a := 1 / 20) (by have := hz.1; simp only [ptCentre] at this; linarith)
      (by have := hz.2; simp only [ptCentre] at this; linarith) (by linarith) hξ.le
  have hBξ : sqBox u (2 * lam) ⊆ dzzVXi ξ := fun z hz => by
    have h1 := abs_le.1 hz.1
    have h2 := abs_le.1 hz.2
    exact mem_dzzVXi_of_near (a := 1 / 2 - ξ) (abs_le.2 ⟨by linarith, by linarith⟩)
      (abs_le.2 ⟨by linarith, by linarith⟩) (by linarith) hξ.le
  -- the similarity `θ(z) = 20λ z + b`, `b = u − 20λ ū`
  set κ := 20 * lam with hκdef
  have hκ : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by linarith
  have ha0 : ((κ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
  have hanorm : ‖((κ : ℝ) : ℂ)‖ = κ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le hγ hγ2 hξ (by linarith) (isClosed_sqBox _ _)
    hKξ ha0 (by rw [hanorm]; exact hκ1)
  set b := u - ((κ : ℝ) : ℂ) * ptCentre with hbdef
  have hθc : simMap ((κ : ℝ) : ℂ) b ptCentre = u := by simp [simMap, hbdef]
  have hθK : simMap ((κ : ℝ) : ℂ) b '' K = sqBox u (2 * lam) := by
    rw [hKdef, simMap_ofReal_image_sqBox hκ, hθc, hκdef]; congr 1; ring
  have hθF : simMap ((κ : ℝ) : ℂ) b '' frontier (sqBox ptCentre (1 / 20)) =
      frontier (sqBox u lam) := by
    rw [simMap_image_frontier ha0, simMap_ofReal_image_sqBox hκ, hθc, hκdef]; congr 2; ring
  have hθs : simMap ((κ : ℝ) : ℂ) b '' {ptCentre} = {u} := by rw [image_singleton, hθc]
  have hcK : ptCentre ∈ K := ⟨by norm_num, by norm_num⟩
  have hF₀K : frontier (sqBox ptCentre (1 / 20)) ⊆ K := fun z hz => by
    have hz' : z ∈ sqBox ptCentre (1 / 20) :=
      (isClosed_sqBox _ _).closure_eq ▸ frontier_subset_closure hz
    exact ⟨hz'.1.trans (by norm_num), hz'.2.trans (by norm_num)⟩
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hbd⟩ := hcpl b (hθK ▸ hBξ)
  haveI := hW₁.isProbabilityMeasure
  -- the exponents
  set ι₁ := ι / 2 with hι₁
  set ι' : ℝ := min (1 / 2) (ι / (2 * |χ| + ι + 1)) with hι'
  have hι'0 : 0 < ι' := lt_min (by norm_num) (div_pos hι (by positivity))
  have hι'h : ι' ≤ 1 / 2 := min_le_left _ _
  have hι'le : ι' * (2 * |χ| + ι + 1) ≤ ι := by
    have := min_le_right (1 / 2) (ι / (2 * |χ| + ι + 1))
    rwa [le_div_iff₀ (by positivity)] at this
  have hexp_le : (1 - ι') * -(χ - ι₁) ≤ -(χ - ι) := by
    nlinarith [mul_nonneg hι'0.le (sub_nonneg.2 (le_abs_self χ)), mul_nonneg hι'0.le hι.le]
  obtain ⟨α, hα, δr, hδr, hR⟩ := alphaHighProb_ref_lower hW hγ hγ2 hL hwalls
    (ι := ι₁) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂s⟩ := exists_Ioo_of_eventually_nhdsGT
    (eventually_rpow_lt (by linarith : (0 : ℝ) < 1 - ι') hδr)
  set T := -2 * Real.log κ / ι' with hT
  refine hasRate_of_le (c₁ := ι' ^ 2 / (4 * C)) (C₁ := C) (c₂ := (1 - ι') * α) (C₂ := 1)
    (by positivity) (mul_pos (by linarith) hα)
    (lt_min (lt_min hδ₂ one_pos) (Real.exp_pos (-(max T 1)))) fun δ hδ => ?_
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ2 : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : δ < Real.exp (-(max T 1)) := hδ.2.trans_le (min_le_right _ _)
  set L := Real.log δ⁻¹ with hLdef
  have hlogδ : Real.log δ = -L := by rw [hLdef, Real.log_inv, neg_neg]
  have hLT : max T 1 < L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp, hlogδ] at this; linarith
  have hL1 : 1 ≤ L := ((le_max_right T 1).trans hLT.le)
  have hlogκ : Real.log κ ≤ 0 := Real.log_nonpos hκ.le hκ1
  have hTL : -2 * Real.log κ < ι' * L := by
    have := (le_max_left T 1).trans_lt hLT
    rw [hT, div_lt_iff₀ hι'0] at this; linarith
  set lam' := ι' * L + Real.log κ with hlam'
  have hlam'2 : ι' * L / 2 ≤ lam' := by rw [hlam']; linarith
  have hlam'0 : 0 ≤ lam' := le_trans (by positivity) hlam'2
  set δ₀ := δ ^ (1 - ι') with hδ₀def
  have hδ₀pos : 0 < δ₀ := Real.rpow_pos_of_pos hδ0 _
  have hpos' := Real.rpow_pos_of_pos hδ0 (-ι')
  have hel : Real.exp lam' = δ ^ (-ι') * κ := by
    rw [hlam', Real.exp_add, hLdef, exp_mul_log_inv hδ0, Real.exp_log hκ]
  have hδ₀eq : δ₀ = δ * δ ^ (-ι') := by
    rw [hδ₀def, sub_eq_add_neg, Real.rpow_add hδ0, Real.rpow_one]
  have hsc : ‖((κ : ℝ) : ℂ)‖ * δ₀ * Real.exp (-lam') = δ := by
    rw [hanorm, Real.exp_neg, hel, hδ₀eq]; field_simp
  have hpow : δ ^ (-(χ - ι)) ≤ δ₀ ^ (-(χ - ι₁)) := by
    rw [hδ₀def, ← Real.rpow_mul hδ0.le]
    exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hexp_le
  -- transfer to the coupling space
  have e1 := prob_lgdMinSet_wall_eq hW hW₂ hγ hγ2 (sqBox u (2 * lam)) δ {u}
    (frontier (sqBox u lam)) {n | ¬ ENNReal.ofReal (δ ^ (-(χ - ι))) ≤ (n : ℝ≥0∞)}
  have e2 := prob_lgdMinSet_wall_eq hW hW₁ hγ hγ2 K δ₀ {ptCentre}
    (frontier (sqBox ptCentre (1 / 20))) {n | ¬ ENNReal.ofReal (δ₀ ^ (-(χ - ι₁))) ≤ (n : ℝ≥0∞)}
  set Bad := {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
      lgdDZZ (dzzWall (simMap ((κ : ℝ) : ℂ) b '' K) (dzzMuIn γ W₂ ω))
          (‖((κ : ℝ) : ℂ)‖ * δ * Real.exp lam') (simMap ((κ : ℝ) : ℂ) b x)
          (simMap ((κ : ℝ) : ℂ) b y) ≤ lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y ∧
        lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y ≤
          lgdDZZ (dzzWall (simMap ((κ : ℝ) : ℂ) b '' K) (dzzMuIn γ W₂ ω))
            (‖((κ : ℝ) : ℂ)‖ * δ * Real.exp (-lam')) (simMap ((κ : ℝ) : ℂ) b x)
            (simMap ((κ : ℝ) : ℂ) b y)} with hBad
  have hBadle : P'.real Bad ≤ C * Real.exp (-lam' ^ 2 / C) := hbd lam' hlam'0
  have he := Real.exp_pos (-(Real.log δ⁻¹) ^ (0.7 : ℝ))
  -- the coupling tail `C e^{−λ'²/C} ≤ C δ^{ι'²/(4C)}`
  have hsq : ι' ^ 2 * L / 4 ≤ lam' ^ 2 := by
    have h1 : (ι' * L / 2) ^ 2 ≤ lam' ^ 2 := pow_le_pow_left₀ (by positivity) hlam'2 2
    have h2 : L ≤ L ^ 2 := le_self_pow₀ hL1 two_ne_zero
    have h3 : ι' ^ 2 * L ≤ ι' ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    calc ι' ^ 2 * L / 4 ≤ ι' ^ 2 * L ^ 2 / 4 := by linarith
      _ = (ι' * L / 2) ^ 2 := by ring
      _ ≤ _ := h1
  have hrp : δ ^ (ι' ^ 2 / (4 * C)) = Real.exp (-((ι' ^ 2 * L / 4) / C)) := by
    rw [Real.rpow_def_of_pos hδ0, hlogδ]; congr 1; field_simp
  have hexpC : Real.exp (-lam' ^ 2 / C) ≤ δ ^ (ι' ^ 2 / (4 * C)) := by
    rw [hrp, neg_div]
    exact Real.exp_le_exp.2 (neg_le_neg (div_le_div_of_nonneg_right hsq hC.le))
  have hB1 : P' Bad ≤ ENNReal.ofReal (C * (δ ^ (ι' ^ 2 / (4 * C)) +
      Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)))) := by
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal (hBadle.trans (mul_le_mul_of_nonneg_left ?_ hC.le))
    linarith
  -- the reference bound at the scale `δ₀ = δ^{1−ι'}`
  have hB2 : P' {ω | lgdMinSet (dzzWall K (dzzMuIn γ W₁ ω)) δ₀ {ptCentre}
        (frontier (sqBox ptCentre (1 / 20))) ∈ {n : ℕ∞ | ¬ ENNReal.ofReal (δ₀ ^ (-(χ - ι₁))) ≤
          (n : ℝ≥0∞)}} ≤ ENNReal.ofReal (1 * (δ ^ ((1 - ι') * α) +
      Real.exp (-(Real.log δ⁻¹) ^ (0.7 : ℝ)))) := by
    rw [← e2]
    refine (hR δ₀ ⟨hδ₀pos, hδ₂s δ ⟨hδ0, hδ2⟩⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hδ₀def, ← Real.rpow_mul hδ0.le]
    linarith
  calc P _ = P {ω | lgdMinSet (dzzWall (sqBox u (2 * lam)) (dzzMuIn γ W ω)) δ {u}
        (frontier (sqBox u lam)) ∈ {n : ℕ∞ | ¬ ENNReal.ofReal (δ ^ (-(χ - ι))) ≤
          (n : ℝ≥0∞)}} := rfl
    _ = _ := e1
    _ ≤ P' (Bad ∪ {ω | lgdMinSet (dzzWall K (dzzMuIn γ W₁ ω)) δ₀ {ptCentre}
        (frontier (sqBox ptCentre (1 / 20))) ∈ {n : ℕ∞ | ¬ ENNReal.ofReal (δ₀ ^ (-(χ - ι₁))) ≤
          (n : ℝ≥0∞)}}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hg : ω ∈ Bad
        · exact Or.inl hg
        · refine Or.inr fun hle => hω ?_
          simp only [hBad, mem_ofPred_eq, not_not] at hg
          have hmin : lgdMinSet (dzzWall K (dzzMuIn γ W₁ ω)) δ₀ {ptCentre}
              (frontier (sqBox ptCentre (1 / 20))) ≤
              lgdMinSet (dzzWall (simMap ((κ : ℝ) : ℂ) b '' K) (dzzMuIn γ W₂ ω)) δ
                (simMap ((κ : ℝ) : ℂ) b '' {ptCentre})
                (simMap ((κ : ℝ) : ℂ) b '' frontier (sqBox ptCentre (1 / 20))) :=
            lgdMinSet_le_image fun x hx z hz => by
              have h := (hg x (by rw [mem_singleton_iff.mp hx]; exact hcK) z (hF₀K hz) δ₀
                hδ₀pos).2
              rwa [hsc] at h
          rw [hθK, hθs, hθF] at hmin
          have hle' : ENNReal.ofReal (δ₀ ^ (-(χ - ι₁))) ≤
              ((lgdMinSet (dzzWall K (dzzMuIn γ W₁ ω)) δ₀ {ptCentre}
                (frontier (sqBox ptCentre (1 / 20))) : ℕ∞) : ℝ≥0∞) := hle
          exact (ENNReal.ofReal_le_ofReal hpow).trans (hle'.trans (ENat.toENNReal_le.2 hmin))
    _ ≤ P' Bad + _ := measure_union_le _ _
    _ ≤ _ := add_le_add hB1 hB2

end DZZ
end LQGMetric
