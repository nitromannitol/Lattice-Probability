/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiA2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5ChiA1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11A
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61G1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54G1

/-!
# DZZ Proposition 5.1, upper bound at `μIn` for interior pairs, with rates (D129, P-129A)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, Prop 5.1 (l. 2254–2258), proof of
the upper bound l. 2308–2331: the chain `y_i = u + (i/l)(v − u)`, the scaling coupling
(`lem-scaling-coupling`, l. 611–624) sending a fixed pair of `𝕍̄` to `(y_i, y_{i+1})`, the bound
(Eq.boundfortildeD) from Prop 3.17 + Lemma 5.3 at the fixed pair, and the triangle inequality.
Decision D129 (`decisions/DEC-129.md` §2 (S1)–(S2), §4 P-129A).

* `hasRate_ref_upper`: the reference pair `ū = 1/2 − 1/40 + i/2`, `v̄ = 1/2 + 1/40 + i/2` of `𝕍̄`
  (`|v̄ − ū| = 1/20`): `P[D̃_δ(ū,v̄) > δ^{−χ−ι}] ≤ rate`, from the walled P3.17 at
  `tildeBox ū v̄ ∈ dgWalls` and `hasRate_upper_of_conc` (S5ChiA1);
* `hasRate_tilde_link`: the same for any pair `x ≠ y`, `|y − x| ≤ |v̄ − ū|`, with
  `𝕍̃_{x,y} ⊆ 𝕍^ξ`, through `dzzSimCoupleU_of_norm_le` (template: `dzzTildeCouple_of_norm_le`,
  S5L53B11A) and `prob_tilde_scaled_le` (S6L61G1, law transfer `prob_lgdWall_eq`), with
  `λ = ι' log δ⁻¹` (tail `C e^{−λ²/C} ≤ C δ^{ι'²/C}`) and the scale `δ^{1+ι'}` absorbed in `ι`
  (DZZ use `λ` large and fixed, "with high probability"; **DV-D129-1**);
* **`hasRate_dzzMuIn_upper_interior`**: Prop 5.1's upper bound at `μIn` for `u ≠ v ∈ 𝕍°`.
  The chain length `l` is chosen so that every `𝕍̃_{y_i,y_{i+1}}` lies in `𝕍^ξ` and
  `|y_{i+1} − y_i| ≤ |v̄ − ū|` (**DEVIATIONS DV-D129-2**: DZZ's step `2ξ/√5`, l. 2311, only gives
  `𝕍̃ ⊆ 𝕍`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma dzzVXi_anti_chi {ξ ξ' : ℝ} (h : ξ ≤ ξ') : dzzVXi ξ' ⊆ dzzVXi ξ :=
  fun _ hz => ⟨hz.1, h.trans hz.2⟩

/-! ### The reference pair -/

/-- `ū = 1/2 − 1/40 + i/2` -/
def chiRefU : ℂ := ⟨1 / 2 - 1 / 40, 1 / 2⟩

/-- `v̄ = 1/2 + 1/40 + i/2` -/
def chiRefV : ℂ := ⟨1 / 2 + 1 / 40, 1 / 2⟩

lemma chiRefU_mem : chiRefU ∈ dzzVbar := by
  simp only [dzzVbar, sqBox, mem_ofPred_eq, chiRefU]; norm_num

lemma chiRefV_mem : chiRefV ∈ dzzVbar := by
  simp only [dzzVbar, sqBox, mem_ofPred_eq, chiRefV]; norm_num

lemma chiRef_sub : chiRefV - chiRefU = ((1 / 20 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [chiRefU, chiRefV] <;> norm_num

lemma chiRef_norm : ‖chiRefV - chiRefU‖ = 1 / 20 := by
  rw [chiRef_sub, Complex.norm_real, Real.norm_eq_abs]; norm_num

lemma chiRef_ne : chiRefU ≠ chiRefV := by
  intro h
  have := chiRef_norm
  rw [h, sub_self, norm_zero] at this
  norm_num at this

lemma chiRef_dist : dist chiRefU chiRefV = 1 / 20 := by
  rw [dist_eq_norm, norm_sub_rev, chiRef_norm]

/-- **(Eq.boundfortildeD) at the reference pair, rate form** (DZZ l. 2318–2325): P3.17 at the
wall `𝕍̃_{ū,v̄} ∈ dgWalls` and L5.3. -/
theorem hasRate_ref_upper (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    (hL : DZZLem53Exp P (dzzMuIn γ W) χ)
    (hwalls : ∃ ξ₂ : ℝ, 0 < ξ₂ ∧ ∀ ξ, 0 < ξ → ξ < ξ₂ → DZZProp317Walls P (dzzMuIn γ W) ξ dgWalls)
    {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ((lgdDZZ (dzzWall (tildeBox chiRefU chiRefV) (dzzMuIn γ W ω)) δ
      chiRefU chiRefV : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(χ + ι)))}) := by
  obtain ⟨ξ₂, hξ₂, hw⟩ := hwalls
  set ξ := min (ξ₂ / 2) (1 / 40) with hξdef
  have hξ : 0 < ξ := lt_min (by linarith) (by norm_num)
  have hξ40 : ξ ≤ 1 / 40 := min_le_right _ _
  have hξlt : ξ < ξ₂ := (min_le_left _ _).trans_lt (by linarith)
  have h317 := dzzProp317In_tildeBox_of_walls (hw ξ hξ hξlt) chiRefU_mem chiRefV_mem chiRef_ne
  have hU : chiRefU ∈ dzzVXi ξ := dzzVXi_anti_chi (hξ40.trans (by norm_num))
    (tildeBox_subset_dzzVXi chiRefU_mem chiRefV_mem chiRef_ne (mem_tildeBox_left _ _))
  have hV : chiRefV ∈ dzzVXi ξ := dzzVXi_anti_chi (hξ40.trans (by norm_num))
    (tildeBox_subset_dzzVXi chiRefU_mem chiRefV_mem chiRef_ne (mem_tildeBox_right _ _))
  have hAB := isXiAdmissible_const_singleton hU hV (by rw [chiRef_dist]; linarith)
  have h2ξ : 2 * ξ ≤ dist chiRefU chiRefV := by rw [chiRef_dist]; linarith
  have := hasRate_upper_of_conc
    (μ := fun ω => dzzWall (tildeBox chiRefU chiRefV) (dzzMuIn γ W ω)) h317 hAB
    (fun _ _ => ⟨singleton_subset_iff.2 (mem_kXi_tildeBox_left chiRef_ne h2ξ),
      singleton_subset_iff.2 (mem_kXi_tildeBox_right chiRef_ne h2ξ)⟩)
    (hL _ chiRefU_mem _ chiRefV_mem chiRef_ne)
    (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [ae_lgd_tilde_lt_top hW hγ hγ2 chiRefU_mem chiRefV_mem chiRef_ne hδ]
        with ω hω
      simpa only [lgdMinSet_singleton] using hω) hι
  simpa only [lgdMinSet_singleton] using this

/-! ### One link of the chain, by the scaling coupling -/

/-- **One link** (DZZ l. 2318–2325): for `x ≠ y` with `|y − x| ≤ |v₀ − u₀|` and `𝕍̃_{x,y} ⊆ 𝕍^ξ`,
the rate bound at `(u₀, v₀)` transfers to `(x, y)` through the scaling coupling. -/
theorem hasRate_tilde_link (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {χ : ℝ}
    {u₀ v₀ x y : ℂ} (hu₀ : u₀ ∈ dzzVbar) (hv₀ : v₀ ∈ dzzVbar) (hne : u₀ ≠ v₀) (hxy : x ≠ y)
    (hle : ‖y - x‖ ≤ ‖v₀ - u₀‖) {ξ : ℝ} (hξ : 0 < ξ) (hξ4 : ξ ≤ 1 / 4)
    (hbox : tildeBox x y ⊆ dzzVXi ξ)
    (href : ∀ ι : ℝ, 0 < ι → HasRate P (fun δ => {ω |
      ((lgdDZZ (dzzWall (tildeBox u₀ v₀) (dzzMuIn γ W ω)) δ u₀ v₀ : ℕ∞) : ℝ≥0∞) ≤
        ENNReal.ofReal (δ ^ (-(χ + ι)))}))
    {ι : ℝ} (hι : 0 < ι) :
    HasRate P (fun δ => {ω | ((lgdDZZ (dzzWall (tildeBox x y) (dzzMuIn γ W ω)) δ x y : ℕ∞) :
      ℝ≥0∞) ≤ ENNReal.ofReal (δ ^ (-(χ + ι)))}) := by
  have hvu : v₀ - u₀ ≠ 0 := sub_ne_zero.2 hne.symm
  set a : ℂ := (y - x) / (v₀ - u₀) with ha
  set b : ℂ := x - a * u₀ with hb
  have ha0 : a ≠ 0 := div_ne_zero (sub_ne_zero.2 hxy.symm) hvu
  have ha1 : ‖a‖ ≤ 1 := by
    rw [ha, norm_div, div_le_one (norm_pos_iff.2 hvu)]; exact hle
  have hθu : simMap a b u₀ = x := by simp only [simMap, hb]; ring
  have hθv : simMap a b v₀ = y := by
    simp only [simMap, hb, ha]; field_simp; ring
  have himg : simMap a b '' tildeBox u₀ v₀ = tildeBox x y := by
    rw [simMap_image_tildeBox ha0, hθu, hθv]
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le (ξ := ξ) hγ hγ2 hξ (by linarith)
    (isClosed_tildeBox u₀ v₀)
    ((tildeBox_subset_dzzVXi hu₀ hv₀ hne).trans (dzzVXi_anti_chi hξ4)) ha0 ha1
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hbd⟩ := hcpl b (himg ▸ hbox)
  have hP' : IsProbabilityMeasure P' := hW₁.isProbabilityMeasure
  have hone : ∀ lam : ℝ, 0 ≤ lam →
      P'.real {ω | ¬ ∀ x ∈ tildeBox u₀ v₀, ∀ y ∈ tildeBox u₀ v₀, ∀ δ : ℝ, 0 < δ →
        lgdDZZ (dzzWall (simMap a b '' tildeBox u₀ v₀) (dzzMuIn γ W₂ ω))
            (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
          lgdDZZ (dzzWall (tildeBox u₀ v₀) (dzzMuIn γ W₁ ω)) δ x y} ≤
        C * Real.exp (-lam ^ 2 / (C * (((0 : ℕ) : ℝ) + 1))) := by
    intro lam hlam
    rw [Nat.cast_zero, zero_add, mul_one]
    refine le_trans (measureReal_mono fun ω hω => ?_) (hbd lam hlam)
    exact fun h => hω fun x hx y hy δ hδ => (h x hx y hy δ hδ).1
  -- the exponents
  set ι₁ := ι / 2 with hι₁
  set ι' : ℝ := min 1 (ι / (2 * |χ| + ι + 1)) with hι'
  have hι'0 : 0 < ι' := lt_min one_pos (div_pos hι (by positivity))
  have hι'le : ι' * (2 * |χ| + ι + 1) ≤ ι := by
    have := min_le_right 1 (ι / (2 * |χ| + ι + 1))
    rwa [le_div_iff₀ (by positivity)] at this
  have hexp_le : -(χ + ι) ≤ (1 + ι') * -(χ + ι₁) := by
    nlinarith [mul_nonneg hι'0.le (sub_nonneg.2 (le_abs_self χ))]
  obtain ⟨c₂, C₂, δ₂, hc₂, hδ₂, hR⟩ :=
    (href ι₁ (by positivity)).comp_rpow (p := 1 + ι') (by linarith)
  refine hasRate_of_le (c₁ := ι' ^ 2 / C) (C₁ := C) (C₂ := C₂) (c₂ := c₂) (by positivity) hc₂
    (lt_min (lt_min hδ₂ one_pos) (Real.exp_pos (-1))) fun δ hδ => ?_
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ < 1 := hδ.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδ2 : δ < δ₂ := hδ.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδe : δ < Real.exp (-1) := hδ.2.trans_le (min_le_right _ _)
  set L := Real.log δ⁻¹ with hL
  have hL1 : 1 ≤ L := by
    have := Real.log_lt_log hδ0 hδe
    rw [Real.log_exp] at this
    rw [hL, Real.log_inv]; linarith
  set lam := ι' * L with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have key := prob_tilde_scaled_le hW hγ hγ2 (K := tildeBox u₀ v₀) (m := 0) ha0
    ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hone⟩ (mem_tildeBox_left u₀ v₀) (mem_tildeBox_right u₀ v₀)
    hlam0 hδ0 (ENNReal.ofReal (δ ^ (-(χ + ι))))
  rw [himg, hθu, hθv] at key
  refine key.trans (add_le_add ?_ ?_)
  · -- the coupling tail `C e^{−λ²/C} ≤ C δ^{ι'²/C}`
    rw [Nat.cast_zero, zero_add, mul_one]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le)
    have hrp : δ ^ (ι' ^ 2 / C) = Real.exp (-(ι' ^ 2 / C * L)) := by
      rw [Real.rpow_def_of_pos hδ0, hL, Real.log_inv]; ring_nf
    have h1 : ι' ^ 2 / C * L ≤ lam ^ 2 / C := by
      rw [hlam, mul_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hC]
      have : L ≤ L ^ 2 := by nlinarith
      nlinarith [sq_nonneg ι']
    have h2 : Real.exp (-lam ^ 2 / C) ≤ δ ^ (ι' ^ 2 / C) := by
      rw [hrp, neg_div]; exact Real.exp_le_exp.2 (neg_le_neg h1)
    have := Real.exp_pos (-(Real.log δ⁻¹) ^ (0.7 : ℝ))
    linarith
  · -- the reference bound at the scale `δ^{1+ι'}`
    refine le_trans (measure_mono ?_) ((hR δ ⟨hδ0, hδ2⟩).trans_eq rfl)
    intro ω hω hgood
    apply hω
    have hs0 : 0 < δ ^ (1 + ι') := Real.rpow_pos_of_pos hδ0 _
    have hel : Real.exp lam = δ ^ (-ι') := by rw [hlam, hL, exp_mul_log_inv hδ0]
    have hsle : δ ^ (1 + ι') ≤ δ / (‖a‖ * Real.exp lam) := by
      rw [le_div_iff₀ (mul_pos (norm_pos_iff.2 ha0) (Real.exp_pos _)), hel]
      have hm : δ ^ (1 + ι') * δ ^ (-ι') = δ := by
        rw [← Real.rpow_add hδ0]; simp
      have : δ ^ (1 + ι') * (‖a‖ * δ ^ (-ι')) = ‖a‖ * δ := by
        calc _ = ‖a‖ * (δ ^ (1 + ι') * δ ^ (-ι')) := by ring
          _ = ‖a‖ * δ := by rw [hm]
      rw [this]; nlinarith
    have hpow : (δ ^ (1 + ι')) ^ (-(χ + ι₁)) ≤ δ ^ (-(χ + ι)) := by
      rw [← Real.rpow_mul hδ0.le]
      exact Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hexp_le
    exact (ENat.toENNReal_le.2 (lgdDZZ_antitone _ hs0.le hsle u₀ v₀)).trans
      (hgood.trans (ENNReal.ofReal_le_ofReal hpow))

end DZZ
end LQGMetric
