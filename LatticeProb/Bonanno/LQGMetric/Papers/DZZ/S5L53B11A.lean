/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53B11A at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11

/-!
# DZZ Lemma 5.3 at `μIn` from part 1 only (packet P-53T, DEC-117 §2(d))

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2423): `χ` does not depend on `u, v`. Here:

* `dzz_lem53_pair_tendsto_dzzMuIn`: the per-pair limit `E log D̃_δ(u,v)/log δ⁻¹ → χ(u,v)` from
  `DZZLem53Event` (DZZ L5.3 part 2, l. 2421–2422, via `dzz_lem53_pair_tendsto`);
* **`dzzTildeCouple_of_norm_le`**: `DZZTildeCouple γ u v u' v'` when `|v' − u'| ≤ |v − u|`, from
  the scaling coupling `dzzSimCoupleU_of_norm_le` (lem-scaling-coupling, l. 611–624) for
  `θ = simMap a b`, `a = (v'−u')/(v−u)`, `b = u' − a u` (so `θ(𝕍̃_{u,v}) = 𝕍̃_{u',v'}`), the
  sandwich `D̃_{|a|δe^λ}(u',v') ≤ D̃_δ(u,v) ≤ D̃_{|a|δe^{−λ}}(u',v')` and
  `tendsto_close_of_sandwich` (S5L53B11);
* **`dzzTildeCouple_of_event`**: all pairs (the other order by symmetry of `DZZTildeCouple`);
* **`dzzLem53Exp_dzzMuIn_of_event_only`**: DZZ Lemma 5.3 at `μIn` from `DZZLem53Event` alone.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **DZZ L5.3 part 2 for one pair at `μIn`** (l. 2421–2422): the per-pair limit exists, given
the good event of part 1. -/
theorem dzz_lem53_pair_tendsto_dzzMuIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v)
    (hev : DZZLem53Event P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v) :
    ∃ χ, Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ {u} {v}
      ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  have hP : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hmeas := aemeasurable_wickQArea_ball hW hγ hγ2
  obtain ⟨A, B, hA, hB, hsq⟩ := lintegral_sq_log_tilde_le (P := P) hW hγ hγ2
  obtain ⟨M, hM⟩ := chiDy_tilde_le (P := P) hW hγ hγ2
  refine dzz_lem53_pair_tendsto (θ := 0.01) (by norm_num) (by norm_num) ?_ (hM u hu v hv huv)
    (fun δ hδ => ae_lgd_tilde_lt_top hW hγ hγ2 hu hv huv hδ)
    (fun δ hδ => integrable_log_tilde hW hγ hγ2 hmeas hu hv huv hδ)
  refine dzzLem53Subadd_of_event (A := A) hA hB
    (fun k => integrable_log_tilde hW hγ hγ2 hmeas hu hv huv (by positivity))
    (fun k hk => ?_) hev
  have hδ2 : (2 : ℝ)⁻¹ ^ k ≤ 1 / 2 := by
    rw [one_div]; exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hL : Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ = k * Real.log 2 := by
    rw [inv_pow, inv_inv, Real.log_pow]
  have := hsq u hu v hv huv _ (by positivity) hδ2
  rwa [hL] at this

lemma log_toNat_le_of_le {m n : ℕ∞} (h : m ≤ n) (hn : n < ⊤) (hm : 1 ≤ m) :
    Real.log (m.toNat : ℝ) ≤ Real.log (n.toNat : ℝ) := by
  have h2 : 1 ≤ m.toNat := by
    have := ENat.toNat_le_toNat hm (h.trans_lt hn).ne
    simpa using this
  have h2' : (0 : ℝ) < (m.toNat : ℝ) := by exact_mod_cast h2
  exact Real.log_le_log h2' (by exact_mod_cast ENat.toNat_le_toNat h hn.ne)

/-- `DZZTildeCouple` is symmetric in the two pairs. -/
lemma dzzTildeCouple_symm {γ : ℝ} {u v u' v' : ℂ} (h : DZZTildeCouple γ u v u' v') :
    DZZTildeCouple γ u' v' u v := by
  obtain ⟨Ω', m, P', W₁, W₂, h₁, h₂, hc⟩ := h
  exact ⟨Ω', m, P', W₂, W₁, h₂, h₁, fun ε hε => by simpa only [abs_sub_comm] using hc ε hε⟩

/-- **DZZ L5.3 part 3, the coupling** (l. 2423) for `|v' − u'| ≤ |v − u|`, from the scaling
coupling and the existence of the limit for the pair `(u',v')`. -/
theorem dzzTildeCouple_of_norm_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {u v u' v' : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (hu' : u' ∈ dzzVbar)
    (hv' : v' ∈ dzzVbar) (huv' : u' ≠ v') (hle : ‖v' - u'‖ ≤ ‖v - u‖)
    (hχ : ∃ χ, Tendsto (fun δ => (∫ ω, logMinLGD (dzzWall (tildeBox u' v') (dzzMuIn γ W ω)) δ
      {u'} {v'} ∂P) / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)) :
    DZZTildeCouple γ u v u' v' := by
  obtain ⟨χ, hχ⟩ := hχ
  have hvu : v - u ≠ 0 := sub_ne_zero.2 huv.symm
  set a : ℂ := (v' - u') / (v - u) with ha
  set b : ℂ := u' - a * u with hb
  have ha0 : a ≠ 0 := div_ne_zero (sub_ne_zero.2 huv'.symm) hvu
  have ha1 : ‖a‖ ≤ 1 := by
    rw [ha, norm_div, div_le_one (norm_pos_iff.2 hvu)]; exact hle
  have hθu : simMap a b u = u' := by simp only [simMap, hb]; ring
  have hθv : simMap a b v = v' := by
    simp only [simMap, hb, ha]; field_simp; ring
  have himg : simMap a b '' tildeBox u v = tildeBox u' v' := by
    rw [simMap_image_tildeBox ha0, hθu, hθv]
  obtain ⟨C, hC, hcpl⟩ := dzzSimCoupleU_of_norm_le (ξ := 1 / 4) hγ hγ2 (by norm_num)
    (by norm_num) (isClosed_tildeBox u v) (tildeBox_subset_dzzVXi hu hv huv) ha0 ha1
  obtain ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, hbd⟩ :=
    hcpl b (himg ▸ tildeBox_subset_dzzVXi hu' hv' huv')
  rw [himg] at hbd
  have hP' : IsProbabilityMeasure P' := hW₁.isProbabilityMeasure
  refine ⟨Ω', _, P', W₁, W₂, hW₁, hW₂, fun ε hε => ?_⟩
  -- choice of `λ` for a given failure probability `η`
  have ht : Tendsto (fun lam : ℝ => C * Real.exp (-lam ^ 2 / C)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun lam : ℝ => lam ^ 2 / C) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_div_const hC
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    simpa [neg_div] using h2
  refine tendsto_close_of_sandwich (s := ‖a‖) (χ := χ) (norm_pos_iff.2 ha0)
    (fun δ hδ => integrable_log_tilde hW₂ hγ hγ2 (aemeasurable_wickQArea_ball hW₂ hγ hγ2)
      hu' hv' huv' hδ)
    (fun δ δ' hδ hδδ' => by
      filter_upwards [ae_lgd_tilde_lt_top hW₂ hγ hγ2 hu' hv' huv' hδ] with ω hω
      exact logMinLGD_singleton_anti _ hδ.le hδδ' u' v' hω)
    (hχ.congr fun δ => by rw [integral_logTilde_eq hW hW₂ hγ hγ2]) (fun η hη => ?_) hε
  obtain ⟨lam, hlam, hlam0⟩ := ((ht.eventually (ge_mem_nhds hη)).and
    (eventually_ge_atTop 0)).exists
  refine ⟨lam, fun δ hδ => ?_⟩
  have hδ' : 0 < ‖a‖ * δ * Real.exp (-lam) := by
    have := norm_pos_iff.2 ha0; positivity
  set bad : Set Ω' := {ω | ¬ ∀ x ∈ tildeBox u v, ∀ y ∈ tildeBox u v, ∀ δ : ℝ, 0 < δ →
    lgdDZZ (dzzWall (tildeBox u' v') (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp lam)
        (simMap a b x) (simMap a b y) ≤ lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ x y ∧
      lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W₁ ω)) δ x y ≤
        lgdDZZ (dzzWall (tildeBox u' v') (dzzMuIn γ W₂ ω)) (‖a‖ * δ * Real.exp (-lam))
          (simMap a b x) (simMap a b y)} with hbad
  have hbadP : P' bad ≤ ENNReal.ofReal η := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal ((hbd lam hlam0).trans hlam)
  refine le_trans (measure_mono_ae ?_) hbadP
  filter_upwards [ae_lgd_tilde_lt_top hW₁ hγ hγ2 hu hv huv hδ,
    ae_lgd_tilde_lt_top hW₂ hγ hγ2 hu' hv' huv' hδ'] with ω h1 h2 hω
  by_contra hgood
  apply hω
  have hg : ¬ ¬ _ := hgood
  rw [not_not] at hg
  obtain ⟨hl, hr⟩ := hg u (mem_tildeBox_left u v) v (mem_tildeBox_right u v) δ hδ
  rw [hθu, hθv] at hl hr
  simp only [logMinLGD_singleton]
  exact ⟨log_toNat_le_of_le hl h1 (one_le_lgdDZZ _ _ _ _),
    log_toNat_le_of_le hr h2 (one_le_lgdDZZ _ _ _ _)⟩

/-- **DZZ L5.3 part 3** (l. 2423) for all pairs, from part 1 (`DZZLem53Event`). -/
theorem dzzTildeCouple_of_event (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hev : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Event P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v)
    {u v u' v' : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) (hu' : u' ∈ dzzVbar)
    (hv' : v' ∈ dzzVbar) (huv' : u' ≠ v') : DZZTildeCouple γ u v u' v' := by
  rcases le_total ‖v' - u'‖ ‖v - u‖ with h | h
  · exact dzzTildeCouple_of_norm_le hW hγ hγ2 hu hv huv hu' hv' huv' h
      (dzz_lem53_pair_tendsto_dzzMuIn hW hγ hγ2 hu' hv' huv' (hev u' hu' v' hv' huv'))
  · exact dzzTildeCouple_symm (dzzTildeCouple_of_norm_le hW hγ hγ2 hu' hv' huv' hu hv huv h
      (dzz_lem53_pair_tendsto_dzzMuIn hW hγ hγ2 hu hv huv (hev u hu v hv huv)))

/-- **DZZ Lemma 5.3 at `μIn`** (l. 2292–2297) from part 1 (`DZZLem53Event`, l. 2382–2404)
alone: part 3 (`DZZTildeCouple`, l. 2423) is `dzzTildeCouple_of_event`. -/
theorem dzzLem53Exp_dzzMuIn_of_event_only (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hev : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v →
      DZZLem53Event P (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v) :
    ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ :=
  dzzLem53Exp_dzzMuIn_of_event_couple hW hγ hγ2 hev
    (fun _ hu _ hv huv _ hu' _ hv' huv' =>
      dzzTildeCouple_of_event hW hγ hγ2 hev hu hv huv hu' hv' huv')

end DZZ
end LQGMetric
