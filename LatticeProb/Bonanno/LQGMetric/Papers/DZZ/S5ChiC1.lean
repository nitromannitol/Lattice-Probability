/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5ChiC1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta9D
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W14
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5Lower
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Tail
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Lower

/-!
# D129 packet P-129C, part 1: the small-ball lower tail of `μIn` (P2-CHIC)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 2.12
(`lem-obvious-bounds`), l. 748–755: w.h.p. every ball of LQG mass `≤ δ²` is small. DZZ derive
this from (eq-max-white-noise-process) and (eq-LQG-negative-moment), which are not in Lean.
Following DEC-129 §4 (DV-D129-4) we use instead two results of DZZ §3 already formalized:

* DZZ (eq-Euclidean-Ball-covering), l. 1164–1168 (`l32BallCover_dzzMuIn_eta`, S3Eta9D):
  w.h.p. `D'_{γ,δ'}(u,v) ≤ 4 D_{γ,δ}(u,v)` for all `u, v ∈ 𝕍`, `δ' = δ e^{(log δ⁻¹)^{0.8}}`;
* DZZ Lemma 3.1 at `δ'` (`highProb_cellSize_p32Up`, S3P32W14): w.h.p. all cells of `𝒱_{δ'}` have
  side `≤ δ'^{C_Mc}`, and DZZ (Eq.lowerboundforDprime), l. 1080 (`approxDist_ge_of_dist`, S3L5Lower).

A ball `B(w, s) ⊆ 𝕍` of mass `≤ δ²` contains a ball with rational centre `z` and radius `s/2`,
so `D_δ(z, z + s/4) ≤ 1`, hence `D'_{δ'}(z, z + s/4) ≤ 4`, hence `s/4 ≤ 8 δ'^{C_Mc}`
(`radius_le_of_ballCover`). Since `δ' ≤ δ^{1/2}`, w.h.p. every ball of mass `≤ δ²` has radius
`≤ 32 δ^{C_Mc/2}` (`prob_light_ball_le`), and choosing `δ = √t` gives the polynomial tail
`BallMassLowerTail` (`ballMassLowerTail_dzzMuIn`); the last step is own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- **Deterministic core.** If `D'_{δ'} ≤ 4 D_δ` on `𝕍` and all cells of `𝒱_{δ'}` have side
`≤ σ`, then a ball `B(w, s) ⊆ 𝕍` of `μ`-mass `≤ δ²` has `s ≤ 32 σ`. -/
lemma radius_le_of_ballCover {m : DyBox → ℝ} {δ' δ σ : ℝ} {μ : Measure ℂ}
    (hcov : ∀ u ∈ dzzV, ∀ v ∈ dzzV, approxDist m δ' u v ≤ 4 * lgdDZZ μ δ u v)
    (hcell : ∀ b, IsCell m δ' b → b.side ≤ σ) {w : ℂ} {s : ℝ} (hs : 0 < s)
    (hsub : ball w s ⊆ dzzV) (hm : μ (ball w s) ≤ ENNReal.ofReal (δ ^ 2)) : s ≤ 32 * σ := by
  obtain ⟨q, hq⟩ := exists_ratPt_dist_lt w (show 0 < s / 4 by positivity)
  set z := ratPt q
  have hball : ball z (s / 2) ⊆ ball w s := by
    intro y hy
    rw [mem_ball] at hy ⊢
    linarith [dist_triangle y z w]
  set v : ℂ := z + ((s / 4 : ℝ) : ℂ)
  have hzv : dist v z = s / 4 := by
    simp only [v, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by positivity)
  have hz : z ∈ ball z (s / 2) := mem_ball_self (by positivity)
  have hv : v ∈ ball z (s / 2) := by rw [mem_ball, hzv]; linarith
  have hJ : JoinedIn (ball z (s / 2)) z v :=
    ((convex_ball z (s / 2)).isPathConnected (nonempty_ball.2 (by positivity))).joinedIn z hz v hv
  have hlgd : lgdDZZ μ δ z v ≤ 1 := by
    have : lgdDZZ μ δ z v ≤ ((1 : ℕ) : ℕ∞) := by
      unfold lgdDZZ
      refine iInf₂_le 1 ⟨fun _ => q, fun _ => s / 2, hJ.somePath,
        fun _ => ⟨by positivity, (measure_mono hball).trans hm⟩,
        fun t => ⟨0, hJ.somePath_mem t⟩⟩
    simpa using this
  have h4 : approxDist m δ' z v ≤ ((4 : ℕ) : ℕ∞) := by
    have := hcov z (hsub (hball hz)) v (hsub (hball hv))
    refine this.trans ?_
    calc (4 : ℕ∞) * lgdDZZ μ δ z v ≤ 4 * 1 := by gcongr
      _ = ((4 : ℕ) : ℕ∞) := by norm_num
  by_contra hlt
  push Not at hlt
  have hd : 2 * σ * (4 : ℕ) < dist z v := by rw [dist_comm, hzv]; push_cast; linarith
  have h5 := approxDist_ge_of_dist hcell hd
  have : ((4 : ℕ) : ℕ∞) + 1 ≤ ((4 : ℕ) : ℕ∞) := h5.trans h4
  norm_num at this

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **W.h.p. light balls are small**: there are `c, κ > 0`, `δ₁ ∈ (0, 1)` such that for
`δ < δ₁` and any ball `B(w, s) ⊆ 𝕍` with `s > 32 δ^κ`, `P(μIn(B(w, s)) ≤ δ²) ≤ δ^c`
(`κ = C_Mc/2`). -/
theorem prob_light_ball_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ c κ δ₁ : ℝ, 0 < c ∧ 0 < κ ∧ 0 < δ₁ ∧ δ₁ ≤ 1 ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₁, ∀ w : ℂ, ∀ s : ℝ,
      ball w s ⊆ dzzV → 32 * δ ^ κ < s →
        P {ω | dzzMuIn γ W ω (ball w s) ≤ ENNReal.ofReal (δ ^ 2)} ≤ ENNReal.ofReal (δ ^ c) := by
  obtain ⟨c, hc, δ₀, hδ₀, hG⟩ := (l32BallCover_dzzMuIn_eta hW hγ hγ2).inter
    (highProb_cellSize_p32Up hW hγ hγ2)
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := 1) (b := 0) one_pos
  refine ⟨c, dzzCMc γ / 2, min (min δ₀ δa) 1, hc, by have := dzzCMc_pos γ; positivity,
    lt_min (lt_min hδ₀ hδa) one_pos, min_le_right _ _, fun δ hδ w s hsub hs => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  simp only [lt_min_iff] at hδ1
  refine (measure_mono ?_).trans (hG δ ⟨hδ0, hδ1.1.1⟩)
  intro ω hω
  rw [mem_ofPred_eq] at hω
  intro hgood
  obtain ⟨hcov, hcs⟩ := hgood
  have hsq := p32Up_le_sqrt hδ0 (hasym δ ⟨hδ0, hδ1.1.2⟩).1
  have hσ : (p32Up δ) ^ dzzCMc γ ≤ δ ^ (dzzCMc γ / 2) := by
    calc (p32Up δ) ^ dzzCMc γ ≤ (δ ^ (1 / 2 : ℝ)) ^ dzzCMc γ :=
          Real.rpow_le_rpow (p32Up_pos hδ0).le hsq (dzzCMc_pos γ).le
      _ = δ ^ (dzzCMc γ / 2) := by rw [← Real.rpow_mul hδ0.le]; ring_nf
  have hcell : ∀ b, IsCell (approxLQG γ W ω) (p32Up δ) b → b.side ≤ δ ^ (dzzCMc γ / 2) :=
    fun b hb => ((hcs.2 b hb).2).trans hσ
  have := radius_le_of_ballCover (m := approxLQG γ W ω) (μ := dzzMuIn γ W ω) hcov hcell
    ((by positivity : (0 : ℝ) ≤ 32 * δ ^ (dzzCMc γ / 2)).trans_lt hs) hsub hω
  linarith

/-- **The small-ball lower tail of `μIn`** (DEC-129 §4, P-129C): the input `BallMassLowerTail`
of `dzz_lemma212_lower_whp` holds for `μIn = dzzMuIn γ W` on every compact `K ⊆ 𝕍°`. -/
theorem ballMassLowerTail_dzzMuIn (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {K : Set ℂ} (hK : IsCompact K) (hKV : K ⊆ openSquare) :
    BallMassLowerTail P (dzzMuIn γ W) K := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨c, κ, δ₁, hc, hκ, hδ₁, hδ₁1, hlight⟩ := prob_light_ball_le hW hγ hγ2
  obtain ⟨r, hr, hrK⟩ := hK.exists_thickening_subset_open isOpen_openSquare hKV
  set p := c / 2 with hp
  set A := c / κ with hA
  set C : ℝ := (32 : ℝ) ^ A + (δ₁ ^ 2) ^ (-p) + 1 with hC
  have hp0 : 0 < p := by positivity
  have hA0 : 0 ≤ A := by positivity
  refine ⟨p, A, C, min r 1, hp0, hA0, lt_min hr one_pos, fun w hw s hs hsr t ht => ?_⟩
  have hs1 : s ≤ 1 := hsr.trans (min_le_right _ _)
  have hsub : ball w s ⊆ dzzV := ((ball_subset_thickening hw s).trans
    (thickening_mono (hsr.trans (min_le_left _ _)) K)).trans (hrK.trans openSquare_subset_dzzV)
  have hsA : 1 ≤ s ^ (-A) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs1 (by linarith)
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht p
  have hC1 : 1 ≤ C := by have : 0 ≤ (32 : ℝ) ^ A := by positivity
                         have : 0 ≤ (δ₁ ^ 2) ^ (-p) := by positivity
                         linarith
  set δ := Real.sqrt t with hδ
  have hδ0 : 0 < δ := Real.sqrt_pos.2 ht
  have hδt : δ ^ 2 = t := Real.sq_sqrt ht.le
  have htpδ : t ^ p = δ ^ c := by
    rw [← hδt, ← Real.rpow_natCast, ← Real.rpow_mul hδ0.le, hp]; norm_num; ring_nf
  -- trivial bound by `1`
  have htriv : (1 : ℝ) ≤ C * t ^ p * s ^ (-A) →
      P {ω | dzzMuIn γ W ω (ball w s) ≤ ENNReal.ofReal t} ≤
        ENNReal.ofReal (C * t ^ p * s ^ (-A)) := fun h1 =>
    prob_le_one.trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1)
  by_cases hbig : δ₁ ≤ δ
  · apply htriv
    have h1 : (δ₁ ^ 2) ^ p ≤ t ^ p := Real.rpow_le_rpow (by positivity)
      (by rw [← hδt]; exact pow_le_pow_left₀ hδ₁.le hbig 2) hp0.le
    have h2 : (δ₁ ^ 2) ^ (-p) * (δ₁ ^ 2) ^ p = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    have h3 : (δ₁ ^ 2) ^ (-p) ≤ C := by
      have : 0 ≤ (32 : ℝ) ^ A := by positivity
      linarith
    calc (1 : ℝ) = (δ₁ ^ 2) ^ (-p) * (δ₁ ^ 2) ^ p := h2.symm
      _ ≤ C * t ^ p := mul_le_mul h3 h1 (by positivity) (by linarith)
      _ ≤ C * t ^ p * s ^ (-A) := le_mul_of_one_le_right (by positivity) hsA
  push Not at hbig
  by_cases hsmall : s ≤ 32 * δ ^ κ
  · apply htriv
    -- `s^A ≤ 32^A δ^{κA} = 32^A t^p`
    have hsA' : s ^ A ≤ (32 : ℝ) ^ A * t ^ p := by
      calc s ^ A ≤ (32 * δ ^ κ) ^ A := Real.rpow_le_rpow hs.le hsmall hA0
        _ = (32 : ℝ) ^ A * t ^ p := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hδ0.le, htpδ, hA]
          congr 2; field_simp
    have hsApos : 0 < s ^ A := Real.rpow_pos_of_pos hs A
    have hinv : s ^ (-A) * s ^ A = 1 := by rw [← Real.rpow_add hs]; simp
    have h32 : (32 : ℝ) ^ A ≤ C := by
      have : 0 ≤ (δ₁ ^ 2) ^ (-p) := by positivity
      linarith
    calc (1 : ℝ) = s ^ (-A) * s ^ A := hinv.symm
      _ ≤ s ^ (-A) * ((32 : ℝ) ^ A * t ^ p) := by gcongr
      _ ≤ s ^ (-A) * (C * t ^ p) := by gcongr
      _ = C * t ^ p * s ^ (-A) := by ring
  push Not at hsmall
  have h := hlight δ ⟨hδ0, hbig⟩ w s hsub hsmall
  rw [hδt] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← htpδ]
  calc t ^ p = 1 * t ^ p * 1 := by ring
    _ ≤ C * t ^ p * s ^ (-A) := by gcongr

end DZZ
end LQGMetric
