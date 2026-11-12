/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W3

/-!
# D97, packet P-3: `L32BallCover` at the internal measure from (eq-Euclidean-Ball-covering)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1160–1168): with `δ' = δ e^{(log δ⁻¹)^{0.8}}`, "the
key to the proof is the claim that with high probability (eq-Euclidean-Ball-covering) every
Euclidean ball with LQG-measure `≤ δ²` can be covered by 4 cells in `𝒱_{δ'}`. Provided with
(eq-Euclidean-Ball-covering), it is clear that with high probability we have that
`D'_{γ,δ'}(u, v) ≤ 4 D_{γ,δ}(u, v)` for all `u, v ∈ 𝕍`."

For a family `ν` of measures (D97: `ν = M^W`, DZZ's `M_γ^{h̃}` (eq-def-M-eta)) and the internal
measure `dzzWall dzzV (ν ω)` (balls inside `𝕍`):

* `ballCoverEvent γ W ν δ`: the event (eq-Euclidean-Ball-covering), for rational balls inside `𝕍`;
* **`l32BallCover_of_ballCover`**: (eq-Euclidean-Ball-covering) w.h.p. implies
  `L32BallCover P γ W (fun ω => dzzWall dzzV (ν ω))`. The "it is clear" step is
  `approxDist_le_four_mul_lgd` (S3P32W3) on the event of Lemma 3.1 at `δ'` (`dzz_lemma31_bound`:
  every point of `𝕍` lies in a cell, and cells have side `≥ δ'^{C_mc}`, hence bounded level).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- DZZ (eq-Euclidean-Ball-covering) (l. 1162–1164), for rational balls inside `𝕍`: every such
ball of `ν`-mass `≤ δ²` is covered by 4 cells of `𝒱_{δ'}`, `δ' = δ e^{(log δ⁻¹)^{0.8}}`. -/
def ballCoverEvent (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) (δ : ℝ) : Set Ω :=
  {ω | ∀ (c : ℚ × ℚ) (ρ : ℝ), Metric.ball (ratPt c) ρ ⊆ dzzV →
    ν ω (Metric.ball (ratPt c) ρ) ≤ ENNReal.ofReal (δ ^ 2) →
      BallInCells (approxLQG γ W ω) (p32Up δ) (Metric.ball (ratPt c) ρ)}

omit [MeasurableSpace Ω] in
/-- Cells of side `≥ x > 0` have bounded level. -/
lemma exists_level_bound {m : DyBox → ℝ} {δ x : ℝ} (hx : 0 < x)
    (h : ∀ b, IsCell m δ b → x ≤ b.side) : ∃ N₀ : ℕ, ∀ b, IsCell m δ b → b.n ≤ N₀ := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hx (by norm_num : (2 : ℝ)⁻¹ < 1)
  refine ⟨N, fun b hb => ?_⟩
  by_contra hlt
  have h1 : b.side ≤ (2 : ℝ)⁻¹ ^ N := by
    unfold DyBox.side; exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  linarith [h b hb]

omit [MeasurableSpace Ω] in
/-- **DZZ l. 1166–1167** on the event of Lemma 3.1 at `δ'`. -/
theorem ballCover_inter_cellSize_subset (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ)
    {δ : ℝ} (hδ : 0 < p32Up δ) :
    ballCoverEvent γ W ν δ ∩ cellSizeEvent γ W (p32Up δ) ⊆
      {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        approxLGD γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (dzzWall dzzV (ν ω)) δ u v} := by
  rintro ω ⟨hcov, hpart, hside⟩ u hu v hv
  obtain ⟨N₀, hN₀⟩ := exists_level_bound (Real.rpow_pos_of_pos hδ (dzzCmc γ))
    fun b hb => (hside b hb).1
  exact approxDist_le_four_mul_lgd hpart hN₀ (hcov · ·) hu hv

lemma p32Up_pos {δ : ℝ} (hδ : 0 < δ) : 0 < p32Up δ := by unfold p32Up; positivity

/-- `δ' ≤ δ^{1/2}` for small `δ`. -/
lemma p32Up_le_sqrt {δ : ℝ} (hδ0 : 0 < δ)
    (h : Real.log δ⁻¹ ^ (0.8 : ℝ) ≤ Real.log δ⁻¹ / 2) : p32Up δ ≤ δ ^ (1 / 2 : ℝ) := by
  rw [← Real.log_le_log_iff (p32Up_pos hδ0) (Real.rpow_pos_of_pos hδ0 _), p32Up,
    Real.log_mul hδ0.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_rpow hδ0]
  rw [Real.log_inv] at h ⊢
  linarith

/-- **P-3 assembly (DZZ l. 1160–1168)**: (eq-Euclidean-Ball-covering) with high probability gives
`L32BallCover` for the internal measure `dzzWall dzzV ν`. -/
theorem l32BallCover_of_ballCover {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Ω → Measure ℂ}
    (hcov : HighProb P (ballCoverEvent γ W ν)) :
    L32BallCover P γ W (fun ω => dzzWall dzzV (ν ω)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨c₁, hc₁, δ₁, hδ₁, hcv⟩ := hcov
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := 1) (b := 0) one_pos
  set K := l31const γ with hKdef
  have hK : 0 ≤ K := by rw [hKdef]; unfold l31const; positivity
  set c := min c₁ (1 / 2) with hcdef
  have hc : 0 < c := lt_min hc₁ (by norm_num)
  refine ⟨c / 2, by positivity, min (min δa δ₁) (min (1 / 4) ((1 / (1 + K)) ^ (2 / c))),
    by positivity, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδa' : δ < δa := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδq : δ < 1 / 4 := hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδK : δ < (1 / (1 + K)) ^ (2 / c) := hδ.trans_le ((min_le_right _ _).trans
    (min_le_right _ _))
  have hδ1 : δ < 1 := by linarith
  have hs := p32Up_le_sqrt hδ0 (hasym δ ⟨hδ0, hδa'⟩).1
  have hsq : δ ^ (1 / 2 : ℝ) ≤ 1 / 2 := by
    calc δ ^ (1 / 2 : ℝ) ≤ (1 / 4 : ℝ) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hδ0.le hδq.le (by norm_num)
      _ = 1 / 2 := by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  have hp0 := p32Up_pos hδ0
  have p2 := dzz_lemma31_bound hW hγ hγ2 hp0 (hs.trans hsq)
  have p2' : P (cellSizeEvent γ W (p32Up δ))ᶜ ≤ ENNReal.ofReal (K * δ ^ (1 / 2 : ℝ)) :=
    ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).2 p2).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs hK))
  have p1 := hcv δ ⟨hδ0, hδ1'⟩
  have hm1 : δ ^ c₁ ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
  have hm2 : δ ^ (1 / 2 : ℝ) ≤ δ ^ c :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right _ _)
  have hhalf : δ ^ (c / 2) ≤ 1 / (1 + K) := by
    have := Real.rpow_le_rpow hδ0.le hδK.le (by positivity : 0 ≤ c / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / c * (c / 2) = 1 by field_simp,
      Real.rpow_one] at this
  have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
    rw [← Real.rpow_add hδ0]; ring_nf
  calc P {ω | ∀ u ∈ dzzV, ∀ v ∈ dzzV,
        approxLGD γ W (p32Up δ) u v ω ≤ 4 * lgdDZZ (dzzWall dzzV (ν ω)) δ u v}ᶜ
      ≤ P ((ballCoverEvent γ W ν δ)ᶜ ∪ (cellSizeEvent γ W (p32Up δ))ᶜ) := by
        refine measure_mono ?_
        rw [← compl_inter]
        exact compl_subset_compl.2 (ballCover_inter_cellSize_subset γ W ν hp0)
    _ ≤ ENNReal.ofReal (δ ^ c₁) + ENNReal.ofReal (K * δ ^ (1 / 2 : ℝ)) :=
        (measure_union_le _ _).trans (add_le_add p1 p2')
    _ = ENNReal.ofReal (δ ^ c₁ + K * δ ^ (1 / 2 : ℝ)) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h0 : 0 ≤ δ ^ (c / 2) := by positivity
        have h3 : δ ^ c₁ + K * δ ^ (1 / 2 : ℝ) ≤ (1 + K) * δ ^ c := by
          have : K * δ ^ (1 / 2 : ℝ) ≤ K * δ ^ c := mul_le_mul_of_nonneg_left hm2 hK
          linarith
        have h4 : (1 + K) * δ ^ (c / 2) ≤ 1 := by
          rw [le_div_iff₀ (by positivity)] at hhalf; linarith
        rw [hsplit] at h3
        nlinarith

end DZZ
end LQGMetric
