import LatticeProb.Bonanno.LQGMetric.Dimension.LGDScale

/-!
# Invariance of the Liouville graph distance exponent under similarities and constant factors

For the Liouville graph distance `D_δ(μ)(u, v)` of Ding-Zeitouni-Zhang (the least number of balls of
`μ`-mass at most `δ²` covering a path from `u` to `v`):

* `LatticeProb.LQG.lgdDZZ_ofReal_smul`: `D_δ(c μ) = D_{δ/√c}(μ)` for `c > 0`;
* `LatticeProb.LQG.tendsto_lgdRatio_comp_mul`: a fixed positive change of the scale `δ ↦ κ δ`
  does not change the exponent `lim log D_δ / log δ⁻¹`;
* `LatticeProb.LQG.tendsto_lgdRatio_of_map_simMap_eq_smul`: if `φ_* ν = c μ` for a similarity
  `φ z = a z + b` and `c > 0`, the exponent of `ν` between `u` and `v` is that of `μ` between
  `φ u` and `φ v`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

/-- **A constant factor rescales `δ`.** For `c > 0`, `D_δ(c μ)(u, v) = D_{δ/√c}(μ)(u, v)`. -/
theorem _root_.LatticeProb.LQG.lgdDZZ_ofReal_smul (μ : Measure ℂ) {c : ℝ} (hc : 0 < c) (δ : ℝ)
    (u v : ℂ) : lgdDZZ (ENNReal.ofReal c • μ) δ u v = lgdDZZ μ (δ / Real.sqrt c) u v := by
  simp only [lgdDZZ, Measure.smul_apply, smul_eq_mul, smul_mass_le_iff hc]

/-- **A fixed change of scale does not change the exponent.** If
`log g(δ) / log δ⁻¹ → χ` as `δ ↓ 0`, then also `log g(δ κ) / log δ⁻¹ → χ` for every `κ > 0`. -/
theorem _root_.LatticeProb.LQG.tendsto_lgdRatio_comp_mul {g : ℝ → ℕ∞} {χ κ : ℝ} (hκ : 0 < κ)
    (h : Tendsto (fun δ : ℝ => Real.log (g δ).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)) :
    Tendsto (fun δ : ℝ => Real.log (g (δ * κ)).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  have h1 : Tendsto (fun δ : ℝ => δ * κ) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact ((continuous_id.mul continuous_const).tendsto' 0 0 (zero_mul κ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ) using mul_pos hδ hκ
  have hlog : Tendsto (fun δ : ℝ => Real.log δ⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun δ : ℝ => 1 - Real.log κ / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hlog)
  have h3 := (h.comp h1).mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  have hpos : (0 : ℝ) < min 1 κ⁻¹ := lt_min one_pos (inv_pos.2 hκ)
  filter_upwards [Ioo_mem_nhdsGT hpos] with δ ⟨hδ0, hδ1⟩
  have hδ1' : δ < 1 := hδ1.trans_le (min_le_left _ _)
  have hδκ : δ * κ < 1 := by
    calc δ * κ < κ⁻¹ * κ := by gcongr; exact hδ1.trans_le (min_le_right _ _)
      _ = 1 := inv_mul_cancel₀ hκ.ne'
  have hL : 0 < Real.log δ⁻¹ := Real.log_pos ((one_lt_inv₀ hδ0).2 hδ1')
  have hL' : 0 < Real.log (δ * κ)⁻¹ := Real.log_pos ((one_lt_inv₀ (mul_pos hδ0 hκ)).2 hδκ)
  have e : Real.log (δ * κ)⁻¹ = Real.log δ⁻¹ - Real.log κ := by
    rw [Real.log_inv, Real.log_inv, Real.log_mul hδ0.ne' hκ.ne']; ring
  simp only [Function.comp_apply]
  rw [e] at hL' ⊢
  rw [one_sub_div hL.ne', div_mul_div_comm, mul_comm (Real.log δ⁻¹ - Real.log κ) (Real.log δ⁻¹),
    mul_div_mul_right _ _ hL'.ne']

/-- **The exponent is invariant under similarities and constant factors.** If `φ_* ν = c μ` for
the similarity `φ z = a z + b` (`a ≠ 0`) and a constant `c > 0`, and
`log D_δ(μ)(φ u, φ v) / log δ⁻¹ → χ` as `δ ↓ 0`, then `log D_δ(ν)(u, v) / log δ⁻¹ → χ`. -/
theorem _root_.LatticeProb.LQG.tendsto_lgdRatio_of_map_simMap_eq_smul {ν μ : Measure ℂ} {a : ℂ}
    (ha : a ≠ 0) (b : ℂ) {c : ℝ} (hc : 0 < c) (hνμ : ν.map (simMap a b) = ENNReal.ofReal c • μ)
    {u v : ℂ} {χ : ℝ}
    (h : Tendsto (fun δ : ℝ => Real.log (lgdDZZ μ δ (simMap a b u) (simMap a b v)).toNat /
      Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)) :
    Tendsto (fun δ : ℝ => Real.log (lgdDZZ ν δ u v).toNat / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ) := by
  have e : ∀ δ : ℝ, lgdDZZ ν δ u v =
      lgdDZZ μ (δ * (Real.sqrt c)⁻¹) (simMap a b u) (simMap a b v) := fun δ => by
    rw [← lgdDZZ_map_similarity ha b ν δ u v, hνμ, LatticeProb.LQG.lgdDZZ_ofReal_smul μ hc,
      div_eq_mul_inv]
  have h' := LatticeProb.LQG.tendsto_lgdRatio_comp_mul
    (g := fun δ => lgdDZZ μ δ (simMap a b u) (simMap a b v)) (inv_pos.2 (Real.sqrt_pos.2 hc)) h
  refine h'.congr fun δ => ?_
  rw [e δ]

end LQGMetric
