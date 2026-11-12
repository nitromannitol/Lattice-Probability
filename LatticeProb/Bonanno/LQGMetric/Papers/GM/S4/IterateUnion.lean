/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ConditionalGrid
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# GM Theorem 4.2: the union bound over grid pairs

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, proof of Theorem 4.2
(l. 2437–2446): "truncate on `ℰ_𝕣`, then take a union bound over all pairs
`𝕫, 𝕨 ∈ (ε^q𝕣ℤ²) ∩ (𝕣U)` with `|𝕫 − 𝕨| ≥ 4ℓ𝕣`", the number of pairs being polynomial in `ε`
(implicit in the paper).

* `gm_grid_card_le`: points of the grid `sℤ²` in `B_L(0)` number at most `4(L + 2s)²/s²`
  (own elementary proof by disjoint grid cells, `gm_card_mul_le_volume`); with `s = ε^q𝕣`,
  `L = ρ𝕣`, this is `≤ 4(ρ+2)² ε^{-2q}` uniformly in `𝕣`.
* `gm_mem_gridPts_of_T42`: the grid points of `T4_2` (`(s : ℂ)(m₁ + m₂ i)`) lie in `gridPts s`.
* `gm_T4_2_union`: `P[(⋂_{x∈S} Good_x)ᶜ] ≤ P[ℰᶜ] + #S · max_x P[ℰ ∩ Good_xᶜ]`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the grid points of `T4_2`, `(s : ℂ)(m₁ + m₂ i)`, are the points of `gridPts s` -/
theorem gm_mem_gridPts_of_T42 {s : ℝ} {a : ℂ} (ha : ∃ m : ℤ × ℤ, a = (s : ℂ) * (m.1 + m.2 * Complex.I)) :
    a ∈ gridPts s := by
  obtain ⟨m, rfl⟩ := ha
  refine ⟨m.1, m.2, ?_⟩
  apply Complex.ext <;> simp <;> ring

/-- **Grid count** (own elementary proof): `#(sℤ² ∩ B_L(0)) · s² ≤ 4(L + 2s)²` -/
theorem gm_grid_card_le {s L : ℝ} (hs : 0 < s) (hL : 0 ≤ L) (Zs : Finset ℂ)
    (hZ : ∀ z ∈ Zs, z ∈ gridPts s ∧ ‖z‖ < L) :
    (Zs.card : ℝ) * s ^ 2 ≤ 4 * (L + 2 * s) ^ 2 := by
  have hX : ∀ z ∈ Zs, gridCell z s ⊆ ball (0 : ℂ) (L + 2 * s) := by
    intro z hz
    refine (gm_gridCell_subset_ball hs.le le_rfl (by linarith)).trans ?_
    intro x hx
    rw [mem_ball, dist_zero_right]
    rw [mem_ball, dist_eq_norm] at hx
    have := norm_le_norm_add_norm_sub' x z
    have := (hZ z hz).2
    linarith
  have h := gm_card_mul_le_volume hs.le le_rfl Zs (fun z hz => (hZ z hz).1) hX
  rw [Complex.volume_ball] at h
  have hpi : (NNReal.pi : ℝ≥0∞) ≤ ENNReal.ofReal 4 := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
    exact ENNReal.ofReal_le_ofReal Real.pi_le_four
  have h2 : (Zs.card : ℝ≥0∞) * ENNReal.ofReal (s ^ 2) ≤
      ENNReal.ofReal (4 * (L + 2 * s) ^ 2) := by
    refine h.trans ?_
    rw [ENNReal.ofReal_mul (by norm_num), mul_comm (ENNReal.ofReal 4),
      ENNReal.ofReal_pow (by linarith)]
    gcongr
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)] at h2
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **The union bound of the proof of GM Theorem 4.2** (l. 2441–2444) -/
theorem gm_T4_2_union {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Reg : Set Ω) (S : Finset ι) (Good : ι → Set Ω) {δ₀ δ : ℝ}
    (hReg : P.real Regᶜ ≤ δ₀) (hpair : ∀ x ∈ S, P.real (Reg ∩ (Good x)ᶜ) ≤ δ) :
    P.real {ω | ∀ x ∈ S, ω ∈ Good x}ᶜ ≤ δ₀ + S.card * δ := by
  have hsub : {ω | ∀ x ∈ S, ω ∈ Good x}ᶜ ⊆ Regᶜ ∪ ⋃ x ∈ S, Reg ∩ (Good x)ᶜ := by
    intro ω hω
    simp only [mem_compl_iff, mem_ofPred_eq, not_forall] at hω
    obtain ⟨x, hx, hn⟩ := hω
    by_cases hR : ω ∈ Reg
    · exact Or.inr (mem_biUnion hx ⟨hR, hn⟩)
    · exact Or.inl hR
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  have := (measureReal_biUnion_finset_le (μ := P) S (fun x => Reg ∩ (Good x)ᶜ)).trans
    (Finset.sum_le_sum hpair)
  simp only [Finset.sum_const, nsmul_eq_mul] at this
  linarith

end LQGMetric.GM
