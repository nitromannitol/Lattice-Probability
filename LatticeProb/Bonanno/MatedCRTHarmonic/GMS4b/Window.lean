/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.Window at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing

/-!
# The local segment `η([τ_z − ε, τ_z + ε])`: hitting times and the two diameter bounds of (4.18)

Source: [18] (4.2) and (4.18), with the corrected argument
of the lower bound (an upper mass bound instead of Lemma 2.8).

* `hitTime_spec`: for a continuous transient curve, `η(τ_z) = z` for every point `z` of its range.
* `diam_locWindow_le_two_mul`: if every segment of time length `≤ ε` meeting `B_ρ(0)` has diameter `≤ D₀`
  ([18] Lemma 2.7, all segments) and `η(t₀) ∈ B_ρ(0)`, then `diam η([t₀ − ε, t₀ + ε]) ≤ 2 D₀`
  (`[18]`: `η([τ_z − ε, τ_z + ε])` is covered by `ε`-segments containing `z`).
* `pow_le_diam_locWindow`: the lower bound of (4.18) from an upper mass bound at one radius `2ε^{p₁}`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- **`η(τ_z) = z`.** For a continuous curve with `η(t) → ∞` as `|t| → ∞`, the infimum (4.2) is attained at every
point of the range. -/
theorem hitTime_spec {c : ℝ → ℂ} (hc : Continuous c) (htrans : Tendsto c (cocompact ℝ) (cocompact ℂ))
    {z : ℂ} (hz : z ∈ range c) : c (hitTime c z) = z := by
  have hS : IsClosed {t : ℝ | c t = z} := isClosed_singleton.preimage hc
  obtain ⟨t, ht⟩ := hz
  have hne : ({t : ℝ | c t = z}).Nonempty := ⟨t, ht⟩
  have hbdd : BddBelow {t : ℝ | c t = z} := by
    have hmem : c ⁻¹' ({z} : Set ℂ)ᶜ ∈ cocompact ℝ := htrans isCompact_singleton.compl_mem_cocompact
    obtain ⟨K, hK, hKsub⟩ := mem_cocompact.mp hmem
    refine hK.bddBelow.mono fun s hs => ?_
    by_contra hsK
    exact hKsub hsK (show c s ∈ ({z} : Set ℂ) from hs)
  exact hS.csInf_mem hne hbdd

/-- The local segment is the union of the two `ε`-segments ending and starting at `t₀`. -/
theorem locWindow_eq_union (ε : ℝ) (c : ℝ → ℂ) {t₀ : ℝ} (hε : 0 ≤ ε) :
    locWindow ε c t₀ = c '' Icc (t₀ - ε) t₀ ∪ c '' Icc t₀ (t₀ + ε) := by
  rw [locWindow, ← image_union, Icc_union_Icc_eq_Icc (by linarith) (by linarith)]

/-- **Upper bound in (4.18).** If every segment of time length `≤ ε` meeting `B_ρ(0)` has diameter at most `D₀`, and
`c(t₀) ∈ B_ρ(0)`, then `diam(c([t₀ − ε, t₀ + ε])) ≤ 2 D₀`. -/
theorem diam_locWindow_le_two_mul {ε ρ D₀ : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (hε : 0 ≤ ε)
    (hseg : ∀ a b : ℝ, b - a ≤ ε → (c '' Icc a b ∩ ball (0 : ℂ) ρ).Nonempty → diam (c '' Icc a b) ≤ D₀)
    (ht₀ : c t₀ ∈ ball (0 : ℂ) ρ) :
    diam (locWindow ε c t₀) ≤ 2 * D₀ := by
  have h1 : diam (c '' Icc (t₀ - ε) t₀) ≤ D₀ :=
    hseg _ _ (by linarith) ⟨c t₀, mem_image_of_mem c ⟨by linarith, le_rfl⟩, ht₀⟩
  have h2 : diam (c '' Icc t₀ (t₀ + ε)) ≤ D₀ :=
    hseg _ _ (by linarith) ⟨c t₀, mem_image_of_mem c ⟨le_rfl, by linarith⟩, ht₀⟩
  rw [locWindow_eq_union ε c hε]
  have h3 := diam_union (s := c '' Icc (t₀ - ε) t₀) (t := c '' Icc t₀ (t₀ + ε))
    (mem_image_of_mem c ⟨by linarith, le_rfl⟩) (mem_image_of_mem c ⟨le_rfl, by linarith⟩)
  rw [dist_self, add_zero] at h3
  linarith

/-- **Lower bound in (4.18)** (from an *upper* mass bound). Let `μ(c([a, b])) = b − a` for `a ≤ b` and
`0 < ε < 1`, `0 < ξ ≤ 1`. If the ball `B_{2ε^{2/ξ}}(c(t₀))` has `μ`-mass at most `(2ε^{2/ξ})^ξ`, then
`diam(c([t₀ − ε, t₀ + ε])) ≥ ε^{2/ξ}`. -/
theorem pow_le_diam_locWindow {ε ξ : ℝ} {c : ℝ → ℂ} (hc : Continuous c) {μ : Measure ℂ}
    (harea : ∀ a b : ℝ, a ≤ b → μ (c '' Icc a b) = ENNReal.ofReal (b - a))
    (hε : 0 < ε) (hε1 : ε < 1) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) {t₀ : ℝ}
    (hmass : μ (ball (c t₀) (2 * ε ^ (2 / ξ))) ≤ ENNReal.ofReal ((2 * ε ^ (2 / ξ)) ^ ξ)) :
    ε ^ (2 / ξ) ≤ diam (locWindow ε c t₀) := by
  by_contra hlt
  rw [not_le] at hlt
  set D := diam (locWindow ε c t₀)
  have hpos : 0 < ε ^ (2 / ξ) := Real.rpow_pos_of_pos hε _
  have hbW : Bornology.IsBounded (locWindow ε c t₀) := (isCompact_Icc.image hc).isBounded
  have hsub : locWindow ε c t₀ ⊆ ball (c t₀) (2 * ε ^ (2 / ξ)) := by
    intro w hw
    rw [mem_ball]
    have := dist_le_diam_of_mem hbW hw
      (mem_image_of_mem c (show t₀ ∈ Icc (t₀ - ε) (t₀ + ε) from ⟨by linarith, by linarith⟩))
    linarith
  have h1 : ENNReal.ofReal (2 * ε) ≤ ENNReal.ofReal ((2 * ε ^ (2 / ξ)) ^ ξ) := by
    calc ENNReal.ofReal (2 * ε) = μ (locWindow ε c t₀) := by
          rw [locWindow, harea _ _ (by linarith)]; congr 1; ring
      _ ≤ μ (ball (c t₀) (2 * ε ^ (2 / ξ))) := measure_mono hsub
      _ ≤ _ := hmass
  have h2 : (2 * ε ^ (2 / ξ)) ^ ξ = 2 ^ ξ * ε ^ (2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hpos.le, ← Real.rpow_mul hε.le, div_mul_cancel₀ _ hξ.ne']
  have h3 : (2 : ℝ) ^ ξ ≤ 2 := by
    calc (2 : ℝ) ^ ξ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hξ1
      _ = 2 := Real.rpow_one 2
  have h4 : 2 ^ ξ * ε ^ (2 : ℝ) < 2 * ε := by
    rw [Real.rpow_two]
    have : ε ^ 2 < ε := by nlinarith
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) ξ]
  rw [h2] at h1
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  linarith

/-- **Exponent bookkeeping for the packing bound.** With `r₀ = D^{1/(1−r)}`, `r = ζ/(4p + ζ)` and `ε^p ≤ D ≤ 1`,
`(4D / r₀)² ≤ 16 ε^{−ζ/2}`. -/
theorem packing_ratio_le {ε D p ζ : ℝ} (hε : 0 < ε) (hp : 0 < p) (hζ : 0 < ζ) (hD : ε ^ p ≤ D) :
    (4 * D / D ^ (1 / (1 - ζ / (4 * p + ζ)))) ^ 2 ≤ 16 * ε ^ (-(ζ / 2)) := by
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hDpos : 0 < D := hεp.trans_le hD
  have h4 : 0 < 4 * p + ζ := by positivity
  have hr1 : 1 - ζ / (4 * p + ζ) = 4 * p / (4 * p + ζ) := by
    rw [eq_div_iff h4.ne', sub_mul, div_mul_cancel₀ _ h4.ne']; ring
  have he : 1 / (1 - ζ / (4 * p + ζ)) = 1 + ζ / (4 * p) := by
    rw [hr1]; field_simp
  rw [he, Real.rpow_add hDpos, Real.rpow_one]
  have hDe : 0 < D ^ (ζ / (4 * p)) := Real.rpow_pos_of_pos hDpos _
  have hsimp : 4 * D / (D * D ^ (ζ / (4 * p))) = 4 * (D ^ (ζ / (4 * p)))⁻¹ := by
    field_simp
  rw [hsimp, mul_pow]
  have hkey : (D ^ (ζ / (4 * p)))⁻¹ ^ 2 ≤ ε ^ (-(ζ / 2)) := by
    rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, ← Real.rpow_neg hDpos.le]
    have hx : -(ζ / (4 * p) * ((2 : ℕ) : ℝ)) ≤ 0 := by
      have : 0 ≤ ζ / (4 * p) * ((2 : ℕ) : ℝ) := by positivity
      linarith
    calc D ^ (-(ζ / (4 * p) * ((2 : ℕ) : ℝ))) ≤ (ε ^ p) ^ (-(ζ / (4 * p) * ((2 : ℕ) : ℝ))) :=
          Real.rpow_le_rpow_of_nonpos hεp hD hx
      _ = ε ^ (-(ζ / 2)) := by
          rw [← Real.rpow_mul hε.le]
          congr 1
          push_cast
          field_simp
          ring
  nlinarith

end MatedCRTHarmonic.GMS4b
