/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SAsymptotic at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Lemma27

/-!
# Arbitrarily strong small-window failure exponent

The exponent in [18] Lemma 2.7 diverges as its diameter exponent tends to
zero. This is the quantitative choice used for a superpolynomially good
window containment event at any fixed interior disk.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology Set Metric

namespace MatedCRTHarmonic.GMS4b

/-- The failure exponent of [18] Lemma 2.7 tends to infinity as its
diameter exponent tends to zero from above. -/
theorem l46s_lemma27Exponent_tendsto_atTop {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun q : ℝ => GMSLemma27.lemma27Exponent q γ)
      (𝓝[>] (0 : ℝ)) atTop := by
  let c : ℝ := 2 + γ ^ 2 / 2
  let A : ℝ := 1 / (2 * γ ^ 2)
  let B : ℝ := c ^ 2 / (2 * γ ^ 2) - 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hexp (q : ℝ) (hq : q ≠ 0) :
      GMSLemma27.lemma27Exponent q γ = A * q⁻¹ + q * B - c / γ ^ 2 := by
    dsimp [GMSLemma27.lemma27Exponent, A, B, c]
    field_simp
    ring
  have hmain : Tendsto (fun q : ℝ => A * q⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_const_mul_atTop_of_pos hA).2 tendsto_inv_nhdsGT_zero
  have hq0 : Tendsto (fun q : ℝ => q * B) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun q : ℝ => q) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.mul_const B
  refine tendsto_atTop.2 ?_
  intro b
  have hlarge := hmain.eventually (eventually_ge_atTop (b + |c / γ ^ 2| + 1))
  have hsmall := hq0.eventually (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hlarge, hsmall, self_mem_nhdsWithin] with q hlarge hsmall hq
  have hqne : q ≠ 0 := (show 0 < q from hq).ne'
  rw [hexp q hqne]
  have hB : -1 < q * B ∧ q * B < 1 := hsmall
  have hc : c / γ ^ 2 ≤ |c / γ ^ 2| := le_abs_self _
  linarith

/-- For every requested polynomial failure power, Lemma 2.7 has an
admissible diameter exponent with a larger failure exponent. -/
theorem l46s_exists_lemma27_q_for_power {γ : ℝ} (hγ : 0 < γ)
    (s : ℝ) :
    ∃ q : ℝ, 0 < q ∧ q < 2 / (2 + γ) ^ 2 ∧
      s < GMSLemma27.lemma27Exponent q γ := by
  have hbound : 0 < 2 / (2 + γ) ^ 2 := by positivity
  have hlarge := (l46s_lemma27Exponent_tendsto_atTop hγ).eventually
    (eventually_gt_atTop s)
  have hsmall : ∀ᶠ q in 𝓝[>] (0 : ℝ), q < 2 / (2 + γ) ^ 2 :=
    (gt_mem_nhds hbound).filter_mono nhdsWithin_le_nhds
  obtain ⟨q, ⟨hlarge, hsmall⟩, hq⟩ :=
    ((hlarge.and hsmall).and self_mem_nhdsWithin).exists
  exact ⟨q, hq, hsmall, hlarge⟩

end MatedCRTHarmonic.GMS4b
