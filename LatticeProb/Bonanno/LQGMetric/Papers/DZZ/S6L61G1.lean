/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61F2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5D117E1

/-!
# D117 P-61G (3): the short crossings by scaling, one pair (P2-DZZ61G)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2566–2568 ("by (eq-delta_0) and a
similar scaling argument as in the proof of (eq-z-open) we have that with probability tending
to 1 … `D̃_δ(x,y) ≤ δ^{−χ+ι}` for all such `(x,y)`"); the scaling argument is
(eq-scaling-invariance-approximate), l. 2474, and (eq-M-A-upper-bound-bis), l. 2455–2459.

**Why `DZZSimCoupleU` does not suffice.** The neighbouring red points are at distance
`d ≍ δ^κ → 0`, so the similarity `θ` sending the fixed pair `(u₀, v₀)` of (eq-delta_0) to a red pair
has `‖a‖ = 2^{−m}` with `m = m(δ) → ∞`. `DZZSimCoupleU γ ξ K a` (proved for dyadic `a`,
`dzzSimCoupleU_dyadic`) has a constant `C = C(a)` (DZZ lem-scaling-coupling, l. 619:
`C = C(ξ, κ₁, κ₂)`), so it gives nothing uniform in `m`. Moreover the mass scaling is not
`‖a‖²`: the η-field at scale `a` carries a coarse part of variance `≈ log ‖a‖⁻¹` (DZZ's `ĥ`),
so `M_{γ,η}(θB) ≈ ‖a‖^{2+γ²/2} e^{γ ĥ} M_{γ,η}(B)` and the LGD scale factor is
`‖a‖^{1+γ²/4} e^{γ ĥ/2}` with `Var ĥ = O(m + 1)`. DZZ treat this in (eq-z-open) by conditioning
on the coarse field (l. 2455: `M_γ(A) ≤ δ² s_i^{−2} M^{η̌}(A) e^{(log δ⁻¹)^{0.91}}`).

We therefore take the one-sided, scale-uniform coupling `DZZSimCoupleScale γ ξ K` as the input
(exact statement below; DZZ l. 2474–2548 for the fine field, plus the coarse field as above), and
prove from it:

* `prob_lgdWall_eq`: the law of a walled LGD of `dzzMuIn γ W` does not depend on the white
  noise (from `prob_ballMassQ_dzzMuIn_eq`, S5D117E1, and `lgdDZZ_eq_lgdRat`, LGDMeas);
* `prob_tilde_scaled_le`: `P[D^{θK}_δ(θx,θy) > M] ≤ C e^{−λ²/(C(m+1))} + P[D^K_{δ'}(x,y) > M]`
  with `δ' = δ / (‖a‖ e^{λ})` (factor `‖a‖`, DZZ's form; decision D125).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise QuantumZipper

/-- **Scale-uniform similarity coupling, upper half** (input; DZZ (eq-scaling-invariance-
approximate), l. 2474, with the coarse field of (eq-M-A-upper-bound-bis), l. 2455): for
`θ = simMap a b` with `‖a‖ = 2^{−m}`, `θ K ⊆ 𝕍^ξ`, there is a coupling `(W₁, W₂)` such that,
outside an event of probability `≤ C e^{−λ²/(C(m+1))}` (`C` independent of `m` and `b`), for all
`x, y ∈ K` and `δ > 0`: `D^{θK}_{‖a‖ δ e^{λ}}(θx, θy)[W₂] ≤ D^K_δ(x, y)[W₁]` (factor `‖a‖`, DZZ's form l. 2502; decision D125). -/
def DZZSimCoupleScale (γ ξ : ℝ) (K : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : ℂ), ‖a‖ = (1 / 2 : ℝ) ^ m → ∀ b : ℂ,
    simMap a b '' K ⊆ dzzVXi ξ →
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
      IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
        P'.real {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' K) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤
          C * Real.exp (-lam ^ 2 / (C * (m + 1)))

/-- the walled rational ball masses as a function of the rational ball masses -/
def wallMass (K : Set ℂ) (m : ℚ × ℚ → ℚ → ℝ≥0∞) : ℚ × ℚ → ℚ → ℝ≥0∞ :=
  fun c q => m c q + ⊤ * volume (Metric.ball (ratPt c) q ∩ Kᶜ)

lemma ballMassQ_dzzWall (K : Set ℂ) (μ : Measure ℂ) :
    ballMassQ (dzzWall K μ) = wallMass K (ballMassQ μ) := by
  funext c q
  simp only [ballMassQ, wallMass, dzzWall_apply_ball]

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'}

/-- **the law of a walled LGD of `dzzMuIn γ W` does not depend on the white noise** -/
theorem prob_lgdWall_eq {W : WNSpace → Ω → ℝ} {W' : WNSpace → Ω' → ℝ}
    (hW : IsWhiteNoise P W) (hW' : IsWhiteNoise P' W') {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (δ : ℝ) (x y : ℂ) (T : Set ℕ∞) :
    P {ω | lgdDZZ (dzzWall K (dzzMuIn γ W ω)) δ x y ∈ T} =
      P' {ω | lgdDZZ (dzzWall K (dzzMuIn γ W' ω)) δ x y ∈ T} := by
  have hev : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => m c q :=
    fun c q => (measurable_pi_apply q).comp (measurable_pi_apply c)
  have hmeas : Measurable fun m : ℚ × ℚ → ℚ → ℝ≥0∞ => lgdRat (wallMass K m) δ {x} {y} :=
    measurable_lgdRat (m := fun m => wallMass K m) (fun c q => (hev c q).add measurable_const)
      δ {x} {y}
  have h := prob_ballMassQ_dzzMuIn_eq hW hW' hγ hγ2 (hmeas (T.to_countable.measurableSet))
  simp only [mem_preimage] at h
  simp_rw [lgdDZZ_eq_lgdRat, ballMassQ_dzzWall]
  exact h

/-- **one short crossing by scaling** (DZZ l. 2566–2568): through the coupling of
`DZZSimCoupleScale`, `P[D^{θK}_δ(θx,θy) > M] ≤ C e^{−λ²/(C(m+1))} + P[D^K_{δ'}(x,y) > M]`,
`δ' = δ / (‖a‖ e^{λ})` (D125). -/
theorem prob_tilde_scaled_le {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {K : Set ℂ} {C : ℝ} {m : ℕ} {a b : ℂ} (ha : a ≠ 0)
    (hcpl : ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W₁ W₂ : WNSpace → Ω' → ℝ),
      IsWhiteNoise P' W₁ ∧ IsWhiteNoise P' W₂ ∧ ∀ lam : ℝ, 0 ≤ lam →
        P'.real {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' K) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} ≤
          C * Real.exp (-lam ^ 2 / (C * (m + 1))))
    {x y : ℂ} (hx : x ∈ K) (hy : y ∈ K) {lam δ : ℝ} (hlam : 0 ≤ lam) (hδ : 0 < δ) (M : ℝ≥0∞) :
    P {ω | ¬ (lgdDZZ (dzzWall (simMap a b '' K) (dzzMuIn γ W ω)) δ (simMap a b x)
        (simMap a b y) : ℝ≥0∞) ≤ M} ≤
      ENNReal.ofReal (C * Real.exp (-lam ^ 2 / (C * (m + 1)))) +
        P {ω | ¬ (lgdDZZ (dzzWall K (dzzMuIn γ W ω))
          (δ / (‖a‖ * Real.exp lam)) x y : ℝ≥0∞) ≤ M} := by
  obtain ⟨Ω₁, _, P₁, W₁, W₂, hW₁, hW₂, hP⟩ := hcpl
  have := hW₁.isProbabilityMeasure
  set δ' := δ / (‖a‖ * Real.exp lam) with hδ'
  have hpos : 0 < ‖a‖ * Real.exp lam :=
    mul_pos (norm_pos_iff.2 ha) (Real.exp_pos _)
  have hδ'0 : 0 < δ' := div_pos hδ hpos
  have hδeq : ‖a‖ * δ' * Real.exp lam = δ := by
    rw [hδ']; field_simp
  have e1 := prob_lgdWall_eq hW hW₂ hγ hγ2 (simMap a b '' K) δ (simMap a b x) (simMap a b y)
    {n | ¬ (n : ℝ≥0∞) ≤ M}
  have e2 := prob_lgdWall_eq hW hW₁ hγ hγ2 K δ' x y {n | ¬ (n : ℝ≥0∞) ≤ M}
  simp only [mem_ofPred_eq] at e1 e2
  rw [e1, e2]
  set E := {ω | ¬ ∀ x ∈ K, ∀ y ∈ K, ∀ δ : ℝ, 0 < δ →
          lgdDZZ (dzzWall (simMap a b '' K) (dzzMuIn γ W₂ ω))
              (‖a‖ * δ * Real.exp lam) (simMap a b x) (simMap a b y) ≤
            lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ x y} with hE
  calc P₁ {ω | ¬ (lgdDZZ (dzzWall (simMap a b '' K) (dzzMuIn γ W₂ ω)) δ (simMap a b x)
        (simMap a b y) : ℝ≥0∞) ≤ M}
      ≤ P₁ (E ∪ {ω | ¬ (lgdDZZ (dzzWall K (dzzMuIn γ W₁ ω)) δ' x y : ℝ≥0∞) ≤ M}) := by
        refine measure_mono fun ω hω => ?_
        by_cases hg : ω ∈ E
        · exact Or.inl hg
        · refine Or.inr fun hle => hω ?_
          simp only [hE, mem_ofPred_eq, not_not] at hg
          have := hg x hx y hy δ' hδ'0
          rw [hδeq] at this
          exact (ENat.toENNReal_le.2 this).trans hle
    _ ≤ P₁ E + _ := measure_union_le _ _
    _ ≤ _ := by
        gcongr
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal (hP lam hlam)

end DZZ
end LQGMetric
