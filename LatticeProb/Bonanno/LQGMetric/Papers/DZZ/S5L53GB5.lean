/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53GB5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GB4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53K1

/-!
# DZZ Lemma 5.3, node 3: G-J3 for the proxy mass maps (P2-DZZ53GB)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2433–2514; DEC-131 §9, DEC-131-IF §3 G-M, G-J3.
`l53_box_desirable_prob_proxy`: `l53_box_desirable_prob` (S5L53GB4) for the proxies
`proxyMass W γ m c_B 𝕍_{c_z,5t}` (S5L53K1), which is `l53MB W γ k b B κ ℓ` (S5L53GA2) by
definition (`m = n_b + κ + ℓ`, `c_B = 2^{-2k} s_b^{-2} e^{L^{0.91}}`); the locality is
`l53_proxyMass_local`. The per-site bound `hε` is then `l53_bad_cond_proxy` (S5L53Y4).
`l53_box_rhs_le`: the Peierls bound in closed form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **G-J3 for the proxies** `M z = proxyMass W γ m c_B 𝕍_{c_z, 5t}` (the form of `l53MB`,
S5L53GA2, with `m = n_b + κ + ℓ`): the locality `hloc` of `l53_box_desirable_prob` holds by
`l53_proxyMass_local` (S5L53K1) when `2^{-m} ≤ s` and `(2^{-m} log 2^m + 2^{-m})/2 < t`. -/
theorem l53_box_desirable_prob_proxy (hW : IsWhiteNoise P W) (C : DyBox) {κ N n : ℕ}
    (hK : 2 ^ κ = 2 * N + 2) (hn : 1 ≤ n) (hnN : n ≤ N)
    (γ : ℝ) (m : ℕ) (cB : ℝ≥0∞) {s : ℝ} (hms : (2 : ℝ)⁻¹ ^ m ≤ s)
    (hmt : ((2 : ℝ)⁻¹ ^ m * Real.log ((2 : ℝ)⁻¹ ^ m)⁻¹ + (2 : ℝ)⁻¹ ^ m) / 2 <
      (2 : ℝ)⁻¹ ^ (C.n + κ))
    {R₀ : Set (ℝ × ℂ)} {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀) (h0 : P A₀ ≠ 0)
    (hR₀ : ∀ z ∈ l53EvenBox N, Disjoint R₀
      (Ioo 0 (s ^ 2) ×ˢ sqBox (l53Sub C κ N z).center (7 * (l53Sub C κ N z).side)))
    (δ T : ℝ) {Kt : ℝ≥0∞} (hK8 : 8 ≤ Kt)
    {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹) (hεθ : ε ≤ θ ^ ((7 + 1) ^ 2))
    (hε : ∀ z ∈ l53EvenBox N, P[l53ZBadQ (proxyMass W γ m cB
      (sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side))) δ T
      (frontier (l53Sub C κ N z).closedBox)
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox))
      (Kt⁻¹ * μH[1] (frontier (l53Sub C κ N z).closedBox)) | A₀] ≤ ε)
    (j : ℕ) (E : Set Ω) (ν : Ω → Measure ℂ) (Kw : Set ℂ)
    (hKw : ∀ z ∈ l53EvenBox N,
      sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) ⊆ Kw)
    (hdom : ∀ ω ∈ E, ∀ z ∈ l53EvenBox N, ∀ (c : ℚ × ℚ) (q : ℚ),
      Metric.ball (ratPt c) q ⊆ sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side) →
        ν ω (Metric.ball (ratPt c) q) ≤
          proxyMass W γ m cB (sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side)) ω c q)
    (Prev Next : Finset (PercDir × ℤ))
    (hrange : ∀ p, (p ∈ Prev ∨ p ∈ Next) → (N : ℤ) - n < p.2 ∧ p.2 < N + n)
    {Λprev Λnext : Set ℂ} (hΛp : μH[1] Λprev ≠ ⊤) (hΛn : μH[1] Λnext ≠ ⊤)
    (hPrev : ∀ p ∈ Prev, l53CellSeg C κ n N p ⊆ Λprev)
    (hNext : ∀ p ∈ Next, l53CellSeg C κ n N p ⊆ Λnext)
    (hcovP : 0.2 * (μH[1] : Measure ℂ).real Λprev + 4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ))
      ≤ (μH[1] : Measure ℂ).real (⋃ p ∈ Prev, l53CellSeg C κ n N p))
    (hcardP : (Prev.card : ℝ) * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal ≤
      0.1 * (μH[1] : Measure ℂ).real Λprev)
    (hcovN : (μH[1] : Measure ℂ).real (Λnext \ ⋃ p ∈ Next, l53CellSeg C κ n N p) +
      Next.card * (Kt⁻¹ * (4 * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (C.n + κ)))).toReal +
        4 * (7 + 1) * j * (4 * (2 : ℝ)⁻¹ ^ (C.n + κ)) < 0.1 * (μH[1] : Measure ℂ).real Λnext) :
    P[E ∩ {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (dzzWall Kw (ν ω)) δ
        (T + Real.log ((((2 * N + 2) ^ 2 : ℕ) : ℝ) + 1)) Λprev Λnext} | A₀] ≤
      4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (7 + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) :=
  l53_box_desirable_prob hW C hK hn hnN
    (fun z => proxyMass W γ m cB (sqBox (l53Sub C κ N z).center (5 * (l53Sub C κ N z).side))) s
    (fun _z _ c q => l53_proxyMass_local hW γ hms hmt cB _ c q) hA₀ h0 hR₀ δ T hK8 hθ hεθ hε j E
    ν Kw hKw hdom Prev Next hrange hΛp hΛn hPrev hNext hcovP hcardP hcovN

/-- **The Peierls bound of `l53_box_desirable_prob` in closed form** (DZZ (eq-par), l. 1960–1975,
used at l. 2510–2514): if `8θ ≤ 1/2` and `(2N+1)(N+1)ε ≤ 1/2`, the right-hand side is at most
`4(2N+1) 2^{-(N-n+1)} + 32 · 2^{-j}` (`choose ≤ pow`, `Nat.choose_le_pow`). -/
lemma l53_box_rhs_le {N n j : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) {ε θ : ℝ≥0∞} (hθ : 8 * θ ≤ 2⁻¹)
    (hε : ((2 * N + 1 : ℕ) : ℝ≥0∞) * (((N + 1 : ℕ) : ℝ≥0∞) * ε) ≤ 2⁻¹) :
    4 * ((2 * N + 1 : ℕ) * (8 * θ) ^ (N - n + 1)) +
        4 * (7 + 1) * (((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j) ≤
      4 * ((2 * N + 1 : ℕ) * (2⁻¹ : ℝ≥0∞) ^ (N - n + 1)) + 32 * (2⁻¹ : ℝ≥0∞) ^ j := by
  have h1 : (8 * θ) ^ (N - n + 1) ≤ (2⁻¹ : ℝ≥0∞) ^ (N - n + 1) := pow_le_pow_left' hθ _
  have hch : ((2 * N + 1).choose j : ℝ≥0∞) ≤ ((2 * N + 1 : ℕ) : ℝ≥0∞) ^ j := by
    exact_mod_cast Nat.choose_le_pow (2 * N + 1) j
  have hNn : ((N - n + 2 : ℕ) : ℝ≥0∞) ≤ ((N + 1 : ℕ) : ℝ≥0∞) := by
    exact_mod_cast (by omega : N - n + 2 ≤ N + 1)
  have h2 : ((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j ≤
      (2⁻¹ : ℝ≥0∞) ^ j := by
    calc ((2 * N + 1).choose j : ℝ≥0∞) * (((N - n + 2 : ℕ) : ℝ≥0∞) * ε) ^ j
        ≤ ((2 * N + 1 : ℕ) : ℝ≥0∞) ^ j * (((N + 1 : ℕ) : ℝ≥0∞) * ε) ^ j := by gcongr
      _ = (((2 * N + 1 : ℕ) : ℝ≥0∞) * (((N + 1 : ℕ) : ℝ≥0∞) * ε)) ^ j := (mul_pow _ _ _).symm
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ j := pow_le_pow_left' hε _
  have e : (4 : ℝ≥0∞) * (7 + 1) = 32 := by norm_num
  rw [e]
  gcongr

end DZZ
end LQGMetric
