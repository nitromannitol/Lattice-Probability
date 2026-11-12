/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P17S4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17S3
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3P17
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L4Mid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DG Proposition 3.17: (eqn-lfpp-lower-show) (P2-DG317S)

Source: Ding–Gwynne arXiv:1807.01072, `metric-comparison-final.tex`, proof of Prop 3.17, Steps
1–3 (DG:1533–1591), with `β = 1/(2+γ)²` (DG:1524), i.e. `ε = δ^{(2+γ)²}`.
* Step 1 (DG:1541–1555): the event of Lemma 3.13 at level `m = m_δ + 1` (`dg_lemma313`,
  `dg_lemma313V`; rectangles `δ_ε × δ_ε/2`, corners in `(δ_ε/2)ℤ²`, DG: "`N = 2`"), the field
  control (eqn-field-control) from Lemma 3.5 (`dg_lemma35`, `|ĥ_δ| ≤ (2+η') log δ⁻¹` on `𝕊`) and
  Lemma 3.6 (`dg_lemma36` with `A = δ 2^m ∈ [2,4)`, `|ĥ_{2^{-m}}(v) − ĥ_δ(v)| ≤ η' log δ⁻¹`).
* Step 2: `p17s_hyp_of_event`, `p17s_hY`, `p17s_hadj`, `p17s_hnear` (files S3P17S1, S3P17S2).
* Step 3: `dg_prop317_step3'` (P2-DG105k) with the lower bound input `DGP317Lb` (DG: Lemma 3.2
  and Theorem `thm-diam`, "with polynomially high probability `D^ε(K', ∂U') ≥ ε^{-1/(d+ζ̃)}`",
  DG:1587–1589; a separate packet, hypothesis here), and the exponent algebra `p17s_alg`.

`DGP317Lb P μ d Q` is used for `K' = cthickening (r₀/3) K`, `U' = thickening (2r₀/3) K`
(`thickening r₀ K ⊆ U`): points `ρ`-close to `K` lie in `K'`, points `ρ`-close to `∂U` lie
outside `U'`. The measure `μ` (DG's `μ_ĥ`) and the domain `Q ⊇ [−r, 1+r]²` (DG's `𝕊(1/2)`)
are parameters: Lemma 3.11 at scale (`DGLem311Scaled`, `DGLem311ScaledV`, the inputs of
`dg_lemma313`) and `DGP317Lb` are taken for this `μ`, as their consumers in P3.9/L3.14 do.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DG

open Blueprint WhiteNoise

variable {Ω : Type} [MeasurableSpace Ω]

/-- **the lower-bound input** of DG:1587–1589 (DG Theorem `thm-diam` + Lemma 3.2 for `μ_ĥ`):
for compact `K'` and open `U' ⊇ K'` in `𝕊`, with polynomially high probability as `ε → 0`,
`D^ε(y, y'; Q) ≥ ε^{-1/(d+ζ)}` for all `y ∈ K'`, `y' ∉ U'` (i.e. `D^ε(K', ∂U') ≥ ε^{-1/(d+ζ)}`). -/
def DGP317Lb (P : Measure Ω) (μ : Ω → Measure ℂ) (d : ℝ) (Q : Set ℂ) : Prop :=
  ∀ K' U' : Set ℂ, IsCompact K' → IsOpen U' → K' ⊆ U' → U' ⊆ closedUnitSquare →
    ∀ ζ ∈ Ioo (0 : ℝ) 1, ∃ p C ε₀ : ℝ, 0 < p ∧ 0 < ε₀ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      P {ω | ¬ ∀ y ∈ K', ∀ y' ∈ U'ᶜ,
        ENNReal.ofReal (ε ^ (-(1 / (d + ζ)))) ≤ dgLGD (μ ω) ε Q y y'} ≤
        ENNReal.ofReal (C * ε ^ p)

/-- union bound with polynomial rates -/
lemma p17s_union2 {P : Measure Ω} {A B : Set Ω} {C₁ C₂ q₁ q₂ p δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (h1 : P A ≤ ENNReal.ofReal (C₁ * δ ^ q₁))
    (h2 : P B ≤ ENNReal.ofReal (C₂ * δ ^ q₂)) (hp1 : p ≤ q₁) (hp2 : p ≤ q₂) :
    P (A ∪ B) ≤ ENNReal.ofReal ((|C₁| + |C₂|) * δ ^ p) := by
  have hq : ∀ (C q : ℝ), p ≤ q → C * δ ^ q ≤ |C| * δ ^ p := fun C q hq =>
    mul_le_mul (le_abs_self C) (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hq)
      (Real.rpow_nonneg hδ.le _) (abs_nonneg C)
  calc P (A ∪ B) ≤ P A + P B := measure_union_le _ _
    _ ≤ ENNReal.ofReal (|C₁| * δ ^ p) + ENNReal.ofReal (|C₂| * δ ^ p) :=
        add_le_add (h1.trans (ENNReal.ofReal_le_ofReal (hq _ _ hp1)))
          (h2.trans (ENNReal.ofReal_le_ofReal (hq _ _ hp2)))
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]

lemma p17s_sq_bdd : Bornology.IsBounded closedUnitSquare :=
  (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun z hz => by
    obtain ⟨a, b, c, d⟩ := hz
    rw [mem_closedBall_zero_iff]
    refine (Complex.norm_le_abs_re_add_abs_im z).trans ?_
    rw [abs_of_nonneg a, abs_of_nonneg c]; linarith

lemma p17s_frontier_sub {U : Set ℂ} (hUS : U ⊆ closedUnitSquare) :
    frontier U ⊆ closedUnitSquare :=
  frontier_subset_closure.trans (closure_minimal hUS p17_isClosed_sq)

/-- `e^{-λ m} ≤ δ^{λ/log 2}` for `m ≥ log₂ δ⁻¹` -/
lemma p17s_exp_m {δ lam : ℝ} {m : ℕ} (hδ : 0 < δ) (hlam : 0 < lam)
    (hm : Real.logb 2 δ⁻¹ ≤ m) : Real.exp (-(lam * m)) ≤ δ ^ (lam / Real.log 2) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [← neg_neg (lam / Real.log 2), ← p17s_exp_log hδ, Real.exp_le_exp]
  rw [Real.logb, div_le_iff₀ hl] at hm
  have : -(lam / Real.log 2) * Real.log δ⁻¹ = -(lam * (Real.log δ⁻¹ / Real.log 2)) := by ring
  rw [this, neg_le_neg_iff]
  refine mul_le_mul_of_nonneg_left ?_ hlam.le
  rw [div_le_iff₀ hl]; linarith

/-- **DG Steps 2–3 on the good event** (DG:1556–1591), deterministic: the rectangle bounds of
L3.13 at level `m_δ + 1` (`hH`, `hV`, field `φt = ĥ_{2^{-m}}`), the field control
(`h3`, `h4`, `φδ = ĥ_δ`) and the lower bound `h5` give `δ^{λ+ζ} ≤ D̂^δ(z, w; 𝕊)`. -/
theorem p17s_good {γ d ζ δ r r₀ : ℝ} (hγ : 0 < γ) (hd : 1 ≤ d) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hδ : 0 < δ) (hδe : δ ≤ Real.exp (-1)) (hδr : δ ≤ r) (hδr₀ : δ ≤ r₀ / 6)
    (hs1 : δ ^ (ζ / 2) ≤ 1 / 12) (hs2 : δ ^ (ζ / 8) ≤ (ζ / 8) ^ 3 / 768)
    {μ : Measure ℂ} {Q : Set ℂ} (hQ : p39Box 0 1 r ⊆ Q) {φt φδ : ℂ → ℝ} (hφt : Continuous φt)
    (hH : ∀ x ∈ l313Grid Q 0 (dgM δ + 1),
      (l313Set μ (δ ^ ((2 + γ) ^ 2)) (l313Str (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1)
        (l313Left (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1)
        (l313Right (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal (l313Tgt γ d (p17sEta γ ζ) (δ ^ ((2 + γ) ^ 2)) (dgM δ + 1)
        (sInf (φt '' l313Str (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1))))
    (hV : ∀ x ∈ l313GridV Q 0 (dgM δ + 1),
      (l313Set μ (δ ^ ((2 + γ) ^ 2)) (l313StrV (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1)
        (l313Bot (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1)
        (l313Top (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1) : ℝ≥0∞) ≤
      ENNReal.ofReal (l313Tgt γ d (p17sEta γ ζ) (δ ^ ((2 + γ) ^ 2)) (dgM δ + 1)
        (sInf (φt '' l313StrV (p39d (dgM δ + 1)) (l313Corner 0 (dgM δ + 1) x) 1))))
    (h3 : ∀ z ∈ closedUnitSquare, |φδ z| ≤ (2 + p17sEta' γ d ζ) * Real.log δ⁻¹)
    (h4 : ∀ z ∈ closedUnitSquare, |φt z - φδ z| ≤ p17sEta' γ d ζ * Real.log δ⁻¹)
    {K U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U) (hUS : U ⊆ closedUnitSquare)
    (hthick : thickening r₀ K ⊆ U)
    (h5 : ∀ y ∈ cthickening (r₀ / 3) K, ∀ y' ∈ (thickening (2 * r₀ / 3) K)ᶜ,
      ENNReal.ofReal ((δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d + p17sEta γ ζ)))) ≤
        dgLGD μ (δ ^ ((2 + γ) ^ 2)) Q y y') :
    ∀ z ∈ K, ∀ w ∈ frontier U, δ ^ ((1 - 2 / d - γ ^ 2 / (2 * d)) + ζ) ≤
      dgApproxLFPP (γ / d) δ φδ z w := by
  intro z hz w hw
  set M := dgM δ with hMdef
  set ε := δ ^ ((2 + γ) ^ 2) with hεdef
  set η := p17sEta γ ζ
  set η' := p17sEta' γ d ζ
  set L := Real.log δ⁻¹ with hL
  have hd0 : 0 < d := by linarith
  have hδ1 : δ < 1 := hδe.trans_lt (by
    have := Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num); rwa [Real.exp_zero] at this)
  have hε : 0 < ε := Real.rpow_pos_of_pos hδ _
  have hL0 : 0 ≤ L := (Real.log_pos ((one_lt_inv₀ hδ).2 hδ1)).le
  obtain ⟨hM1, hM2, hM3, hM4⟩ := p17s_dgM hδ hδ1
  have ht : p39d (M + 1) = (2 : ℝ)⁻¹ ^ M / 2 := p39d_succ M
  have ht0 := p39d_pos (M + 1)
  -- the bound `N_S`
  set X := p17sX γ d ζ δ (M + 1) with hX
  set N : ℤ × ℤ → ℝ := fun k => X * Real.exp (γ / d * φδ (dgCenter M k)) with hN
  have hX1 : 0 ≤ (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
      (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * ((M + 1 : ℕ) : ℝ) / d)) :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.rpow_nonneg (by norm_num) _)
  have hX2 : 0 < ((M + 1 : ℕ) : ℝ) ^ 3 * δ ^ (-(γ / d * (2 + η'))) :=
    mul_pos (by positivity) (Real.rpow_pos_of_pos hδ _)
  have hX0 : 0 < X := by
    rw [hX, p17sX]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hX1 (Real.exp_pos _).le) hX2
  have hN0 : ∀ k, 0 ≤ N k := fun k => mul_nonneg hX0.le (Real.exp_pos _).le
  have hNb : ∀ k ∈ dgIdx M, l313Tgt γ d η ε (M + 1) (φt (dgCenter M k)) ≤ N k := by
    intro k hk
    have hv := p17_center_mem hk
    have e3 := abs_le.1 (h3 _ hv)
    have e4 := abs_le.1 (h4 _ hv)
    have hξ : 0 ≤ γ / d := by positivity
    have hexp : Real.exp (γ / d * φt (dgCenter M k)) ≤
        Real.exp (γ / d * (η' * L)) * Real.exp (γ / d * φδ (dgCenter M k)) := by
      rw [← Real.exp_add, Real.exp_le_exp, ← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hξ
    have hlow : 1 ≤ δ ^ (-(γ / d * (2 + η'))) * Real.exp (γ / d * φδ (dgCenter M k)) := by
      rw [← p17s_exp_log hδ, ← Real.exp_add, Real.one_le_exp_iff]
      have : γ / d * (2 + η') * Real.log δ⁻¹ + γ / d * φδ (dgCenter M k) =
          γ / d * ((2 + η') * L + φδ (dgCenter M k)) := by rw [hL]; ring
      rw [this]
      exact mul_nonneg hξ (by linarith)
    unfold l313Tgt
    rw [hN, hX, p17sX]
    refine max_le ?_ ?_
    · have : ((M + 1 : ℕ) : ℝ) ^ 3 ≤ ((M + 1 : ℕ) : ℝ) ^ 3 *
          (δ ^ (-(γ / d * (2 + η'))) * Real.exp (γ / d * φδ (dgCenter M k))) :=
        le_mul_of_one_le_right (by positivity) hlow
      have h0 : 0 ≤ (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
          (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * ((M + 1 : ℕ) : ℝ) / d)) *
          Real.exp (γ / d * (η' * L)) * Real.exp (γ / d * φδ (dgCenter M k)) :=
        mul_nonneg (mul_nonneg hX1 (Real.exp_pos _).le) (Real.exp_pos _).le
      nlinarith
    · have h0 : 0 ≤ ((M + 1 : ℕ) : ℝ) ^ 3 * δ ^ (-(γ / d * (2 + η'))) *
          Real.exp (γ / d * φδ (dgCenter M k)) := by positivity
      calc _ ≤ (δ ^ ((2 + γ) ^ 2)) ^ (-(1 / (d - η))) *
            (2 : ℝ) ^ (-((2 + γ ^ 2 / 2 - η) * ((M + 1 : ℕ) : ℝ) / d)) *
            (Real.exp (γ / d * (η' * L)) * Real.exp (γ / d * φδ (dgCenter M k))) :=
            mul_le_mul_of_nonneg_left hexp hX1
        _ ≤ _ := by nlinarith
  obtain ⟨KH, KV, Hyp⟩ := p17s_hyp_of_event hd0 hγ hε hφt hQ (by rw [ht]; linarith) hH hV hNb
  -- Step 3
  have hzS : z ∈ closedUnitSquare := hUS (hKU hz)
  have hwS : w ∈ closedUnitSquare := p17s_frontier_sub hUS hw
  have hρ : 4 * p39d (M + 1) ≤ r₀ / 3 := by rw [ht]; linarith
  have hLb : ∀ y y' : ℂ, ‖y - z‖ ≤ 4 * p39d (M + 1) → ‖y' - w‖ ≤ 4 * p39d (M + 1) →
      ENNReal.ofReal (ε ^ (-(1 / (d + η)))) ≤ dgLGD μ ε Q y y' := by
    intro y y' hy hy'
    refine h5 y (mem_cthickening_of_dist_le y z _ K hz ?_) y' ?_
    · rw [dist_eq_norm]; linarith
    · intro hmem
      obtain ⟨z', hz', hd'⟩ := mem_thickening_iff.1 hmem
      have hwU : w ∈ U := hthick (mem_thickening_iff.2 ⟨z', hz', by
        calc dist w z' ≤ dist w y' + dist y' z' := dist_triangle _ _ _
          _ < r₀ := by rw [dist_comm, dist_eq_norm]; linarith⟩)
      have := hU.inter_frontier_eq
      exact (this ▸ mem_inter hwU hw : w ∈ (∅ : Set ℂ))
  have hT : 0 < 6 * X := by positivity
  have step := dg_prop317_step3' (μ := μ) (ε := ε) (Q := Q) (Lb := ε ^ (-(1 / (d + η))))
    (ξ := γ / d) (φ := φδ) (Y := p17sY KH KV M) hδ hT
    (fun k hk y hy y' hy' => (p17s_hY Hyp hN0 k hk y hy y' hy').trans_eq
      (congrArg ENNReal.ofReal (by rw [hN]; ring)))
    (p17s_hadj Hyp) (p17s_hnear Hyp) hzS hwS hLb
  have alg := p17s_alg hγ hd hζ hζ1 hδ hδe (m := M + 1)
    ((pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ M)).trans hM1)
    (by push_cast; linarith) hs1 hs2
  rw [← hX] at alg
  have := alg.trans step
  rw [mul_comm (6 * X)] at this
  exact le_of_mul_le_mul_right this hT

end LQGMetric.DG
