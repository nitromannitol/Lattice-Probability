/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSAppA.LongRange at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSAppA.LongRangeCore
import Mathlib.Probability.Independence.Integration

/-!
# [18] Lemma A.3, abstract form: the product structure (A.16) and the final bound

[18] = Gwynne–Miller–Sheffield, arXiv 1807.07511v3, proof of Lemma A.3. With `M_δ = ∏_{k ≤ N} M_δ^k` a product of independent Radon–Nikodym derivatives with
`E[(M_δ^k)^{±a₀/δ}] ≲ 1` (Lemma A.5), the Chebyshev/union bound (A.16)

  `P[M_δ > 1 + δ^s] ≤ Σ_k P[M_δ^k > (1 + δ^s)^{1/N}] ≲ (1 + δ^s)^{−a₀/(Nδ)} ≤ e^{−b₀ s/δ^{1−s}}`

and Hölder (A.17)–(A.18) give (A.6):
`E|E[X | h|_{ℂ∖𝔻}] − E[X | h_1(0)]|^p ≲ δ^{sp} E[|X|^p] + e^{−b/δ^{1−s}} E[|X|^{p₀}]^{p/p₀}`.

This file proves that implication for an arbitrary probability space: given the two change-of-measure identities of
`LongRangeCore` with `M = ∏_k M_k`, `M_k ≥ 0` independent and `∫ M_k^{±a₀/δ} ≤ K`, the bound (A.6) holds for
`δ ∈ (0, a]` with constants `a, b, C` depending only on `N, p, p₀, s, a₀, K`.

* `GMSAppA.lintegral_rpow_le_rpow_lintegral` — Lyapunov's inequality.
* `GMSAppA.measure_prod_gt_le`, `GMSAppA.measure_prod_lt_le` — (A.16) for products.
* `GMSAppA.lintegral_prod_rpow_le` — moments of the product.
* **`GMSAppA.lemmaA3_abstract`** — (A.6) from the change-of-measure identities.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace MatedCRTHarmonic.GMSAppA

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {P : Measure Ω}

/-- **Lyapunov's inequality**: `∫ Z^s ≤ (∫ Z^q)^{s/q}` on a probability space for `0 < s ≤ q`. -/
theorem lintegral_rpow_le_rpow_lintegral [IsProbabilityMeasure P] {Z : Ω → ℝ≥0∞}
    (hZ : AEMeasurable Z P) {s q : ℝ} (hs : 0 < s) (hsq : s ≤ q) :
    ∫⁻ ω, Z ω ^ s ∂P ≤ (∫⁻ ω, Z ω ^ q ∂P) ^ (s / q) := by
  rcases eq_or_lt_of_le hsq with rfl | hlt
  · rw [div_self hs.ne', ENNReal.rpow_one]
  have hq : 0 < q := hs.trans hlt
  have hconj : (q / s).HolderConjugate (q / (q - s)) := by
    refine ⟨?_, div_pos hq hs, div_pos hq (by linarith)⟩
    rw [inv_div, inv_div, ← add_div, add_sub_cancel, div_self hq.ne', inv_one]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj (hZ.pow_const s)
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  refine h.trans (le_of_eq ?_)
  rw [one_div_div]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hs.ne']

/-- Markov for an upper tail: `P[Z > c] ≤ ∫ Z^q / c^q`. -/
theorem measure_gt_le_lintegral_rpow {Z : Ω → ℝ} (hZ : Measurable Z) {c q : ℝ} (hc : 0 < c)
    (hq : 0 < q) :
    P {ω | c < Z ω} ≤ (∫⁻ ω, ENNReal.ofReal (Z ω) ^ q ∂P) / ENNReal.ofReal c ^ q := by
  have hsub : {ω | c < Z ω} ⊆ {ω | ENNReal.ofReal c ^ q ≤ ENNReal.ofReal (Z ω) ^ q} := by
    intro ω hω
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_of_lt hω)) hq.le
  refine (measure_mono hsub).trans ?_
  refine meas_ge_le_lintegral_div (hZ.ennreal_ofReal.pow_const q).aemeasurable ?_ ?_
  · exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hc) ENNReal.ofReal_ne_top).ne'
  · exact ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top

/-- Markov for a lower tail through the negative moment: `P[Z < c] ≤ c^q ∫ Z^{−q}`. -/
theorem measure_lt_le_lintegral_rpow_neg {Z : Ω → ℝ} (hZ : Measurable Z) {c q : ℝ} (hc : 0 < c)
    (hq : 0 < q) :
    P {ω | Z ω < c} ≤ (∫⁻ ω, ENNReal.ofReal (Z ω) ^ (-q) ∂P) * ENNReal.ofReal c ^ q := by
  have hcq0 : ENNReal.ofReal c ^ q ≠ 0 := (ENNReal.rpow_pos (ENNReal.ofReal_pos.2 hc)
    ENNReal.ofReal_ne_top).ne'
  have hcqt : ENNReal.ofReal c ^ q ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top
  have hsub : {ω | Z ω < c} ⊆ {ω | ENNReal.ofReal c ^ (-q) ≤ ENNReal.ofReal (Z ω) ^ (-q)} := by
    intro ω hω
    simp only [mem_ofPred_eq, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hω.le) hq.le)
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div (hZ.ennreal_ofReal.pow_const (-q)).aemeasurable ?_ ?_).trans
    (le_of_eq ?_)
  · rw [ENNReal.rpow_neg]; exact ENNReal.inv_ne_zero.2 hcqt
  · rw [ENNReal.rpow_neg]; exact ENNReal.inv_ne_top.2 hcq0
  · rw [ENNReal.rpow_neg, div_eq_mul_inv, inv_inv]

variable {N : ℕ}

/-- **(A.16), upper tail of a product**: if `M = ∏_{k<N} M_k` with `M_k ≥ 0` and `∫ M_k^q ≤ K`, then
`P[M > 1 + t] ≤ N K (1 + t)^{−q/N}`. -/
theorem measure_prod_gt_le (hN : 0 < N) {Mk : Fin N → Ω → ℝ} (hMm : ∀ k, Measurable (Mk k))
    (hM0 : ∀ k ω, 0 ≤ Mk k ω) {q K t : ℝ} (hq : 0 < q) (ht : 0 ≤ t)
    (hK : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ q ∂P ≤ ENNReal.ofReal K) :
    P {ω | 1 + t < ∏ k, Mk k ω} ≤ ENNReal.ofReal (N * K * (1 + t) ^ (-(q / N))) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (1 + t) ^ (1 / (N : ℝ)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by linarith) _
  have hcN : c ^ N = 1 + t := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel hN'.ne',
      Real.rpow_one]
  have hsub : {ω | 1 + t < ∏ k, Mk k ω} ⊆ ⋃ k ∈ (Finset.univ : Finset (Fin N)),
      {ω | c < Mk k ω} := by
    intro ω hω
    by_contra hcon
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hcon
    have : ∏ k, Mk k ω ≤ ∏ _k : Fin N, c :=
      Finset.prod_le_prod₀ (fun k _ => hM0 k ω) fun k _ => hcon k
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcN] at this
    exact absurd hω (not_lt.2 this)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ k, P {ω | c < Mk k ω} ≤ ENNReal.ofReal (K * (1 + t) ^ (-(q / N))) := by
    intro k
    refine (measure_gt_le_lintegral_rpow (hMm k) hc0 hq).trans ?_
    have hcq : ENNReal.ofReal c ^ q = ENNReal.ofReal ((1 + t) ^ (q / N)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hc0.le hq.le, hc, ← Real.rpow_mul (by linarith)]
      congr 2
      ring
    rw [hcq]
    have hpos : 0 < (1 + t) ^ (q / N) := Real.rpow_pos_of_pos (by linarith) _
    calc (∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ q ∂P) / ENNReal.ofReal ((1 + t) ^ (q / N))
        ≤ ENNReal.ofReal K / ENNReal.ofReal ((1 + t) ^ (q / N)) := by gcongr; exact hK k
      _ = ENNReal.ofReal (K * (1 + t) ^ (-(q / N))) := by
          rw [← ENNReal.ofReal_div_of_pos hpos, Real.rpow_neg (by linarith), div_eq_mul_inv]
  calc ∑ k ∈ (Finset.univ : Finset (Fin N)), P {ω | c < Mk k ω}
      ≤ ∑ _k ∈ (Finset.univ : Finset (Fin N)), ENNReal.ofReal (K * (1 + t) ^ (-(q / N))) :=
        Finset.sum_le_sum fun k _ => hone k
    _ = ENNReal.ofReal (N * K * (1 + t) ^ (-(q / N))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (N : ℝ) * K * (1 + t) ^ (-(q / N)) = N * (K * (1 + t) ^ (-(q / N))) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **(A.16), lower tail of a product**: if `M = ∏_{k<N} M_k` with `M_k ≥ 0` and `∫ M_k^{−q} ≤ K`, then for
`0 ≤ t < 1`, `P[M < 1 − t] ≤ N K (1 − t)^{q/N}`. -/
theorem measure_prod_lt_le (hN : 0 < N) {Mk : Fin N → Ω → ℝ} (hMm : ∀ k, Measurable (Mk k))
    {q K t : ℝ} (hq : 0 < q) (ht1 : t < 1)
    (hK : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ (-q) ∂P ≤ ENNReal.ofReal K) :
    P {ω | ∏ k, Mk k ω < 1 - t} ≤ ENNReal.ofReal (N * K * (1 - t) ^ (q / N)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := (1 - t) ^ (1 / (N : ℝ)) with hc
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by linarith) _
  have hcN : c ^ N = 1 - t := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel hN'.ne',
      Real.rpow_one]
  have hsub : {ω | ∏ k, Mk k ω < 1 - t} ⊆ ⋃ k ∈ (Finset.univ : Finset (Fin N)),
      {ω | Mk k ω < c} := by
    intro ω hω
    by_contra hcon
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_ofPred_eq, not_exists, not_lt] at hcon
    have : ∏ _k : Fin N, c ≤ ∏ k, Mk k ω :=
      Finset.prod_le_prod₀ (fun _ _ => hc0.le) fun k _ => hcon k
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcN] at this
    exact absurd hω (not_lt.2 this)
  refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ k, P {ω | Mk k ω < c} ≤ ENNReal.ofReal (K * (1 - t) ^ (q / N)) := by
    intro k
    refine (measure_lt_le_lintegral_rpow_neg (hMm k) hc0 hq).trans ?_
    have hcq : ENNReal.ofReal c ^ q = ENNReal.ofReal ((1 - t) ^ (q / N)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hc0.le hq.le, hc, ← Real.rpow_mul (by linarith)]
      congr 2
      ring
    rw [hcq]
    have hpos : 0 ≤ (1 - t) ^ (q / N) := (Real.rpow_pos_of_pos (by linarith) _).le
    calc (∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ (-q) ∂P) * ENNReal.ofReal ((1 - t) ^ (q / N))
        ≤ ENNReal.ofReal K * ENNReal.ofReal ((1 - t) ^ (q / N)) := by gcongr; exact hK k
      _ = ENNReal.ofReal (K * (1 - t) ^ (q / N)) := by
          by_cases hK0 : 0 ≤ K
          · rw [ENNReal.ofReal_mul hK0]
          · push Not at hK0
            rw [ENNReal.ofReal_of_nonpos hK0.le, zero_mul,
              ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hK0.le hpos)]
  calc ∑ k ∈ (Finset.univ : Finset (Fin N)), P {ω | Mk k ω < c}
      ≤ ∑ _k ∈ (Finset.univ : Finset (Fin N)), ENNReal.ofReal (K * (1 - t) ^ (q / N)) :=
        Finset.sum_le_sum fun k _ => hone k
    _ = ENNReal.ofReal (N * K * (1 - t) ^ (q / N)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (N : ℝ) * K * (1 - t) ^ (q / N) = N * (K * (1 - t) ^ (q / N)) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- **Moments of a product of independent factors**: if `M_k ≥ 0` are independent with `∫ M_k^q ≤ K`, `K ≥ 1`, then
for `0 < s ≤ q`, `∫ (∏_k M_k)^s ≤ K^N`. -/
theorem lintegral_prod_rpow_le [IsProbabilityMeasure P] {Mk : Fin N → Ω → ℝ}
    (hMm : ∀ k, Measurable (Mk k)) (hM0 : ∀ k ω, 0 ≤ Mk k ω) (hind : iIndepFun Mk P)
    {q s K : ℝ} (hs : 0 < s) (hsq : s ≤ q) (hK1 : 1 ≤ K)
    (hK : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ q ∂P ≤ ENNReal.ofReal K) :
    ∫⁻ ω, ENNReal.ofReal (∏ k, Mk k ω) ^ s ∂P ≤ ENNReal.ofReal K ^ N := by
  have hq : 0 < q := hs.trans_le hsq
  have e : (fun ω => ENNReal.ofReal (∏ k, Mk k ω) ^ s) =
      fun ω => ∏ k, ENNReal.ofReal (Mk k ω) ^ s := by
    funext ω
    rw [ENNReal.ofReal_prod_of_nonneg fun k _ => hM0 k ω, ENNReal.prod_rpow_of_nonneg hs.le]
  rw [e]
  have hind' : iIndepFun (fun k ω => ENNReal.ofReal (Mk k ω) ^ s) P :=
    hind.comp (fun _ x => ENNReal.ofReal x ^ s)
      fun _ => ENNReal.measurable_ofReal.pow_const s
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _ hind'
    fun k => (hMm k).ennreal_ofReal.pow_const s]
  have hone : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ s ∂P ≤ ENNReal.ofReal K := by
    intro k
    refine (lintegral_rpow_le_rpow_lintegral (hMm k).ennreal_ofReal.aemeasurable hs hsq).trans ?_
    have hK1' : 1 ≤ ENNReal.ofReal K := by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hK1
    calc (∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ q ∂P) ^ (s / q) ≤ ENNReal.ofReal K ^ (s / q) :=
          ENNReal.rpow_le_rpow (hK k) (div_pos hs hq).le
      _ ≤ ENNReal.ofReal K ^ (1 : ℝ) :=
          ENNReal.rpow_le_rpow_of_exponent_le hK1' ((div_le_one hq).2 hsq)
      _ = ENNReal.ofReal K := ENNReal.rpow_one _
  calc ∏ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ s ∂P ≤ ∏ _k : Fin N, ENNReal.ofReal K :=
        Finset.prod_le_prod fun k _ => hone k
    _ = ENNReal.ofReal K ^ N := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ### Real inequalities for (A.16) -/

/-- `(1 + t)^{−x} ≤ e^{−xt/2}` for `t ∈ [0,1]`, `x ≥ 0`. -/
lemma one_add_rpow_neg_le_exp {t x : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : 0 ≤ x) :
    (1 + t) ^ (-x) ≤ Real.exp (-(x * t) / 2) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  refine Real.exp_le_exp.2 ?_
  have hlog : t / 2 ≤ Real.log (1 + t) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1 + t by linarith)
    have h2 : t / 2 ≤ 1 - (1 + t)⁻¹ := by
      rw [show 1 - (1 + t)⁻¹ = t / (1 + t) by field_simp; ring]
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  nlinarith

/-- `(1 − t)^{x} ≤ e^{−xt}` for `t ∈ [0,1)`, `x ≥ 0`. -/
lemma one_sub_rpow_le_exp {t x : ℝ} (ht1 : t < 1) (hx : 0 ≤ x) :
    (1 - t) ^ x ≤ Real.exp (-(x * t)) := by
  rw [Real.rpow_def_of_pos (by linarith)]
  refine Real.exp_le_exp.2 ?_
  have hlog : Real.log (1 - t) ≤ -t := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 - t by linarith)
    linarith
  nlinarith

/-! ### The assembled bound -/

/-- the Hölder exponent `r = p₀/(p₀ − p)` -/
def holderR (p p₀ : ℝ) : ℝ := p₀ / (p₀ - p)

/-- the threshold `a` of [18] Lemma A.3 in the abstract form -/
def lemmaA3a (p p₀ a₀ : ℝ) : ℝ := min (1 / 2) (a₀ / (2 * (p * holderR p p₀)))

/-- the rate `b` of [18] Lemma A.3 in the abstract form -/
def lemmaA3b (N : ℕ) (p p₀ a₀ : ℝ) : ℝ := (1 - p / p₀) * a₀ / (4 * N)

/-- the constant `C` of [18] Lemma A.3 in the abstract form -/
def lemmaA3C (N : ℕ) (p p₀ K : ℝ) : ℝ :=
  4 ^ (p - 1) * (1 + (K ^ N * (N * K)) ^ ((1 - p / p₀) / 2) + (N * K) ^ (1 - p / p₀))

/-- **[18] Lemma A.3, abstract form** (proof ). Let `p₀ > p ≥ 1`, `s ∈ (0,1)`, `N ≥ 1`,
`a₀ > 0`, `K ≥ 1`, and `δ ∈ (0, a]` with `a = lemmaA3a p p₀ a₀`. Suppose `X̃ ≥ 0`, `M = ∏_{k<N} M_k` with `M_k ≥ 0`
independent and `∫ M_k^{±a₀/δ} ≤ K` (the conclusion of Lemma A.5), and the change-of-measure identities
`E[X | m] = E[M X̃ | m]`, `E[X̃ | m] = Y` hold. Then
`E|E[X | m] − Y|^p ≤ C (δ^{sp} E[X̃^p] + e^{−b/δ^{1−s}} E[X̃^{p₀}]^{p/p₀})` with `b = lemmaA3b N p p₀ a₀`,
`C = lemmaA3C N p p₀ K`; the constants do not depend on `δ`, `m`, the probability space or the variables. -/
theorem lemmaA3_abstract [IsProbabilityMeasure P] (hm : m ≤ m0) {N : ℕ} (hN : 0 < N)
    {p p₀ s a₀ K : ℝ} (hp : 1 ≤ p) (hpp₀ : p < p₀) (hs0 : 0 < s) (ha₀ : 0 < a₀) (hK1 : 1 ≤ K)
    {δ : ℝ} (hδ0 : 0 < δ) (hδa : δ ≤ lemmaA3a p p₀ a₀) {X Xt Y : Ω → ℝ} {Mk : Fin N → Ω → ℝ}
    (hMm : ∀ k, Measurable (Mk k)) (hM0 : ∀ k ω, 0 ≤ Mk k ω) (hind : iIndepFun Mk P)
    (hKp : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ (a₀ / δ) ∂P ≤ ENNReal.ofReal K)
    (hKn : ∀ k, ∫⁻ ω, ENNReal.ofReal (Mk k ω) ^ (-(a₀ / δ)) ∂P ≤ ENNReal.ofReal K)
    (hX : ∀ ω, 0 ≤ Xt ω) (hXti : Integrable Xt P)
    (hMXi : Integrable (fun ω => (∏ k, Mk k ω) * Xt ω) P)
    (hcm : P[X | m] =ᵐ[P] P[(fun ω => (∏ k, Mk k ω) * Xt ω) | m]) (hY : P[Xt | m] =ᵐ[P] Y) :
    ∫⁻ ω, ENNReal.ofReal |P[X | m] ω - Y ω| ^ p ∂P ≤
      ENNReal.ofReal (lemmaA3C N p p₀ K) *
        (ENNReal.ofReal (δ ^ (s * p)) * ∫⁻ ω, ENNReal.ofReal (Xt ω) ^ p ∂P +
          ENNReal.ofReal (Real.exp (-(lemmaA3b N p p₀ a₀ / δ ^ (1 - s)))) *
            (∫⁻ ω, ENNReal.ofReal (Xt ω) ^ p₀ ∂P) ^ (p / p₀)) := by
  -- parameters
  have hp0 : 0 < p := by linarith
  have hp₀ : 0 < p₀ := by linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : 0 < p₀ / (p₀ - p) := div_pos hp₀ (by linarith)
  set θ := 1 - p / p₀ with hθ
  have hθ0 : 0 < θ := by rw [hθ, sub_pos, div_lt_one hp₀]; exact hpp₀
  have hδ1 : δ ≤ 1 / 2 := hδa.trans (min_le_left _ _)
  have hδq : 2 * (p * (p₀ / (p₀ - p))) ≤ a₀ / δ := by
    have := hδa.trans (min_le_right _ _)
    have h2 : 0 < 2 * (p * (p₀ / (p₀ - p))) := by positivity
    unfold holderR at this
    rw [le_div_iff₀ h2] at this
    rw [le_div_iff₀ hδ0]
    linarith
  set q := a₀ / δ with hq
  have hq0 : 0 < q := div_pos ha₀ hδ0
  set t := δ ^ s with ht
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hδ0 s).le
  have ht1 : t < 1 := Real.rpow_lt_one hδ0.le (by linarith) hs0
  set u := a₀ / δ ^ (1 - s) with hu
  have hu0 : 0 < u := div_pos ha₀ (Real.rpow_pos_of_pos hδ0 _)
  have hqt : q * t = u := by
    rw [hq, ht, hu, Real.rpow_sub hδ0, Real.rpow_one]
    field_simp
  set M : Ω → ℝ := fun ω => ∏ k, Mk k ω with hMdef
  have hMm' : Measurable M := Finset.measurable_prod _ fun k _ => hMm k
  have hM0' : ∀ ω, 0 ≤ M ω := fun ω => Finset.prod_nonneg fun k _ => hM0 k ω
  -- step 1: (A.15)
  have h1 := lintegral_rpow_condExp_sub_le hm hMm' hM0' hX hXti hMXi hcm hY ht0 hp
  -- the two tail terms
  set E₀ := (∫⁻ ω, ENNReal.ofReal (Xt ω) ^ p₀ ∂P) ^ (p / p₀) with hE₀
  set A : Set Ω := {ω | 1 + t < M ω} with hAdef
  set B : Set Ω := {ω | M ω < 1 - t} with hBdef
  have hA : MeasurableSet A := measurableSet_lt measurable_const hMm'
  have hB : MeasurableSet B := measurableSet_lt hMm' measurable_const
  have eT : ∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P =
      ∫⁻ ω, A.indicator (fun ω => (ENNReal.ofReal (M ω) * ENNReal.ofReal (Xt ω)) ^ p) ω ∂P := by
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ A
    · rw [tailMul, Set.indicator_of_mem hω, Set.indicator_of_mem hω, ENNReal.ofReal_mul (hM0' ω)]
    · rw [tailMul, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp0]
  have eI : ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P =
      ∫⁻ ω, B.indicator (fun ω => ENNReal.ofReal (Xt ω) ^ p) ω ∂P := by
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ B
    · rw [tailInd, Set.indicator_of_mem hω, Set.indicator_of_mem hω]
    · rw [tailInd, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, ENNReal.ofReal_zero,
        ENNReal.zero_rpow_of_pos hp0]
  have hXm : AEMeasurable (fun ω => ENNReal.ofReal (Xt ω)) P := hXti.aemeasurable.ennreal_ofReal
  have hT := lintegral_mul_rpow_indicator_le (P := P) hXm hMm'.ennreal_ofReal.aemeasurable hA hp0
    hpp₀
  have hI := lintegral_rpow_indicator_le (P := P) hXm hB hp0 hpp₀
  have hMom : ∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * (p * (p₀ / (p₀ - p)))) ∂P ≤
      ENNReal.ofReal K ^ N :=
    lintegral_prod_rpow_le hMm hM0 hind (by positivity) hδq hK1 hKp
  have hPA : P A ≤ ENNReal.ofReal (N * K * Real.exp (-(u / (2 * N)))) := by
    refine (measure_prod_gt_le hN hMm hM0 hq0 ht0 hKp).trans (ENNReal.ofReal_le_ofReal ?_)
    have := one_add_rpow_neg_le_exp ht0 ht1.le (div_pos hq0 hN').le
    have e : -((q / N) * t) / 2 = -(u / (2 * N)) := by rw [← hqt]; field_simp
    rw [e] at this
    have hNK : 0 ≤ (N : ℝ) * K := by positivity
    exact mul_le_mul_of_nonneg_left this hNK
  have hPB : P B ≤ ENNReal.ofReal (N * K * Real.exp (-(u / N))) := by
    refine (measure_prod_lt_le hN hMm hq0 ht1 hKn).trans (ENNReal.ofReal_le_ofReal ?_)
    have := one_sub_rpow_le_exp ht1 (div_pos hq0 hN').le
    have e : -((q / N) * t) = -(u / N) := by rw [← hqt]; field_simp
    rw [e] at this
    have hNK : 0 ≤ (N : ℝ) * K := by positivity
    exact mul_le_mul_of_nonneg_left this hNK
  -- real constants
  set eb := Real.exp (-(lemmaA3b N p p₀ a₀ / δ ^ (1 - s))) with heb
  have heb0 : 0 ≤ eb := (Real.exp_pos _).le
  set C₂ := (K ^ N * (N * K)) ^ (θ / 2) + (N * K) ^ θ with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hb : lemmaA3b N p p₀ a₀ / δ ^ (1 - s) = θ * u / (4 * N) := by
    rw [lemmaA3b, hu, hθ]; field_simp
  -- the upper tail term
  have hT2 : ∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P ≤
      E₀ * ENNReal.ofReal ((K ^ N * (N * K)) ^ (θ / 2) * eb) := by
    rw [eT]
    refine hT.trans ?_
    gcongr
    calc ((∫⁻ ω, ENNReal.ofReal (M ω) ^ (2 * (p * (p₀ / (p₀ - p)))) ∂P) ^ (1 / 2 : ℝ) *
          P A ^ (1 / 2 : ℝ)) ^ θ
        ≤ ((ENNReal.ofReal K ^ N) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (N * K * Real.exp (-(u / (2 * N)))) ^ (1 / 2 : ℝ)) ^ θ := by
          gcongr
      _ = ENNReal.ofReal ((K ^ N * (N * K)) ^ (θ / 2) * eb) := by
          rw [← ENNReal.ofReal_pow (by linarith), ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.rpow_mul,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
          congr 1
          rw [show K ^ N * (N * K * Real.exp (-(u / (2 * N)))) =
            (K ^ N * (N * K)) * Real.exp (-(u / (2 * N))) by ring,
            Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, heb, hb]
          congr 2
          · ring
          · field_simp
            norm_num
  -- the lower tail term
  have hI2 : ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P ≤
      E₀ * ENNReal.ofReal ((N * K) ^ θ * eb) := by
    rw [eI]
    refine hI.trans ?_
    gcongr
    calc P B ^ θ ≤ ENNReal.ofReal (N * K * Real.exp (-(u / N))) ^ θ := by gcongr
      _ = ENNReal.ofReal ((N * K) ^ θ * Real.exp (-(θ * u / N))) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hθ0.le,
            Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
          congr 3
          ring
      _ ≤ ENNReal.ofReal ((N * K) ^ θ * eb) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
          rw [heb, hb]
          refine Real.exp_le_exp.2 ?_
          have : θ * u / (4 * N) ≤ θ * u / N := by
            apply div_le_div_of_nonneg_left (by positivity) hN' (by linarith)
          linarith
  -- assembly
  have h4 : (4 : ℝ≥0∞) ^ (p - 1) = ENNReal.ofReal (4 ^ (p - 1)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) (by linarith)]
    norm_num
  have htp : ENNReal.ofReal t ^ p = ENNReal.ofReal (δ ^ (s * p)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg ht0 hp0.le, ht, ← Real.rpow_mul hδ0.le]
  refine h1.trans ?_
  rw [htp, h4]
  set E1 := ∫⁻ ω, ENNReal.ofReal (Xt ω) ^ p ∂P
  set x := ENNReal.ofReal (δ ^ (s * p))
  have hTT : ∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P +
      ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P ≤
      ENNReal.ofReal C₂ * (ENNReal.ofReal eb * E₀) := by
    refine (add_le_add hT2 hI2).trans (le_of_eq ?_)
    rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (K ^ N * (N * K)) ^ (θ / 2) * eb + (N * K) ^ θ * eb = C₂ * eb by rw [hC₂]; ring,
      ENNReal.ofReal_mul hC₂0]
    ring
  have h1C : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 + C₂) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hCC : ENNReal.ofReal C₂ ≤ ENNReal.ofReal (1 + C₂) := ENNReal.ofReal_le_ofReal (by linarith)
  calc ENNReal.ofReal (4 ^ (p - 1)) * (x * E1 +
        ∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P)
      = ENNReal.ofReal (4 ^ (p - 1)) * (x * E1 +
        (∫⁻ ω, ENNReal.ofReal (tailMul M Xt t ω) ^ p ∂P +
        ∫⁻ ω, ENNReal.ofReal (tailInd M Xt t ω) ^ p ∂P)) := by rw [add_assoc]
    _ ≤ ENNReal.ofReal (4 ^ (p - 1)) * (x * E1 + ENNReal.ofReal C₂ * (ENNReal.ofReal eb * E₀)) := by
        gcongr
    _ ≤ ENNReal.ofReal (4 ^ (p - 1)) * (ENNReal.ofReal (1 + C₂) * (x * E1) +
        ENNReal.ofReal (1 + C₂) * (ENNReal.ofReal eb * E₀)) := by
        gcongr ENNReal.ofReal (4 ^ (p - 1)) * ?_
        exact add_le_add (le_mul_of_one_le_left' h1C) (mul_le_mul_left hCC _)
    _ = ENNReal.ofReal (lemmaA3C N p p₀ K) * (x * E1 + ENNReal.ofReal eb * E₀) := by
        rw [← mul_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [lemmaA3C, hC₂, hθ]
        ring

end MatedCRTHarmonic.GMSAppA
