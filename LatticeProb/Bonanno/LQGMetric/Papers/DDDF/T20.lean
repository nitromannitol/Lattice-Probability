/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.T20 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20Ind
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L24
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.C8

/-!
# DDDF Theorem 20 from the recursive inequality (5.70)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 1069–1213 (proof of `thm:AssTthm`; blueprint node DDDF.T20, work package WP-104).

DDDF's proof has five steps. Steps 2–4 produce the recursive inequality (5.70) =
`eq:RecursiveIneq` (l. 1179–1182):
`Var log L^{(n)}_{1,1}(ψ) ≤ C₁ K + e^{-C₂ K} Λ_{n-K}(ψ, p/2)²` for `K` large and `n ≥ K`.
This file proves Steps 1 and 5 and the transfer to `φ`:

* `dddf_thm20_psi_of_recursive`: (5.70) ⟹ `Λ_∞(ψ, p/2) < ∞` and
  `sup_n Var log L^{(n)}_{1,1}(ψ) < ∞` (Step 1 = (5.56) via `L24.ratio_le_of_variance`
  (Lemma 22), Step 5 via `T20.t20_step5`, Lemma 24 for (5.72)).
* `LambdaN_le_LambdaNPsi`: `Λ_n(φ, p) ≤ C Λ_n(ψ, p/2)` uniformly in `n` (DDDF l. 1212,
  "thus `Λ_∞(φ,p) < ∞`"; the comparison (2.27) = `eq:RatiosPsiPhi`, l. 478–487, in the direction
  `φ ≤ ψ`, proved like (2.27) from Prop 5 through `ellQ_phi_le_of_tail`/`ellQ_psi_le_of_tail`).
* `dddf_thm20_of_recursive`: all three conclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

namespace T20

/-- `ℓ(q) > 0` for the crossing length of `[0,1]²` (the length is everywhere positive). -/
lemma ellQ_pos [IsProbabilityMeasure P] {ξ : ℝ} {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < ellQ ξ P Y (rectAB 1 1) q := by
  have hLpos : ∀ ω, 0 < lenObs ξ Y (rectAB 1 1) ω := lenObs_pos hYc _ (by simp [rectAB])
    (by simp [rectAB]) (by simp [rectAB, MarkedRect.crossWidth])
  have hlo := prob_le_ellQ (ξ := ξ) (P := P) hYc hYm (rectAB 1 1) hq0 hq1
  by_contra hneg
  push_neg at hneg
  have : {ω | lenObs ξ Y (rectAB 1 1) ω ≤ ellQ ξ P Y (rectAB 1 1) q} = ∅ :=
    eq_empty_of_forall_notMem fun ω h => absurd ((hLpos ω).trans_le h) (not_lt.2 hneg)
  rw [this, measure_empty] at hlo
  exact absurd hlo (not_le.2 hq0)

/-- `ℓ(q) ≤ ℓ̄(q)` for `q ≤ 1/2`. -/
lemma ellQ_le_ellBarQ [IsProbabilityMeasure P] {ξ : ℝ} {Y : ℂ → Ω → ℝ} {q : ℝ} (hq0 : 0 < q) (hq : q < 1 / 2) :
    ellQ ξ P Y (rectAB 1 1) (ENNReal.ofReal q) ≤ ellBarQ ξ P Y (rectAB 1 1) (ENNReal.ofReal q) := by
  have hq0' : 0 < ENNReal.ofReal q := ENNReal.ofReal_pos.2 hq0
  refine ellQ_mono _ hq0' (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0'.ne') ?_
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hq0.le]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- `Λ_n = max_{k ≤ n} r_k` is monotone with `Λ_{n+1} = Λ_n ∨ r_{n+1}`. -/
lemma sup'_range_succ (r : ℕ → ℝ) (n : ℕ) :
    (Finset.range (n + 2)).sup' Finset.nonempty_range_add_one r =
      max ((Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r) (r (n + 1)) := by
  refine le_antisymm (Finset.sup'_le _ _ fun k hk => ?_) (max_le ?_ ?_)
  · rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hk) with h | h
    · exact (Finset.le_sup' r (Finset.mem_range.2 h)).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _
  · exact Finset.sup'_le _ _ fun k hk =>
      Finset.le_sup' r (Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega))
  · exact Finset.le_sup' r (Finset.mem_range.2 (by omega))

lemma monotone_sup'_range (r : ℕ → ℝ) :
    Monotone fun n => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r := by
  intro m n hmn
  exact Finset.sup'_le _ _ fun k hk =>
    Finset.le_sup' r (Finset.mem_range.2 (by have := Finset.mem_range.1 hk; omega))

end T20

open T20 L24

/-- **DDDF Theorem 20, Steps 1 and 5** (l. 1072–1076, 1176–1213): the recursive inequality
(5.70) (output of Steps 2–4) implies `Λ_∞(ψ, p/2) = sup_n Λ_n(ψ, p/2) < ∞` and
`sup_n Var log L^{(n)}_{1,1}(ψ) < ∞`. -/
theorem dddf_thm20_psi_of_recursive (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2)
    (hrec : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      Var[logLenPsi ξ Q W P n; P] ≤
        C₁ * K + exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2) :
    (∃ B : ℝ, ∀ n, LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) ≤ B) ∧
      ∃ B : ℝ, ∀ n, Var[logLenPsi ξ Q W P n; P] ≤ B := by
  have := hW.isProbabilityMeasure
  obtain ⟨C₁, C₂, hC₁, hC₂, hrec⟩ := hrec
  have hq0 : 0 < p / 2 := by positivity
  have hq : p / 2 < 1 / 2 := by linarith
  set q := ENNReal.ofReal (p / 2)
  set r : ℕ → ℝ := fun k =>
    ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) q / ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) q
  set V : ℕ → ℝ := fun n => Var[logLenPsi ξ Q W P n; P]
  have hΛdef : ∀ n, LambdaNPsi ξ Q W P n q =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one r := fun n => rfl
  obtain ⟨Cv, hCv0, hCv⟩ := psi_memLp_variance hW Q ξ
  obtain ⟨Ct, hCt⟩ := dddf_lemma24 hW Q ξ hq0 hq
  -- Step 1 (5.56): `r_n ≤ e^{C_p √V_n}` with `C_p = √2 / (p/2)`
  have hr : ∀ n, r n ≤ exp (√2 / (p / 2) * √(V n)) := by
    intro n
    have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    refine (L24.ratio_le_of_variance hv.cont hv.meas (hCv n).1 hq0 hq).trans_eq ?_
    congr 1
    rw [Real.sqrt_mul (by norm_num)]
    have hVn : V n = Var[fun ω => Real.log (lenObs ξ (psiMN Q W P 0 n) (rectAB 1 1) ω); P] := rfl
    rw [hVn]
    ring
  have hnonneg : ∀ n, 0 ≤ LambdaNPsi ξ Q W P n q := by
    intro n
    have hv := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le 0)
    have h0 := ellQ_pos (P := P) (ξ := ξ) hv.cont hv.meas (ENNReal.ofReal_pos.2 hq0)
      (by rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith))
    refine le_trans ?_ (Finset.le_sup' r (Finset.mem_range.2 (Nat.succ_pos n)))
    exact div_nonneg (h0.le.trans (ellQ_le_ellBarQ hq0 hq)) h0.le
  obtain ⟨K, hK1, B, -, hB, hVK⟩ := t20_step5 (r := r) (V := V)
    (Λ := fun n => LambdaNPsi ξ Q W P n q) hC₁ hC₂ (by positivity) hnonneg
    (by simpa only [hΛdef] using monotone_sup'_range r)
    (fun n => by simp only [hΛdef]; rw [sup'_range_succ])
    hr hrec (fun n hn => hCt n hn)
  refine ⟨⟨B, hB⟩, max (2 * C₁ * K) (Cv * K), fun n => ?_⟩
  rcases le_or_gt K n with h | h
  · exact (hVK n h).trans (le_max_left _ _)
  · refine ((hCv n).2.trans ?_).trans (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left (max_le (by exact_mod_cast h.le) (by exact_mod_cast hK1))
      hCv0


/-- **`Λ_n(φ, p) ≤ C Λ_n(ψ, p/2)` uniformly in `n`** (DDDF l. 1212: "`Λ_∞(ψ,p/2) < ∞` thus
`Λ_∞(φ,p) < ∞`"; the `φ ↔ ψ` mirror of (2.27) = `eq:RatiosPsiPhi`, l. 478–487, from Prop 5 through
the tail of `X_{1,1}`). -/
theorem LambdaN_le_LambdaNPsi (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤
      C * LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, c, hC, hc, htail⟩ := exists_tail_XAB_unif hW Q 1
  have hq0 : 0 < p / 2 := by positivity
  set M : ℝ := √(max 1 (Real.log (C / (p / 2))) / c)
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hε := htail 1 1 le_rfl le_rfl (p / 2) hq0
  set e := exp (|ξ| * M) with he
  have he0 : 0 < e := exp_pos _
  have hqq : ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_add hq0.le hq0.le]; congr 1; ring
  have hp1 : ENNReal.ofReal p < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have hbar : 1 - ENNReal.ofReal p + ENNReal.ofReal (p / 2) = 1 - ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hp0.le, ← ENNReal.ofReal_add (by linarith)
      hq0.le, ← ENNReal.ofReal_sub _ hq0.le]
    congr 1; ring
  have hq1 : ENNReal.ofReal (p / 2) < 1 := by
    rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  have hq0' : 0 < ENNReal.ofReal (p / 2) := ENNReal.ofReal_pos.2 hq0
  have hp0' : 0 < ENNReal.ofReal p := ENNReal.ofReal_pos.2 hp0
  have hk : ∀ n, ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p) ≤
      e ^ 2 * (ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
        ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))) := by
    intro n
    have hvφ := isPhiVersion_phiMN hW (Nat.zero_le n)
    have hvψ := isPsiVersion_psiMN (Q := Q) hW (Nat.zero_le n)
    -- `ℓ_n(ψ, p/2) ≤ e ℓ_n(φ, p)`
    have h1 := ellQ_psi_le_of_tail hW Q (ξ := ξ) zero_le_one zero_le_one hM0 hε hq0'
      (by rw [hqq]; exact hp1) n
    rw [hqq] at h1
    -- `ℓ̄_n(φ, p) ≤ e ℓ̄_n(ψ, p/2)`
    have h2 := ellQ_phi_le_of_tail hW Q (ξ := ξ) zero_le_one zero_le_one hM0 hε
      (p := 1 - ENNReal.ofReal p) (tsub_pos_of_lt hp1)
      (by rw [hbar]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hq0'.ne') n
    rw [hbar] at h2
    have hψ0 := ellQ_pos (P := P) (ξ := ξ) hvψ.cont hvψ.meas hq0' hq1
    have hψb : 0 ≤ ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2)) :=
      hψ0.le.trans (ellQ_le_ellBarQ hq0 (by linarith))
    set a := ellBarQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))
    set b := ellQ ξ P (psiMN Q W P 0 n) (rectAB 1 1) (ENNReal.ofReal (p / 2))
    have h2' : ellBarN ξ W P n (ENNReal.ofReal p) ≤ e * a := h2
    have h1' : e⁻¹ * b ≤ ellN ξ W P n (ENNReal.ofReal p) := by
      rw [inv_mul_le_iff₀ he0]; exact h1
    calc ellBarN ξ W P n (ENNReal.ofReal p) / ellN ξ W P n (ENNReal.ofReal p)
        ≤ (e * a) / (e⁻¹ * b) := div_le_div₀ (by positivity) h2' (by positivity) h1'
      _ = e ^ 2 * (a / b) := by field_simp
  refine ⟨e ^ 2, by positivity, fun n => ?_⟩
  refine Finset.sup'_le _ _ fun k hk' => (hk k).trans ?_
  exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun k =>
    ellBarQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2)) /
      ellQ ξ P (psiMN Q W P 0 k) (rectAB 1 1) (ENNReal.ofReal (p / 2))) hk') (by positivity)


/-- **DDDF Theorem 20 from (5.70)**: the recursive inequality of Steps 2–4 gives
`Λ_∞(φ, p) < ∞`, `Λ_∞(ψ, p/2) < ∞` and `sup_n Var log L^{(n)}_{1,1}(ψ) < ∞` (DDDF l. 1185,
1212). -/
theorem dddf_thm20_of_recursive (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ) {p : ℝ}
    (hp0 : 0 < p) (hp : p < 1 / 2)
    (hrec : ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
      Var[logLenPsi ξ Q W P n; P] ≤
        C₁ * K + exp (-(C₂ * K)) * LambdaNPsi ξ Q W P (n - K) (ENNReal.ofReal (p / 2)) ^ 2) :
    (∃ B : ℝ, ∀ n, LambdaN ξ W P n (ENNReal.ofReal p) ≤ B) ∧
      (∃ B : ℝ, ∀ n, LambdaNPsi ξ Q W P n (ENNReal.ofReal (p / 2)) ≤ B) ∧
      ∃ B : ℝ, ∀ n, Var[logLenPsi ξ Q W P n; P] ≤ B := by
  obtain ⟨⟨B, hB⟩, hV⟩ := dddf_thm20_psi_of_recursive hW Q ξ hp0 hp hrec
  obtain ⟨C, hC, hΛ⟩ := LambdaN_le_LambdaNPsi hW Q ξ hp0 hp
  exact ⟨⟨C * B, fun n => (hΛ n).trans (mul_le_mul_of_nonneg_left (hB n) hC.le)⟩, ⟨B, hB⟩, hV⟩

end DDDF
end LQGMetric
