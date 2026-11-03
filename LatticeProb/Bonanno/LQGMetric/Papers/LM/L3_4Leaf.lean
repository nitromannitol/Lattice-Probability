/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_4Leaf at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4Iter
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InAsm

/-!
# LM Lemma 3.4 (= (3.10)) from the scale-domination input

Source: LM arXiv:1905.00379, Lemma 3.4 (l. 696–706); MQ arXiv:1812.03913 (`lqg_geodesics.tex`),
Prop 4.3, Lemma 4.4, Remark (eq. `(zero-boundary)`) and the proof of Prop 4.3 (l. 613–733).

* `LMScaleDomLeaf` — the GFF input of MQ's proof (exact remaining statement): there are
  nonnegative variables `W_j` (MQ: `W_0` = oscillation of the harmonic part `𝔥^{r_0}` on a ball
  `B_{s'' r_0}`, `W_{j+1}` = oscillation of the harmonic part at scale `r_{j+1}` of the zero-boundary
  GFF `h̊^{r_j}`, i.e. of `𝔥^{r_{j+1}} − 𝔥^{r_j}`), adapted to a filtration (MQ: `𝓕_{r_j}`),
  `W_{j+1}` independent of `𝓕_{r_j}` (MQ l. 700: "`𝔥̃_{0,r_ℓ}` is independent of `𝓕_{0,1}`"),
  with a uniform exponential moment (MQ Lemma 4.4 and Remark eq. `(zero-boundary)`: Gaussian tail),
  such that the oscillation at a bad scale `k` is dominated by `C ∑_{j ≤ k} q^{k-j} W_j`
  (MQ l. 677–681: derivative estimate for harmonic functions, `q = s₁`).
* `lmGoodScaleLeaf_of_dom` — `LMGoodScaleLeaf` from it, via `count_good_tail`.
* `lmLem3_1a_of_dom`, `lmLem3_1b_of_dom` — LM Lemma 3.1 from `LMScaleDomLeaf`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- **The GFF input of MQ Prop 4.3** (MQ l. 664–700, Lemma 4.4, Remark eq. `(zero-boundary)`) for
the scales `r_k` of LM Lemma 3.4: adapted, independent increments `W_j ≥ 0` with a uniform
exponential moment dominating the oscillation `𝔐^{r_k}_{s' r_k}` (read off by `lmGood`) linearly
with geometric weights. -/
def LMScaleDomLeaf (s₁ s₂ : ℝ) : Prop :=
  ∃ C q A : ℝ, 0 < C ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ A ∧
    ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
      (∀ k, r (k + 1) / r k ≤ s₁) →
      ∃ (F : ℕ → MeasurableSpace Ω) (W : ℕ → Ω → ℝ), Monotone F ∧ (∀ j, F j ≤ mΩ) ∧
        (∀ j ω, 0 ≤ W j ω) ∧ (∀ j, Measurable[F j] (W j)) ∧
        (∀ j, Indep (MeasurableSpace.comap (W (j + 1)) inferInstance) (F j) P) ∧
        (∀ j, ∫⁻ ω, ENNReal.ofReal (Real.exp (W j ω)) ∂P ≤ ENNReal.ofReal A) ∧
        ∀ hh0 hz G : ℕ → Ω → DistC, (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) →
          ∀ k, 1 ≤ k → ∀ M : ℝ, ∀ᵐ ω ∂P,
            ω ∉ lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2) M h (G k) (r k) →
            M < C * ∑ j ∈ range (k + 1), q ^ (k - j) * W j ω

/-- **LM Lemma 3.4** ((3.10)) from the GFF input `LMScaleDomLeaf`. -/
theorem lmGoodScaleLeaf_of_dom {s₁ s₂ : ℝ} (hD : LMScaleDomLeaf s₁ s₂) :
    LMGoodScaleLeaf s₁ s₂ := by
  obtain ⟨C, q, A, hC, hq0, hq, hA0, HD⟩ := hD
  set A₁ := max A 1
  have hA₁ : 1 ≤ A₁ := le_max_right _ _
  have hA₁0 : 0 < A₁ := one_pos.trans_le hA₁
  have hlog : 0 ≤ Real.log A₁ := Real.log_nonneg hA₁
  refine ⟨fun a b => C * (a + Real.log A₁) / ((1 - q) * (1 - b)), fun _ _ => A₁,
    fun _ _ => hA₁0, ?_⟩
  intro Ω _ P _ h hh r hr0 hrA hrs hh0 hz G hrep a ha b hb0 hb1 K
  obtain ⟨F, W, hF, hFle, hW0, hWm, hWi, hA, hdom⟩ := HD P h hh r hr0 hrA hrs
  have hq1 : 0 < 1 - q := by linarith
  have hb : 0 < 1 - b := by linarith
  have hM : 0 ≤ C * (a + Real.log A₁) / ((1 - q) * (1 - b)) := by positivity
  have H := count_good_tail P F hF hFle W hW0 hWm hWi hA₁0.le
    (fun j => (hA j).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))) (b := b) hq0 hq hC hM _
    (fun k hk => hdom hh0 hz G hrep k hk _) K
  refine H.trans (le_of_eq ?_)
  have hθ : (1 - q) * (1 - b) * (C * (a + Real.log A₁) / ((1 - q) * (1 - b))) / C * K =
      (a + Real.log A₁) * K := by
    field_simp
  rw [hθ, pow_succ, mul_comm (A₁ ^ K) A₁, mul_assoc]
  congr 1
  rw [← Real.exp_log hA₁0, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_log hA₁0]
  congr 1; ring

/-- **LM Lemma 3.1 (1)** (`N = 0`) from the GFF input of MQ Prop 4.3. -/
theorem lmLem3_1a_of_dom
    (hD : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMScaleDomLeaf s₁ s₂) : LMLem3_1a :=
  lmLem3_1a_of_leaf fun s₁ s₂ h1 h2 h3 => lmGoodScaleLeaf_of_dom (hD s₁ s₂ h1 h2 h3)

end LQGMetric.LM
